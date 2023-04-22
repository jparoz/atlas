use std::{
    fmt::{self, Display},
    iter,
};

use im::HashMap;
use itertools::Itertools;
use nonempty::{nonempty, NonEmpty};

use crate::typecheck::{ExpList, TypeVar, Typechecker};

/// Represents the type environment at a particular point in a chunk.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    /// The stack of subscopes.
    /// When a block is entered,
    /// a new subscope should be pushed;
    /// when a block is closed,
    /// the corresponding subscope should be popped.
    // @Todo @Fixme: This isn't a persistent data structure any more!
    // Probably want to change this to be an im::Vector instead of a NonEmpty
    subscopes: NonEmpty<SubScope>,

    /// The globals assigned by the current chunk.
    globals_assigned: HashMap<String, TypeVar>,

    /// The globals assumed to exist by the current chunk.
    /// That is,
    /// any variables free in the chunk,
    /// any global variable accesses.
    globals_assumed: HashMap<String, TypeVar>,
}

/// Represents one layer of the current lexical scope,
/// e.g. the scope inside a function or for-loop.
/// Includes an optional [`ExpList`] determining if the subscope represents a variadic function.
#[derive(Debug, Default, Clone)]
pub struct SubScope {
    variables: HashMap<String, TypeVar>,
    varargs: Option<ExpList>,
}

impl Scope {
    /// Makes a new top-level scope.
    /// This includes a varargs expression representing command line arguments (or similar).
    pub fn new_top_level() -> Self {
        Scope {
            subscopes: nonempty![SubScope {
                varargs: Some(ExpList::default()),
                ..SubScope::default()
            }],
            globals_assigned: HashMap::new(),
            globals_assumed: HashMap::new(),
        }
    }

    /// Opens a new Lua scope;
    /// i.e. pushes a new subscope to the stack.
    pub fn open_scope(&mut self) {
        self.subscopes.push(SubScope::default());
    }

    /// Closes the current Lua scope;
    /// i.e. pops the top subscope from the stack.
    pub fn close_scope(&mut self) {
        self.subscopes.pop();
    }

    /// Adds a new variable to the scope,
    /// as in `local foo`.
    pub fn declare_local(&mut self, name: String, typevar: TypeVar) {
        self.subscopes.last_mut().variables.insert(name, typevar);
    }

    /// Adds a new global variable to the scope,
    /// as in `foo = nil`.
    pub fn declare_global(&mut self, name: String, typevar: TypeVar) {
        // @Todo: maybe handle this differently?
        assert!(self.globals_assigned.insert(name, typevar).is_none());
    }

    /// Assumes that a global variable should exist.
    pub fn assume_global(&mut self, name: String, typevar: TypeVar) {
        // @Todo: maybe handle this differently?
        assert!(self.globals_assumed.insert(name, typevar).is_none());
    }

    /// Returns true if the given variable name is known to be in scope,
    /// either local or global.
    pub fn contains_key(&self, name: &str) -> bool {
        self.subscopes
            .iter()
            .any(|s| s.variables.contains_key(name))
            || self.globals_assigned.contains_key(name)
            || self.globals_assumed.contains_key(name)
    }

    /// If the given name is in the local scope,
    /// or if it's a previously-used global,
    /// returns a reference to its current constraints.
    pub fn get(&self, name: &str) -> Option<TypeVar> {
        self.subscopes
            .iter()
            .rev()
            .find_map(|s| s.variables.get(name))
            .or_else(|| self.globals_assigned.get(name))
            .or_else(|| self.globals_assumed.get(name))
            .copied()
    }

    /// Inserts a name & typevar pair into the scope,
    /// overwriting the existing typevar for the name (if there is one),
    /// or adding a new global (if there isn't).
    pub fn insert(&mut self, name: String, typevar: TypeVar) -> Option<TypeVar> {
        if let Some(existing) = self
            .subscopes
            .tail
            .iter_mut()
            .rev()
            .chain(iter::once(&mut self.subscopes.head))
            .find_map(|s| s.variables.get_mut(&name))
            .or_else(|| self.globals_assigned.get_mut(&name))
            .or_else(|| self.globals_assumed.get_mut(&name))
        {
            let res = *existing;
            *existing = typevar;
            Some(res)
        } else {
            self.declare_global(name, typevar);
            None
        }
    }

    /// If the given name is in scope,
    /// removes it from the innermost subscope,
    /// and returns the constraints.
    pub fn remove(&mut self, name: &str) -> Option<TypeVar> {
        // self.subscopes.iter_mut().rev().find_map(|s| s.remove(name))
        self.subscopes
            .tail
            .iter_mut()
            .rev()
            .chain(iter::once(&mut self.subscopes.head))
            .find_map(|s| s.variables.remove(name))
    }

    /// If the current subscope is from a variadic function (or the top level scope),
    /// return a mutable reference to the varargs explist.
    /// Otherwise, return `None`.
    pub fn varargs_mut(&mut self) -> Option<&mut ExpList> {
        self.subscopes.last_mut().varargs.as_mut()
    }
}

impl Extend<(String, TypeVar)> for Scope {
    fn extend<T: IntoIterator<Item = (String, TypeVar)>>(&mut self, iter: T) {
        self.subscopes.last_mut().variables.extend(iter)
    }
}

impl Typechecker {
    pub fn format_scope(&self, scope: &Scope) -> String {
        format!(
            "{{{}}}",
            scope
                .globals_assigned
                .iter()
                .map(|(name, typevar)| format!(
                    "{name}: {}",
                    self.format_constraint_set(self.get(*typevar))
                ))
                .chain(scope.globals_assumed.iter().map(|(name, typevar)| format!(
                    "(assumed) {name}: {}",
                    self.format_constraint_set(self.get(*typevar))
                )))
                .chain(scope.subscopes.iter().flat_map(|sub| &sub.variables).map(
                    |(name, typevar)| format!(
                        "local {name}: {}",
                        self.format_constraint_set(self.get(*typevar))
                    )
                ))
                .join(", ")
        )
    }
}
