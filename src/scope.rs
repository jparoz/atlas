use std::{
    fmt::{self, Display},
    iter,
};

use im::HashMap;
use itertools::Itertools;
use nonempty::{nonempty, NonEmpty};

use crate::typecheck::{ConstraintSet, ExpList};

/// Represents the type environment at a particular point in a chunk.
///
/// This is modelled as a stack of subscopes;
/// when a block is entered,
/// a new subscope should be pushed;
/// when a block is closed,
/// the corresponding subscope should be popped.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    // @Todo @Fixme: This isn't a persistent data structure any more!
    // Probably want to change this to be an im::Vector instead of a NonEmpty
    subscopes: NonEmpty<SubScope>,
}

/// Represents one layer of the current lexical scope,
/// e.g. the scope inside a function or for-loop.
/// Includes an optional [`ExpList`] determining if the subscope represents a variadic function.
#[derive(Debug, Default, Clone)]
pub struct SubScope {
    variable_constraints: HashMap<String, ConstraintSet>,
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
    pub fn declare(&mut self, name: String) {
        self.subscopes
            .last_mut()
            .variable_constraints
            .insert(name, ConstraintSet::default());
    }

    /// Adds a new variable to the scope with the type given by the constraint set,
    /// as in `local foo = 123`.
    pub fn declare_and_assign(&mut self, k: String, v: ConstraintSet) -> Option<ConstraintSet> {
        self.subscopes.last_mut().variable_constraints.insert(k, v)
    }

    pub fn contains_key(&self, k: &str) -> bool {
        self.subscopes
            .iter()
            .any(|s| s.variable_constraints.contains_key(k))
    }

    /// If the given name is in scope,
    /// returns a reference to its current constraints.
    pub fn get(&self, name: &str) -> Option<&ConstraintSet> {
        self.subscopes
            .iter()
            .rev()
            .find_map(|s| s.variable_constraints.get(name))
    }

    /// If the given name is in scope,
    /// returns a reference to its current constraints.
    pub fn get_mut(&mut self, name: &str) -> Option<&mut ConstraintSet> {
        // self.subscopes.iter_mut().rev().find_map(|s| s.get_mut(name))
        self.subscopes
            .tail
            .iter_mut()
            .rev()
            .chain(iter::once(&mut self.subscopes.head))
            .find_map(|s| s.variable_constraints.get_mut(name))
    }

    /// If the given name is in scope,
    /// removes it from the innermost subscope,
    /// and returns the constraints.
    pub fn remove(&mut self, name: &str) -> Option<ConstraintSet> {
        // self.subscopes.iter_mut().rev().find_map(|s| s.remove(name))
        self.subscopes
            .tail
            .iter_mut()
            .rev()
            .chain(iter::once(&mut self.subscopes.head))
            .find_map(|s| s.variable_constraints.remove(name))
    }

    /// If the current subscope is from a variadic function (or the top level scope),
    /// return a mutable reference to the varargs explist.
    /// Otherwise, return `None`.
    pub fn varargs_mut(&mut self) -> Option<&mut ExpList> {
        self.subscopes.last_mut().varargs.as_mut()
    }
}

impl Extend<String> for Scope {
    fn extend<T: IntoIterator<Item = String>>(&mut self, iter: T) {
        self.subscopes
            .last_mut()
            .variable_constraints
            .extend(iter.into_iter().zip(iter::repeat(ConstraintSet::default())))
    }
}

impl Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.subscopes
                .iter()
                .flat_map(|sub| &sub.variable_constraints)
                .map(|(name, constraints)| format!("{name} : {constraints}"))
                .join(", ")
        )
    }
}
