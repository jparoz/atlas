use std::{
    fmt::{self, Display},
    iter,
};

use im::HashMap;
use itertools::Itertools;
use nonempty::NonEmpty;

use crate::typecheck::ConstraintSet;

/// Represents the type environment at a particular point in a chunk.
///
/// This is modelled as a stack of subscopes;
/// when a block is entered,
/// a new subscope should be pushed;
/// when a block is closed,
/// the corresponding subscope should be popped.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    subscopes: NonEmpty<HashMap<String, ConstraintSet>>,
}

impl Scope {
    /// Opens a new Lua scope;
    /// i.e. pushes a new subscope to the stack.
    pub fn open_scope(&mut self) {
        self.subscopes.push(HashMap::default());
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
            .insert(name, ConstraintSet::default());
    }

    /// Adds a new variable to the scope with the type given by the constraint set,
    /// as in `local foo = 123`.
    pub fn declare_and_assign(&mut self, k: String, v: ConstraintSet) -> Option<ConstraintSet> {
        self.subscopes.last_mut().insert(k, v)
    }

    pub fn contains_key(&self, k: &str) -> bool {
        self.subscopes.iter().any(|s| s.contains_key(k))
    }

    /// If the given name is in scope,
    /// returns a reference to its current constraints.
    pub fn get(&self, name: &str) -> Option<&ConstraintSet> {
        self.subscopes.iter().rev().find_map(|s| s.get(name))
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
            .find_map(|s| s.get_mut(name))
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
            .find_map(|s| s.remove(name))
    }
}

impl Extend<String> for Scope {
    fn extend<T: IntoIterator<Item = String>>(&mut self, iter: T) {
        self.subscopes
            .last_mut()
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
                .flatten()
                .map(|(name, constraints)| format!("{name} : {constraints}"))
                .join(", ")
        )
    }
}
