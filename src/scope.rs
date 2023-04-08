use std::{
    fmt::{self, Display},
    iter,
};

use im::HashMap;
use itertools::Itertools;

use crate::typecheck::ConstraintSet;

/// Represents the type environment at a particular point in a chunk.
#[derive(Debug, Default, Clone)]
pub struct Scope {
    names: HashMap<String, ConstraintSet>,
}

impl Scope {
    pub fn insert(&mut self, k: String, v: ConstraintSet) -> Option<ConstraintSet> {
        self.names.insert(k, v)
    }

    pub fn contains_key(&self, k: &str) -> bool {
        self.names.contains_key(k)
    }

    pub fn get(&self, key: &str) -> Option<&ConstraintSet> {
        self.names.get(key)
    }

    pub fn get_mut(&mut self, key: &str) -> Option<&mut ConstraintSet> {
        self.names.get_mut(key)
    }
}

impl Extend<String> for Scope {
    fn extend<T: IntoIterator<Item = String>>(&mut self, iter: T) {
        self.names
            .extend(iter.into_iter().zip(iter::repeat(ConstraintSet::default())))
    }
}

impl Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.names
                .iter()
                .map(|(name, constraints)| format!("{name} : {constraints}"))
                .join(", ")
        )
    }
}
