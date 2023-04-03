use std::io;

use crate::typecheck::FileID;

/// Reasons that including a file might fail.
#[derive(Debug, thiserror::Error)]
pub enum IncludeError {
    #[error("IO error: {0}")]
    IO(#[from] io::Error),

    #[error("Parsing timed out")]
    ParseTimeout,
}

/// Reasons that a type query might fail.
#[derive(Debug, thiserror::Error)]
pub enum QueryError {
    #[error("Tried to query a file which was not included into the context: {0}")]
    FileNotIncluded(FileID),

    #[error("Couldn't find point {0} in file {1}")]
    PointNotFound(tree_sitter::Point, FileID),

    #[error("Couldn't find any typeable node at point {0} in file {1}")]
    NotTypeable(tree_sitter::Point, FileID),

    #[error("Failed to typecheck at point {0} in file {1}")]
    TypecheckingIncomplete(tree_sitter::Point, FileID),
}
