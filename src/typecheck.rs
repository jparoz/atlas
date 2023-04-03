use std::collections::HashMap;
use std::fmt::{self, Display};
use std::path::Path;
use std::{fs, io};

use crate::lua_file::{Environment, LuaFile};

/// A struct representing a typechecking context.
/// That is, all the files containing code to be typechecked,
/// and all needed state and bookkeeping to return useful type information.
pub struct Typechecker {
    parser: tree_sitter::Parser,
    files: HashMap<FileID, LuaFile>,
}

impl Typechecker {
    /// Makes a new typechecking context.
    pub fn new() -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(tree_sitter_lua::language())
            .expect("Error loading Lua grammar");

        let files = HashMap::new();

        Typechecker { parser, files }
    }

    /// Includes a Lua file into the typechecking context.
    pub fn include<P: AsRef<Path>>(&mut self, path: &P) -> Result<(), IncludeError> {
        let id = FileID::from(&path);

        let contents = fs::read_to_string(path)?;
        let tree = self
            .parser
            .parse(&contents, None)
            .ok_or(IncludeError::ParseTimeout)?;

        if tree.root_node().has_error() {
            // @Todo: something more? Print the node/s containing the error/s?
            log::warn!("Syntax error");
        }

        log::debug!("parsed:\n{}", tree.root_node().to_sexp());

        let file = LuaFile::new(tree, contents);
        // @Cleanup: use a helper function instead of using Environment directly
        let scopes = Environment::new(&file).scopes;
        log::debug!("type environment: {:#?}", scopes);

        // @Todo: check if we overwrote an entry here
        self.files.insert(id, file);

        Ok(())
    }
}

impl Default for Typechecker {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Typechecker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Typechecker")
            .field(
                "files",
                &self.files.keys().map(|id| &id.0).collect::<Vec<_>>(),
            )
            .finish_non_exhaustive()
    }
}

/// An identifier used to refer to a particular file.
// @Note: Implementation will almost certainly change.
// Currently it's just the filename given at the CLI as a string.
// See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocumentIdentifier
#[derive(Debug, Default, PartialEq, Eq, Hash, Clone)]
pub struct FileID(String);

impl Display for FileID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<P: AsRef<Path>> From<&P> for FileID {
    fn from(path: &P) -> Self {
        FileID(path.as_ref().to_string_lossy().to_string())
    }
}

#[derive(Debug, Default, Clone)]
pub enum Type {
    // Basic scalar types
    Nil,
    Boolean,
    Number,
    String,
    LightUserdata,

    // Parametric types
    // @Todo @Fixme @XXX: include some parameters in these lol
    Function,
    Thread,
    Table,

    // Other
    FullUserdata,

    // Pseudo-types
    Uninitialized,
    #[default]
    Unknown,
}

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
