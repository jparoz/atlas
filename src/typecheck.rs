use std::collections::HashMap;
use std::fmt::{self, Display};
use std::path::Path;
use std::{fs, io};

use tree_sitter::{Node, Parser};

use crate::lua_file::{Environment, LuaFile};

/// A struct representing a typechecking context.
/// That is, all the files containing code to be typechecked,
/// and all needed state and bookkeeping to return useful type information.
pub struct Typechecker {
    parser: Parser,
    files: HashMap<FileID, LuaFile>,
}

impl Typechecker {
    /// Makes a new typechecking context.
    pub fn new() -> Self {
        let mut parser = Parser::new();
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

    /// Given a file, line (0-based), and column (0-based),
    /// return the type of the AST node at that point.
    pub fn type_at_point(&self, id: FileID, row: usize, column: usize) -> Result<Type, QueryError> {
        let LuaFile { tree, src, .. } = self
            .files
            .get(&id)
            .ok_or_else(|| QueryError::FileNotIncluded(id.clone()))?;
        let root = tree.root_node();

        let point = tree_sitter::Point { row, column };

        let smallest_node = root
            .named_descendant_for_point_range(point, point)
            .ok_or_else(|| QueryError::PointNotFound(point, id.clone()))?;
        let node_type = smallest_node.kind();
        log::trace!("Found smallest node at point {point}, node type `{node_type}`");

        log::trace!("Searching upwards for a typeable node...");
        let mut the_node = Some(smallest_node);
        while let Some(node) = the_node {
            let node_type = node.kind();
            log::trace!("Checking if node type {node_type} is typeable...");
            if is_typeable(node) {
                log::trace!(
                    "Found typeable node, node type `{node_type}`:\n{}",
                    &src[node.byte_range()]
                );

                return Ok(self.type_of_node(node));
            }
            the_node = node.parent();
        }

        log::error!("Couldn't find a typeable parent node!");
        Err(QueryError::NotTypeable(point, id))
    }

    /// Find the type of a node.
    fn type_of_node(&self, node: Node) -> Type {
        debug_assert!(is_typeable(node));
        match node.kind() {
            // Primitive types
            "nil" => Type::Nil,
            "true" | "false" => Type::Boolean,
            "number" => Type::Number,
            "string" => Type::String,

            // Tables
            "table" => todo!(),

            // Other expressions
            "expression" | "variable" | "binary_expression" => todo!(),

            // Assignments
            "variable_assignment" | "local_variable_declaration" => todo!(),

            // Functions
            "function_definition_statement"
            | "local_function_definition_statement"
            | "function_definition" => self.type_of_function_body(node),

            _ => unreachable!("previously asserted that this node `is_typeable`"),
        }
    }

    /// Find the type of a function body.
    fn type_of_function_body(&self, node: Node) -> Type {
        log::trace!("Finding Lua type of node with node type: {}", node.kind());

        let params = node.child_by_field_name("parameters").unwrap();
        let body = node.child_by_field_name("body").unwrap();

        log::debug!("params: {}", params.to_sexp());
        log::debug!("body: {}", body.to_sexp());
        todo!()
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

/// Takes a tree-sitter node,
/// and returns whether or not the node represents a Lua value which has a type.
fn is_typeable(node: Node) -> bool {
    matches!(
        node.kind(),
        "function_definition_statement"
            | "local_function_definition_statement"
            | "variable_assignment"
            | "local_variable_declaration"
            | "expression"
            | "binary_expression"
            | "variable"
            | "nil"
            | "true"
            | "false"
            | "number"
            | "string"
            | "function_definition"
            | "table"
    )
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
