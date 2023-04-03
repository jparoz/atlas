use std::fmt::{self, Display};
use std::fs;
use std::iter;
use std::path::Path;

use im::hashmap::HashMap;
use tree_sitter::{Node, Tree};

use crate::error::IncludeError;

/// A struct representing a typechecking context.
/// That is, all the files containing code to be typechecked,
/// and all needed state and bookkeeping to return useful type information.
pub struct Typechecker {
    parser: tree_sitter::Parser,
    files: HashMap<FileID, (tree_sitter::Tree, TypedFile)>,
}

impl Typechecker {
    /// Makes a new typechecking context.
    pub fn new() -> Self {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(tree_sitter_lua::language())
            .expect("Error loading Lua grammar");

        Typechecker {
            parser,
            files: HashMap::new(),
        }
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

        let file_env = TypedFile::new(&tree, contents);

        // @Todo: check if we overwrote an entry here
        self.files.insert(id, (tree, file_env));

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

/// Manages the typechecking of a single Lua file.
#[derive(Debug, Clone)]
pub struct TypedFile {
    /// The contents of the file as it was read from disk.
    /// This is the string which was given to the tree-sitter parser to produce the `Tree`.
    pub src: String,

    /// The current local scope.
    local_scope: HashMap<String, Type>,

    /// A map from a tree-sitter [`Node`]'s ID
    /// to the type environment at that node.
    /// The IDs used are from the tree-sitter [`Tree`] given to [`TypedFile::new`].
    pub scopes: HashMap<usize, HashMap<String, Type>>,
}

impl TypedFile {
    /// Builds the type environment at each statement in the given file.
    pub fn new(tree: &Tree, src: String) -> Self {
        let mut env = TypedFile {
            src,
            local_scope: HashMap::new(),
            scopes: HashMap::new(),
        };
        env.typecheck_block(tree.root_node());
        env
    }

    /// Builds the type environment in a block.
    /// Returns the return type of the block.
    fn typecheck_block(&mut self, block: Node) -> Type {
        // For each statement,
        // build the type environment at that point.
        let mut cursor = block.walk();
        for statement in block.children(&mut cursor) {
            // Save the current state of the type environment.
            log::trace!("local scope:\n{:?}", self.local_scope);
            self.scopes.insert(statement.id(), self.local_scope.clone());

            log::trace!(
                "Processing statement (kind == {kind}):\n{src}",
                kind = statement.kind(),
                src = &self.src[statement.byte_range()]
            );

            match statement.kind() {
                // @Todo: global environment
                // @Note: This could either be assigning a global,
                // or modifying a previously-declared local.
                "variable_assignment" => {
                    let var_list = statement.named_child(0).expect("non-optional");
                    let expr_list = statement.named_child(1).expect("non-optional");
                    self.assign(var_list, expr_list);
                }

                "local_variable_declaration" => {
                    let var_list = statement.named_child(0).expect("non-optional");
                    self.declare_local(var_list);
                    if let Some(expr_list) = statement.named_child(1) {
                        self.assign(var_list, expr_list);
                    }
                }

                "do_statement" => {
                    let saved_scope = self.local_scope.clone();

                    if let Some(body) = statement.child_by_field_name("body") {
                        self.typecheck_block(body);
                    }

                    self.local_scope = saved_scope;
                }

                "while_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // while
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_type = self.typecheck_expression(condition);
                    // @Todo: something with condition_type

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.typecheck_block(body);
                    }

                    self.local_scope = saved_scope;
                }

                "repeat_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // repeat
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.typecheck_block(body);
                    }

                    // until
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_type = self.typecheck_expression(condition);
                    // @Todo: something with condition_type

                    self.local_scope = saved_scope;
                }

                // for name = start, end [, step] do [body] end
                "for_numeric_statement" => {
                    let saved_scope = self.local_scope.clone();

                    let name = statement.child_by_field_name("name").expect("non-optional");
                    let name_str = self.src[name.byte_range()].to_string();

                    // @Todo: the numerical for converts its arguments to numbers.
                    // See section 3.3.5 of Lua 5.4 manual.
                    let start = statement
                        .child_by_field_name("start")
                        .expect("non-optional");
                    let start_type = self.typecheck_expression(start);
                    // @Todo: check that start can be converted to a number

                    // @Note: Numerical for loops convert their arguments to numbers,
                    // so the bound variable is guaranteed to have the type `number`
                    // (either integer or float; see section 3.3.5 of Lua 5.4 manual).
                    self.local_scope.insert(name_str, Type::Number);

                    let end = statement.child_by_field_name("end").expect("non-optional");
                    // @Todo: check that end can be converted to a number

                    if let Some(step) = statement.child_by_field_name("step") {
                        // @Todo: check that step can be converted to a number
                    }

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.typecheck_block(body);
                    }

                    self.local_scope = saved_scope;
                }

                // for left in right do [body] end
                //   left: variable_list
                //   right: expression_list
                "for_generic_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // @XXX @Fixme @Todo:
                    // This is wrong!
                    // It should do the following
                    // (taken fron the Lua 5.4 manual, section 3.3.5):
                    //
                    // The loop starts by evaluating explist to produce four values:
                    // an iterator function,
                    // a state,
                    // an initial value for the control variable,
                    // and a closing value.
                    // Then, at each iteration,
                    // Lua calls the iterator function with two arguments:
                    // the state
                    // and the control variable.
                    // The results from this call are then assigned to the loop variables,
                    // following the rules of multiple assignments.
                    let var_list = statement.child_by_field_name("left").expect("non-optional");
                    let expr_list = statement
                        .child_by_field_name("right")
                        .expect("non-optional");

                    self.assign(var_list, expr_list);

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.typecheck_block(body);
                    }

                    self.local_scope = saved_scope;
                }

                "if_statement" => {
                    // if condition then [consequence]
                    // {elseif condition then [consequence]}
                    // [else [body]]
                    // end

                    // if condition
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_type = self.typecheck_expression(condition);
                    // @Todo: something with condition_type

                    // then [consequence]
                    if let Some(consequence) = statement.child_by_field_name("consequence") {
                        let saved_scope = self.local_scope.clone();
                        self.typecheck_block(consequence);
                        self.local_scope = saved_scope;
                    }

                    let mut cursor = statement.walk();
                    for elseif in statement.children_by_field_name("alternative", &mut cursor) {
                        // {elseif condition then [consequence]}
                        if let Some(condition) = elseif.child_by_field_name("condition") {
                            // elseif condition
                            let condition_type = self.typecheck_expression(condition);
                            // @Todo: something with condition_type

                            // then [consequence]
                            if let Some(consequence) = elseif.child_by_field_name("consequence") {
                                let saved_scope = self.local_scope.clone();
                                self.typecheck_block(consequence);
                                self.local_scope = saved_scope;
                            }
                        // [else [body]]
                        } else if let Some(body) = elseif.child_by_field_name("body") {
                            let saved_scope = self.local_scope.clone();
                            self.typecheck_block(body);
                            self.local_scope = saved_scope;
                        }
                    }
                }

                "function_definition_statement" => {
                    let name = statement.named_child(0).expect("non-optional");
                    let function = statement.named_child(1).expect("non-optional");

                    // @Todo @Fixme: change this to accept table type names,
                    // e.g. `function foo.bar:baz() body end`
                    self.assign(name, function);
                }

                "local_function_definition_statement" => {
                    let name = statement.named_child(0).expect("non-optional");
                    let function = statement.named_child(1).expect("non-optional");

                    self.declare_local(name);
                    self.assign(name, function);
                }

                // Ignore these, as they don't (visibly) change the type environment.
                "shebang" | "call" | "empty_statement" | "label_statement" | "goto_statement" => (),

                // @Todo @Checkme: can/should we do an early return here?
                // Code after a `break` is unreachable,
                // so anything in that unreachable code doesn't really have a type anyway.
                // @Todo: emit a warning about any unreachable code after this break.
                // @XXX @Todo @Fixme
                "break_statement" => return todo!(),

                // @Todo: the type of this return statement
                // is sort of the type of the containing block;
                // We should probably do something with this.
                //
                // @Note: it's actually a syntax error to have code after this return statement;
                // currently we do an early return of this function,
                // but possibly we could still check some stuff after the return statement.
                "return_statement" => {
                    if let Some(exp_list) = statement.child(1) {
                        // @Todo: do something with this
                        log::debug!("returned: `{}`", &self.src[exp_list.byte_range()])
                    }

                    // @XXX
                    return Type::Unknown;
                }

                _ => unreachable!("covered all statement types"),
            }
        }

        // If we're here,
        // we didn't have any return statement;
        // so the return type of the block is nil.
        Type::Nil
    }

    /// Typecheck an expression.
    pub fn typecheck_expression(&self, expr: Node) -> Type {
        log::trace!(
            "Finding type of expression `{}`",
            &self.src[expr.byte_range()]
        );

        match expr.kind() {
            // Primitive types
            "nil" => Type::Nil,
            "true" | "false" => Type::Boolean,
            "number" => Type::Number,
            "string" => Type::String,

            // Variable references
            "variable" => {
                // @Todo: lookup globals as well
                let var_str = &self.src[expr.byte_range()];
                self.local_scope.get(var_str).cloned().unwrap_or_default()
            }

            // Tables
            "table" => Type::Table,

            // Functions
            "function_definition" => self.typecheck_function(expr),

            // @Todo @XXX:
            // Lookup the type of the function/object being called,
            // check the argument types (?),
            // and return the return type.
            "call" => Type::Unknown,

            "parenthesized_expression" => {
                self.typecheck_expression(expr.named_child(0).expect("non-optional"))
            }

            // @Todo: probably need a specific type for varargs;
            // similar to a list type,
            // similar to a multiple return type,
            // but a bit different to both.
            "vararg_expression" => todo!(),

            // @Todo: handle metatables
            // @Todo: check the type of the operand (here? or elsewhere?)
            "unary_expression" => {
                let operator = expr.child_by_field_name("operator").expect("non-optional");
                match &self.src[operator.byte_range()] {
                    // number
                    "-" | "#" => Type::Number,

                    // integer
                    // @Todo: not Type::Number
                    "~" => Type::Number,

                    // bool
                    "not" => Type::Boolean,

                    _ => unreachable!(),
                }
            }

            // @Todo: handle metatables
            // @Todo: check the type of the operands (here? or elsewhere?)
            "binary_expression" => {
                let operator = expr.child_by_field_name("operator").expect("non-optional");
                match &self.src[operator.byte_range()] {
                    // number
                    "+" | "-" | "*" | "//" | "%" => Type::Number,

                    // float
                    "/" | "^" => Type::Number,

                    // bool
                    "==" | "~=" | "<" | ">" | "<=" | ">=" => Type::Boolean,

                    // short-circuiting
                    // @XXX @Todo @Fixme: not always boolean
                    "or" | "and" => Type::Boolean,

                    // integer
                    // @Todo: not Type::Number
                    "|" | "~" | "&" | "<<" | ">>" => Type::Number,

                    // string
                    ".." => Type::String,

                    _ => unreachable!(),
                }
            }

            _ => unreachable!("should have covered all types of expression"),
        }
    }

    /// Typecheck a function (either a [local] definition or an anonymous function expression).
    pub fn typecheck_function(&self, function_body: Node) -> Type {
        let params = function_body.child_by_field_name("parameters").unwrap();
        let body = function_body.child_by_field_name("body").unwrap();

        log::debug!("params: {}", params.to_sexp());
        log::debug!("body: {}", body.to_sexp());

        // todo!()

        // @XXX @Todo: make this return a properly parameterised and inferred type
        Type::Function
    }

    /// Gets a list of child nodes as `Vec<String>`.
    fn list(&self, list: Node) -> Vec<String> {
        let mut cursor = list.walk();
        list.named_children(&mut cursor)
            .map(|node| self.src[node.byte_range()].to_string())
            .collect()
    }

    /// Finds the types of a Lua explist
    /// (in tree-sitter it's called an expression_list).
    ///
    /// It does this by taking all arguments except the last
    /// and adjusting their types to be a single return value;
    /// then appends all the types of the last argument.
    ///
    /// For example,
    /// the explist `foo(), 3, true, foo()`
    /// (where `foo` has return type `number, string`),
    /// will be evaluated to have the type `number, number, bool, number, string`.
    fn explist(&self, list: Node) {
        todo!("@Todo: implement this after changing Type to handle multiple return values")
    }

    /// Adds the given variables to the local scope
    /// (with the uninitialized type).
    ///
    /// As in, `local foo`.
    fn declare_local(&mut self, var_list: Node) {
        let names = self.list(var_list);
        self.local_scope
            .extend(names.into_iter().zip(iter::repeat(Type::Uninitialized)));
    }

    /// Assigns the given variables to have the types according to the given expressions.
    /// If there are more variables than expressions,
    /// the extra variables are left untouched;
    /// if there are more expressions than variables,
    /// the extra expressions are ignored.
    ///
    /// As in, `foo, bar, baz = 1, 3`.
    fn assign(&mut self, var_list: Node, expr_list: Node) {
        let names = self.list(var_list);

        let mut expr_cursor = expr_list.walk();

        #[allow(clippy::needless_collect)]
        let types: Vec<Type> = expr_list
            .children_by_field_name("value", &mut expr_cursor)
            .map(|value_node| self.typecheck_expression(value_node))
            .into_iter()
            .collect();

        // @Todo @Fixme:
        // If the variable isn't already in the local_scope,
        // instead of assigning it there anyway,
        // we should add it to the global table
        // (or the equivalent _ENV nonsense).
        self.local_scope
            .extend(names.into_iter().zip(types.into_iter()));
    }
}
