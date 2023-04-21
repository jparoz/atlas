use std::fmt::{self, Display};
use std::fs;
use std::path::Path;
use std::sync::atomic::{self, AtomicUsize};

use im::{HashMap, HashSet};
use itertools::Itertools;
use tree_sitter::Node;

use crate::error::IncludeError;
use crate::scope::Scope;

/// A handle to the type of a particular expression/variable.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeVar(usize);

/// A struct representing a typechecking context.
/// That is, all the files containing code to be typechecked,
/// and all needed state and bookkeeping to return useful type information.
pub struct Typechecker {
    parser: tree_sitter::Parser,
    pub files: HashMap<FileID, (tree_sitter::Tree, TypedChunk)>,

    /// The mapping from type variables to type constraints.
    /// Implemented as a `Vec`,
    /// because the type variables in existence
    /// are guaranteed to have IDs in the range `0..N`
    /// where `N` is the ID of the freshest type var.
    typevars: Vec<ConstraintSet>,
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
            typevars: Vec::new(),
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

        log::trace!("Parsed:\n{}", tree.root_node().to_sexp());

        if tree.root_node().has_error() {
            // @Todo: something more? Print the node/s containing the error/s?
            log::warn!("Syntax error");
        }

        let chunk = {
            let mut builder = ChunkBuilder {
                typechecker: self,
                src: contents,
                scopes: HashMap::new(),
                scope: Scope::new_top_level(),
                node_types: HashMap::new(),
            };

            let return_type = builder.typecheck_block(tree.root_node());

            let ChunkBuilder {
                src,
                scopes,
                scope,
                node_types: type_constraints,
                ..
            } = builder;
            TypedChunk {
                src,
                scopes,
                scope,
                type_constraints,
                return_type,
            }
        };

        // @Todo: check if we overwrote an entry here
        self.files.insert(id, (tree, chunk));

        Ok(())
    }

    /// Makes a fresh type variable,
    /// adds it to the mapping,
    /// and returns the [`TypeVar`].
    fn fresh(&mut self) -> TypeVar {
        static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
        let var = TypeVar(id);
        self.typevars.push(ConstraintSet::default());
        debug_assert_eq!(self.typevars.len() - 1, id);
        var
    }

    /// Constrains a type variable to include the given constraints.
    fn constrain(&mut self, typevar: TypeVar, constraints: ConstraintSet) {
        self.get_mut(typevar).0.extend(constraints.0);
    }

    /// Returns a fresh type variable,
    /// constrained by the given constraints.
    fn fresh_constrain(&mut self, constraints: ConstraintSet) -> TypeVar {
        let typevar = self.fresh();
        self.constrain(typevar, constraints);
        typevar
    }

    /// Gets the type constraints corresponding to the given [`TypeVar`].
    fn get(&self, var: TypeVar) -> &ConstraintSet {
        self.typevars
            .get(var.0)
            .expect("all TypeVars in existence should have been added to the mapping")
    }

    /// Gets a mutable reference to the type constraints corresponding to the given [`TypeVar`].
    fn get_mut(&mut self, var: TypeVar) -> &mut ConstraintSet {
        self.typevars
            .get_mut(var.0)
            .expect("all TypeVars in existence should have been added to the mapping")
    }

    /// Combines the constraints of two `ExpList`s.
    fn combine(&mut self, explist: &ExpList, other: &ExpList) {
        // For each item in the lists (item-wise),
        // extend the set in `explist` with the new constraints from `other`.
        for (existing_typevar, new_typevar) in
            explist.0.iter().copied().zip(other.0.iter().copied())
        {
            let new_constraints = self.get(new_typevar).clone();
            let existing_constraints = self.get_mut(existing_typevar);
            existing_constraints.0.extend(new_constraints.0);
        }
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
            .field(
                "typevars",
                &self.typevars.iter().enumerate().collect::<Vec<_>>(),
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

/// Represents the results of typechecking a single Lua chunk.
#[derive(Debug, Clone)]
pub struct TypedChunk {
    /// The contents of the file as it was read from disk.
    /// This is the string which was given to the tree-sitter parser to produce the `Tree`.
    pub src: String,

    /// A map from a tree-sitter [`Node`]'s ID
    /// to the type environment at that node.
    /// The IDs used are from the tree-sitter [`Tree`] given to [`TypedChunk::new`].
    pub scopes: HashMap<usize, Scope>,

    /// The scope at the end of the top level of the chunk.
    pub scope: Scope,

    /// A map from a tree-sitter [`Node`]'s ID
    /// to the set of type constraints upon the expression at that node.
    /// The IDs used are from the tree-sitter [`Tree`] given to [`TypedChunk::new`].
    pub type_constraints: HashMap<usize, ExpList>,

    /// The return type of the chunk.
    pub return_type: ExpList,
}

/// Manages the typechecking of a single Lua chunk.
/// See [`TypedChunk`] for documentation of fields.
#[derive(Debug)]
struct ChunkBuilder<'a> {
    typechecker: &'a mut Typechecker,
    src: String,
    scopes: HashMap<usize, Scope>,
    scope: Scope,
    node_types: HashMap<usize, ExpList>,
}

impl<'a> ChunkBuilder<'a> {
    /// Builds the type environment in a block.
    /// Returns a list of all the possible return types of the block.
    fn typecheck_block(&mut self, block: Node) -> ExpList {
        let return_type = ExpList::default();

        // For each statement,
        // build the type environment at that point.
        let mut cursor = block.walk();
        for statement in block.named_children(&mut cursor) {
            // Save the current state of the type environment.
            log::trace!("scope:\n{}", self.scope);
            self.scopes.insert(statement.id(), self.scope.clone());

            log::trace!(
                "Processing statement (kind == {kind}):\n{src}",
                kind = statement.kind(),
                src = &self.src[statement.byte_range()]
            );

            match statement.kind() {
                // @Todo: transitive type constraints somehow, e.g.:
                //     function Foobar(a)
                //         local b = a
                //         local res = b + 1
                //         return res
                //     end
                // should constrain `a` to be type `number`,
                // but it only constrains `b` (which is internal to the function).
                "variable_assignment" => {
                    // @Todo: Handle table variables (table.field and table[index]),
                    // either here or in self.assign
                    let names_node = statement.named_child(0).expect("non-optional");
                    let names = self.list(names_node);

                    let explist_node = statement.named_child(1).expect("non-optional");
                    let explist = self.explist(explist_node);

                    self.assign(names, explist.0);
                }

                "local_variable_declaration" => {
                    let names_node = statement.named_child(0).expect("non-optional");
                    let names = self.list(names_node);
                    for name in names.iter() {
                        self.scope
                            .declare_local(name.clone(), self.typechecker.fresh());
                    }

                    if let Some(explist_node) = statement.named_child(1) {
                        let explist = self.explist(explist_node);
                        self.assign(names, explist.0);
                    }
                }

                "do_statement" => {
                    self.scope.open_scope();

                    if let Some(body) = statement.child_by_field_name("body") {
                        let return_list = self.typecheck_block(body);
                        self.typechecker.combine(&return_type, &return_list);
                    }

                    self.scope.close_scope();
                }

                "while_statement" => {
                    self.scope.open_scope();

                    // while
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_types = self.typecheck_expression(condition);
                    // @Todo: something with condition_types

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        let return_list = self.typecheck_block(body);
                        self.typechecker.combine(&return_type, &return_list);
                    }

                    self.scope.close_scope();
                }

                "repeat_statement" => {
                    self.scope.open_scope();

                    // repeat
                    if let Some(body) = statement.child_by_field_name("body") {
                        let return_list = self.typecheck_block(body);
                        self.typechecker.combine(&return_type, &return_list);
                    }

                    // until
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_type = self.typecheck_expression(condition);
                    // @Todo: something with condition_type

                    self.scope.close_scope();
                }

                // for name = start, end [, step] do [body] end
                "for_numeric_statement" => {
                    // This is effectively a constant.
                    // @Todo @Cleanup: reuse the same typevars for types of literals
                    let num_typevar = self.typechecker.fresh();
                    self.typechecker.constrain(num_typevar, Type::Number.into());
                    let num_explist = ExpList(vec![num_typevar]);

                    self.scope.open_scope();

                    // @Note: Numerical for loops convert their arguments to numbers,
                    // so the bound variable is guaranteed to have the type `number`
                    // (either integer or float; see section 3.3.5 of Lua 5.4 manual).

                    // name
                    let name_node = statement.child_by_field_name("name").expect("non-optional");
                    let name = self.src[name_node.byte_range()].to_string();
                    self.scope.declare_local(name, num_typevar);

                    // start
                    let start_node = statement
                        .child_by_field_name("start")
                        .expect("non-optional");
                    let start_explist = self.typecheck_expression(start_node);
                    self.typechecker.combine(&start_explist, &num_explist);

                    // end
                    let end_node = statement.child_by_field_name("end").expect("non-optional");
                    let end_explist = self.typecheck_expression(end_node);
                    self.typechecker.combine(&end_explist, &num_explist);

                    // [step]
                    if let Some(step_node) = statement.child_by_field_name("step") {
                        let step_explist = self.typecheck_expression(step_node);
                        self.typechecker.combine(&step_explist, &num_explist);
                    }

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        let return_list = self.typecheck_block(body);
                        self.typechecker.combine(&return_type, &return_list);
                    }

                    self.scope.close_scope();
                }

                // for names in explist do [body] end
                "for_generic_statement" => {
                    self.scope.open_scope();

                    // From the Lua 5.4 manual, section 3.3.5:
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

                    let explist_node = statement
                        .child_by_field_name("right")
                        .expect("non-optional");
                    let mut explist = self.explist(explist_node);
                    explist.0.resize(4, self.typechecker.fresh());
                    let iterator_typevar = explist.0.get(0).unwrap();
                    let state_typevar = explist.0.get(1).unwrap();
                    let control_typevar = explist.0.get(2).unwrap();

                    // This is the explist of the minimal type for
                    // the iterator function of a generic for loop.
                    let iterator_type =
                        ConstraintSet(im::hashset![Constraint::IsType(Type::Function {
                            arguments: ExpList(vec![*state_typevar, *control_typevar]),
                            // Default makes no assumptions about the return type
                            returns: ExpList::default(),
                        })]);
                    self.typechecker.constrain(*iterator_typevar, iterator_type);

                    let names_node = statement.child_by_field_name("left").expect("non-optional");
                    let names = self.list(names_node);
                    for (name, typevar) in names.iter().zip(explist.0) {
                        self.scope.declare_local(name.clone(), typevar);
                    }

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        let return_list = self.typecheck_block(body);
                        self.typechecker.combine(&return_type, &return_list);
                    }

                    self.scope.close_scope();
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
                        self.scope.open_scope();

                        let return_list = self.typecheck_block(consequence);
                        self.typechecker.combine(&return_type, &return_list);

                        self.scope.close_scope();
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
                                self.scope.open_scope();

                                let return_list = self.typecheck_block(consequence);
                                self.typechecker.combine(&return_type, &return_list);

                                self.scope.close_scope();
                            }
                        // [else [body]]
                        } else if let Some(body) = elseif.child_by_field_name("body") {
                            self.scope.open_scope();

                            let return_list = self.typecheck_block(body);
                            self.typechecker.combine(&return_type, &return_list);

                            self.scope.close_scope();
                        }
                    }
                }

                "function_definition_statement" => {
                    let name_node = statement.child_by_field_name("name").expect("non-optional");
                    let name = self.src[name_node.byte_range()].to_string();

                    log::trace!("Typechecking function `{name}`");
                    let function_type = self.typecheck_function(statement);
                    let function_typevar = self.typechecker.fresh();
                    self.typechecker
                        .constrain(function_typevar, function_type.into());

                    // @Todo @Fixme: change this to accept table type names,
                    // e.g. `function foo.bar:baz() body end`
                    self.scope.insert(name, function_typevar);
                }

                "local_function_definition_statement" => {
                    let name_node = statement.child_by_field_name("name").expect("non-optional");
                    let name = self.src[name_node.byte_range()].to_string();

                    log::trace!("Typechecking function `{name}`");
                    let function_type = self.typecheck_function(statement);
                    let function_typevar = self.typechecker.fresh();
                    self.typechecker
                        .constrain(function_typevar, function_type.into());

                    self.scope.declare_local(name, function_typevar);
                }

                // @Todo @Checkme: should we do an early return here?
                // Code after a `break` is unreachable,
                // so anything in that unreachable code doesn't really have a type anyway.
                // @Todo: emit a warning about any unreachable code after this break.
                // @Todo: check if we're inside a loop (?)
                "break_statement" => break,

                // @Note: it's actually a syntax error to have code after this return statement;
                // currently we do an early return of this function,
                // but possibly we could still check some stuff after the return statement.
                "return_statement" => {
                    let return_list = if let Some(explist_node) = statement.child(1) {
                        self.explist(explist_node)
                    } else {
                        // `return;` means `return nil;`
                        // This is effectively a constant.
                        // @Todo @Cleanup: reuse the same typevars for types of literals
                        let nil_typevar = self.typechecker.fresh();
                        self.typechecker.constrain(nil_typevar, Type::Nil.into());
                        ExpList(vec![nil_typevar])
                    };
                    self.typechecker.combine(&return_type, &return_list);

                    break;
                }

                // Ignore these, as they don't (visibly) change the type environment.
                "shebang" | "call" | "empty_statement" | "label_statement" | "goto_statement"
                | "comment" => (),

                kind => unreachable!("covered all statement types, got: {kind}"),
            }
        }

        log::trace!("Block return type: {return_type:?}");

        return_type
    }

    /// Typecheck an expression.
    /// Note that an expression may be a multiple return
    /// (e.g. from a function call or varargs expression),
    /// so this function returns an [`ExpList`].
    fn typecheck_expression(&mut self, expr: Node) -> ExpList {
        log::trace!(
            "Finding type of expression `{}`",
            &self.src[expr.byte_range()]
        );

        let explist = match expr.kind() {
            // Primitive types
            "nil" => explist![self.typechecker.fresh_constrain(Type::Nil.into())],
            "true" | "false" => explist![self.typechecker.fresh_constrain(Type::Boolean.into())],
            "number" => explist![self.typechecker.fresh_constrain(Type::Number.into())],
            "string" => explist![self.typechecker.fresh_constrain(Type::String.into())],

            // Variable references
            "variable" => {
                let var_str = &self.src[expr.byte_range()];
                let typevar = if let Some(typevar) = self.scope.get(var_str) {
                    typevar
                } else {
                    let typevar = self.typechecker.fresh();
                    self.scope.assume_global(var_str.to_string(), typevar);
                    typevar
                };
                explist![typevar]
            }

            // Tables
            "table" => explist![self.typechecker.fresh_constrain(Type::Table.into())],

            // Functions
            "function_definition" => {
                log::trace!("Typechecking anonymous function defined at {expr:?}");
                let function_type = self.typecheck_function(expr);
                explist![self.typechecker.fresh_constrain(function_type.into())]
            }

            // @Todo @XXX:
            // Lookup the type of the function/object being called,
            // check the argument types (?),
            // and return the return type.
            "call" => explist![self.typechecker.fresh_constrain(Type::Unknown.into())],

            "parenthesized_expression" => {
                let sub_expr = expr.named_child(0).expect("non-optional");
                let mut types = self.typecheck_expression(sub_expr);
                types.0.truncate(1);
                types
            }

            "vararg_expression" => {
                if let Some(varargs_explist) = self.scope.varargs_mut() {
                    varargs_explist.clone()
                } else {
                    todo!("@Todo: scope error (not a varargs function)")
                }
            }

            // @Todo: handle metatables
            "unary_expression" => {
                let operator = expr.child_by_field_name("operator").expect("non-optional");
                let operand = expr.child_by_field_name("argument").expect("non-optional");

                match &self.src[operator.byte_range()] {
                    // number
                    "-" => {
                        let typevar = self.typechecker.fresh_constrain(Type::Number.into());
                        let explist = explist![typevar];
                        self.constrain_node(operand, &explist);
                        explist
                    }

                    "#" => {
                        let typevar =
                            self.typechecker.fresh_constrain(ConstraintSet(im::hashset![
                                Constraint::Or(vec![Type::Table.into(), Type::String.into()])
                            ]));
                        self.constrain_node(operand, &explist![typevar]);
                        explist![self.typechecker.fresh_constrain(Type::Number.into())]
                    }

                    // integer
                    // @Todo: not Type::Number
                    "~" => {
                        let typevar = self.typechecker.fresh_constrain(Type::Number.into());
                        let explist = explist![typevar];
                        self.constrain_node(operand, &explist);
                        explist
                    }

                    // bool
                    "not" => explist![self.typechecker.fresh_constrain(Type::Boolean.into())],

                    _ => unreachable!(),
                }
            }

            // @Todo: handle metatables
            "binary_expression" => {
                let operator = expr.child_by_field_name("operator").expect("non-optional");
                let left = expr.child_by_field_name("left").expect("non-optional");
                let right = expr.child_by_field_name("right").expect("non-optional");

                match &self.src[operator.byte_range()] {
                    // number
                    "+" | "-" | "*" | "//" | "%" => {
                        let num_typevar = self.typechecker.fresh_constrain(Type::Number.into());
                        let num_explist = explist![num_typevar];
                        self.constrain_node(left, &num_explist);
                        self.constrain_node(right, &num_explist);
                        num_explist
                    }

                    // float
                    // @Todo: not Type::Number
                    "/" | "^" => {
                        let num_typevar = self.typechecker.fresh_constrain(Type::Number.into());
                        let num_explist = explist![num_typevar];
                        self.constrain_node(left, &num_explist);
                        self.constrain_node(right, &num_explist);
                        num_explist
                    }

                    // bool
                    "==" | "~=" | "<" | ">" | "<=" | ">=" => {
                        // @Checkme: is this always right?
                        // Might want to do some analysis to work out
                        // which type is more general or something,
                        // and constrain only in one direction.
                        let left_explist = self.typecheck_expression(left);
                        let right_explist = self.typecheck_expression(right);
                        self.constrain_node(left, &right_explist);
                        self.constrain_node(right, &left_explist);

                        explist![self.typechecker.fresh_constrain(Type::Boolean.into())]
                    }

                    // integer
                    // @Todo: not Type::Number
                    "|" | "~" | "&" | "<<" | ">>" => {
                        let num_typevar = self.typechecker.fresh_constrain(Type::Number.into());
                        let num_explist = explist![num_typevar];
                        self.constrain_node(left, &num_explist);
                        self.constrain_node(right, &num_explist);
                        num_explist
                    }

                    // string
                    ".." => {
                        let string_typevar = self.typechecker.fresh_constrain(Type::Number.into());
                        let string_explist = explist![string_typevar];
                        self.constrain_node(left, &string_explist);
                        self.constrain_node(right, &string_explist);
                        string_explist
                    }

                    // short-circuiting
                    //
                    // @Note @Fixme:
                    // These are the expressions
                    // (along with function calls)
                    // which mess up the idea that an expression can only have one possible type.
                    //
                    // For simplicity,
                    // for the moment,
                    // instead of capturing the possibility within an `or` expression
                    // of having two different types,
                    // we'll simply type the whole `or` expression
                    // as having the same type as its second operand;
                    // and do the same for `and`.
                    //
                    // That is,
                    // the expression `foo or 123`
                    // is given the type `number`;
                    // even though a more precise type would be `type(foo) | number`.
                    // `foo and 123` is given the same type `number`.
                    //
                    // This is essentially arbitrary,
                    // but it's at least sometimes right.
                    "or" | "and" => {
                        let left = expr.child_by_field_name("left").expect("non-optional");
                        let right = expr.child_by_field_name("right").expect("non-optional");

                        let left_explist = self.typecheck_expression(left);
                        let right_explist = self.typecheck_expression(right);

                        let left_constraints = self.typechecker.get(left_explist.0[0]);
                        let right_constraints = self.typechecker.get(right_explist.0[0]);

                        let res_typevar =
                            self.typechecker
                                .fresh_constrain(ConstraintSet(im::hashset! {
                                    Constraint::Or(
                                        left_constraints.0
                                            .clone()
                                            .into_iter()
                                            .chain(right_constraints.0.clone())
                                            .collect()
                                        )
                                }));
                        explist![res_typevar]
                    }

                    _ => unreachable!(),
                }
            }

            _ => unreachable!("should have covered all types of expression"),
        };

        // @Todo: check for clashes
        self.node_types.insert(expr.id(), explist.clone());

        explist
    }

    /// Typecheck a function (either a \[local] definition or an anonymous function expression).
    pub fn typecheck_function(&mut self, function_body: Node) -> Type {
        self.scope.open_scope();

        let mut argument_names = Vec::new();

        if let Some(params) = function_body.child_by_field_name("parameters") {
            let mut cursor = params.walk();
            for param in params.named_children(&mut cursor) {
                match param.kind() {
                    "identifier" => {
                        let name = self.src[param.byte_range()].to_string();
                        argument_names.push(name.clone());
                        let typevar = self.typechecker.fresh();
                        self.scope.declare_local(name.clone(), typevar);
                    }

                    "vararg_expression" => todo!(),

                    _ => unreachable!("covered all parameter types"),
                }
            }
        }

        let returns = if let Some(body) = function_body.child_by_field_name("body") {
            self.typecheck_block(body)
        } else {
            ExpList::default()
        };

        let mut arguments = ExpList::default();
        for name in argument_names {
            let typevar = self
                .scope
                .remove(&name)
                .expect("declare_local should have inserted this key");
            arguments.0.push(typevar);
        }

        self.scope.close_scope();

        let typ = Type::Function { arguments, returns };
        log::trace!("Function has type: {typ}");
        typ
    }

    /// Gets a list of child nodes as `Vec<String>`.
    fn list(&self, list: Node) -> Vec<String> {
        let mut cursor = list.walk();
        list.named_children(&mut cursor)
            .map(|node| self.src[node.byte_range()].to_string())
            .collect()
    }

    /// Finds the types of a Lua explist
    /// (in tree-sitter it's called an `expression_list`).
    ///
    /// It does this by taking all arguments except the last
    /// and adjusting their types to be a single return value;
    /// then appends all the types of the last argument.
    ///
    /// For example,
    /// the explist `foo(), 3, true, foo()`
    /// (where `foo` has return type `number, string`),
    /// will be evaluated to have the type `number, number, bool, number, string`.
    fn explist(&mut self, list: Node) -> ExpList {
        let mut types = ExpList::default();

        let count = list.named_child_count();
        let mut cursor = list.walk();

        for (i, mut ts) in list
            .named_children(&mut cursor)
            .map(|expr| self.typecheck_expression(expr))
            .enumerate()
        {
            if i + 1 < count {
                types.0.push(ts.0.swap_remove(0))
            } else {
                types.0.extend(ts.0)
            }
        }

        types
    }

    /// Constrains the given node to include the constraints in the given [`ExpList`].
    /// Also, if the node represents a variable,
    /// adds the first constraint to the variable scope as well.
    fn constrain_node(&mut self, expr: Node, explist: &ExpList) {
        if explist.0.is_empty() {
            // nothing to add
            return;
        }

        // Add the first constraint to the variable's set,
        // if it is indeed a variable.
        match expr.kind() {
            "variable" => {
                let typevar = self.typechecker.fresh();

                let var = &self.src[expr.byte_range()];
                if !self.scope.contains_key(var) {
                    self.scope.assume_global(var.to_string(), typevar);
                }

                let constraints = self.typechecker.get(explist.0[0]);
                self.typechecker.constrain(typevar, constraints.clone());
            }

            "varargs_expression" => {
                if let Some(varargs_explist) = self.scope.varargs_mut() {
                    self.typechecker.combine(varargs_explist, explist);
                } else {
                    todo!("@Todo: scope error (not a varargs function)")
                }
            }

            _ => (),
        }

        // Add the constraints to the expression's sets.
        let existing_explist = self.node_types.entry(expr.id()).or_default();
        self.typechecker.combine(existing_explist, explist);
    }

    /// Assigns the given variables to have the types according to the given expressions.
    /// If there are more variables than expressions,
    /// the extra variables are left untouched;
    /// if there are more expressions than variables,
    /// the extra expressions are ignored.
    ///
    /// As in, `foo, bar, baz = 1, 3`.
    fn assign<I, T>(&mut self, names: I, typevars: T)
    where
        // @Cleanup: this probs doesn't need to be String
        I: IntoIterator<Item = String>,
        T: IntoIterator<Item = TypeVar>,
    {
        for (name, typevar) in names.into_iter().zip(typevars) {
            self.scope.insert(name, typevar);
        }
    }
}

/// A `Type` represents all the possible Lua types,
/// including some pseudo-types such as the state of being an uninitialized variable.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    // Basic scalar types
    Nil,
    Boolean,
    Number,
    String,
    LightUserdata,

    // Parametric types
    Function {
        arguments: ExpList,
        returns: ExpList,
    },
    // @Todo @Fixme @XXX: include some parameters in these lol
    Thread,
    Table,

    // Other
    FullUserdata,

    // Pseudo-types
    Uninitialized,
    #[default]
    Unknown,
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Type::*;
        match self {
            Nil => write!(f, "nil"),
            Boolean => write!(f, "boolean"),
            Number => write!(f, "number"),
            String => write!(f, "string"),

            LightUserdata | FullUserdata => write!(f, "userdata"),

            // Parametric types
            Function { arguments, returns } => {
                write!(f, "(({arguments:?}) -> {returns:?})")
            }

            Thread => write!(f, "thread"),
            Table => write!(f, "table"),

            // Pseudo-types
            Uninitialized => write!(f, "uninitialized (nil)"),
            Unknown => write!(f, "unknown"),
        }
    }
}

/// An `ExpList` represents a Lua explist,
/// e.g. a multiple return or varargs expression.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpList(Vec<TypeVar>);

#[macro_export]
macro_rules! explist {
    ($($x:expr),*) => {
        ExpList(vec![$($x,)*])
    };
}
use explist;

/// A `Constraint` represents the set of operations that the type of a variable must admit,
/// based on uses of the variable.
/// This set of operations can be resolved to a concrete type,
/// e.g. to find the type of a function.
///
/// For now, operations are modelled directly as types;
/// This doesn't allow for operations which accept multiple types.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constraint {
    IsType(Type),
    Or(Vec<Constraint>),
    And(Vec<Constraint>),
}

impl Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Constraint::*;
        match self {
            IsType(typ) => typ.fmt(f),
            And(constraints) => write!(f, "{}", constraints.iter().join(" & ")),
            Or(constraints) => write!(f, "{}", constraints.iter().join(" | ")),
        }
    }
}

impl From<Type> for Constraint {
    fn from(typ: Type) -> Self {
        Constraint::IsType(typ)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintSet(HashSet<Constraint>);

impl From<Type> for ConstraintSet {
    fn from(typ: Type) -> Self {
        ConstraintSet(im::hashset! {typ.into()})
    }
}

impl Display for ConstraintSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            // @Cleanup: Is this the best spot for this logic?
            // Feels a bit wrong to have this be in the Display impl.
            write!(f, "any")
        } else {
            write!(f, "{}", self.0.iter().join(" & "))
        }
    }
}
