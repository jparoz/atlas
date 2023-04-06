use std::fmt::{self, Display};
use std::fs;
use std::iter;
use std::path::Path;

use im::{HashMap, HashSet};
use itertools::Itertools;
use tree_sitter::{Node, Tree};

use crate::error::IncludeError;

/// A struct representing a typechecking context.
/// That is, all the files containing code to be typechecked,
/// and all needed state and bookkeeping to return useful type information.
pub struct Typechecker {
    parser: tree_sitter::Parser,
    pub files: HashMap<FileID, (tree_sitter::Tree, TypedChunk)>,
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

        log::trace!("Parsed:\n{}", tree.root_node().to_sexp());

        if tree.root_node().has_error() {
            // @Todo: something more? Print the node/s containing the error/s?
            log::warn!("Syntax error");
        }

        let chunk = TypedChunk::new(&tree, contents);

        // @Todo: check if we overwrote an entry here
        self.files.insert(id, (tree, chunk));

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

/// Represents the results of typechecking a single Lua chunk.
#[derive(Debug, Clone)]
pub struct TypedChunk {
    /// The contents of the file as it was read from disk.
    /// This is the string which was given to the tree-sitter parser to produce the `Tree`.
    pub src: String,

    /// A map from a tree-sitter [`Node`]'s ID
    /// to the type environment at that node.
    /// The IDs used are from the tree-sitter [`Tree`] given to [`TypedChunk::new`].
    pub scopes: HashMap<usize, HashMap<String, ConstraintSet>>,

    /// A map from a tree-sitter [`Node`]'s ID
    /// to the set of type constraints upon the expression at that node.
    /// The IDs used are from the tree-sitter [`Tree`] given to [`TypedChunk::new`].
    pub type_constraints: HashMap<usize, ExpList>,

    /// The set of all free variables in the chunk.
    /// These are usually translated to global variable accesses.
    pub free_variables: HashMap<String, ConstraintSet>,

    /// The set of all assigned globals in the chunk.
    pub provided_globals: HashMap<String, ConstraintSet>,

    /// The return type of the chunk.
    pub return_type: ExpList,
}

/// Manages the typechecking of a single Lua chunk.
/// See [`TypedChunk`] for documentation of fields.
#[derive(Debug, Clone)]
struct ChunkBuilder {
    src: String,
    local_scope: HashMap<String, ConstraintSet>,
    scopes: HashMap<usize, HashMap<String, ConstraintSet>>,
    type_constraints: HashMap<usize, ExpList>,
    free_variables: HashMap<String, ConstraintSet>,
    provided_globals: HashMap<String, ConstraintSet>,
}

impl TypedChunk {
    /// Builds the type environment at each statement in the given chunk.
    /// Returns the new `TypedChunk`.
    pub fn new(tree: &Tree, src: String) -> Self {
        let mut builder = ChunkBuilder {
            src,

            local_scope: HashMap::new(),

            scopes: HashMap::new(),
            type_constraints: HashMap::new(),
            free_variables: HashMap::new(),
            provided_globals: HashMap::new(),
        };

        let return_type = builder.typecheck_block(tree.root_node());

        let ChunkBuilder {
            src,
            scopes,
            type_constraints,
            free_variables,
            provided_globals,
            ..
        } = builder;
        TypedChunk {
            src,
            scopes,
            type_constraints,
            free_variables,
            provided_globals,
            return_type,
        }
    }
}

impl ChunkBuilder {
    /// Builds the type environment in a block.
    /// Returns a list of all the possible return types of the block.
    fn typecheck_block(&mut self, block: Node) -> ExpList {
        let mut return_type = ExpList::new();

        // For each statement,
        // build the type environment at that point.
        let mut cursor = block.walk();
        for statement in block.named_children(&mut cursor) {
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
                    let names = self.list(var_list);

                    let expr_list = statement.named_child(1).expect("non-optional");
                    let types = self.explist(expr_list);

                    self.assign(names, types.0);
                }

                "local_variable_declaration" => {
                    let var_list = statement.named_child(0).expect("non-optional");
                    let names = self.list(var_list);
                    self.declare_local(names.clone());

                    if let Some(expr_list) = statement.named_child(1) {
                        let types = self.explist(expr_list);
                        self.assign(names, types.0);
                    }
                }

                "do_statement" => {
                    let saved_scope = self.local_scope.clone();

                    if let Some(body) = statement.child_by_field_name("body") {
                        let types = self.typecheck_block(body);
                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }
                    }

                    self.local_scope = saved_scope;
                }

                "while_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // while
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_types = self.typecheck_expression(condition);
                    // @Todo: something with condition_types

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        let types = self.typecheck_block(body);
                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }
                    }

                    self.local_scope = saved_scope;
                }

                "repeat_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // repeat
                    if let Some(body) = statement.child_by_field_name("body") {
                        let types = self.typecheck_block(body);
                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }
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
                    self.local_scope.insert(name_str, Type::Number.into());

                    let end = statement.child_by_field_name("end").expect("non-optional");
                    // @Todo: check that end can be converted to a number

                    if let Some(step) = statement.child_by_field_name("step") {
                        // @Todo: check that step can be converted to a number
                    }

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        let types = self.typecheck_block(body);
                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }
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
                    let names = self.list(var_list);

                    let expr_list = statement
                        .child_by_field_name("right")
                        .expect("non-optional");
                    let types = self.explist(expr_list);

                    self.assign(names, types.0);

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        let types = self.typecheck_block(body);
                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }
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

                        let types = self.typecheck_block(consequence);
                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }

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

                                let types = self.typecheck_block(consequence);
                                for (constraints, new_constraints) in
                                    return_type.0.iter_mut().zip(types.0.into_iter())
                                {
                                    constraints.0.extend(new_constraints.0);
                                }

                                self.local_scope = saved_scope;
                            }
                        // [else [body]]
                        } else if let Some(body) = elseif.child_by_field_name("body") {
                            let saved_scope = self.local_scope.clone();

                            let types = self.typecheck_block(body);
                            for (constraints, new_constraints) in
                                return_type.0.iter_mut().zip(types.0.into_iter())
                            {
                                constraints.0.extend(new_constraints.0);
                            }

                            self.local_scope = saved_scope;
                        }
                    }
                }

                "function_definition_statement" => {
                    let name = statement.child_by_field_name("name").expect("non-optional");
                    let name_string = self.src[name.byte_range()].to_string();

                    log::trace!("Typechecking function `{name_string}`");
                    let function_type = self.typecheck_function(statement);

                    // @Todo @Fixme: change this to accept table type names,
                    // e.g. `function foo.bar:baz() body end`
                    self.assign([name_string], [function_type.into()]);
                }

                "local_function_definition_statement" => {
                    let name = statement.child_by_field_name("name").expect("non-optional");
                    let name_string = self.src[name.byte_range()].to_string();

                    log::trace!("Typechecking function `{name_string}`");
                    let function_type = self.typecheck_function(statement);

                    self.declare_local([name_string.clone()]);
                    self.assign([name_string], [function_type.into()]);
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
                    if let Some(exp_list) = statement.child(1) {
                        let types = self.explist(exp_list);

                        if return_type.0.len() < types.0.len() {
                            return_type
                                .0
                                .resize(types.0.len(), ConstraintSet::default());
                        }

                        for (constraints, new_constraints) in
                            return_type.0.iter_mut().zip(types.0.into_iter())
                        {
                            constraints.0.extend(new_constraints.0);
                        }
                    } else {
                        // `return;` means `return nil;`
                        return_type
                            .0
                            .get_mut(0)
                            .map(|cons| cons.0.insert(Type::Nil.into()));
                    }
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
            "nil" => vec![Type::Nil.into()].into(),
            "true" | "false" => vec![Type::Boolean.into()].into(),
            "number" => vec![Type::Number.into()].into(),
            "string" => vec![Type::String.into()].into(),

            // Variable references
            "variable" => {
                let var_str = &self.src[expr.byte_range()];
                if let Some(local) = self.local_scope.get(var_str) {
                    vec![local.clone()].into()
                } else if let Some(global_defined_here) = self.provided_globals.get(var_str) {
                    vec![global_defined_here.clone()].into()
                } else if let Some(global_already_referenced) = self.free_variables.get(var_str) {
                    vec![global_already_referenced.clone()].into()
                } else {
                    // @Todo @XXX: input type variables??
                    let constraints = ConstraintSet::new();
                    self.free_variables
                        .insert(var_str.to_string(), constraints.clone());
                    vec![constraints].into()
                }
            }

            // Tables
            "table" => vec![Type::Table.into()].into(),

            // Functions
            "function_definition" => {
                log::trace!("Typechecking anonymous function defined at {expr:?}");
                vec![self.typecheck_function(expr).into()].into()
            }

            // @Todo @XXX:
            // Lookup the type of the function/object being called,
            // check the argument types (?),
            // and return the return type.
            "call" => vec![Type::Unknown.into()].into(),

            "parenthesized_expression" => {
                let sub_expr = expr.named_child(0).expect("non-optional");
                let mut types = self.typecheck_expression(sub_expr);
                types.0.truncate(1);
                types
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
                    "-" | "#" => vec![Type::Number.into()].into(),

                    // integer
                    // @Todo: not Type::Number
                    "~" => vec![Type::Number.into()].into(),

                    // bool
                    "not" => vec![Type::Boolean.into()].into(),

                    _ => unreachable!(),
                }
            }

            // @Todo: handle metatables
            // @Todo: check the type of the operands (here? or elsewhere?)
            "binary_expression" => {
                let operator = expr.child_by_field_name("operator").expect("non-optional");
                match &self.src[operator.byte_range()] {
                    // number
                    "+" | "-" | "*" | "//" | "%" => vec![Type::Number.into()].into(),

                    // float
                    "/" | "^" => vec![Type::Number.into()].into(),

                    // bool
                    "==" | "~=" | "<" | ">" | "<=" | ">=" => vec![Type::Boolean.into()].into(),

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
                        let right = expr.child_by_field_name("right").expect("non-optional");
                        let mut types = self.typecheck_expression(right);
                        types.0.truncate(1);
                        types
                    }

                    // integer
                    // @Todo: not Type::Number
                    "|" | "~" | "&" | "<<" | ">>" => vec![Type::Number.into()].into(),

                    // string
                    ".." => vec![Type::String.into()].into(),

                    _ => unreachable!(),
                }
            }

            _ => unreachable!("should have covered all types of expression"),
        };

        // @Todo: check for clashes
        self.type_constraints.insert(expr.id(), explist.clone());

        explist
    }

    /// Typecheck a function (either a \[local] definition or an anonymous function expression).
    pub fn typecheck_function(&mut self, function_body: Node) -> Type {
        let saved_scope = self.local_scope.clone();

        let mut arguments = ExpList::new();

        if let Some(params) = function_body.child_by_field_name("parameters") {
            let mut cursor = params.walk();
            for param in params.named_children(&mut cursor) {
                match param.kind() {
                    "identifier" => {
                        let name = self.src[param.byte_range()].to_string();
                        let constraints = ConstraintSet::new();

                        arguments.0.push(constraints.clone());

                        log::trace!("Binding function argument `{name}` to type: {constraints:?}");
                        self.declare_local([name.clone()]);
                        self.assign([name], [constraints]);
                    }

                    "vararg_expression" => todo!(),

                    _ => unreachable!("covered all parameter types"),
                }
            }
        }

        let returns = if let Some(body) = function_body.child_by_field_name("body") {
            self.typecheck_block(body)
        } else {
            ExpList::new()
        };

        self.local_scope = saved_scope;

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
        let mut types = ExpList::new();

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

    /// Adds the given variables to the local scope
    /// (with the uninitialized type).
    ///
    /// As in, `local foo`.
    fn declare_local<I>(&mut self, names: I)
    where
        I: IntoIterator<Item = String>,
    {
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
    fn assign<I, T>(&mut self, names: I, cons_sets: T)
    where
        I: IntoIterator<Item = String>,
        T: IntoIterator<Item = ConstraintSet>,
    {
        for (name, constraints) in names.into_iter().zip(cons_sets.into_iter()) {
            if self.local_scope.contains_key(&name) {
                // If it's been declared as a local,
                // then overwrite the type of that local.
                self.local_scope.insert(name, constraints);
            } else {
                // If it's not a local,
                // mark that this chunk assigns a global variable of this name and type.
                self.provided_globals.insert(name, constraints);
            }
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
                write!(f, "(({arguments:?}) -> {returns:?})",)
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
pub struct ExpList(Vec<ConstraintSet>);

impl ExpList {
    fn new() -> Self {
        ExpList(Vec::new())
    }
}

impl From<Vec<ConstraintSet>> for ExpList {
    fn from(exps: Vec<ConstraintSet>) -> Self {
        ExpList(exps)
    }
}

impl Display for ExpList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.iter().join(", "))
    }
}

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

impl ConstraintSet {
    /// Tries to find a type which satisfies all constraints in the set.
    // @Todo: not Option<Type>, maybe Vec<Type>? or Result<Type>
    fn unify(self) -> Option<Type> {
        todo!()
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Constraint::*;
        match self {
            IsType(typ) => typ.fmt(f),
            And(constraints) => write!(f, "({})", constraints.iter().join(" & ")),
            Or(constraints) => write!(f, "({})", constraints.iter().join(" | ")),
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

impl ConstraintSet {
    fn new() -> Self {
        ConstraintSet(HashSet::new())
    }
}

impl From<Type> for ConstraintSet {
    fn from(typ: Type) -> Self {
        ConstraintSet(im::hashset! {typ.into()})
    }
}

impl Display for ConstraintSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", self.0.iter().join(" & "))
    }
}
