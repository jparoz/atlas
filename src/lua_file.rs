use std::iter;

use im::hashmap::HashMap;
use tree_sitter::{Node, Tree};

use crate::typecheck::Type;

#[derive(Debug, Clone)]
pub struct LuaFile {
    /// The tree-sitter [`Tree`] for this file.
    pub tree: Tree,

    /// The contents of the file as it was read from disk.
    /// This is the string which was given to the tree-sitter parser to produce the `Tree`.
    pub src: String,
}

impl LuaFile {
    /// Makes a new `LuaFile` from the parsed tree and source code.
    pub fn new(tree: Tree, src: String) -> Self {
        LuaFile { tree, src }
    }

    /// Find the type of an expression,
    /// given a type scope.
    pub fn type_of_expression(&self, scope: &HashMap<String, Type>, node: Node) -> Type {
        log::trace!(
            "Finding type of expression `{}`",
            &self.src[node.byte_range()]
        );

        match node.kind() {
            // Primitive types
            "nil" => Type::Nil,
            "true" | "false" => Type::Boolean,
            "number" => Type::Number,
            "string" => Type::String,

            // Variable references
            "variable" => {
                // @Todo: lookup globals as well
                let var_str = &self.src[node.byte_range()];
                scope.get(var_str).cloned().unwrap_or_default()
            }

            // Tables
            "table" => Type::Table,

            // Functions
            "function_definition" => Type::Function,

            // @Todo @XXX:
            // Lookup the type of the function/object being called,
            // check the argument types (?),
            // and return the return type.
            "call" => Type::Unknown,

            "parenthesized_expression" => {
                self.type_of_expression(scope, node.named_child(0).expect("non-optional"))
            }

            // @Todo: probably need a specific type for varargs;
            // similar to a list type,
            // similar to a multiple return type,
            // but a bit different to both.
            "vararg_expression" => todo!(),

            // @Todo: fill these out.
            // All operators are known ahead of time;
            // need to include their default types,
            // and eventually need to check for metatables somehow
            // (which might change the operator's effective type).
            "unary_expression" => todo!(),
            "binary_expression" => todo!(),

            _ => unreachable!("should have covered all types of expression"),
        }
    }
}

pub struct Environment<'a> {
    // @Todo: document this
    file: &'a LuaFile,

    /// The current local scope.
    local_scope: HashMap<String, Type>,

    /// A map from a tree-sitter [`Node`]'s ID
    /// to the type environment at that node.
    /// The IDs used are from the `LuaFile`'s `tree` field.
    pub types: HashMap<usize, HashMap<String, Type>>,
}

impl<'a> Environment<'a> {
    /// Builds the type environment at each statement in the given file.
    pub fn new(file: &'a LuaFile) -> Self {
        let mut env = Environment {
            file,
            local_scope: HashMap::new(),
            types: HashMap::new(),
        };
        env.type_block(file.tree.root_node());
        env
    }

    /// Builds the type environment in a block.
    fn type_block(&mut self, block: Node<'a>) {
        // For each statement,
        // build the type environment at that point.
        let mut cursor = block.walk();
        for statement in block.children(&mut cursor) {
            // Save the current state of the type environment.
            log::trace!("local scope:\n{:?}", self.local_scope);
            self.types.insert(statement.id(), self.local_scope.clone());

            log::trace!(
                "Processing statement (kind == {kind}):\n{src}",
                kind = statement.kind(),
                src = &self.file.src[statement.byte_range()]
            );

            match statement.kind() {
                // @Todo: global environment
                // @Note: This could either be assigning a global,
                // or modifying a previously-declared local.
                "variable_assignment" => todo!(),

                "local_variable_declaration" => {
                    let var_list = statement.named_child(0).expect("non-optional");
                    let expr_list = statement.named_child(1);
                    self.assign(var_list, expr_list);
                }

                "do_statement" => {
                    let saved_scope = self.local_scope.clone();

                    if let Some(body) = statement.child_by_field_name("body") {
                        self.type_block(body);
                    }

                    self.local_scope = saved_scope;
                }

                "while_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // while
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_type = self.file.type_of_expression(&self.local_scope, condition);
                    // @Todo: something with condition_type

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.type_block(body);
                    }

                    self.local_scope = saved_scope;
                }

                "repeat_statement" => {
                    let saved_scope = self.local_scope.clone();

                    // repeat
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.type_block(body);
                    }

                    // until
                    let condition = statement
                        .child_by_field_name("condition")
                        .expect("non-optional");
                    let condition_type = self.file.type_of_expression(&self.local_scope, condition);
                    // @Todo: something with condition_type

                    self.local_scope = saved_scope;
                }

                // for name = start, end [, step] do [body] end
                "for_numeric_statement" => {
                    let saved_scope = self.local_scope.clone();

                    let name = statement.child_by_field_name("name").expect("non-optional");
                    let name_str = self.file.src[name.byte_range()].to_string();

                    // @Todo: the numerical for converts its arguments to numbers.
                    // See section 3.3.5 of Lua 5.4 manual.
                    let start = statement
                        .child_by_field_name("start")
                        .expect("non-optional");
                    let start_type = self.file.type_of_expression(&self.local_scope, start);
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
                        self.type_block(body);
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

                    self.assign(var_list, Some(expr_list));

                    // do
                    if let Some(body) = statement.child_by_field_name("body") {
                        self.type_block(body);
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
                    let condition_type = self.file.type_of_expression(&self.local_scope, condition);
                    // @Todo: something with condition_type

                    // then [consequence]
                    if let Some(consequence) = statement.child_by_field_name("consequence") {
                        let saved_scope = self.local_scope.clone();
                        self.type_block(consequence);
                        self.local_scope = saved_scope;
                    }

                    let mut cursor = statement.walk();
                    for elseif in statement.children_by_field_name("alternative", &mut cursor) {
                        // {elseif condition then [consequence]}
                        if let Some(condition) = elseif.child_by_field_name("condition") {
                            // elseif condition
                            let condition_type =
                                self.file.type_of_expression(&self.local_scope, condition);
                            // @Todo: something with condition_type

                            // then [consequence]
                            if let Some(consequence) = elseif.child_by_field_name("consequence") {
                                let saved_scope = self.local_scope.clone();
                                self.type_block(consequence);
                                self.local_scope = saved_scope;
                            }
                        // [else [body]]
                        } else if let Some(body) = elseif.child_by_field_name("body") {
                            let saved_scope = self.local_scope.clone();
                            self.type_block(body);
                            self.local_scope = saved_scope;
                        }
                    }
                }

                // @Todo: function definition statements
                "function_definition_statement" => todo!(),
                "local_function_definition_statement" => todo!(),

                // Ignore these, as they don't (visibly) change the type environment.
                "shebang" | "call" | "empty_statement" | "label_statement" | "goto_statement" => (),

                // @Todo @Checkme: can/should we do an early return here?
                // Code after a `break` is unreachable,
                // so anything in that unreachable code doesn't really have a type anyway.
                // @Todo: emit a warning about any unreachable code after this break.
                "break_statement" => return,

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
                        log::debug!("returned: `{}`", &self.file.src[exp_list.byte_range()])
                    }

                    return;
                }

                _ => unreachable!("covered all statement types"),
            }
        }
    }

    /// Gets a list of child nodes as `Vec<String>`.
    fn list(&self, list: Node<'a>) -> Vec<String> {
        let mut cursor = list.walk();
        list.named_children(&mut cursor)
            .map(|node| self.file.src[node.byte_range()].to_string())
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
    fn explist(&self, list: Node<'a>) {
        todo!("@Todo: implement this after changing Type to handle multiple return values")
    }

    /// Adds variables to the local scope representing a Lua assignment.
    fn assign(&mut self, var_list: Node<'a>, expr_list: Option<Node<'a>>) {
        let names = self.list(var_list);

        let mut expr_cursor = expr_list.map(|node| node.walk());

        #[allow(clippy::needless_collect)]
        let types: Vec<Type> = expr_list
            .map(|values_node| {
                values_node
                    .children_by_field_name("value", expr_cursor.as_mut().unwrap())
                    .map(|value_node| self.file.type_of_expression(&self.local_scope, value_node))
            })
            .into_iter()
            .flatten()
            .collect();

        self.local_scope.extend(
            names
                .into_iter()
                .zip(types.into_iter().chain(iter::repeat(Type::Uninitialized))),
        );
    }
}
