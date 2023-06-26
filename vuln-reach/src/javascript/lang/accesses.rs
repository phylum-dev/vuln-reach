//! Accesses from functions to symbols.
use std::collections::{HashMap, HashSet, VecDeque};

use lazy_static::lazy_static;
use tree_sitter::{Node, Query, QueryCursor};

use super::symbol_table::SymbolTable;
use crate::{Cursor, Error, Result, Tree, TreeCursorCache, JS};

/// An instance of a variable access (call or right-hand assignment).
/// Represents an edge from the access scope to the declaration scope.
/// It means that `decl_scope` is accessed in `access_scope` through `node`.
#[derive(Debug, Clone, Copy)]
pub struct Access<'a> {
    /// The identifier that is being accessed.
    pub node: Node<'a>,
    /// The scope the identifier lives in.
    pub scope: Node<'a>,
    /// The place the identifier is declared at.
    pub decl_node: Node<'a>,
    /// The scope the identifier is declared in.
    pub decl_scope: Node<'a>,
    /// The node which accesses this node.
    pub accessor: Option<Node<'a>>,
}

impl<'a> Access<'a> {
    pub fn repr(&self, tree: &Tree) -> String {
        format!(
            "Node {}:{},{} ({:?}) declared at {:?} ({:?}) accessed by {:?}",
            tree.repr_of(self.node),
            self.node.start_position().row,
            self.node.start_position().column,
            self.scope,
            self.decl_node,
            self.decl_scope,
            self.accessor
        )
    }

    // We define as "side effect" an access which is:
    // - not accessed by another identifier
    // - to an identifier in the top scope of the module
    // - not the subject of a declaration (i.e. node != decl_node)
    pub fn is_side_effect(&self) -> bool {
        self.accessor.is_none() && self.scope.kind() == "program" && self.node != self.decl_node
    }
}

#[derive(Clone, Copy, Debug)]
pub struct AccessEdge<'a> {
    accessed: Node<'a>,
    access: Access<'a>,
}

impl<'a> AccessEdge<'a> {
    pub fn new(accessed: Node<'a>, access: Access<'a>) -> Self {
        Self { accessed, access }
    }

    pub fn accessed(&self) -> Node<'a> {
        self.accessed
    }

    pub fn access(&self) -> Access<'a> {
        self.access
    }
}

#[derive(Debug)]
pub struct AccessGraph<'a> {
    // Adjacency list of all the accesses to a given declaration.
    accesses: HashMap<Node<'a>, Vec<Access<'a>>>,
    tree: &'a Tree,
}

impl<'a> AccessGraph<'a> {
    pub fn new(tree: &'a Tree, symbol_table: &SymbolTable<'a>) -> Self {
        lazy_static! {
            static ref QUERY: Query = Query::new(*JS, "(identifier) @ident").unwrap();
        }

        let mut cursor_cache = TreeCursorCache::new(tree);

        let mut cur = QueryCursor::new();
        let accesses = cur
            .matches(&QUERY, tree.root_node(), tree.buf().as_bytes())
            .filter_map(|query_match| {
                // The node is the first capture of the query, and it's always present.
                let node = query_match.captures[0].node;

                // Find the scope this node belongs to.
                //
                // The scope is either the top-level "program" node or the "body" field of a
                // function, which is of kind "statement_block".
                let mut scope_cursor = cursor_cache.cursor(node).unwrap();
                let scope = loop {
                    let node = scope_cursor.goto_parent().unwrap();

                    let kind = node.kind();
                    if kind == "program"
                        || (kind == "statement_block"
                            && scope_cursor
                                .parent()
                                .and_then(|parent| parent.child_by_field_name("body"))
                                .is_some())
                    {
                        break node;
                    }
                };

                // Get the declaration scope by looking up the node in the symbol table.
                let decl_cursor = cursor_cache.cursor(node).unwrap();
                let (decl_scope, decl_node) = symbol_table.lookup(decl_cursor)?;

                let decl_scope = decl_scope.node();

                // Get the scope of the next parent accessing this node.
                let accessor = AccessGraph::find_accessor(&mut cursor_cache, node)
                    .and_then(|node| {
                        let cursor = cursor_cache.cursor(node).ok()?;
                        symbol_table.lookup(cursor)
                    })
                    .map(|(_, accessor)| accessor);

                Some(Access { node, scope, decl_node, decl_scope, accessor })
            })
            .fold(HashMap::new(), |mut accesses, access| {
                // Store accesses grouped by the node of the declaration that is accessed.
                let entry: &mut Vec<Access> = accesses.entry(access.decl_node).or_default();
                entry.push(access);
                accesses
            });

        Self { accesses, tree }
    }

    /// Find the parent identifier of a node.
    ///
    /// This function recursively searches the AST upwards from a node to find
    /// the next identifier accessing the node.
    ///
    /// ```js,ignore
    /// function bar() { }
    ///
    /// var foo = () => {
    ///   test = bar();
    /// }
    ///
    /// function baz() {
    ///   test();
    /// }
    /// ```
    ///
    /// In the above example the accesses are as follows:
    ///
    ///  - function `bar`, `foo`, and `baz` are not accessed by anything, since
    ///    they're defined at the root scope without any parents
    ///  - assignment `test` is accessed by `foo`, since `foo` is the identifier
    ///    for the lambda in which `test` is used
    ///  - function call `bar` is accessed by `test`, since `test` is the next
    ///    identifier (before `foo`)
    ///  - function call `test` is accessed by `baz`
    ///
    /// NOTE: `test` in this example is not declared as variable and thus
    /// hoisted to the global scope. This is why the accessor of `bar` cannot be
    /// `foo`, otherwise the access from `baz` to `bar` would not be detected.
    fn find_accessor(cursor_cache: &mut TreeCursorCache<'a>, node: Node<'a>) -> Option<Node<'a>> {
        let cursor = cursor_cache.cursor(node).unwrap();

        for parent in cursor.parents() {
            match parent.kind() {
                // Check node to avoid declarations using themselves as accessor.
                "class_declaration" | "function_declaration" => {
                    return parent.child_by_field_name("name").filter(|&name| name != node);
                },
                // Find the next parent identifier if node is an anonymous declaration.
                "class" | "function" | "arrow_function" => (),
                kind @ ("variable_declarator"
                | "assignment_expression"
                | "augmented_assignment_expression") => {
                    let lhs = if kind == "variable_declarator" {
                        parent.child_by_field_name(b"name").unwrap()
                    } else {
                        parent.child_by_field_name(b"left").unwrap()
                    };

                    if !lhs.byte_range().contains(&node.start_byte()) {
                        // Use LHS identifier if node is in RHS of the assignment.
                        //
                        // Pick the outermost `identifier` node by retrieving the smallest node at
                        // the start of the line. This accounts for more complex kinds of nodes
                        // beyond `identifier` (e.g. `member_expression`).
                        if let Some(accessor) = parent
                            .named_descendant_for_point_range(
                                lhs.start_position(),
                                lhs.start_position(),
                            )
                            .filter(|node| node.kind() == "identifier")
                        {
                            return Some(accessor);
                        }

                        // If the node found is not an identifier, the LHS
                        // has a destructuring assignment. In that case, keep
                        // searching for the next accessor in the parent
                        // hierarchy.
                    }
                },
                _ => (),
            }
        }

        None
    }

    /// Compute paths between a source node and one or more target nodes.
    ///
    /// The supplied predicate determines what is considered a target node.
    ///
    /// The path finding algorithm is a breadth-first search based on a queue.
    /// The first node that is visited is the supplied source node.
    /// Each element of the queue contains the node to be visited, and a node
    /// path to start from. On each iteration, the node path is augmented
    /// with new edges, cloned and forwarded to future iterations.
    pub fn compute_paths<F>(
        &self,
        is_target: F,
        source: Node<'a>,
    ) -> Result<Vec<Vec<AccessEdge<'a>>>>
    where
        F: Fn(&Access<'a>) -> bool,
    {
        type NodePath<'a> = Vec<AccessEdge<'a>>;

        let mut bfs_q: VecDeque<(Node<'a>, NodePath)> = VecDeque::new();
        bfs_q.push_back((source, Vec::new()));

        let mut found_paths = Vec::new();
        let mut visited_nodes = HashSet::new();

        // Collect accesses in a dictionary where the key is the accessed
        // identifier.
        //
        // This is different from `self.accesses`, where the key is the _declaration_
        // node (rather than the _accessed_ node).
        let access_scopes = self
            .accesses
            .values()
            .flatten()
            .map(|access| (access.node, access))
            .collect::<HashMap<_, _>>();

        while let Some((node, path)) = bfs_q.pop_front() {
            // Skip if we already visited this node.
            if visited_nodes.contains(&node) {
                continue;
            }
            visited_nodes.insert(node);

            // Retrieve the access scope of the current node, which must exist for all
            // identifiers.
            let access = access_scopes.get(&node).copied().ok_or_else(|| {
                Error::Generic(format!(
                    "All identifiers should have an access scope: {:?} {}",
                    node,
                    self.tree.repr_of(node)
                ))
            })?;

            // Retrieve the accesses linked to the declaration node from the access above.
            // Ensure every declaration node has an entry in `self.accesses`.
            let declaration_accesses = self.accesses.get(&access.decl_node).ok_or_else(|| {
                Error::Generic(format!(
                    "All declarations should have a list of accesses: {:?} {}",
                    access.decl_node,
                    self.tree.repr_of(access.decl_node)
                ))
            })?;

            // Create edges from the current node to all of its declaration node's
            // accessors.
            for declaration_access in declaration_accesses {
                let mut path = path.clone();
                // Add an edge from the current node to the declaration node's access.
                path.push(AccessEdge::new(node, *declaration_access));

                // If the access is a target according to the supplied predicate, add the path
                // to the list of found paths.
                if is_target(declaration_access) {
                    found_paths.push(path.to_vec());
                }

                // Push suitable accessors of the current node to the bottom of the queue.
                //
                // A suitable accessor is a node of kind "identifier" which is also not a
                // function parameter or a catch statement parameters, as those identifiers
                // act like a declaration in their scope.
                if let Some(accessor) = declaration_access.accessor.filter(|node| {
                    let mut cursor = Cursor::new(self.tree, *node).unwrap();
                    cursor.goto_parent().map_or(false, |node| node.kind() != "formal_parameters")
                }) {
                    // If the accessor is suitable, push it onto the queue alongside the
                    // path that leads to it.
                    bfs_q.push_back((accessor, path));
                }
            }
        }

        Ok(found_paths)
    }

    pub fn accesses_of(&self, node: Node<'a>) -> Option<&Vec<Access<'a>>> {
        self.accesses.get(&node)
    }
}

#[cfg(test)]
mod tests {
    use tree_sitter::Point;

    use super::*;

    impl<'a> AccessEdge<'a> {
        pub fn repr(&self, tree: &Tree) -> String {
            if let Some(accessor) = self.access.accessor.as_ref().copied() {
                format!(
                    "Node `{}` ({}, {}) accessed from node `{}` ({}, {})",
                    tree.repr_of(self.accessed),
                    self.accessed.start_position().row,
                    self.accessed.start_position().column,
                    tree.repr_of(accessor),
                    accessor.start_position().row,
                    accessor.start_position().column,
                )
            } else {
                format!(
                    "Node `{}` ({}, {}) accessed",
                    tree.repr_of(self.accessed),
                    self.accessed.start_position().row,
                    self.accessed.start_position().column,
                )
            }
        }
    }

    // Test that the identifier in a catch expression is correctly inserted into its
    // scope.
    #[test]
    fn test_try_catch_scope() {
        let tree = Tree::new(r#"try { } catch (exception) { exception; }"#.to_string()).unwrap();
        let st = SymbolTable::new(&tree);
        let accesses = AccessGraph::new(&tree, &st);

        // The `exception` catch parameter
        let param = tree
            .root_node()
            .descendant_for_point_range(Point::new(0, 15), Point::new(0, 24))
            .unwrap();

        // The `exception` identifier in the catch block.
        let ident = tree
            .root_node()
            .descendant_for_point_range(Point::new(0, 28), Point::new(0, 36))
            .unwrap();

        let paths = accesses.compute_paths(|access| access.node == param, ident).unwrap();
        println!("{paths:#?}");
        assert!(!paths.is_empty());
    }

    #[test]
    fn accessor_function_declarations() {
        let code = r#"
            function foo() {
                function bar() {
                }

                let quux = bar;
            }
        "#;

        // The `foo` declaration has no accessor.
        assert!(is_accessor(code, (1, 21, 23), None));
        // The `bar` declaration has no accessor.
        assert!(is_accessor(code, (2, 25, 27), None));
        // The `bar` node in `quux = bar` has `quux` as accessor.
        assert!(is_accessor(code, (5, 27, 29), Some((5, 20, 24))));
        // The `quux` node has the `foo` declaration as accessor.
        assert!(is_accessor(code, (5, 20, 24), Some((1, 21, 23))));
    }

    #[test]
    fn accessor_anonymous_function() {
        let code = r#"
            let bar = function() { foo() }
            function baz() {
                (function() { foo() }())
            }
        "#;

        // The `foo` call's accessor is the `bar` lexical declaration.
        assert!(is_accessor(code, (1, 35, 37), Some((1, 16, 18))));
        // In the IIFE, the `foo` call's accessor is the `baz` function declaration.
        assert!(is_accessor(code, (3, 30, 32), Some((2, 21, 23))));
    }

    // Check if the accessor of the node is the expected one.
    //
    // As identifiers can't span more than one row, they are specified as
    // `(row, start_column, end_column)` here for brevity.
    fn is_accessor(
        code: &str,
        accessed: (usize, usize, usize),
        accessor: Option<(usize, usize, usize)>,
    ) -> bool {
        let tree = Tree::new(code.to_string()).unwrap();
        let mut cursor_cache = TreeCursorCache::new(&tree);
        let accessed = tree
            .root_node()
            .descendant_for_point_range(
                Point::new(accessed.0, accessed.1),
                Point::new(accessed.0, accessed.2),
            )
            .unwrap();
        let accessor = accessor.and_then(|accessor| {
            tree.root_node().descendant_for_point_range(
                Point::new(accessor.0, accessor.1),
                Point::new(accessor.0, accessor.2),
            )
        });

        let found_accessor = AccessGraph::find_accessor(&mut cursor_cache, accessed);
        println!("Found accessor: {found_accessor:?}");
        accessor == found_accessor
    }

    #[test]
    fn named_function() {
        let code = r#"
            function foo() { }

            function bar() {
                foo();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn named_parenthesized_function() {
        let code = r#"
            function foo() { }

            function bar() {
                (foo());
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn immediate_named_function() {
        let code = r#"
            function foo() { }

            function bar() {
                (function test() { foo(); })();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn assigned_named_function() {
        let code = r#"
            function foo() { }

            function bar() {
                var xxx = function test() {
                    foo();
                };
                xxx();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn assigned_anonymous_function() {
        let code = r#"
            function foo() { }

            function bar() {
                var test = function() { foo(); };
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn assigned_anonymous_parenthesized_function() {
        let code = r#"
            function foo() { }

            function bar() {
                var test = (((function() { foo(); })));
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn immediate_anonymous_function() {
        let code = r#"
            function foo() { }

            function bar() {
                (function() { foo(); })();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn assigned_lambda() {
        let code = r#"
            function foo() { }

            function bar() {
                var test = () => { foo(); };
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn immediate_lambda() {
        let code = r#"
            function foo() { }

            function bar() {
                () => { foo(); }();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn bracketed_lambda() {
        let code = r#"
            function foo() { }

            function bar() {
                {x = (
                    () => { foo(); }
                )}

                x()
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn renamed_function() {
        let code = r#"
            function foo() { }

            renamed = foo;

            function bar() {
                renamed();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn leaked_renamed_function() {
        let code = r#"
            function foo() { }

            {
                var leaked = foo;
            }

            function bar() {
                leaked();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn parenthesized_variable() {
        let code = r#"
            function foo() { }

            var leaked = ( ( ( foo ) ) );

            function bar() {
                leaked();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn simple_var_declaration() {
        let code = r#"
            function foo() { }

            var test = foo;

            function bar() {
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn simple_let_declaration() {
        let code = r#"
            function foo() { }

            let test = foo;

            function bar() {
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn simple_const_declaration() {
        let code = r#"
            function foo() { }

            const test = foo;

            function bar() {
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn convoluted_variables() {
        let code = r#"
            function foo() { }

            function hoisting() {
                hoisted = foo;
            }

            let global = hoisted;

            function bar() {
                global();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn structured_variables() {
        let code = r#"
            function foo() { }

            var test = {
                sub: {
                    subsub: {
                        fun: foo,
                    },
                },
            };

            function bar() {
                test.sub.subsub.fun();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn indexed_access() {
        let code = r#"
            function foo() { }

            var test = {
                sub: foo,
            };

            function bar() {
                test["sub"]();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn hoisted_variable() {
        let code = r#"
            function foo() { }

            function hoisting() {
                test = foo;
            }
            hoisting();

            function bar() {
                test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn anonymous_assigned_class() {
        let code = r#"
            function foo() { }

            Test = class {
                constructor() {
                    foo();
                }
            };

            function bar() {
                new Test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn named_class() {
        let code = r#"
            function foo() { }

            class Test {
                constructor() {
                    foo();
                }
            };

            function bar() {
                new Test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_getter() {
        let code = r#"
            function foo() { }

            class Test {
                get width() {
                    foo();
                }
            };

            function bar() {
                var test = new Test();
                test.width();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_static() {
        let code = r#"
            function foo() { }

            class Test {
                static func = foo;
            };

            function bar() {
                Test.func();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_field_unreachable() {
        let code = r#"
            function foo() { }

            var func = foo;

            class Test {
                func = 3;
            };

            function bar() {
                Test.func();
            }
        "#;
        assert!(!is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_field_private() {
        let code = r#"
            function foo() { }

            class Test {
                #func = foo;

                constructor() {
                    this.func();
                }
            };

            function bar() {
                new Test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_inheritance() {
        let code = r#"
            function foo() { }

            class Parent {
                constructor() {
                    foo();
                }
            }

            class Test extends Parent {
                constructor() {
                    super();
                }
            };

            function bar() {
                new Test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_field_inheritance() {
        let code = r#"
            function foo() { }

            class Parent {
                field = foo;
            }

            class Test extends Parent {
                constructor() {
                    super.field();
                }
            };

            function bar() {
                new Test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_function_inheritance() {
        let code = r#"
            function foo() { }

            class Parent {
                proxy() {
                    foo();
                }
            }

            class Test extends Parent {
                constructor() {
                    super.proxy();
                }
            };

            function bar() {
                new Test();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_function() {
        let code = r#"
            function foo() { }

            class Test {
                proxy() {
                    foo();
                }
            };

            function bar() {
                new Test().proxy();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn class_generator() {
        let code = r#"
            function foo() { }

            class Test {
                *proxy() {
                    yield foo();
                }
            };

            function bar() {
                new Test().proxy();
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn try_block() {
        let code = r#"
            function foo() { }

            function bar() {
                try {
                    foo();
                } catch(error) {
                }
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn catch_block() {
        let code = r#"
            function foo() { }

            function bar() {
                try {
                } catch(error) {
                    foo();
                }
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn catch_variable_unreachable() {
        let code = r#"
            function foo() { }

            function bar() {
                try {
                } catch(foo) {
                    foo();
                }
            }
        "#;
        assert!(!is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn try_catch_separate_scopes() {
        let code = r#"
            function foo() { }

            function bar() {
                try {
                    let foo = 13;
                } catch(error) {
                    foo();
                }
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn catch_variable_not_leaking() {
        let code = r#"
            function foo() { }

            function bar() {
                foo();
                try { } catch(foo) { }
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));

        let code = r#"
            function foo() { }

            function bar() {
                try {
                    foo();
                } catch(foo) { }
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn array_destructuring_assignment() {
        let code = r#"
            function foo() {}

            function bar() {
                var [ foo ] = [ foo ];
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));

        let code = r#"
            function foo() {}

            function bar() {
                let [ foo ] = [ foo ];
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    #[test]
    fn object_destructuring_assignment() {
        let code = r#"
            function foo() {}

            function bar() {
                var { foo } = { foo: foo };
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));

        let code = r#"
            function foo() {}

            function bar() {
                let { foo } = { foo: foo };
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    // This test fails because the node in the RHS of the assignment is of kind
    // "shorthand_property_identifier". Note that the LHS also does not have an
    // identifier, but it has a "shorthand_property_identifier_pattern".
    #[test]
    #[ignore]
    fn object_destructuring_assignment_with_shorthand() {
        let code = r#"
            function foo() {}

            function bar() {
                var { foo } = { foo };
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));

        let code = r#"
            function foo() {}

            function bar() {
                let { foo } = { foo };
            }
        "#;
        assert!(is_reachable(code, "bar", "foo"));
    }

    /// Check if the `origin` node is able to reach the `target` node.
    fn is_reachable(code: &str, origin: &str, target: &str) -> bool {
        // Find node ranges for start and end.
        let mut origin_range = None;
        let mut target_range = None;
        for (i, line) in code.lines().enumerate() {
            if let Some(offset) = line.find(origin).filter(|_| origin_range.is_none()) {
                let start = Point::new(i, offset);
                let end = Point::new(i, offset + origin.len());
                origin_range = Some((start, end));
            }

            if let Some(offset) = line.find(target).filter(|_| target_range.is_none()) {
                let start = Point::new(i, offset);
                let end = Point::new(i, offset + origin.len());
                target_range = Some((start, end));
            }
        }

        let origin_range = origin_range.unwrap();
        let target_range = target_range.unwrap();

        // Create access graph.
        let tree = Tree::new(code.into()).unwrap();
        let st = SymbolTable::new(&tree);
        let accesses = AccessGraph::new(&tree, &st);
        st.pretty_display();

        // Get the tree nodes for the origin and target.
        let origin_node =
            tree.root_node().descendant_for_point_range(origin_range.0, origin_range.1).unwrap();
        let target_node =
            tree.root_node().descendant_for_point_range(target_range.0, target_range.1).unwrap();

        // Ensure origin can reach target.
        let paths =
            accesses.compute_paths(|access| access.node == origin_node, target_node).unwrap();

        !paths.is_empty()
    }
}
