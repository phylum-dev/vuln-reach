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

                // Get the accessor as defined by the method.
                let accessor = AccessGraph::find_accessor(symbol_table, &mut cursor_cache, node)
                    .and_then(|node| {
                        let cursor = cursor_cache.cursor(node).ok()?;
                        symbol_table.lookup(cursor)
                    })
                    .map(|(_, accessor)| accessor);

                Some(Access { node, scope, decl_node, decl_scope, accessor })
            })
            .fold(HashMap::new(), |mut accesses, access| {
                let entry: &mut Vec<Access> = accesses.entry(access.decl_node).or_default();
                entry.push(access);
                accesses
            });

        Self { accesses, tree }
    }

    // An `accessor` of `node` is defined here as a node which is either:
    // - The identifier of the function surrounding the statement that `node` is in
    // - The scope of the function surrounding the statement that `node` is in (let
    //   something = function() { I access `node` }; something()) This is a special
    //   case and won't yield an identifier, so it will have to be filtered by
    //   `compute_paths` which requires identifiers.
    // - The leftmost identifier in a LHS, if `node` is in a RHS
    // - The identifier of a class name, if the node is accessed in one of its
    //   methods
    //
    // This definition is brittle. Other unaccounted for cases:
    // - something[3] = function { I access `node` }; something[3]()
    // - `node` appears as a function call parameter
    // - { functionName() { } }
    //
    // This is a good spot to improve, but requires deeply thinking about
    // use cases, as "access" does not have a well-defined meaning statically.
    fn find_accessor(
        symbol_table: &SymbolTable<'a>,
        cursor_cache: &mut TreeCursorCache<'a>,
        node: Node<'a>,
    ) -> Option<Node<'a>> {
        // Determine the scope the identifier is in.
        let parent_scope = Self::find_parent_scope(symbol_table, cursor_cache, node);

        // Class declaration identifiers
        if let Some(accessor) = parent_scope.and_then(|scope| {
            let cursor = cursor_cache.cursor(scope).ok()?;
            let class_decl = cursor.parents().find(|node| node.kind() == "class_declaration")?;
            class_decl.child_by_field_name("name")
        }) {
            return Some(accessor);
        }

        // Functions and lambdas.
        if let Some(accessor) = parent_scope.and_then(|scope| {
            // Ensure parent node is a function.
            let mut cursor = cursor_cache.cursor(scope).ok()?;
            match cursor.goto_parent()?.kind() {
                // Find accessor for anonymous functions.
                "function" | "arrow_function" => {
                    // Check if the function is executed or assigned.
                    Self::find_function_access(symbol_table, cursor_cache, cursor.node())
                },
                // Find accessor for named functions.
                "function_declaration" => {
                    // Check the name the function is defined as.
                    let child = cursor.node().child_by_field_name("name")?;

                    // Check if the function is renamed or immediately executed.
                    let access = Self::find_function_access(symbol_table, cursor_cache, child);

                    // If the function is not renamed or executed, fall back to its original name.
                    Some(access.unwrap_or(child))
                },
                _ => None,
            }
        }) {
            return Some(accessor);
        }

        // Generic statement scopes
        if let Some(accessor) = parent_scope {
            return Some(accessor);
        }

        // LHS/RHS expressions
        let lhs_rhs_cursor = cursor_cache.cursor(node).unwrap();
        if let Some(expr) = lhs_rhs_cursor.parents().find(|node| {
            matches!(node.kind(), "assignment_expression" | "augmented_assignment_expression")
        }) {
            let lhs = expr.child_by_field_name(b"left").unwrap();
            // This is very crude. Get the leftmost node in an assignment expression,
            // assuming that it is an identifier.
            let accessor = lhs
                .named_descendant_for_point_range(lhs.start_position(), lhs.start_position())
                .unwrap();
            assert!(accessor.kind() == "identifier" || accessor.kind() == "this");
            return Some(accessor);
        }

        None
    }

    /// Find the parent scope of a node.
    fn find_parent_scope(
        symbol_table: &SymbolTable<'a>,
        cursor_cache: &mut TreeCursorCache<'a>,
        node: Node<'a>,
    ) -> Option<Node<'a>> {
        let mut parent_cursor = cursor_cache.cursor(node).unwrap();
        while let Some(node) = parent_cursor.goto_parent() {
            let parent = parent_cursor.parent()?;

            if parent.child_by_field_name("body") == Some(node)
                && symbol_table.get_scope(node).is_some()
            {
                return Some(node);
            }
        }
        None
    }

    /// Check where a function is assigned to or executed from.
    fn find_function_access(
        symbol_table: &SymbolTable<'a>,
        cursor_cache: &mut TreeCursorCache<'a>,
        node: Node<'a>,
    ) -> Option<Node<'a>> {
        let mut access_node = None;

        let mut cursor = cursor_cache.cursor(node).unwrap();
        while let Some(parent) = cursor.goto_parent() {
            match parent.kind() {
                // Get identifier if this function is assigned to a variable.
                "variable_declarator" => access_node = Some(parent),
                // Find the parent scope for immediately executed anonymous functions.
                "call_expression" => {
                    let scope = Self::find_parent_scope(symbol_table, cursor_cache, parent);
                    access_node = scope?.parent();
                },
                // Running into another function without the current one being executed or
                // assigned means it can never be reached.
                "function" | "arrow_function" => break,
                _ => (),
            }
        }

        access_node?.child_by_field_name("name")
            // TODO: Is this actually necessary?
            .filter(|accessor| accessor.kind() == "identifier")
    }

    // Compute paths between a source node and one or more target nodes.
    // The target nodes are established by the supplied predicate.
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
        let mut visited = HashSet::new();

        let access_scopes = self
            .accesses
            .values()
            .flatten()
            .map(|access| (access.node, access))
            .collect::<HashMap<_, _>>();

        while let Some((node, path)) = bfs_q.pop_front() {
            if visited.contains(&node) {
                continue;
            }

            visited.insert(node);

            let access = access_scopes.get(&node).copied().ok_or_else(|| {
                Error::Generic(format!(
                    "All identifiers should have an access scope: {:?} {}",
                    node,
                    self.tree.repr_of(node)
                ))
            })?;

            let declaration_accesses = self.accesses.get(&access.decl_node).ok_or_else(|| {
                Error::Generic(format!(
                    "All declarations should have a list of accesses: {:?} {}",
                    access.decl_node,
                    self.tree.repr_of(access.decl_node)
                ))
            })?;

            for declaration_access in declaration_accesses {
                let mut path = path.clone();
                path.push(AccessEdge::new(node, *declaration_access));

                if is_target(declaration_access) {
                    found_paths.push(path.to_vec());
                }

                if let Some(accessor) = declaration_access.accessor.filter(|node| {
                    if node.kind() != "identifier" {
                        return false;
                    }

                    let mut cursor = Cursor::new(self.tree, *node).unwrap();
                    cursor.goto_parent().map_or(false, |node| node.kind() != "formal_parameters")
                }) {
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
    fn immediate_unassigned_lambda() {
        let code = r#"
            function foo() { }

            function bar() {
                (() => {
                    () => { foo(); };
                })();
            }
        "#;
        assert!(!is_reachable(code, "bar", "foo"));
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
