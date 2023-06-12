//! Table of symbols in a source file.

use std::collections::{HashMap, HashSet};
use std::mem;

use itertools::Itertools;
use tree_sitter::{Node, QueryCursor};

use crate::{Cursor, Tree};

// A (lexical) scope.
#[derive(Debug)]
pub struct Scope<'a> {
    level: usize,
    node: Node<'a>,
    names: HashSet<Node<'a>>,
    assignments: HashSet<Node<'a>>,
}

impl<'a> Scope<'a> {
    /// The nesting level of the scope. 0 is the scope for the `program` node.
    pub fn level(&self) -> usize {
        self.level
    }

    /// The tree node for this scope.
    pub fn node(&self) -> Node<'a> {
        self.node
    }

    /// The names that are defined in this scope.
    pub fn names(&self) -> &HashSet<Node<'a>> {
        &self.names
    }

    /// Add a symbol to the names in the scope.
    pub fn define(&mut self, symbol: Node<'a>) {
        self.names.insert(symbol);
    }

    /// Lookup a symbol by name.
    ///
    /// Find the node among the `names` whose representation is equivalent to
    /// the supplied string.
    pub fn lookup_by_name(&self, name: &str, tree: &Tree) -> HashSet<Node<'a>> {
        self.names.iter().filter(|&&n| tree.repr_of(n) == name).copied().collect()
    }
}

// A stateful visitor that traverses the AST and gather the scoped symbol table.
#[derive(Debug, Default)]
struct SymbolTableBuilder<'a> {
    cur_level: usize,
    scope_table: Vec<Scope<'a>>,
    scope_stack: Vec<Scope<'a>>,
    visited_nodes: HashSet<Node<'a>>,
}

impl<'a> SymbolTableBuilder<'a> {
    fn build(tree: &'a Tree) -> SymbolTable<'a> {
        // Instantiate an empty builder.
        let mut visitor = SymbolTableBuilder::default();

        // Recursively visit all the nodes in the tree, starting from the root.
        visitor.visit(tree.root_node());

        // Reverse the scope table. This makes it so that the first scope is the
        // `program` node's scope.
        visitor.scope_table = visitor.scope_table.into_iter().rev().collect();

        // Create a dictionary that associates each scope node to its index
        // in the scope table. This dictionary can be accessed in O(1) to retrieve
        // the scope object pertaining to a given scope node.
        let scope_indices = visitor
            .scope_table
            .iter()
            .enumerate()
            .map(|(idx, scope)| (scope.node, idx))
            .collect::<HashMap<_, _>>();

        let mut table = SymbolTable { tree, scopes: visitor.scope_table, scope_indices };

        // Hoist assignments which were not declared as variables.
        for i in 0..table.scopes.len() {
            let assignments = mem::take(&mut table.scopes[i].assignments);
            for name in assignments {
                let cursor = Cursor::new(tree, name).unwrap();
                if table.lookup(cursor).is_none() {
                    table.scopes[0].define(name);
                }
            }
        }

        table
    }

    // Retrieve the root scope, the only one that has a level of 0.
    // TODO can we assume that this is always the first scope on the stack?
    // If so, this could be changed to `self.scope_stack.first_mut().unwrap()`.
    fn root_scope(&mut self) -> &mut Scope<'a> {
        self.scope_stack.iter_mut().find(|scope| scope.level == 0).unwrap()
    }

    // Starting from the end of the scope stack, find the first scope that's a
    // function; default to the program scope if none is found.
    fn find_parent_function_scope(&mut self) -> Option<&mut Scope<'a>> {
        self.scope_stack.iter_mut().rev().find(|scope| {
            if scope.level == 0 {
                return true;
            }

            let parent = match scope.node.parent() {
                Some(parent) => parent,
                None => return false,
            };

            matches!(
                parent.kind(),
                "function_declaration"
                    | "generator_function_declaration"
                    | "function"
                    | "generator_function"
            )
        })
    }

    // Push a scope on the stack, and increment the current level.
    // This operation happens when entering a new scope.
    fn push_scope(&mut self, node: Node<'a>) {
        self.scope_stack.push(Scope {
            node,
            level: self.cur_level,
            assignments: Default::default(),
            names: Default::default(),
        });
        self.cur_level += 1;
    }

    // Pop the last scope off the stack, add it to the scope table, and decrease the
    // current level. This operation happens when leaving a scope.
    fn pop_scope(&mut self) {
        self.scope_table.push(self.scope_stack.pop().unwrap());
        self.cur_level -= 1;
    }

    // Visit a node.
    fn visit(&mut self, node: Node<'a>) {
        // If the node has already been visited, return.
        if self.visited_nodes.contains(&node) {
            return;
        }

        // Insert the node among those that have been visited.
        self.visited_nodes.insert(node);

        match node.kind() {
            "statement_block" | "program" => {
                // Statement block and program nodes are the only node types
                // that create a new scope.
                self.push_scope(node);

                let mut cur_node = node.prev_named_sibling();

                // Move leftwards through the sibling nodes, searching for a
                // node of kind `formal_parameters`. If one is found, visit it:
                // that will define the identifiers that are found in the formal
                // parameters list as variables that are available in the scope
                // we just defined.
                while let Some(node) = cur_node {
                    if node.kind() == "formal_parameters" {
                        self.visit(node);
                    }
                    cur_node = node.prev_named_sibling();
                }

                // Visit all of the children nodes of this scope.
                self.visit_children(node);

                // Exit the scope.
                self.pop_scope();
            },
            "function_declaration" | "generator_function_declaration" | "class_declaration" => {
                // Function declarations show up in the parent *function* scope.

                // Find the name of the function.
                let name = node.child_by_field_name(b"name").unwrap();

                // Find the parent function scope of this declaration.
                let scope = self.find_parent_function_scope().unwrap();

                // Define the name of the function in that scope.
                scope.define(name);

                // Prioritize visiting the statement block and then the formal parameters.
                self.visit_children(node);
            },
            "variable_declaration" => {
                // Variable declarations show up in the parent *function* scope.

                // Loop through the `variable_declarator` child nodes of this node.
                for declarator_node in node.named_children(&mut node.walk()) {
                    if declarator_node.kind() != "variable_declarator" {
                        continue;
                    }

                    // Retrieve the identifier of the declarator.
                    let name = declarator_node.child_by_field_name(b"name").unwrap();

                    // Find the parent function scope of this declaration.
                    let scope = self.find_parent_function_scope().unwrap();

                    // Define the identifier of the declaration in the found scope.
                    scope.define(name);
                }

                self.visit_children(node);
            },
            "lexical_declaration" => {
                // Lexical declarations (const, let) show up in the parent *lexical* scope,
                // i.e. if/for blocks etc.

                // Loop through the `variable_declarator` child nodes of this node.
                for declarator_node in node.named_children(&mut node.walk()) {
                    if declarator_node.kind() != "variable_declarator" {
                        continue;
                    }

                    // Retrieve the current scope from the stack.
                    let scope = self.scope_stack.last_mut().unwrap();

                    // Retrieve the name of the declaration.
                    let name = declarator_node.child_by_field_name(b"name").unwrap();

                    // Define the name in the current scope.
                    scope.define(name);
                }

                self.visit_children(node);
            },
            "assignment_expression" | "augmented_assignment_expression" => {
                // Add assignments to their scope, allowing identification of hoisted variables.
                let scope = self.find_parent_function_scope().unwrap();
                let name = node.child_by_field_name(b"left").unwrap();
                if !scope.names.contains(&name) {
                    scope.assignments.insert(name);
                }

                self.visit_children(node);
            },
            "formal_parameters" => {
                // Formal parameters show up in the sibling function scope, which is also the
                // current scope.

                // Retrieve the current scope.
                let scope = self.scope_stack.last_mut().unwrap();

                // Define each formal parameter's identifier in the current scope.
                for i in 0..node.named_child_count() {
                    let parameter_name = node.named_child(i).unwrap();
                    scope.define(parameter_name);
                }
            },
            "catch_clause" => {
                // Catch clause identifier has to be registered in the child statement block.
                if let Some(catch_statement) = node.child_by_field_name(b"body") {
                    // Create scope for catch block.
                    self.push_scope(catch_statement);

                    // Define catch parameter for its block.
                    let scope = self.scope_stack.last_mut().unwrap();

                    // Define the catch parameter in the current scope.
                    if let Some(catch_param) = node.child_by_field_name(b"parameter") {
                        scope.define(catch_param);
                    }

                    // Parse catch block children.
                    self.visit_children(catch_statement);

                    // Go back to parent scope.
                    self.pop_scope();
                }
            },
            "import_specifier" => {
                // import { a, b as c } from 'foo'

                // Retrieve the root scope, as that's where all imports are defined.
                let scope = self.root_scope();

                // If there is an alias, define that in the root scope; otherwise,
                // define the name. In the example above, the imported `b` would be
                // defined as the node `c` in the root scope because it has an alias, and the
                // imported `a` would be defined as itself because it has no
                // alias.
                let name = node.child_by_field_name(b"name").unwrap();
                let alias = node.child_by_field_name(b"alias");
                scope.define(alias.unwrap_or(name));

                self.visit_children(node);
            },
            "namespace_import" | "import_clause" => {
                // import something from 'foo'
                // import * as something from 'foo'

                // Retrieve the root scope, as that's where all imports are defined.
                let scope = self.root_scope();

                // For namespace imports and import clauses, directly put
                // immediate `identifier` children nodes in the root scope.
                for i in 0..node.named_child_count() {
                    let identifier = node.named_child(i).unwrap();
                    if identifier.kind() == "identifier" {
                        scope.define(identifier);
                    }
                }

                self.visit_children(node);
            },
            _ => {
                // Recursively keep visiting children for all the other kinds of nodes.
                self.visit_children(node);
            },
        }
    }

    fn visit_children(&mut self, node: Node<'a>) {
        // Visit the children in reverse order so that the scopes are pushed
        // onto the stack in the correct order.
        for i in (0..node.named_child_count()).rev() {
            self.visit(node.named_child(i).unwrap());
        }
    }
}

#[derive(Debug)]
pub struct SymbolTable<'a> {
    tree: &'a Tree,
    scopes: Vec<Scope<'a>>,
    // Cache for O(1) lookups of the `scopes` vector. Associate each scope node
    // to its index in the scopes vector.
    scope_indices: HashMap<Node<'a>, usize>,
}

impl<'a> SymbolTable<'a> {
    pub fn new(tree: &'a Tree) -> Self {
        SymbolTableBuilder::build(tree)
    }

    /// Return the list of scopes.
    pub fn scopes(&self) -> &Vec<Scope<'a>> {
        &self.scopes
    }

    /// Return the root scope.
    pub fn root_scope(&self) -> &Scope<'a> {
        &self.scopes[0]
    }

    /// Define a new symbol in the given scope.
    pub fn define(&mut self, scope: Node<'a>, symbol: Node<'a>) {
        if let Some(scope) =
            self.scope_indices.get(&scope).and_then(|&idx| self.scopes.get_mut(idx))
        {
            scope.define(symbol);
        }
    }

    /// Retrieve the scope object for a given scope node.
    pub fn get_scope(&self, scope: Node<'a>) -> Option<&Scope<'a>> {
        self.scope_indices.get(&scope).and_then(|&idx| self.scopes.get(idx))
    }

    /// Lookup an identifier. Returns the scope in which it is defined, and the
    /// node at which it is declared.
    pub fn lookup(&self, mut cursor: Cursor<'a>) -> Option<(&Scope<'a>, Node<'a>)> {
        // Skip lookup if the node is not an identifier.
        let node = cursor.node();
        if node.kind() != "identifier" {
            return None;
        }

        let name = self.tree.repr_of(node);

        // For function parameters, the scope is the function body.
        let mut parent = cursor.goto_parent().unwrap();
        if parent.kind() == "formal_parameters" {
            // Get function body.
            let grandparent = cursor.clone().goto_parent().unwrap();
            let body = grandparent.child_by_field_name("body").unwrap();

            if body.kind() == "statement_block" {
                // Get scope and ensure the identifier is defined in it.
                let scope = self.get_scope(body).unwrap();
                assert!(scope.names.iter().any(|&node| self.tree.repr_of(node) == name));

                return Some((scope, node));
            } else {
                // Lambda parameters without body do not belong to any scope.
                //
                // Example: `(param) => console.log(param);`
                return None;
            }
        }

        // For parameters in a catch clause, the scope is the catch body.
        if parent.kind() == "catch_clause" {
            // Get catch body.
            let body = parent.child_by_field_name("body").unwrap();

            // Get scope and ensure the identifier is defined in it.
            let scope = self.get_scope(body).unwrap();
            assert!(scope.names.iter().any(|&node| self.tree.repr_of(node) == name));

            return Some((scope, node));
        }

        // Find parent scope node. Guaranteed to exist: "program" is the topmost and
        // worst case.
        let parent_scope_node = loop {
            if matches!(parent.kind(), "statement_block" | "program") {
                break parent;
            }

            parent = cursor.goto_parent().unwrap();
        };

        // Find the parent scope (where the identifier is used).
        //
        // Invariants: scope_indices.get(parent_scope_node) exists if the
        // visitor algorithm is correct and all the scopes were accounted
        // for. Otherwise, the algorithm is incorrect and stop-the-world is
        // appropriate behavior.
        let mut parent_scope_index = *self.scope_indices.get(&parent_scope_node).unwrap();

        // Find the declaration scope (where the identifier is declared).
        //
        // Starting from the parent scope's index, walk back through the parent
        // layers until a scope with the node name is declared.
        let (decl_scope, decl_node) =
            loop {
                // Retrieve the scope.
                let scope = &self.scopes[parent_scope_index];

                // If the scope contains a declaration named like the node we are looking up,
                // return the scope and the declaration node.
                if let Some(decl_node) = scope.names.iter().find_map(|&node| {
                    if self.tree.repr_of(node) == name { Some(node) } else { None }
                }) {
                    break (scope, decl_node);
                }

                // If we walked all the way to the program node, we haven't found the
                // declaration. We can directly return `None` from here.
                if parent_scope_index == 0 {
                    return None;
                }

                let cur_level = scope.level;

                // Walking backwards, find the first scope with level less than the current.
                //
                // This assumes that:
                // - all the sibling scopes have the same level as cur_level,
                // - all scopes appear to the right of their parent scope in self.scopes
                // - all scopes' siblings appear contiguously
                // - no scopes of level less than or equal to the parent's level appear between
                //   a parent scope and its child scopes
                while parent_scope_index > 0 && self.scopes[parent_scope_index].level >= cur_level {
                    parent_scope_index -= 1;
                }
            };

        Some((decl_scope, decl_node))
    }

    // Pretty print the source code, with identifiers colored according to the
    // scope they belong to.
    pub fn pretty_display(&self) {
        // color_table[i] is the color of the i-th scope.
        let color_table =
            (0..self.scopes.len()).map(|color| 16 + ((color + 1) * 32) % 231).collect::<Vec<_>>();

        let query = self.tree.query("(identifier) @ident").unwrap();
        let mut cur = QueryCursor::new();
        let colorings: Vec<(Node<'a>, Option<usize>)> = cur
            .matches(&query, self.tree.root_node(), self.tree.buf().as_bytes())
            .map(|query_match| {
                let node = query_match.captures[0].node;
                let cursor = Cursor::new(self.tree, node).unwrap();
                let scope_index = self
                    .lookup(cursor)
                    .map(|(scope, _)| *self.scope_indices.get(&scope.node).unwrap());
                (node, scope_index)
            })
            .sorted_by_key(|(node, _)| node.start_byte())
            .collect();

        let mut cur_point = 0usize;
        let buf = self.tree.buf();
        for (node, color_idx) in colorings {
            if node.start_byte() < cur_point {
                continue;
            }

            print!("\x1b[0m{}", &buf[cur_point..node.start_byte()],);
            if let Some(idx) = color_idx {
                print!("\x1b[38;5;{}m", color_table[idx]);
            } else {
                print!("\x1b[37m\x1b[41m");
            }
            print!("{}", &buf[node.start_byte()..node.end_byte()]);
            cur_point = node.end_byte();
        }
        print!("\x1b[0m{}", &buf[cur_point..]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
        let tree = Tree::new(
            r#"
            const const_global

            function func1_global() {
                const const_scope1

                {
                    const const_scope2
                }
            }

            function func2_global(param_scope3) {
                const const_scope3
                var var_scope3

                if (undefined_ident1 == 2) {
                    let let_scope4
                }

                if (undefined_ident2 == 2) {
                    var var_scope3
                    let let_scope5

                    function func3_scope3() {
                        var var_scope6
                        let let_scope6
                    }
                }
            }
            "#
            .to_string(),
        )
        .unwrap();

        let st = SymbolTable::new(&tree);
        st.pretty_display();
    }

    // Test the uncommon (but valid) situation in which there is a comment between
    // a formal parameter list and a function body.
    #[test]
    fn test_formal_param_comment() {
        let tree = Tree::new(
            r#"
            function fn1(arg1, arg2) {}
            function fn2(arg1, arg2) /* comment */ {}
            "#
            .to_string(),
        )
        .expect("Should not panic");

        let st = SymbolTable::new(&tree);
        st.pretty_display();
    }
}
