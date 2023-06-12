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
    pub fn level(&self) -> usize {
        self.level
    }

    pub fn node(&self) -> Node<'a> {
        self.node
    }

    pub fn names(&self) -> &HashSet<Node<'a>> {
        &self.names
    }

    pub fn define(&mut self, symbol: Node<'a>) {
        self.names.insert(symbol);
    }

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
        let mut visitor = SymbolTableBuilder::default();
        visitor.visit(tree.root_node());

        visitor.scope_table = visitor.scope_table.into_iter().rev().collect();

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

    fn root_scope(&mut self) -> &mut Scope<'a> {
        self.scope_stack.iter_mut().find(|scope| scope.level == 0).unwrap()
    }

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

    fn push_scope(&mut self, node: Node<'a>) {
        self.scope_stack.push(Scope {
            node,
            level: self.cur_level,
            assignments: Default::default(),
            names: Default::default(),
        });
        self.cur_level += 1;
    }

    fn pop_scope(&mut self) {
        self.scope_table.push(self.scope_stack.pop().unwrap());
        self.cur_level -= 1;
    }

    fn visit(&mut self, node: Node<'a>) {
        if self.visited_nodes.contains(&node) {
            return;
        }

        self.visited_nodes.insert(node);

        match node.kind() {
            "statement_block" | "program" => {
                // Statement block and program nodes are the only node types
                // that create a new scope.
                self.push_scope(node);

                let mut cur_node = node.prev_named_sibling();

                while let Some(node) = cur_node {
                    if node.kind() == "formal_parameters" {
                        self.visit(node);
                    }
                    cur_node = node.prev_named_sibling();
                }

                self.visit_children(node);
                self.pop_scope();
            },
            "function_declaration" | "generator_function_declaration" | "class_declaration" => {
                // Function declarations show up in the parent *function* scope.
                let name = node.child_by_field_name(b"name").unwrap();
                let scope = self.find_parent_function_scope().unwrap();
                scope.define(name);

                // Prioritize visiting the statement block and then the formal parameters.
                self.visit_children(node);
            },
            "variable_declaration" => {
                // Variable declarations show up in the parent *function* scope.
                for declarator_node in node.named_children(&mut node.walk()) {
                    if declarator_node.kind() != "variable_declarator" {
                        continue;
                    }
                    let name = declarator_node.child_by_field_name(b"name").unwrap();
                    let scope = self.find_parent_function_scope().unwrap();
                    scope.define(name);
                }

                self.visit_children(node);
            },
            "lexical_declaration" => {
                // Lexical declarations (const, let) show up in the parent *lexical* scope,
                // i.e. if/for blocks etc.
                for declarator_node in node.named_children(&mut node.walk()) {
                    if declarator_node.kind() != "variable_declarator" {
                        continue;
                    }
                    let scope = self.scope_stack.last_mut().unwrap();
                    let name = declarator_node.child_by_field_name(b"name").unwrap();
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
                // Formal parameters show up in the sibling function scope.
                let scope = self.scope_stack.last_mut().unwrap();
                for i in 0..node.named_child_count() {
                    let parameter_name = node.named_child(i).unwrap();
                    scope.define(parameter_name);
                }
            },
            "catch_clause" => {
                // Catch clause identifier has to be registered in the child statement block.
                if let Some(catch_statement) = node.child_by_field_name(b"body") {
                    self.visit(catch_statement);
                    let scope = self.scope_stack.last_mut().unwrap();
                    if let Some(catch_param) = node.child_by_field_name(b"parameter") {
                        scope.define(catch_param);
                    }
                }
            },
            "import_specifier" => {
                // import { a, b as c } from 'foo'
                //
                // Define alias, if it exists, name otherwise, in the root scope.
                let scope = self.root_scope();

                let name = node.child_by_field_name(b"name").unwrap();
                let alias = node.child_by_field_name(b"alias");
                scope.define(alias.unwrap_or(name));

                self.visit_children(node);
            },
            "namespace_import" | "import_clause" => {
                // import something from 'foo'
                // import * as something from 'foo'
                //
                // For namespace imports and import clauses, directly put
                // immediate `identifier` children nodes in the root scope.
                let scope = self.root_scope();

                for i in 0..node.named_child_count() {
                    let identifier = node.named_child(i).unwrap();
                    if identifier.kind() == "identifier" {
                        scope.define(identifier);
                    }
                }

                self.visit_children(node);
            },
            _ => {
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

        // If the identifier is in a formal parameters list, the declaration
        // scope is in the sibling "body" field block.
        let mut parent = cursor.goto_parent().unwrap();
        if parent.kind() == "formal_parameters" {
            // If formal_parameters nodes has a statement_block next sibling, it is a
            // regular function, otherwise it is an arrow function and the
            // identifier doesn't belong to a scope.

            let grandparent = cursor.clone().goto_parent().unwrap();
            let body = grandparent.child_by_field_name("body").unwrap();
            if body.kind() == "statement_block" {
                let scope_index = *self.scope_indices.get(&body).unwrap();
                let scope = &self.scopes[scope_index];
                assert!(scope.names.iter().any(|&node| self.tree.repr_of(node) == name));
                return Some((scope, node));
            }
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
                let scope = &self.scopes[parent_scope_index];
                if let Some(decl_node) = scope.names.iter().find_map(|&node| {
                    if self.tree.repr_of(node) == name { Some(node) } else { None }
                }) {
                    break (scope, decl_node);
                }

                if parent_scope_index == 0 {
                    return None;
                }

                let cur_level = scope.level;
                // Walking backwards, find the first scope with level less than the current.
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
