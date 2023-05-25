//! ESM and CommonJS imports.

use std::iter::Copied;
use std::ops::Deref;

use lazy_static::lazy_static;
use tree_sitter::{Node, Query, QueryCursor};

use crate::{Error, Tree, JS, Cursor};

// CommonJS
//
// Imports in CommonJS are always of a single form:
//
// require("module")
//
// Destructuring, assignments and member lookups should be dealt with by the
// reachability queries.

#[derive(Debug, Clone, Copy)]
pub struct CommonJsImport<'a> {
    node: Node<'a>,
    source: &'a str,
}

impl<'a> CommonJsImport<'a> {
    /// The node of the import.
    ///
    /// # Example
    ///
    /// In the following, it is the node referring to the string segment `bar`.
    ///
    /// ```js
    /// const foo = require('bar')
    /// ```
    pub fn node(&self) -> Node<'a> {
        self.node
    }

    /// The source of the import; a string representation of the import node.
    ///
    /// # Example
    ///
    /// In the following, it is the string `bar`.
    ///
    /// ```js
    /// const foo = require('bar')
    /// ```
    pub fn source(&self) -> &'a str {
        self.source
    }

    /// The node through which the import is accessed.
    ///
    /// # Example
    ///
    /// In the following, the `bar` string segment is `self.node`,
    /// and `foo` is the access node.
    ///
    /// ```js
    /// const foo = require('bar')
    /// ```
    pub fn access_node(&self, tree: &'a Tree) -> Node<'a> {
        let cursor = Cursor::new(tree, self.node).unwrap();
        cursor
            .parents()
            .find_map(|node| match node.kind() {
                "assignment_expression" | "augmented_assignment_expression" => {
                    node.child_by_field_name("left")
                },
                "variable_declarator" => node.child_by_field_name("name"),
                _ => None,
            })
            .unwrap_or(self.node)
    }
}

#[derive(Default, Debug)]
pub struct CommonJsImports<'a>(Vec<CommonJsImport<'a>>);

impl<'a> CommonJsImports<'a> {
    pub fn new(imports: Vec<CommonJsImport<'a>>) -> Self {
        Self(imports)
    }
}

impl<'a> Deref for CommonJsImports<'a> {
    type Target = Vec<CommonJsImport<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> TryFrom<&'a Tree> for CommonJsImports<'a> {
    type Error = Error;

    fn try_from(tree: &'a Tree) -> Result<Self, Self::Error> {
        let mut cur = QueryCursor::new();

        lazy_static! {
            static ref QUERY: Query =
                Query::new(*JS, include_str!("../queries/commonjs-imports.lsp")).unwrap();
        };

        Ok(CommonJsImports(
            cur.matches(&QUERY, tree.root_node(), tree.buf().as_bytes())
                .map(|query_match| query_match.captures[1].node)
                .map(|node| CommonJsImport { node, source: tree.repr_of(node) })
                .collect(),
        ))
    }
}

impl<'a> IntoIterator for CommonJsImports<'a> {
    type IntoIter = <Vec<CommonJsImport<'a>> as IntoIterator>::IntoIter;
    type Item = CommonJsImport<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, 'b> IntoIterator for &'b CommonJsImports<'a> {
    type IntoIter = Copied<<&'b Vec<CommonJsImport<'a>> as IntoIterator>::IntoIter>;
    type Item = CommonJsImport<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().copied()
    }
}

// ESM Imports
//
// All the compatible ESM import statements are the following:
//
// 1. Default imports
//    - import name from 'module' Puts `name` in the module scope, refers to the
//      object exported as `default` in 'module'.
// 2. Namespace imports
//    - import * as name from 'module' Puts `name` in the module scope, refers
//      to the object of all exports from 'module'.
// 3. Named imports
//    - import { foo, bar } from 'module' Puts `foo` and `bar` in the module
//      scope.
// 4. Aliased named imports
//    - import { foo as bar } from 'module' Puts `bar` in the module scope,
//      refers to `foo` in 'module'.
// 5. Reexports (actually an export, but works like an import!)
//    - export { foo as bar } from 'module'
//

#[derive(Debug, Clone)]
pub enum EsmImport<'a> {
    Named {
        name: &'a str,
        alias: Option<&'a str>,
        alias_node: Option<Node<'a>>,
        source: &'a str,
        node: Node<'a>,
    },
    Namespace {
        name: &'a str,
        source: &'a str,
        node: Node<'a>,
    },
    Default {
        name: &'a str,
        source: &'a str,
        node: Node<'a>,
    },
}

#[derive(Default, Debug)]
pub struct EsmImports<'a>(Vec<EsmImport<'a>>);

impl<'a> EsmImports<'a> {
    pub fn new(imports: Vec<EsmImport<'a>>) -> Self {
        Self(imports)
    }
}

impl<'a> Deref for EsmImports<'a> {
    type Target = Vec<EsmImport<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> TryFrom<&'a Tree> for EsmImports<'a> {
    type Error = Error;

    fn try_from(tree: &'a Tree) -> Result<Self, Self::Error> {
        let mut cur = QueryCursor::new();

        lazy_static! {
            static ref QUERY: Query =
                Query::new(*JS, include_str!("../queries/esm-imports.lsp")).unwrap();
        };

        let mut imports = Vec::new();

        for query_match in cur.matches(&QUERY, tree.root_node(), tree.buf().as_bytes()) {
            match query_match.pattern_index {
                0 => {
                    // import name from "module"
                    imports.push(EsmImport::Default {
                        name: tree.repr_of(query_match.captures[0].node),
                        source: tree.repr_of(query_match.captures[1].node),
                        node: query_match.captures[0].node,
                    });
                },
                1 => {
                    // import * as name from "module"
                    imports.push(EsmImport::Namespace {
                        name: tree.repr_of(query_match.captures[0].node),
                        source: tree.repr_of(query_match.captures[1].node),
                        node: query_match.captures[0].node,
                    });
                },
                2 => {
                    // import { foo } from "module"
                    // import { foo as bar } from "module"
                    let import_spec = query_match.captures[0].node;
                    let source = query_match.captures[1].node;
                    let name = import_spec.child_by_field_name("name").unwrap();
                    let alias = import_spec.child_by_field_name("alias");
                    imports.push(EsmImport::Named {
                        name: tree.repr_of(name),
                        source: tree.repr_of(source),
                        alias: alias.map(|node| tree.repr_of(node)),
                        alias_node: alias,
                        node: name,
                    });
                },
                k => unreachable!("{}: {:#?}", k, query_match),
            }
        }

        Ok(EsmImports(imports))
    }
}

impl<'a> IntoIterator for EsmImports<'a> {
    type IntoIter = <Vec<EsmImport<'a>> as IntoIterator>::IntoIter;
    type Item = EsmImport<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, 'b> IntoIterator for &'b EsmImports<'a> {
    type IntoIter = <&'b Vec<EsmImport<'a>> as IntoIterator>::IntoIter;
    type Item = &'b EsmImport<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> EsmImport<'a> {
    pub fn name(&self) -> &str {
        match self {
            &EsmImport::Named { name, .. }
            | &EsmImport::Namespace { name, .. }
            | &EsmImport::Default { name, .. } => name,
        }
    }

    pub fn source(&self) -> &str {
        match self {
            &EsmImport::Named { source, .. }
            | &EsmImport::Namespace { source, .. }
            | &EsmImport::Default { source, .. } => source,
        }
    }

    pub fn alias(&self) -> Option<&str> {
        match self {
            EsmImport::Named { alias, .. } => *alias,
            _ => None,
        }
    }

    pub fn alias_node(&self) -> Option<Node<'a>> {
        match self {
            EsmImport::Named { alias_node, .. } => *alias_node,
            _ => None,
        }
    }

    pub fn node(&self) -> Node<'a> {
        match self {
            EsmImport::Named { node, .. }
            | EsmImport::Namespace { node, .. }
            | EsmImport::Default { node, .. } => *node,
        }
    }
}

#[derive(Debug)]
pub enum Imports<'a> {
    Esm(EsmImports<'a>),
    CommonJs(CommonJsImports<'a>),
    None,
}

impl<'a> Imports<'a> {
    pub fn new(tree: &'a Tree) -> Self {
        if let Ok(esm_imports) = EsmImports::try_from(tree) {
            if !esm_imports.is_empty() {
                return Imports::Esm(esm_imports);
            }
        }

        if let Ok(cjs_imports) = CommonJsImports::try_from(tree) {
            if !cjs_imports.is_empty() {
                return Imports::CommonJs(cjs_imports);
            }
        }

        Imports::None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_commonjs_imports() {
        let tree = Tree::new(
            r#"
            const name1 = require("foo")
            let name2 = require("foo")
            var name3 = require("foo")
            name2 = require("foo").bar.baz
            "#
            .to_string(),
        )
        .unwrap();

        let imports = CommonJsImports::try_from(&tree).unwrap();
        println!("{:#?}", imports);

        assert_eq!(imports.len(), 4);

        for import in imports {
            assert_eq!("foo", tree.repr_of(import.node()));
            assert_eq!("foo", import.source());
        }
    }

    #[test]
    fn test_esm_imports() {
        let tree = Tree::new(
            r#"
            import * as namespaced from 'foo'
            import defaultImport from 'foo'
            import defaultImportComposite, { named1, named2 as foo } from 'foo'
            "#
            .to_string(),
        )
        .unwrap();

        let imports = EsmImports::try_from(&tree).unwrap();
        println!("{:#?}", imports);

        assert_eq!(imports.0.len(), 5);

        assert!(matches!(imports.0[0], EsmImport::Namespace {
            name: "namespaced",
            source: "foo",
            ..
        }));
        assert!(matches!(imports.0[1], EsmImport::Default {
            name: "defaultImport",
            source: "foo",
            ..
        }));
        assert!(matches!(imports.0[2], EsmImport::Default {
            name: "defaultImportComposite",
            source: "foo",
            ..
        }));
        assert!(matches!(imports.0[3], EsmImport::Named {
            name: "named1",
            alias: None,
            source: "foo",
            ..
        }));
        assert!(matches!(imports.0[4], EsmImport::Named {
            name: "named2",
            alias: Some("foo"),
            source: "foo",
            ..
        }));
    }
}
