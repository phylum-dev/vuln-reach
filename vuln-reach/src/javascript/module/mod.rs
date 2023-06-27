//! Module-level (i.e. single Javascript file) data structures and methods.

pub mod module_cache;
pub mod resolver;

use std::collections::HashSet;

use itertools::Itertools;
use ouroboros::self_referencing;
use tree_sitter::Node;

use super::lang::exports::EsmExport;
use crate::javascript::lang::accesses::{AccessEdge, AccessGraph};
use crate::javascript::lang::exports::{CommonJsExports, EsmExports, Exports};
use crate::javascript::lang::imports::Imports;
use crate::javascript::lang::symbol_table::SymbolTable;
pub use crate::javascript::module::module_cache::ModuleCache;
pub use crate::javascript::module::resolver::fs::FilesystemModuleResolver;
pub use crate::javascript::module::resolver::mem::MemModuleResolver;
pub use crate::javascript::module::resolver::tgz::TarballModuleResolver;
pub use crate::javascript::module::resolver::ModuleResolver;
use crate::{Error, Result, Tree};

#[derive(Clone, Debug)]
pub(crate) enum PathToExport<'a> {
    Esm { name: &'a str, access_path: Vec<AccessEdge<'a>> },
    Cjs { name: &'a str, access_path: Vec<AccessEdge<'a>>, export: Node<'a> },
    SideEffect { name: &'a str, access_path: Vec<AccessEdge<'a>>, effect_node: Node<'a> },
}

impl<'a> PathToExport<'a> {
    pub(crate) fn name(&self) -> &str {
        match self {
            PathToExport::Esm { name, .. }
            | PathToExport::Cjs { name, .. }
            | PathToExport::SideEffect { name, .. } => name,
        }
    }
}

/// A module object. It contains all information about symbols, accesses,
/// imports and exports and is self-referencing.
#[self_referencing]
pub struct Module {
    tree: Tree,
    #[borrows(tree)]
    #[covariant]
    symbol_table: SymbolTable<'this>,
    #[borrows(tree, symbol_table)]
    #[covariant]
    accesses: AccessGraph<'this>,
    #[borrows(tree)]
    #[covariant]
    imports: Imports<'this>,
    #[borrows(tree)]
    #[covariant]
    exports: Exports<'this>,
}

impl TryFrom<Tree> for Module {
    type Error = Error;

    fn try_from(tree: Tree) -> Result<Self> {
        // Fail if there is an error anywhere in the AST.
        //
        // `tree-sitter` is capable of parsing code with errors in it, but
        // code with errors won't be executable by a runtime anyway, and as
        // such anything in it will also be unreachable. We can safely skip
        // processing these cases.
        if tree.root_node().has_error() {
            Err(Error::ParseError)
        } else {
            Ok(Module::new(
                tree,
                |tree| SymbolTable::new(tree),
                |tree, symbol_table| AccessGraph::new(tree, symbol_table),
                |tree| Imports::new(tree),
                |tree| Exports::new(tree),
            ))
        }
    }
}

impl Module {
    pub fn tree(&self) -> &Tree {
        self.borrow_tree()
    }

    pub fn imports(&self) -> &Imports {
        self.borrow_imports()
    }

    pub fn exports(&self) -> &Exports {
        self.borrow_exports()
    }

    pub fn symbol_table(&self) -> &SymbolTable {
        self.borrow_symbol_table()
    }

    pub fn accesses(&self) -> &AccessGraph {
        self.borrow_accesses()
    }

    /// Find paths to ES Module exports.
    fn paths_to_exports_esm<'a>(
        &'a self,
        source: Node<'a>,
        exports: &'a EsmExports,
    ) -> Result<Vec<PathToExport<'a>>> {
        let mut export_nodes = HashSet::new();

        // If there is a default export, add its node to the set.
        if let Some(export) = exports.default.as_ref() {
            export_nodes.insert(export.node());
        }

        // Add all exported objects' nodes to the set.
        for export in exports.objects.values() {
            export_nodes.insert(export.node());
        }

        // Compute paths to all ESM export nodes.
        Ok(self
            .accesses()
            .compute_paths(
                |access| {
                    // An access is a target if either its node or its scope are in the set
                    // of export nodes.
                    export_nodes.contains(&access.node) || export_nodes.contains(&access.scope)
                },
                source,
            )?
            .into_iter()
            .map(|access_path| {
                let last_node = access_path.last().unwrap();
                // The name of this path to export is either "default" or the name of the
                // last identifier in the path.
                //
                // The guard condition ensures that `last_node` is the default export node,
                // to prevent shadowing other exports.
                let name = match exports.default.as_ref() {
                    Some(EsmExport::Scope(node)) if node == &last_node.access().scope => "default",
                    Some(EsmExport::Name(node)) if node == &last_node.access().node => "default",
                    Some(export @ EsmExport::Expression(_))
                        if export.expression_contains(last_node.access().node) =>
                    {
                        "default"
                    },
                    _ => self.tree().repr_of(last_node.accessed()),
                };

                PathToExport::Esm { name, access_path }
            })
            .collect())
    }

    /// Find paths to CommonJS exports.
    fn paths_to_exports_cjs<'a>(
        &'a self,
        source: Node<'a>,
        exports: &'a CommonJsExports,
    ) -> Result<Vec<PathToExport<'a>>> {
        Ok(self
            .accesses()
            .compute_paths(
                |access| {
                    // Depending on which kind of export we have in this module, run a different
                    // check against the current access to determine whether that is a target.
                    match exports {
                        CommonJsExports::Name(n) => access.node == *n,
                        CommonJsExports::Scope(s) => access.scope == *s,
                        CommonJsExports::Object(o) => {
                            o.values().contains(&access.node) || o.values().contains(&access.scope)
                        },
                        CommonJsExports::None => false,
                    }
                },
                source,
            )?
            .into_iter()
            .map(|access_path| {
                let last_access = access_path.last().unwrap();

                // Determine the name of the exported node in the path.
                let (name, export) = match exports {
                    &CommonJsExports::Name(n) => (self.tree().repr_of(n), n),
                    &CommonJsExports::Scope(s) => ("<scope>", s),
                    CommonJsExports::Object(o) => o
                        .iter()
                        .find_map(|(&k, &v)| {
                            if last_access.access().node == v || last_access.access().scope == v {
                                Some((k, v))
                            } else {
                                None
                            }
                        })
                        .unwrap(),
                    CommonJsExports::None => unreachable!(),
                };

                PathToExport::Cjs { name, access_path, export }
            })
            .collect())
    }

    /// Find paths to side effects, i.e. nodes that are always accessed when
    /// importing a module.
    fn paths_to_side_effects<'a>(&'a self, source: Node<'a>) -> Result<Vec<PathToExport<'a>>> {
        Ok(self
            .accesses()
            .compute_paths(|access| access.is_side_effect(), source)?
            .into_iter()
            .map(|access_path| {
                let last_access = access_path.last().unwrap().access();

                // The name of this path is the representation of its access node.
                let effect_node = last_access.node;
                let name = self.tree().repr_of(effect_node);

                PathToExport::SideEffect { name, access_path, effect_node }
            })
            .collect())
    }

    /// Find the paths to exports for all kinds of modules.
    pub(crate) fn paths_to_exports<'a>(
        &'a self,
        source: Node<'a>,
    ) -> Result<Vec<PathToExport<'a>>> {
        // Always include paths to side effects.
        let mut paths = self.paths_to_side_effects(source)?;

        match self.exports() {
            Exports::Esm(exports) => paths.extend(self.paths_to_exports_esm(source, exports)?),
            Exports::CommonJs(exports) => paths.extend(self.paths_to_exports_cjs(source, exports)?),
            Exports::None => {},
        }

        Ok(paths)
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use textwrap::dedent;
    use tree_sitter::Point;

    use super::*;

    impl<'a> PathToExport<'a> {
        pub(crate) fn repr(&self, tree: &Tree) -> String {
            let mut buf = String::new();

            match self {
                PathToExport::Esm { name, access_path } => {
                    write!(&mut buf, "`{}`: ", name).ok();
                    for edge in access_path {
                        let accessed = edge.accessed();
                        write!(
                            &mut buf,
                            "{}:{},{}",
                            tree.repr_of(accessed),
                            accessed.start_position().row,
                            accessed.start_position().column
                        )
                        .ok();

                        if edge.access().accessor.is_some() {
                            write!(&mut buf, " -> ").ok();
                        }
                    }
                },
                PathToExport::Cjs { name, access_path, export } => {
                    write!(&mut buf, "`{}`: ", name).ok();
                    for edge in access_path {
                        let accessed = edge.accessed();
                        write!(
                            &mut buf,
                            "{}:{},{}",
                            tree.repr_of(accessed),
                            accessed.start_position().row,
                            accessed.start_position().column
                        )
                        .ok();

                        write!(&mut buf, " -> ").ok();
                    }

                    write!(
                        &mut buf,
                        "{}:{},{}",
                        name,
                        export.start_position().row,
                        export.start_position().column
                    )
                    .ok();
                },
                PathToExport::SideEffect { name, access_path, effect_node } => {
                    write!(&mut buf, "`{}`: ", name).ok();
                    for edge in access_path {
                        let accessed = edge.accessed();
                        write!(
                            &mut buf,
                            "{}:{},{}",
                            tree.repr_of(accessed),
                            accessed.start_position().row,
                            accessed.start_position().column
                        )
                        .ok();

                        write!(&mut buf, " -> ").ok();
                    }

                    write!(
                        &mut buf,
                        "{}:{},{}",
                        name,
                        effect_node.start_position().row,
                        effect_node.start_position().column
                    )
                    .ok();
                },
            }

            buf
        }
    }

    #[ignore]
    #[test]
    fn test_paths_to_exports_mjs_default_function() {
        let module = Module::try_from(
            Tree::new(dedent(
                r#"
                const foo = 3

                function bar() {
                    const c = foo
                }

                export default function() {
                    bar()
                }
                "#,
            ))
            .unwrap(),
        )
        .unwrap();

        let paths = module
            .paths_to_exports(
                module
                    .tree()
                    .root_node()
                    .descendant_for_point_range(Point::new(1, 6), Point::new(1, 8))
                    .unwrap(),
            )
            .unwrap()
            .into_iter()
            .filter(|path| matches!(path, PathToExport::Esm { .. }))
            .collect::<Vec<_>>();

        assert_eq!(paths.len(), 1);

        let path = paths.into_iter().next().unwrap();
        println!("{}", path.repr(module.tree()));
        assert_eq!(path.name(), "default");
    }

    #[ignore]
    #[test]
    fn test_paths_to_exports_mjs_default_binding() {
        let module = Module::try_from(
            Tree::new(dedent(
                r#"
                const foo = 3

                function bar() {
                    const c = foo
                }

                export default bar
                "#,
            ))
            .unwrap(),
        )
        .unwrap();

        let paths = module
            .paths_to_exports(
                module
                    .tree()
                    .root_node()
                    .descendant_for_point_range(Point::new(1, 6), Point::new(1, 8))
                    .unwrap(),
            )
            .unwrap()
            .into_iter()
            .filter(|path| matches!(path, PathToExport::Esm { .. }))
            .collect::<Vec<_>>();

        assert_eq!(paths.len(), 1);

        let path = paths.into_iter().next().unwrap();
        println!("{}", path.repr(module.tree()));
        assert_eq!(path.name(), "default");
    }

    #[test]
    fn test_paths_to_side_effects() {
        let module = Module::try_from(
            Tree::new(dedent(
                r#"
            let value = 3

            function foo() {
                value = 4
            }

            function bar() {
                foo()
            }

            foo()
        "#,
            ))
            .unwrap(),
        )
        .unwrap();

        let paths = module
            .paths_to_exports(
                module
                    .tree()
                    .root_node()
                    .descendant_for_point_range(Point::new(1, 4), Point::new(1, 8))
                    .unwrap(),
            )
            .unwrap();

        assert!(paths.len() == 1, "Wrong number of paths found");

        let Some(PathToExport::SideEffect { name, access_path, effect_node }) =
            paths.into_iter().next() else {
                panic!("Path found is not to a side effect")
            };

        assert_eq!(name, "foo", "Wrong side effect name {name}");
        assert_eq!(
            effect_node.start_position(),
            Point::new(11, 0),
            "Wrong side effect node position"
        );
        assert_eq!(
            access_path.first().unwrap().accessed().start_position(),
            Point::new(1, 4),
            "Wrong node accessed"
        );
    }

    #[test]
    fn test_module_with_errors() {
        let tree = Tree::new(
            r#"
            #[test]
            fn test_function() {
                panic!("I am not even JavaScript code");
            }
        "#
            .to_string(),
        )
        .expect("The tree should be parsed anyway");

        assert!(matches!(Module::try_from(tree), Err(Error::ParseError)));
    }
}
