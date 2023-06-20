use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::path::Path;

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use tree_sitter::{Node, Point};

use crate::javascript::lang::imports::{EsmImport, Imports};
use crate::javascript::module::resolver::resolve_path;
use crate::javascript::module::{ModuleResolver, PathToExport};
use crate::javascript::package::Package;
use crate::{Error, Result, Tree};

// Run for every pair of (source module, imported module) e.g. if source_module
// imports `a`, `b` and `c`, run for (source_module, a), (source_module, b),
// (source_module, c).
fn identify_import_nodes<'a, R: ModuleResolver>(
    package: &'a Package<R>,
    dependent_spec: &Path,
    imported_spec: &Path,
    paths_to_exports: &[PathToExport<'a>],
) -> Vec<Node<'a>> {
    // Retrieve dependent_module's imports from imported_module.

    let imported_spec_abs =
        package.resolver().resolve_relative(imported_spec, dependent_spec).unwrap();

    let dependent_module = package.resolve_absolute(dependent_spec).unwrap();

    // Match source_module's imports to imported_module's exports.
    // The returned nodes are from source_module's tree.
    match dependent_module.imports() {
        Imports::Esm(esm) => {
            let affected_exports =
                paths_to_exports.iter().map(|path| path.name()).collect::<HashSet<_>>();

            esm.into_iter()
                .filter(|esm_import| {
                    let Ok(resolved_spec) = package
                        .resolver()
                        .resolve_relative(esm_import.source(), dependent_spec) else {
                            return false;
                        };

                    resolved_spec == imported_spec_abs
                })
                .filter(|&esm_import| match esm_import {
                    EsmImport::Named { node, .. } | EsmImport::Namespace { node, .. } => {
                        affected_exports.contains(dependent_module.tree().repr_of(*node))
                    },
                    EsmImport::Default { .. } => affected_exports.contains("default"),
                })
                .map(|esm_import| esm_import.alias_node().unwrap_or(esm_import.node()))
                .collect()
        },
        Imports::CommonJs(cjs) => cjs
            .into_iter()
            .filter(|&cjs_import| {
                let Ok(resolved_spec) = package
                    .resolver()
                    .resolve_relative(cjs_import.source(), dependent_spec) else {
                        return false;
                    };

                resolve_path(resolved_spec, |spec| spec == imported_spec_abs).is_some()
            })
            .map(|cjs_import| cjs_import.access_node(dependent_module.tree()))
            .filter(|node| node.kind() == "identifier")
            .collect(),
        Imports::None => Vec::new(),
    }

    // If it's a CommonJS import, tag the LHS of the require() call as the
    // identifier that accesses the export object. Call this node
    // `import_ident`. The exports object of imported_module is tagged as
    // `export_ident`.

    // If it's an ES module import:
    // - If it is named, tag the alias.unwrap_or(name) as `import_ident`.
    // - If it is namespaced (import * as foo from _) tag foo as `import_ident`.
    // - If it is default (import foo from _) tag foo as `import_ident`.
}

fn compute_paths_from_export_to_modules<'a, R: ModuleResolver>(
    package: &'a Package<R>,
    source: &'a Path,
    paths_to_exports: Vec<PathToExport<'a>>,
) -> Result<Vec<(&'a Path, &'a Path, Vec<PathToExport<'a>>)>> {
    // In this algorithm, we call "dependency" an imported module, and
    // "dependent" the module that imports the dependency.
    //
    // The `paths_to_exports` parameter should contain the paths from a
    // vulnerability to all relevant exports in the `source` module.

    struct EvaluationStep<'a> {
        dependent: &'a Path,
        dependency: &'a Path,
        paths_to_dependency_exports: Vec<PathToExport<'a>>,
    }

    // Initialization step

    // Recursion queue.
    let mut q = VecDeque::<EvaluationStep>::new();
    let mut visited = HashSet::new();

    // The first element of the output contains the base case: paths that go
    // from the vulnerable node to the exports. This is represented via an
    // edge between the module containing the vulnerable node and itself.
    let mut output = vec![(source, source, paths_to_exports.clone())];

    // Find all modules that depend on `source`.
    let source_dependents = package.cache().dependents_of(source).collect::<Vec<_>>();

    // Create one step for each of `source`'s dependents.
    for dependent in source_dependents {
        q.push_back(EvaluationStep {
            dependent,
            dependency: source,
            paths_to_dependency_exports: paths_to_exports.clone(),
        });
    }

    // Walk through the entire dependents tree in reverse, starting from `source`.
    while !q.is_empty() {
        let EvaluationStep { dependent, dependency, paths_to_dependency_exports } =
            q.pop_front().unwrap();

        // Visit each dependency->dependent edge exactly once.
        if visited.contains(&(dependent, dependency)) {
            continue;
        }
        visited.insert((dependent, dependency));

        let dependent_module = package.cache().module(dependent).unwrap();

        // Find the dependent import nodes that match the dependency export nodes.
        // Filter by export nodes that are actually affected.
        let dependent_imports =
            identify_import_nodes(package, dependent, dependency, &paths_to_dependency_exports);

        // Find paths from the imported dependency nodes to the dependent export
        // nodes.
        let dependent_paths_from_imports_to_exports = dependent_imports.into_iter().fold(
            Ok::<_, Error>(Vec::new()),
            |out, import_node| {
                let mut out = out?;
                out.extend(dependent_module.paths_to_exports(import_node)?);

                Ok(out)
            },
        )?;

        let dependent_dependents = package.cache().dependents_of(dependent).collect::<Vec<_>>();

        // For each of the dependent's dependents `dd`, create a step to process the
        // paths from `dd`'s imports of the dependent's export and `dd`'s exports.
        for dd in dependent_dependents {
            q.push_back(EvaluationStep {
                dependent: dd,
                dependency: dependent,
                paths_to_dependency_exports: dependent_paths_from_imports_to_exports.to_vec(),
            })
        }

        output.push((dependent, dependency, dependent_paths_from_imports_to_exports));
    }

    Ok(output)
}

/// A vulnerable node.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct VulnerableNode {
    /// The package specifier.
    package: String,
    /// The module specifier.
    module: String,
    /// The starting row (zero-indexed).
    start_row: usize,
    /// The starting column (zero-indexed).
    start_column: usize,
    /// The ending row (zero-indexed).
    end_row: usize,
    /// The ending column (zero-indexed).
    end_column: usize,
}

impl VulnerableNode {
    /// Creates a new vulnerable node. Row and columns are zero-indexed.
    pub fn new<P: Into<String>, M: Into<String>>(
        package: P,
        module: M,
        start_row: usize,
        start_column: usize,
        end_row: usize,
        end_column: usize,
    ) -> Self {
        Self {
            package: package.into(),
            module: module.into(),
            start_row,
            start_column,
            end_row,
            end_column,
        }
    }

    pub fn package(&self) -> &str {
        &self.package
    }

    pub fn module(&self) -> &str {
        &self.module
    }

    pub fn start_row(&self) -> usize {
        self.start_row
    }

    pub fn start_column(&self) -> usize {
        self.start_column
    }

    pub fn end_row(&self) -> usize {
        self.end_row
    }

    pub fn end_column(&self) -> usize {
        self.end_column
    }
}

/// A step in a node path.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct NodeStep {
    symbol: String,
    start_row: usize,
    start_column: usize,
    end_row: usize,
    end_column: usize,
}

impl NodeStep {
    fn new(value: Node<'_>, tree: &Tree) -> Self {
        NodeStep::with_name(tree.repr_of(value), value)
    }

    fn with_name(name: &str, value: Node<'_>) -> Self {
        let Point { row: start_row, column: start_column } = value.start_position();
        let Point { row: end_row, column: end_column } = value.end_position();
        let symbol = name.to_string();
        NodeStep { symbol, start_row, start_column, end_row, end_column }
    }

    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    pub fn start(&self) -> (usize, usize) {
        (self.start_row, self.start_column)
    }

    pub fn end(&self) -> (usize, usize) {
        (self.end_row, self.end_column)
    }
}

impl Display for NodeStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.symbol, self.start_row, self.start_column)
    }
}

/// A path between two given nodes in a source file.
///
/// It is an ordered vector of [`NodeStep`] items. Each [`NodeStep`] element
/// [accesses][`crate::javascript::lang::accesses`] the element after it.
#[derive(Serialize, Deserialize, Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct NodePath(Vec<NodeStep>);

impl NodePath {
    fn new(path_to_exports: PathToExport, tree: &Tree) -> Self {
        match path_to_exports {
            PathToExport::Esm { access_path, .. } => {
                let mut path: Vec<_> = access_path
                    .into_iter()
                    .map(|edge| NodeStep::new(edge.accessed(), tree))
                    .collect();
                path.reverse();

                NodePath(path)
            },
            PathToExport::Cjs { access_path, export, name } => {
                let mut path: Vec<_> = access_path
                    .into_iter()
                    .map(|edge| NodeStep::new(edge.accessed(), tree))
                    .collect();

                path.push(NodeStep::with_name(name, export));
                path.reverse();

                NodePath(path)
            },
            PathToExport::SideEffect { name, access_path, effect_node } => {
                let mut path: Vec<_> = access_path
                    .into_iter()
                    .map(|edge| NodeStep::new(edge.accessed(), tree))
                    .collect();

                path.push(NodeStep::with_name(name, effect_node));
                path.reverse();

                NodePath(path)
            },
        }
    }
}

impl IntoIterator for NodePath {
    type IntoIter = <Vec<NodeStep> as IntoIterator>::IntoIter;
    type Item = NodeStep;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// The graph of all paths in a package which go from a vulnerable node
/// to an export.
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct PackageReachability(HashMap<String, HashMap<String, HashSet<NodePath>>>);

impl PackageReachability {
    pub(crate) fn new<R: ModuleResolver>(
        package: &Package<R>,
        vuln_node: &VulnerableNode,
    ) -> Result<Self> {
        let mut pkg_reachability = PackageReachability(HashMap::new());

        let module = package
            .cache()
            .module(&vuln_node.module)
            .ok_or_else(|| Error::Generic(format!("Module not found: {}", vuln_node.module)))?;
        let vuln_ts_node = module
            .tree()
            .root_node()
            .descendant_for_point_range(
                Point::new(vuln_node.start_row, vuln_node.start_column),
                Point::new(vuln_node.start_row, vuln_node.start_column),
            )
            .ok_or_else(|| Error::Generic(format!("Node not found: {vuln_node:?}")))?;
        let paths_to_exports = module.paths_to_exports(vuln_ts_node)?;

        for (dependent, dependency, paths) in compute_paths_from_export_to_modules(
            package,
            Path::new(&vuln_node.module),
            paths_to_exports,
        )? {
            let entry: &mut HashSet<NodePath> = pkg_reachability
                .0
                .entry(dependent.to_string_lossy().to_string())
                .or_default()
                .entry(dependency.to_string_lossy().to_string())
                .or_default();

            for path in paths {
                entry.insert(NodePath::new(
                    path,
                    package
                        .cache()
                        .module(dependent)
                        .ok_or_else(|| {
                            Error::Generic(format!(
                                "Module not found: {}",
                                dependent.to_string_lossy()
                            ))
                        })?
                        .tree(),
                ));
            }
        }

        Ok(pkg_reachability)
    }

    // Find the first path from the given module to the reachable vulnerability.
    //
    // XXX The results are non-deterministic by virtue of the default
    // `RandomState` in Rust's standard library. We should consider using
    // a different one if we want results to be reproducible across runs
    // (e.g. for tests).
    pub(crate) fn find_path<S: AsRef<str>>(
        &self,
        start_module_spec: S,
    ) -> Option<Vec<(String, NodePath)>> {
        struct EvaluationStep<'a> {
            src_spec: &'a str,
            step_path: Vec<(&'a str, &'a NodePath)>,
        }
        let mut bfs_q = VecDeque::new();
        let mut visited = HashSet::new();

        bfs_q.push_back(EvaluationStep {
            src_spec: start_module_spec.as_ref(),
            step_path: Vec::new(),
        });

        while let Some(EvaluationStep { src_spec, step_path }) = bfs_q.pop_front() {
            if visited.contains(src_spec) {
                continue;
            }
            visited.insert(src_spec);

            // Abort if `src_spec` is not represented in the reachability.
            //
            // This can only happen if a wrong `start_module_spec` is passed
            // in, or if the data structure is broken: all specs in a
            // `PackageReachability` should validly point into itself.
            let dependent = self.0.get(src_spec)?;

            for (dependency, paths) in dependent {
                for path in paths {
                    let mut next_step_path = step_path.clone();
                    next_step_path.push((src_spec, path));

                    // If the edge we are analyzing is in the form (x, x) it
                    // means we found a path to a leaf, i.e. module `x` contains
                    // a path from vulnerable node to export. This means we have
                    // found a list of paths which, if followed, leads to the
                    // vulnerable node.
                    //
                    // XXX We could extend this to return all possible paths by
                    // accruing the found paths here, and returning that once the
                    // queue is empty, rather than stopping early.
                    if src_spec == dependency {
                        return Some(
                            next_step_path
                                .into_iter()
                                .map(|(k, v)| (k.to_string(), v.clone()))
                                .collect(),
                        );
                    }

                    bfs_q.push_back(EvaluationStep {
                        src_spec: dependency,
                        step_path: next_step_path,
                    });
                }
            }
        }

        None
    }

    pub(crate) fn modules(&self) -> impl Iterator<Item = &String> {
        self.0.keys()
    }

    /// Returns all pairs of `(module specifier, exported symbol)` from the
    /// current package.
    pub fn reachable_exports<'a>(&'a self) -> HashSet<(&'a str, &'a str)> {
        // Get the export symbol from the node path.
        let get_export_symbol = |spec: &'a String, node_path: &'a NodePath| {
            node_path.0.first().map(|node_step| (spec.as_str(), node_step.symbol.as_str()))
        };

        // Get all the export symbols from all node paths.
        let get_all_export_symbols = |spec: &'a String, node_paths: &'a HashSet<NodePath>| {
            node_paths.iter().filter_map(move |node_path| get_export_symbol(spec, node_path))
        };

        // Get all the export symbols from all module specs for this package.
        self.0
            .iter()
            .flat_map(|(spec, paths)| {
                paths.values().flat_map(|path| get_all_export_symbols(spec, path))
            })
            .collect()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Display for PackageReachability {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (dependent, dependencies) in &self.0 {
            writeln!(f, "*** {dependent} ***")?;
            for (dependency, paths) in dependencies {
                writeln!(f, "  > {dependency}")?;

                for path in paths {
                    write!(f, "    ")?;
                    for x in Itertools::intersperse(
                        path.0.iter().map(|p| format!("{p}")),
                        " -> ".to_string(),
                    ) {
                        write!(f, "{x}")?;
                    }
                    writeln!(f)?;
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use maplit::{hashmap, hashset};
    use textwrap::dedent;

    use super::*;
    use crate::javascript::module::{MemModuleResolver, ModuleCache};
    use crate::javascript::package::Package;
    use crate::test_util::npm_package;

    fn fixture_esm_package1() -> Package<MemModuleResolver> {
        Package::from_mem(hashmap! {
            "package.json" => r#"{ "main": "index.mjs" }"#.to_string(),
            "index.mjs" => dedent(r#"
                import { reaches1 as reaches2 } from './source1.mjs'
                import * as source2 from './source2.mjs'
                import { reaches } from './source3.mjs'
                import source4 from './source4.mjs'

                reaches()
                reaches2()
                source2.foo()

                export function explicit_export() {
                  reaches2()
                  reaches()
                  source4()
                }

                export default function() {
                  reaches2()
                  reaches()
                  source4()
                }"#),
            "source1.mjs" => dedent(r#"
                import { reaches, not_reaches } from './source3.mjs'

                export let foo = 1
                export let bar = 1
                export function reaches1() {
                  reaches()
                }
                export function reaches2() {
                  reaches()
                }
                export function reaches3() {
                  if (true) {
                    reaches()
                  }
                }
                export function calls_not_reaches() {
                  not_reaches()
                }"#),
            "source2.mjs" => dedent(r#"
                export { reaches } from './source3.mjs'
                export function foo() { }"#),
            "source3.mjs" => dedent(r#"
                function vulnerable() { console.log('I am vulnerable') }
                function a() { vulnerable() }
                function b() { a() }
                function c() { b() }
                function d() { c() }
                export function reaches() { d() }
                export function not_reaches() { }"#),
            "source4.mjs" => dedent(r#"
                import { reaches } from './source3.mjs'
                export default function() {
                    reaches()
                }
                "#)
        })
        .unwrap()
    }

    fn fixture_cjs_package1() -> Package<MemModuleResolver> {
        Package::from_mem(hashmap! {
            "package.json" => r#"{ "main": "index.js" }"#.to_string(),
            "index.js" => dedent(r#"
                const reaches1 = require('./source1.js').reaches1
                const source2 = require('./source2.js')
                const source3 = require('./source3.js')
                const reaches = require('./source3.js').reaches

                reaches()
                reaches1()
                if (false) { source2.foo() }
                source3.reaches()"#),
            "source1.js" => dedent(r#"
                const reaches_source3 = require('./source3.js').reaches

                module.exports = {
                  foo: 1,
                  bar: 1,
                  reaches1: function() {
                    reaches_source3()
                  },
                  reaches2: function() {
                    if (true) {
                      reaches_source3()
                    }
                  },
                  not_reaches1: function() {},
                  not_reaches2() {}
                }

                module.exports.reaches3 = function() {
                  reaches_source3()
                }

                module.exports.reaches4 = function() {
                  if(true) {
                    reaches_source3()
                  }
                }

                module.exports.not_reaches3 = function() {}
                "#),
            "source2.js" => dedent(r#"
                module.exports.reaches = require('./source3.js').reaches
                module.exports.foo = function() { }"#),
            "source3.js" => dedent(r#"
                function vulnerable() {
                  console.log('I am vulnerable, but in commonjs')
                }

                function a() { vulnerable() }
                function b() { a() }
                function c() { b() }
                function d() { c() }
                module.exports.reaches = function() { d() }"#),
        })
        .unwrap()
    }

    fn print_paths(cache: &ModuleCache, paths: HashMap<(&str, &str), Vec<PathToExport>>) {
        for ((dependent, dependency), paths) in paths {
            println!("\n *** For edge {dependent:?} -> {dependency:?}");

            for p in paths {
                println!("     Path: {}", p.repr(cache.module(dependent).unwrap().tree()));
            }
        }
    }

    #[test]
    fn test_package_traversal_esm() {
        let package = fixture_esm_package1();

        let source3 = package.resolve_absolute("source3.mjs").unwrap();
        let vuln_node = source3.tree().root_node().descendant_for_byte_range(15, 16).unwrap();
        println!("{:#?}", package.resolve_absolute("index.mjs").unwrap().symbol_table());
        let paths_to_exports = source3.paths_to_exports(vuln_node).unwrap();

        let paths: HashMap<(_, _), _> = compute_paths_from_export_to_modules(
            &package,
            Path::new("source3.mjs"),
            paths_to_exports,
        )
        .unwrap()
        .into_iter()
        .map(|(a, b, c)| ((a.to_str().unwrap(), b.to_str().unwrap()), c))
        .collect();

        print_paths(package.cache(), paths.clone());

        if let Some(paths) = paths.get(&("source1.mjs", "source3.mjs")) {
            assert_eq!(
                paths.iter().map(|p| p.name()).collect::<HashSet<_>>(),
                hashset! {"reaches1", "reaches2", "reaches3"}
            );
        }

        if let Some(paths) = paths.get(&("index.mjs", "source3.mjs")) {
            assert_eq!(
                paths.iter().map(|p| p.name()).collect::<HashSet<_>>(),
                hashset! {"reaches", "default", "explicit_export"}
            );
        }
    }

    #[test]
    fn test_package_traversal_cjs() {
        let package = fixture_cjs_package1();

        let source3 = package.cache().module("source3.js").unwrap();
        let vuln_node = source3.tree().root_node().descendant_for_byte_range(10, 11).unwrap();
        let paths_to_exports = source3.paths_to_exports(vuln_node).unwrap();

        let paths = compute_paths_from_export_to_modules(
            &package,
            Path::new("source3.js"),
            paths_to_exports,
        )
        .unwrap()
        .into_iter()
        .map(|(a, b, c)| ((a.to_str().unwrap(), b.to_str().unwrap()), c))
        .collect::<HashMap<_, _>>();

        if let Some(paths) = paths.get(&("source1.js", "source3.js")) {
            assert_eq!(
                paths.iter().map(|p| p.name()).collect::<HashSet<_>>(),
                hashset! {"reaches1", "reaches2", "reaches3", "reaches4"}
            );
        }

        if let Some(paths) = paths.get(&("index.js", "source1.js")) {
            assert_eq!(
                paths.iter().map(|p| p.name()).collect::<HashSet<_>>(),
                hashset! {"reaches1"}
            );
        }

        // The `source2` node is unreachable by definition as it is gated by an
        // `if (false) { ... }`; but we don't evaluate statements, so we purposefully
        // want that to be marked as reachable.
        if let Some(paths) = paths.get(&("index.js", "source2.js")) {
            assert!(matches!(paths.first(), Some(PathToExport::SideEffect { .. })));
            assert_eq!(
                paths.iter().map(|p| p.name()).collect::<HashSet<_>>(),
                hashset! {"source2"}
            );
        }

        // XXX This specific case shows the over-coloring of CommonJS. The
        // correct access set would be `reaches` only; `source3` is an
        // over-coloring.
        if let Some(paths) = paths.get(&("index.js", "source3.js")) {
            assert_eq!(
                paths.iter().map(|p| p.name()).collect::<HashSet<_>>(),
                hashset! {"reaches", "source3"}
            );
        }

        print_paths(package.cache(), paths);
    }

    #[test]
    fn test_reachability_esm() {
        let package = fixture_esm_package1();
        let r = PackageReachability::new(
            &package,
            &VulnerableNode::new("fixture", "source3.mjs".to_string(), 1, 9, 1, 16),
        )
        .unwrap();
        println!("{r:#?}");
        println!("{r}");

        assert_eq!(r.reachable_exports(), hashset! {
            ("source1.mjs", "reaches1"),
            ("source1.mjs", "reaches2"),
            ("source1.mjs", "reaches3"),
            ("source3.mjs", "reaches"),
            ("source4.mjs", "reaches"),
            ("index.mjs", "explicit_export"),
            ("index.mjs", "reaches"),
            ("index.mjs", "reaches2"),
            ("index.mjs", "source4"),
        });
    }

    #[test]
    fn test_find_path_esm() {
        let package = fixture_esm_package1();
        let r = PackageReachability::new(
            &package,
            &VulnerableNode::new("fixture", "source3.mjs".to_string(), 1, 9, 1, 16),
        )
        .unwrap();

        println!("{:#?}", r.find_path("index.mjs"));
    }

    #[test]
    fn test_reachability_cjs() {
        let package = fixture_cjs_package1();
        let r = PackageReachability::new(
            &package,
            &VulnerableNode::new("fixture", "source3.js".to_string(), 1, 9, 1, 16),
        )
        .unwrap();
        println!("{r:#?}");
        println!("{r}");
    }

    // This test case's main purpose is checking whether imports without extension
    // (i.e. './lib/Pool', like generic_pool does) are still correctly resolved.
    #[tokio::test]
    async fn test_reachability_generic_pool() {
        let package = npm_package("generic-pool", "3.8.2").await;
        let r = PackageReachability::new(
            &package,
            &VulnerableNode::new("generic-pool", "lib/Pool.js".to_string(), 23, 6, 23, 9),
        )
        .unwrap();

        println!("{r:#?}");
        println!("{r}");

        let node_paths_in_index = r.0.get("index.js").unwrap().get("lib/Pool.js").unwrap();

        assert!(node_paths_in_index.iter().map(|node_path| node_path.0.first().unwrap()).any(
            |node_step| node_step.symbol == "createPool"
                && node_step.start_row == 9
                && node_step.start_column == 40
        ));
    }

    #[tokio::test]
    async fn test_reachability_handlebars_esm() {
        let package = npm_package("handlebars", "4.7.6").await;

        let target_node =
            VulnerableNode::new("handlebars", "dist/cjs/handlebars/runtime.js", 51, 9, 51, 16);
        let r = PackageReachability::new(&package, &target_node).unwrap();

        println!("{r:#?}");
        println!("{r}");
    }

    #[tokio::test]
    async fn test_reachability_handlebars_cjs() {
        let package = npm_package("handlebars", "4.7.6").await;

        let target_node =
            VulnerableNode::new("handlebars", "lib/handlebars/runtime.js", 48, 16, 48, 23);
        let r = PackageReachability::new(&package, &target_node).unwrap();

        println!("{r:#?}");
        println!("{r}");
    }
}
