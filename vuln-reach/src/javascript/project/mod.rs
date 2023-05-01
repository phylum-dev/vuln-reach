//! Project-wide (i.e. tree-of-packages) reachability.

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use serde::{Deserialize, Serialize};
use tree_sitter::Node;

use super::lang::imports::Imports;
use super::package::reachability::{PackageReachability, VulnerableNode};
use super::package::Package;
use crate::javascript::module::resolver::ModuleResolver;
use crate::javascript::package::reachability::NodePath;
use crate::javascript::package::resolver::PackageResolver;

/// Specifies the package and module that direct towards a vulnerability.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct VulnerableEdge {
    package: String,
    module: String,
}

impl VulnerableEdge {
    pub fn new<S1: Into<String>, S2: Into<String>>(package: S1, module: S2) -> Self {
        Self { package: package.into(), module: module.into() }
    }
}

/// An instance of in-package reachability that leads either to
/// the vulnerability itself, or to an intermediate package.
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum ReachabilityEdge {
    /// The vulnerability itself is reachable.
    Own(PackageReachability),
    /// The vulnerability is reachable through another package in the dependency
    /// tree.
    Foreign(PackageReachability, VulnerableEdge),
}

impl ReachabilityEdge {
    fn reachability(&self) -> &PackageReachability {
        match self {
            ReachabilityEdge::Own(p) => p,
            ReachabilityEdge::Foreign(p, _) => p,
        }
    }
}

/// A single path between a node in a package and a vulnerable node.
///
/// This is a hierarchical ordered representation, of the following form:
///
/// ```json
/// {
///   "dependent_package": {
///     "module1.js": ["node1", "node2", ...]
///   },
///   ...,
///   "vulnerable_package": {
///     "module2.js": ["node3", "node4", ... "vulnerable_node"]
///   }
/// }
/// ```
pub type ReachabilityPath = Vec<(String, Vec<(String, NodePath)>)>;

/// Reachability of a given node inside of a project.
///
/// Maps a package name to the graph of accesses (represented as adjacency
/// lists) that lead to the vulnerable node, starting from that package.
#[derive(Serialize, Deserialize, Default, Debug, PartialEq, Eq)]
pub struct ProjectReachability(HashMap<String, Vec<ReachabilityEdge>>);

impl ProjectReachability {
    pub fn new(adjacency_lists: HashMap<String, Vec<ReachabilityEdge>>) -> Self {
        Self(adjacency_lists)
    }

    /// Return the graph edges leaving from the specified package, if they
    /// exist.
    pub fn edges_from(&self, package: &str) -> Option<&Vec<ReachabilityEdge>> {
        self.0.get(package)
    }

    /// Find one possible path from the specified package to the vulnerable
    /// node.
    pub fn find_path<S: AsRef<str>>(&self, start_package: S) -> Option<ReachabilityPath> {
        struct EvaluationStep<'a> {
            src_package: &'a str,
            src_module: &'a str,
            step_path: Vec<(&'a str, Vec<(String, NodePath)>)>,
        }
        let mut bfs_q = VecDeque::new();
        let mut visited = HashSet::new();

        // Initialize the queue with steps for all modules in the top level package.
        //
        // This maps to the client having N files in their project, and starting a
        // search for a path from each of those N files.
        for edge in self.0.get(start_package.as_ref())? {
            for module_spec in edge.reachability().modules() {
                bfs_q.push_back(EvaluationStep {
                    src_package: start_package.as_ref(),
                    src_module: module_spec.as_ref(),
                    step_path: Vec::new(),
                });
            }
        }

        while let Some(EvaluationStep { src_package, src_module, step_path }) = bfs_q.pop_front() {
            // Skip already visited packages (would be a circular dependency).
            if visited.contains(src_package) {
                continue;
            }
            visited.insert(src_package);

            // Stop searching in this branch if it would lead to a non-existing package.
            // In practice, this should only happen in the top-level package if it is
            // misnamed, as `self` should contain only valid edges.
            let Some(edges) = self.0.get(src_package) else { continue };

            for edge in edges {
                // Each edge maintains its own copy of the step path.
                let mut step_path = step_path.clone();

                // If a subpath forward is found, add it to the path. Otherwise,
                // skip processing this edge.
                if let Some(path) = edge.reachability().find_path(src_module) {
                    step_path.push((src_package, path));
                } else {
                    continue;
                }

                match edge {
                    ReachabilityEdge::Own(_) => {
                        // This is the last branch. Return the found path.
                        return Some(
                            step_path.into_iter().map(|(k, v)| (k.to_string(), v)).collect(),
                        );
                    },
                    ReachabilityEdge::Foreign(_, symbol) => {
                        // This is an intermediate branch. Add a step towards the next symbol.
                        bfs_q.push_back(EvaluationStep {
                            src_package: &symbol.package,
                            src_module: &symbol.module,
                            step_path: step_path.clone(),
                        });
                    },
                }
            }
        }

        None
    }
}

pub struct Project<R: ModuleResolver> {
    package_resolver: PackageResolver<R>,
    packages: Vec<String>,
}

impl<R: ModuleResolver> Project<R> {
    pub fn new(package_resolver: PackageResolver<R>, packages: Vec<String>) -> Self {
        Self { package_resolver, packages }
    }

    pub fn reachability(&self, vuln_node: &VulnerableNode) -> ProjectReachability {
        self.reachability_inner(vuln_node, Default::default())
    }

    pub fn reachability_extend(
        &self,
        project_reachability: ProjectReachability,
        vuln_node: &VulnerableNode,
    ) -> ProjectReachability {
        self.reachability_inner(vuln_node, project_reachability)
    }

    pub fn all_packages(&self) -> Vec<(&str, &Package<R>)> {
        self.packages
            .iter()
            .filter_map(|package_spec| {
                self.package_resolver
                    .resolve_package(package_spec)
                    .map(|package| (package_spec.as_str(), package))
            })
            .collect()
    }

    fn reachability_inner<'a>(
        &'a self,
        vuln_node: &'a VulnerableNode,
        package_reachabilities: ProjectReachability,
    ) -> ProjectReachability {
        let ProjectReachability(mut package_reachabilities) = package_reachabilities;

        // Using foreign imports for each package, build a list of edges (a, b)
        // where b depends on a.
        let mut edges = HashSet::<(&str, &str)>::new();

        let all_foreign_imports: HashMap<_, _> = self
            .all_packages()
            .into_iter()
            .map(|(package_spec, package)| (package_spec, (package, package.foreign_imports())))
            .collect();

        for (package_spec, (_package, foreign_imports)) in &all_foreign_imports {
            for dependencies in foreign_imports.values() {
                let insert_edge = |(dependency, _)| {
                    edges.insert((package_spec, dependency));
                };

                match &dependencies {
                    Imports::Esm(imports) => imports
                        .into_iter()
                        .map(|import| import.source())
                        .map(package_spec_split)
                        .for_each(insert_edge),
                    Imports::CommonJs(imports) => imports
                        .into_iter()
                        .map(|import| import.source())
                        .map(package_spec_split)
                        .for_each(insert_edge),
                    Imports::None => continue,
                };
            }
        }

        let edges = edges.into_iter().collect::<Vec<_>>();

        // Find the topological sorting of this graph so that we can find the
        // reachability for the leaves first and for all the dependents afterwards.
        let topo_ordering = topological_sort(&edges);

        // For each dependent A on dependency B, compute reachability between A's
        // imports and B's exports.
        //
        // Let's say that the first package with a vulnerability comes Kth in the list.
        // - Packages 1 to K-1 will have empty reachability data by construction; they
        //   do not depend on (any of) the vulnerable package(s).
        // - Package K will have the reachability information starting from the given
        //   vulnerable node(s).
        // - Packages K+1 to N will be able to construct their reachability information
        //   starting from the information in package K's reachability.

        for package_spec in topo_ordering.into_iter().rev() {
            if package_reachabilities.contains_key(package_spec) {
                continue;
            }

            let mut target_nodes: Vec<(VulnerableNode, Option<VulnerableEdge>)> = Vec::new();

            // If the vulnerable spec pertains to the currently processed package,
            // add the node to the list of target nodes
            if package_spec == vuln_node.package() {
                target_nodes.push((vuln_node.clone(), None));
            }

            // A package in topo_ordering must always be present in the resolver
            // and it should also have an entry in all_foreign_imports. Skip
            // (but report) missing specs as they might be system packages
            // (e.g `fs`, `events`).
            let Some((package, foreign_imports)) = all_foreign_imports.get(package_spec) else {
                eprintln!("Package spec not found in project: {package_spec}");
                continue;
            };

            // Identify target nodes coming from foreign imports. This will not
            // run for the leaves, i.e. packages with no dependencies.
            for (module_spec, specs) in foreign_imports {
                // Link foreign imports to the symbol exported from the foreign package.
                let mut link_exports = |name: Option<&str>, source: &str, node: Node<'_>| {
                    // Extract package name, module name and reachability struct for the
                    // imported foreign package.
                    let (dep_package, dep_module) = package_spec_split(source);
                    let dep_module = dep_module
                        .or_else(|| {
                            let package = self.package_resolver.resolve_package(dep_package)?;
                            Some(package.resolver().entry_point())
                        })
                        .unwrap_or("index.js");
                    let Some(dep_reachabilities) = package_reachabilities.get(dep_package) else {
                        return;
                    };

                    let reachable_exports = dep_reachabilities
                        .iter()
                        .map(|edge| edge.reachability().reachable_exports())
                        .fold(HashSet::new(), |mut set, exports| {
                            set.extend(exports);
                            set
                        });

                    let reachability_check = match name {
                        // The hardcoded "<scope>" check is for CommonJs modules, and it represents
                        // exports that are a function. Unconditionally, any access to exports at
                        // all that are in this form is to be considered
                        // reaching.
                        //
                        // This part in CommonJs is currently shortcircuited by the `None` branch.
                        Some(name) => {
                            reachable_exports.contains(&(dep_module, name))
                                || reachable_exports.contains(&(dep_module, "<scope>"))
                        },
                        // On this branch, all exports match, regardless of their symbol.
                        // This is an over-coloring that is only useful with CommonJs until
                        // a better way of evaluating objects is found.
                        None => reachable_exports.iter().any(|&(module, _)| module == dep_module),
                    };

                    // If there is a reachability match between imports and
                    // foreign exports, insert the current import node in the
                    // target nodes, and attach information about the imported
                    // symbol.
                    if reachability_check {
                        let pos = node.start_position();
                        target_nodes.push((
                            VulnerableNode::new(
                                package_spec,
                                module_spec.to_string_lossy(),
                                pos.row,
                                pos.column,
                            ),
                            Some(VulnerableEdge::new(dep_package, dep_module)),
                        ));
                    }
                };

                match &specs {
                    Imports::Esm(imports) => {
                        for import in imports {
                            link_exports(Some(import.name()), import.source(), import.node());
                        }
                    },
                    Imports::CommonJs(imports) => {
                        for import in imports {
                            link_exports(None, import.source(), import.access_node());
                        }
                    },
                    Imports::None => {},
                }
            }

            // Compute the reachability from each target node to the visible
            // exports/side effects in a package.
            for (reachability, foreign) in target_nodes
                .into_iter()
                .map(|(target_node, foreign)| (package.reachability(&target_node), foreign))
            {
                match reachability {
                    Ok(reachability) => {
                        if !reachability.is_empty() {
                            let reachability_edge = match foreign {
                                Some(foreign) => ReachabilityEdge::Foreign(reachability, foreign),
                                None => ReachabilityEdge::Own(reachability),
                            };

                            package_reachabilities
                                .entry(package_spec.to_string())
                                .or_default()
                                .push(reachability_edge);
                        }
                    },
                    Err(e) => eprintln!("Reachability failed: {e:?}"),
                }
            }
        }

        // Pick out reachability for the topmost package. By construction, it should
        // always be the last one in the topological ordering. We should build tests
        // to ensure this is the case.
        ProjectReachability::new(package_reachabilities)
    }
}

// Utilities
//

// Split a package spec into package name and module spec.
//
// # Example
//
// ```rust
// assert_eq!(package_spec_split("@foo/bar"), ("@foo/bar", None));
// assert_eq!(package_spec_split("@foo/bar/baz.js"), ("@foo/bar", Some("baz.js")));
// assert_eq!(package_spec_split("foo"), ("foo", None));
// assert_eq!(package_spec_split("foo/bar.js"), ("foo", Some("bar.js")));
// ```
fn package_spec_split(s: &str) -> (&str, Option<&str>) {
    let idx = if s.starts_with('@') { 1 } else { 0 };

    s.match_indices('/')
        .nth(idx)
        .map(|(index, _)| s.split_at(index))
        .map(|(package, module)| (package, Some(&module[1..])))
        .unwrap_or_else(|| (s, None))
}

// Implementation of https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm
fn topological_sort<N: Copy + PartialEq + Eq + Hash>(edges: &[(N, N)]) -> Vec<N> {
    let mut nodes = {
        // Build a set of all vertices.
        let all_nodes = edges
            .iter()
            .copied()
            .flat_map(|(dependent, dependency)| [dependent, dependency])
            .collect::<HashSet<_>>();

        // Build a set of vertices with at least one incoming edge.
        let nodes_with_inc_edges =
            edges.iter().copied().map(|(_, dependency)| dependency).collect::<HashSet<_>>();

        // Build the set of vertices with no incoming edge by difference between the two
        // above. This is also going to be the working set of the algorithm.
        all_nodes.difference(&nodes_with_inc_edges).copied().collect::<VecDeque<_>>()
    };

    // Build reversed adjacency lists tp gradually remove edges from.
    let mut adj_lists: HashMap<N, HashSet<N>> =
        edges.iter().copied().fold(HashMap::new(), |mut adj_lists, (dependent, dependency)| {
            adj_lists.entry(dependency).or_default().insert(dependent);
            adj_lists
        });

    let mut ordering = Vec::new();

    while !nodes.is_empty() {
        let n = nodes.pop_front().unwrap();
        ordering.push(n);

        for (dependency, dependents) in &mut adj_lists {
            if dependents.remove(&n) && dependents.is_empty() {
                nodes.push_back(*dependency);
            }
        }
    }

    // Input graph should be a DAG hence not have any cycles; it means that
    // all the edges have been processed.
    assert!(adj_lists.iter().all(|(_, s)| s.is_empty()));

    ordering
}

#[cfg(test)]
mod tests {
    use maplit::hashmap;
    use textwrap::dedent;

    use super::*;
    use crate::javascript::module::MemModuleResolver;
    use crate::javascript::package::Package;

    macro_rules! mem_fixture {
        ($($module:expr => $src:expr,)*) => {
            Package::from_mem(hashmap! {
                $($module => dedent($src)),*
            }).unwrap()
        }
    }

    fn project_trivial_esm() -> Project<MemModuleResolver> {
        let package_resolver = PackageResolver::builder()
            .with_package(
                "dependency",
                mem_fixture!(
                    "package.json" => r#"{ "main": "index.js" }"#,
                    "index.js" => r#"
                        import { vuln } from './vuln.js'

                        export function vuln2() { vuln() }
                    "#,
                    "vuln.js" => r#"
                        export function vuln() { const foo = 2 }
                    "#,
                ),
            )
            .with_package(
                "dependent",
                mem_fixture!(
                    "package.json" => r#"{ "main": "index.js" }"#,
                    "index.js" => r#"
                        import { vuln2 } from 'dependency'

                        export function dependent_vuln() { vuln2() }
                    "#,
                ),
            )
            .build();

        Project { package_resolver, packages: vec!["dependency".into(), "dependent".into()] }
    }

    fn project_trivial_cjs() -> Project<MemModuleResolver> {
        let package_resolver = PackageResolver::builder()
            .with_package(
                "dependency",
                mem_fixture!(
                    "package.json" => r#"{ "main": "index.js" }"#,
                    "index.js" => r#"
                        const vuln = require('./vuln.js')

                        module.exports.vuln2 = function() { vuln.vuln() }
                    "#,
                    "vuln.js" => r#"
                        module.exports.vuln = function() { const foo = 2 }
                    "#,
                ),
            )
            .with_package(
                "dependent",
                mem_fixture!(
                    "package.json" => r#"{ "main": "index.js" }"#,
                    "index.js" => r#"
                        const dependency = require('dependency')

                        module.exports.vuln3 = function() { dependency.vuln2() }
                    "#,
                ),
            )
            .build();

        Project { package_resolver, packages: vec!["dependency".into(), "dependent".into()] }
    }

    #[test]
    fn test_topo_sort() {
        let edges =
            &[(5, 11), (7, 11), (7, 8), (3, 8), (3, 10), (11, 2), (11, 9), (11, 10), (8, 9)];

        let t = topological_sort(edges);

        let is_before =
            |a, b| t.iter().position(|i| i == a).unwrap() < t.iter().position(|i| i == b).unwrap();

        // Every dependent must come before all of its dependencies.
        for (a, b) in edges {
            assert!(is_before(a, b), "{a} -> {b}");
        }
    }

    #[test]
    fn test_package_spec_split() {
        assert_eq!(package_spec_split("@foo/bar"), ("@foo/bar", None));
        assert_eq!(package_spec_split("@foo/bar/baz.js"), ("@foo/bar", Some("baz.js")));
        assert_eq!(package_spec_split("foo"), ("foo", None));
        assert_eq!(package_spec_split("foo/bar.js"), ("foo", Some("bar.js")));
    }

    #[test]
    fn test_trivial_reachability_esm() {
        let project = project_trivial_esm();

        let r = project.reachability_inner(
            &VulnerableNode::new("dependency", "vuln.js", 1, 31),
            Default::default(),
        );
        let path = r.find_path("dependent").unwrap();
        println!("{:#?}", r);
        print_path(path);
    }

    #[test]
    fn test_trivial_reachability_cjs() {
        let project = project_trivial_cjs();

        let r = project.reachability_inner(
            &VulnerableNode::new("dependency", "vuln.js", 1, 41),
            Default::default(),
        );
        let path = r.find_path("dependent").unwrap();
        println!("{:#?}", r);
        print_path(path);
    }

    fn print_path(package_path: Vec<(String, Vec<(String, NodePath)>)>) {
        for (package, module_path) in package_path {
            println!("\x1b[34;1m{package}\x1b[0m:");
            for (module, node_path) in module_path {
                println!("  \x1b[36;1m{module}\x1b[0m:");
                for node_step in node_path {
                    let (r, c) = node_step.start();
                    println!("    {:>4}:{:<5}  {}", r, c, node_step.symbol(),);
                }
            }
        }
    }
}
