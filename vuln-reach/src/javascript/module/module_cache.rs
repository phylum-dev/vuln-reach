use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Write;
use std::path::{Path, PathBuf};

use super::resolver::resolve_path;
use crate::javascript::lang::imports::Imports;
use crate::javascript::module::{Module, ModuleResolver};
use crate::Result;

// Type aliases are just for clarity.
type RelativeSpec = PathBuf;
type AbsoluteSpec = PathBuf;

/// Represents a graph of modules in a package.
pub struct ModuleCache {
    /// The dictionary that maps absolute import specs to Module objects.
    cache: HashMap<AbsoluteSpec, Module>,
    /// The graph of import relationships.
    ///
    /// Example: if `foo/bar/baz.js` imports `../quux.js`, there will
    /// be a mapping of the form
    /// ```js
    /// { "foo/bar/baz.js": { "../quux.js": "foo/quux.js" } }
    /// ```
    module_graph: HashMap<AbsoluteSpec, HashMap<RelativeSpec, AbsoluteSpec>>,
}

impl ModuleCache {
    /// Construct the cache by going through all the paths in the provided
    /// resolver.
    pub fn new<R: ModuleResolver>(resolver: &R) -> Result<Self> {
        ModuleCache::with_initial_nodes(resolver, resolver.all_paths())
    }

    /// Construct the cache by going through the specified entry point only.
    ///
    /// This will create a smaller graph with only the imports reachable from
    /// the specified entry point.
    pub fn with_entry_point<P: AsRef<Path>, R: ModuleResolver>(
        resolver: &R,
        entry_point: P,
    ) -> Result<Self> {
        ModuleCache::with_initial_nodes(resolver, Some(entry_point))
    }

    /// Generic constructor that evaluates edges going out of all the supplied
    /// import paths.
    fn with_initial_nodes<P: AsRef<Path>, R: ModuleResolver>(
        resolver: &R,
        nodes: impl IntoIterator<Item = P>,
    ) -> Result<Self> {
        // Create a queue and add all the supplied import paths.
        let mut q = VecDeque::<(Option<PathBuf>, PathBuf)>::new();
        nodes.into_iter().for_each(|node| {
            q.push_back((None, node.as_ref().to_path_buf()));
        });

        // Cache visited nodes (i.e. modules).
        let mut visited = HashSet::new();

        let mut cache = HashMap::default();
        let mut module_graph: HashMap<AbsoluteSpec, HashMap<RelativeSpec, AbsoluteSpec>> =
            HashMap::default();

        while !q.is_empty() {
            // Pick the top of the queue.
            let (current_module_spec, import_spec) = q.pop_front().unwrap();

            // Skip if the module has already been visited.
            {
                let b = (current_module_spec.clone(), import_spec.clone());
                if visited.contains(&b) {
                    continue;
                }
                visited.insert(b);
            }

            // Ignore resolution errors for now; we only need to load the package's modules.
            // Resolution errors can either be bona fide mistakes (i.e. a module which
            // doesn't exist in the package, but should) or dependency imports
            // (which shouldn't exist in a context where only the package itself
            // exists, i.e. a tarball).

            // Retrieve absolute spec. For example, if 'foo/bar.js' imports '../baz/quux',
            // return 'foo/baz/quux'.
            let absolute_spec = match current_module_spec
                .as_ref()
                .map(|current_module_spec| {
                    resolver.resolve_relative(&import_spec, current_module_spec)
                })
                .unwrap_or_else(|| resolver.resolve_absolute(&import_spec))
            {
                Ok(absolute_spec) => absolute_spec,
                Err(_) => continue,
            };

            // Load modules into cache on demand.
            let module = match cache.entry(absolute_spec.clone()) {
                Entry::Occupied(module) => module.into_mut(),
                Entry::Vacant(vacant) => {
                    // Load a new module.
                    let module = match resolver.load(&absolute_spec) {
                        Ok(module) => module,
                        Err(_) => continue,
                    };
                    vacant.insert(module)
                },
            };

            // Only process import sources now.
            match module.imports() {
                Imports::Esm(esm_imports) => {
                    // Add to the queue all the paths that the current ES Module file imports.
                    for import in esm_imports {
                        q.push_back((Some(absolute_spec.clone()), import.source().into()));
                    }
                },
                Imports::CommonJs(cjs_imports) => {
                    // Add to the queue all the paths that the current CommonJS file imports.
                    for import in cjs_imports {
                        q.push_back((Some(absolute_spec.clone()), import.source().into()));
                    }
                },
                Imports::None => {},
            }

            // Insert an edge to the import in the base module's adjacency list.
            if let Some(current_module) = current_module_spec {
                module_graph
                    .entry(current_module.to_path_buf())
                    .or_default()
                    .insert(import_spec, absolute_spec);
            }
        }

        Ok(Self { cache, module_graph })
    }

    /// Retrieve the dependencies of the given import specification.
    pub fn module_deps<P: AsRef<Path>>(
        &self,
        spec: P,
    ) -> Option<&HashMap<RelativeSpec, AbsoluteSpec>> {
        self.module_graph.get(spec.as_ref())
    }

    /// Retrieve the module associated to the given specification.
    pub fn module<P: AsRef<Path>>(&self, spec: P) -> Option<&Module> {
        self.cache.get(spec.as_ref())
    }

    /// Get the dictionary of all the modules.
    pub fn modules(&self) -> &HashMap<AbsoluteSpec, Module> {
        &self.cache
    }

    /// Get the dependency graph.
    pub fn graph(&self) -> &HashMap<AbsoluteSpec, HashMap<RelativeSpec, AbsoluteSpec>> {
        &self.module_graph
    }

    // Find out which modules import the specified dependency.
    pub fn dependents_of<'a, P: AsRef<Path> + 'a>(
        &'a self,
        dependency: P,
    ) -> impl Iterator<Item = &'a PathBuf> {
        self.graph().iter().filter_map(move |(spec, deps)| {
            deps.values()
                .find_map(|import_spec| resolve_path(import_spec, |f| f == dependency.as_ref()))
                .map(|_| spec)
        })
    }

    // Find out if dependent_spec (absolute) depends on dependency_spec (may be
    // relative)
    pub fn depends_on<P: AsRef<Path>, Q: AsRef<Path>>(
        &self,
        dependent_spec: P,
        dependency_spec: Q,
    ) -> bool {
        let deps = self.graph().get(dependent_spec.as_ref()).unwrap();
        deps.contains_key(dependency_spec.as_ref())
            || deps.values().any(|dep| dep == dependency_spec.as_ref())
    }

    /// Get a module by using a spec relative to another module.
    ///
    /// It is assumed that `spec` can only ever appear inside a given module.
    pub fn module_rel<P: AsRef<Path>, Q: AsRef<Path>>(&self, spec: P, base: Q) -> Option<&Module> {
        self.module_deps(base)
            .and_then(|deps| deps.get(spec.as_ref()))
            .and_then(|absolute_spec| self.cache.get(absolute_spec))
    }

    /// Convert the graph to the Graphviz dot format.
    pub fn to_dot(&self) -> String {
        let mut buf = String::from("digraph G {\n  rankdir = LR;\n");
        let mut node_id = 0usize;
        let mut node_ids = HashMap::<PathBuf, usize>::new();

        for (k, vs) in self.graph() {
            let k_id = *node_ids.entry(k.clone()).or_insert_with(|| {
                node_id += 1;
                node_id
            });

            for v in vs.values() {
                let v_id = *node_ids.entry(v.clone()).or_insert_with(|| {
                    node_id += 1;
                    node_id
                });

                writeln!(buf, "  node{k_id:03} -> node{v_id:03}").unwrap();
            }
        }
        writeln!(buf, "\n").unwrap();

        for (path, id) in node_ids {
            writeln!(buf, "  node{id:03} [label=\"{}\"]", path.display()).unwrap();
        }
        writeln!(buf, "}}").unwrap();

        buf
    }
}
