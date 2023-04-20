//! Package-level (i.e. Javascript files pertaining to a `package.json`) data
//! structures and methods.
pub mod reachability;
pub mod resolver;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use reachability::{PackageReachability, VulnerableNode};

use super::lang::imports::{CommonJsImports, EsmImports};
use crate::javascript::lang::imports::Imports;
use crate::javascript::module::{
    FilesystemModuleResolver, MemModuleResolver, Module, ModuleCache, ModuleResolver,
    TarballModuleResolver,
};
use crate::Result;

/// A Javascript package.
pub struct Package<R: ModuleResolver> {
    cache: ModuleCache,
    resolver: R,
}

impl<R> Package<R>
where
    R: ModuleResolver,
{
    pub fn resolve_relative<P: AsRef<Path>, Q: AsRef<Path>>(
        &self,
        spec: P,
        base: Q,
    ) -> Option<&Module> {
        self.resolver
            .resolve_relative(spec.as_ref(), base.as_ref())
            .ok()
            .and_then(|path| self.cache.module(path))
    }

    pub fn resolve_absolute<P: AsRef<Path>>(&self, spec: P) -> Option<&Module> {
        self.resolver.resolve_absolute(spec.as_ref()).ok().and_then(|path| self.cache.module(path))
    }

    pub fn cache(&self) -> &ModuleCache {
        &self.cache
    }

    pub fn resolver(&self) -> &R {
        &self.resolver
    }

    pub fn reachability(&self, vulnerable_node: &VulnerableNode) -> Result<PackageReachability> {
        PackageReachability::new(self, vulnerable_node)
    }

    /// Identify foreign imports for each module.
    ///
    /// A foreign import is an import from a source that's outside this package.
    /// For convenience, we are going to mark all imports that _don't_ resolve
    /// inside the package as foreign; true unreachable exports will be just
    /// dropped.
    pub fn foreign_imports(&self) -> HashMap<&PathBuf, Imports> {
        let mut foreign_imports = HashMap::new();

        // Strategy for detecting foreign imports: discard trivially relative
        // paths (i.e. starting with '.'), then attempt to resolve paths from
        // inside the package, marking the import as foreign if that fails.
        for (spec, module) in self.cache().modules() {
            let import_filter = |import: &str| {
                !import.starts_with('.') && self.resolve_relative(import, spec).is_none()
            };

            let import_specs = match module.imports() {
                Imports::Esm(imports) => Imports::Esm(EsmImports::new(
                    imports
                        .into_iter()
                        .filter(|import| import_filter(import.source()))
                        .cloned()
                        .collect(),
                )),
                Imports::CommonJs(imports) => Imports::CommonJs(CommonJsImports::new(
                    imports.into_iter().filter(|&import| import_filter(import.source())).collect(),
                )),
                Imports::None => continue,
            };
            foreign_imports.insert(spec, import_specs);
        }

        foreign_imports
    }
}

impl Package<TarballModuleResolver> {
    pub fn from_tarball_path<P: AsRef<Path>>(tarball: P) -> Result<Self> {
        fs::read(tarball.as_ref()).map_err(|e| e.into()).and_then(Package::from_tarball_bytes)
    }

    pub fn from_tarball_bytes(bytes: Vec<u8>) -> Result<Self> {
        let resolver = TarballModuleResolver::new(bytes)?;
        let cache = ModuleCache::new(&resolver)?;
        Ok(Self { resolver, cache })
    }
}

impl Package<FilesystemModuleResolver> {
    pub fn from_path<P: AsRef<Path>>(path: P) -> Result<Self> {
        let resolver = FilesystemModuleResolver::new(path.as_ref())?;
        let cache = ModuleCache::new(&resolver)?;
        Ok(Self { resolver, cache })
    }
}

impl Package<MemModuleResolver> {
    pub fn from_mem<K, V>(backing: HashMap<K, V>) -> Result<Self>
    where
        K: Into<PathBuf>,
        V: Into<String>,
    {
        let resolver = MemModuleResolver::new(backing);
        let cache = ModuleCache::new(&resolver)?;
        Ok(Self { resolver, cache })
    }
}

#[cfg(test)]
mod tests {
    use maplit::hashmap;
    use textwrap::dedent;

    use super::*;

    fn fixture() -> Package<MemModuleResolver> {
        Package::from_mem(hashmap! {
            "package.json" => r#"{ "main": "index.js" }"#.to_string(),
            "index.js" => dedent(r#"
                import foo from '@foo/bar'
                import bar from 'foobar'
                import baz from './baz.js'
                import quux from './quux.js'
            "#),
            "baz.js" => dedent(r#"
                export default const c = 1
            "#)
        })
        .unwrap()
    }

    #[test]
    fn test_foreign_imports() {
        let fixture = fixture();
        let foreign_imports = fixture.foreign_imports();

        fn vec_of_imports<'a>(imports: &'a Imports) -> Vec<&'a str> {
            match imports {
                Imports::Esm(imports) => imports.into_iter().map(|v| v.source()).collect(),
                _ => unreachable!(),
            }
        }

        println!("{:#?}", foreign_imports);
        assert_eq!(
            foreign_imports
                .iter()
                .map(|(&k, v)| (k.clone(), vec_of_imports(v)))
                .collect::<HashMap<PathBuf, _>>(),
            hashmap! {
                PathBuf::from("index.js") => vec!["@foo/bar", "foobar"]
            }
        );
    }
}
