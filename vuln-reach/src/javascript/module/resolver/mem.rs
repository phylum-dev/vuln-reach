use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::{entry_point, is_valid_js_extension};
use crate::javascript::module::resolver::ModuleResolver;
use crate::javascript::module::Module;
use crate::{Error, Result, Tree};

pub struct MemModuleResolver {
    backing: HashMap<PathBuf, String>,
    entry_point: PathBuf,
}

impl MemModuleResolver {
    pub fn new<K, V>(backing: HashMap<K, V>) -> Self
    where
        K: Into<PathBuf>,
        V: Into<String>,
    {
        let backing: HashMap<PathBuf, String> =
            backing.into_iter().map(|(k, v)| (k.into(), v.into())).collect();
        let package_json = backing
            .get(Path::new("package.json"))
            .ok_or_else(|| Error::Generic("package.json: not found".to_string()))
            .unwrap();

        let entry_point = entry_point(package_json).unwrap();

        Self { backing, entry_point }
    }
}

impl ModuleResolver for MemModuleResolver {
    fn entry_point(&self) -> &str {
        // Unwrap is always valid because the entry point comes from a
        // `package.json` file which should be UTF-8 to begin with.
        self.entry_point.to_str().unwrap()
    }

    fn load<P: AsRef<Path>>(&self, path: P) -> Result<Module> {
        let path = self.resolve_absolute(path)?;

        let tree = Tree::new(self.backing.get(path.as_path()).unwrap().to_string())?.into();

        Ok(tree)
    }

    fn all_paths(&self) -> Box<dyn Iterator<Item = PathBuf> + '_> {
        let paths = self.backing.keys().filter(|path| is_valid_js_extension(path)).cloned();
        Box::new(paths)
    }

    fn exists<P: AsRef<Path>>(&self, path: P) -> bool {
        self.backing.contains_key(path.as_ref())
    }

    fn is_dir<P: AsRef<Path>>(&self, _spec: P) -> bool {
        // Paths in memory are never directories.
        false
    }
}

#[cfg(test)]
mod tests {
    use maplit::hashmap;

    use super::*;
    use crate::javascript::lang::exports::{EsmExport, Exports};
    use crate::javascript::lang::imports::{EsmImport, Imports};

    #[test]
    fn test_mem_resolver() {
        let resolver = MemModuleResolver::new(hashmap! {
            "package.json" => "{}",
            "file1.js" => r#"export default function() { console.log("foo") }"#,
            "file2.js" => r#"import foo from "./file1.js""#,
        });

        let module1 = resolver.load("file1.js").unwrap();
        let module2 = resolver.load("file2.js").unwrap();

        match module1.exports() {
            Exports::Esm(e) => {
                if let Some(EsmExport::Scope(e)) = e.default {
                    println!("Default export: {:?}", module1.tree().repr_of(e));
                } else {
                    panic!("Failed assertion: {e:?}");
                }
            },
            Exports::CommonJs(_) => unreachable!(),
            Exports::None => unreachable!(),
        }

        match module2.imports() {
            Imports::Esm(i) => {
                if let Some(EsmImport::Default { name, source, .. }) = i.first() {
                    println!("Default import: {name} from {source}");
                } else {
                    panic!("Failed assertion: {i:?}");
                }
            },
            Imports::CommonJs(_) => unreachable!(),
            Imports::None => unreachable!(),
        }

        let mut paths = resolver.all_paths().collect::<Vec<_>>();
        paths.sort();
        assert_eq!(paths, vec![PathBuf::from("file1.js"), PathBuf::from("file2.js")]);
    }
}
