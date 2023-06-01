use std::fs;
use std::path::{Path, PathBuf};

use walkdir::WalkDir;

use super::{entry_point, is_valid_js_extension};
use crate::javascript::module::resolver::ModuleResolver;
use crate::javascript::module::Module;
use crate::{Error, Result, Tree};

pub struct FilesystemModuleResolver {
    base_path: PathBuf,
    entry_point: PathBuf,
}

impl FilesystemModuleResolver {
    pub fn new<P: AsRef<Path>>(base_path: P) -> Result<Self> {
        let base_path = fs::canonicalize(base_path.as_ref())
            .map_err(|e| Error::Generic(format!("{}: {}", base_path.as_ref().display(), e)))?;

        let package_json = fs::read_to_string(base_path.join("package.json"))
            .map_err(|e| Error::Generic(format!("package.json: {}", e)))?;

        let entry_point = entry_point(&package_json)?;

        Ok(Self { base_path, entry_point })
    }
}

impl ModuleResolver for FilesystemModuleResolver {
    fn entry_point(&self) -> &str {
        // Unwrap is always valid because the entry point comes from a
        // `package.json` file which should be UTF-8 to begin with.
        self.entry_point.to_str().unwrap()
    }

    fn load<P: AsRef<Path>>(&self, path: P) -> Result<Module> {
        let path_abs = self.base_path.join(path.as_ref());
        let path = self.resolve_absolute(path_abs)?;

        let source = fs::read_to_string(&path)
            .map_err(|e| Error::Generic(format!("{}: {}", path.display(), e)))?;
        let tree = Tree::new(source)?.try_into()?;

        Ok(tree)
    }

    fn all_paths(&self) -> Box<dyn Iterator<Item = PathBuf> + '_> {
        let paths = WalkDir::new(&self.base_path)
            .into_iter()
            .flatten()
            .filter(|entry| is_valid_js_extension(entry.path()))
            .filter_map(|entry| {
                entry.path().strip_prefix(&self.base_path).ok().map(|p| p.to_path_buf())
            });
        Box::new(paths)
    }

    fn exists<P: AsRef<Path>>(&self, path: P) -> bool {
        path.as_ref().exists()
    }

    fn is_dir<P: AsRef<Path>>(&self, spec: P) -> bool {
        spec.as_ref().is_dir()
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::javascript::lang::exports::{EsmExport, Exports};
    use crate::javascript::lang::imports::{EsmImport, Imports};

    #[test]
    fn test_filesystem_resolver() {
        let dir = tempfile::tempdir().unwrap();

        let file1 = dir.path().join("file1.js");
        let file2 = dir.path().join("file2.js");
        let package_json = dir.path().join("package.json");

        fs::write(&file1, r#"export default function() { console.log("foo") }"#).unwrap();
        fs::write(&file2, r#"import foo from "./file1.js""#).unwrap();
        fs::write(package_json, r#"{ "main": "file1.js" }"#).unwrap();

        let resolver = FilesystemModuleResolver::new(dir.path()).unwrap();
        let module1 = resolver.load(&file1).unwrap();
        let module2 = resolver.load(&file2).unwrap();

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
