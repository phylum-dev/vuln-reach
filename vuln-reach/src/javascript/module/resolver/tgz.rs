use std::collections::HashMap;
use std::io::Read;
use std::path::{Path, PathBuf};

use flate2::read::GzDecoder;
use tar::Archive;

use super::{entry_point, is_valid_js_extension};
use crate::javascript::module::resolver::ModuleResolver;
use crate::javascript::module::Module;
use crate::{Error, Result, Tree};

pub struct TarballModuleResolver {
    files: HashMap<PathBuf, Vec<u8>>,
    entry_point: PathBuf,
}

impl TarballModuleResolver {
    pub fn new(bytes: Vec<u8>) -> Result<Self> {
        // Immediately extract the file in-memory because random access directly
        // from the tarball object is not possible.
        let files = Archive::new(GzDecoder::new(&bytes[..]))
            .entries()?
            .filter_map(|entry| entry.ok())
            .filter_map(|mut entry| {
                // Skip the toplevel directory, to go to the module's root.
                let mut path = PathBuf::from(entry.path().unwrap());
                path = path.components().skip(1).collect();

                let mut data = Vec::new();
                entry.read_to_end(&mut data).ok()?;

                Some((path, data))
            })
            .collect::<HashMap<_, _>>();

        let package_json = std::str::from_utf8(files.get(Path::new("package.json")).unwrap())
            .map_err(|e| Error::Generic(format!("package.json: {}", e)))?;

        let entry_point = entry_point(package_json)?;

        Ok(Self { files, entry_point })
    }
}

impl ModuleResolver for TarballModuleResolver {
    fn entry_point(&self) -> &str {
        // Unwrap is always valid because the entry point comes from a
        // `package.json` file which should be UTF-8 to begin with.
        self.entry_point.to_str().unwrap()
    }

    fn load<P: AsRef<Path>>(&self, path: P) -> Result<Module> {
        let path = self.resolve_absolute(path)?;

        let source = std::str::from_utf8(self.files.get(&path).unwrap())
            .map_err(|e| Error::Generic(format!("{}: {}", path.display(), e)))?
            .to_string();
        let tree = Tree::new(source)?.into();

        Ok(tree)
    }

    fn all_paths(&self) -> Box<dyn Iterator<Item = PathBuf> + '_> {
        let paths = self.files.keys().filter(|path| is_valid_js_extension(path)).cloned();
        Box::new(paths)
    }

    fn exists<P: AsRef<Path>>(&self, path: P) -> bool {
        self.files.contains_key(path.as_ref())
    }

    fn is_dir<P: AsRef<Path>>(&self, _spec: P) -> bool {
        // Paths in a tarball are never directories.
        false
    }
}
