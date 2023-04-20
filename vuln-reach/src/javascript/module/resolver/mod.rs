pub mod fs;
pub mod mem;
pub mod tgz;

use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::javascript::module::Module;
use crate::{util, Error, Result};

/// Trait for implementing module resolvers.
pub trait ModuleResolver {
    /// Resolve a module spec in an absolute sense.
    ///
    /// This is meant to resolve specs starting from an entry point, i.e. the
    /// `main` key in `package.json`.
    fn resolve_absolute<P: AsRef<Path>>(&self, spec: P) -> Result<PathBuf> {
        let normalized_spec = util::normalize_path(spec.as_ref());
        let full_path = resolve_path(&normalized_spec, |p| self.exists(p) && !self.is_dir(p))
            .ok_or_else(|| {
                Error::Generic(format!("Path not found: {}", normalized_spec.display()))
            })?;

        Ok(full_path)
    }

    /// Resolve a module spec relative to another spec.
    ///
    /// This is meant to resolve specs starting from other modules, i.e. in
    /// import statements inside the code itself.
    fn resolve_relative<P: AsRef<Path>, Q: AsRef<Path>>(
        &self,
        spec: P,
        relative_to_spec: Q,
    ) -> Result<PathBuf> {
        if !is_relative(&spec) {
            return self.resolve_absolute(spec);
        }

        let source_spec = self.resolve_absolute(relative_to_spec)?;
        let base_spec = if !self.is_dir(&source_spec) {
            source_spec.parent().unwrap_or(&source_spec)
        } else {
            &source_spec
        };

        let absolute_spec = base_spec.join(spec);

        self.resolve_absolute(absolute_spec)
    }

    /// Determine a package's entry point module.
    fn entry_point(&self) -> &str;

    /// Load (absolute) a given path into a [`Module`].
    fn load<P: AsRef<Path>>(&self, spec: P) -> Result<Module>;

    /// Return all paths for the package.
    fn all_paths(&self) -> Box<dyn Iterator<Item = PathBuf> + '_>;

    /// Determine whether the supplied module specifier exists within
    /// the current resolver.
    fn exists<P: AsRef<Path>>(&self, spec: P) -> bool;

    /// Determine whether the supplied module specifier is a directory
    /// within the current resolver.
    fn is_dir<P: AsRef<Path>>(&self, spec: P) -> bool;
}

// Implement a best-effort Node.js-compatible module path determination,
// that takes into account both CommonJS and ESM.
// See https://nodejs.org/api/packages.html#determining-module-system
pub(crate) fn resolve_path<P, F>(base_path: P, exists_predicate: F) -> Option<PathBuf>
where
    P: AsRef<Path>,
    F: Fn(&Path) -> bool,
{
    let mut path = base_path.as_ref().to_path_buf();

    // Check if path itself exists.
    if exists_predicate(&path) {
        return Some(path);
    }

    // Try path combined with JavaScript suffixes.
    for suffix in ["js", "mjs", "cjs"] {
        path.set_extension(suffix);
        if exists_predicate(&path) {
            return Some(path);
        }
    }

    // Try entrypoints in the path's directory.
    for entrypoint in ["index.js", "index.mjs", "index.cjs"] {
        path = base_path.as_ref().to_path_buf().join(entrypoint);
        if exists_predicate(&path) {
            return Some(path);
        }
    }

    None
}

// For an import specifier to be recognized as relative in Javascript, it _has_
// to start with either "." or "..". This means that we can use this predicate
// to avoid trying to resolve as relative a spec which is bare or absolute.
//
// https://nodejs.org/api/modules.html#all-together
// https://nodejs.org/api/esm.html#import-specifiers
fn is_relative<P: AsRef<Path>>(path: P) -> bool {
    let path = path.as_ref();
    path.starts_with(".") || path.starts_with("..")
}

fn is_valid_js_extension<P: AsRef<Path>>(path: P) -> bool {
    path.as_ref().extension().map_or(false, |ext| {
        let lowercase_ext = ext.to_string_lossy().to_lowercase();
        ["js", "mjs", "cjs"].contains(&&*lowercase_ext)
    })
}

#[derive(Deserialize)]
struct PackageJson {
    main: Option<PathBuf>,
}

// Retrieve the entry point from the "main" field in `package.json`.
pub(crate) fn entry_point(package_json: &str) -> Result<PathBuf> {
    serde_json::from_str::<PackageJson>(package_json)
        .map_err(|e| Error::Generic(format!("package.json deserialization error: {e:?}")))
        .map(|p| p.main.unwrap_or_else(|| PathBuf::from("index.js")))
        .map(|path| util::normalize_path(&path))
}
