use std::collections::HashMap;
use std::path::{Component, Path};

use crate::javascript::module::{Module, ModuleResolver};
use crate::javascript::package::Package;

/// A cache of packages.
pub struct PackageResolver<R: ModuleResolver> {
    packages: HashMap<String, Package<R>>,
}

impl<R> PackageResolver<R>
where
    R: ModuleResolver,
{
    /// Creates a new builder.
    pub fn builder() -> PackageResolverBuilder<R> {
        Default::default()
    }

    /// Returns the specified package, if present.
    pub fn resolve_package(&self, package: &str) -> Option<&Package<R>> {
        self.packages.get(package)
    }

    /// Resolves a package and a module given a full import spec.
    ///
    /// # Examples
    ///
    /// ```js
    /// import "@foo/bar/baz/quux.js"  // yields ("@foo/bar", "baz/quux.js")
    /// import "foo/bar/baz.js"        // yields ("foo", "bar/baz.js")
    /// ```
    pub fn resolve_spec(&self, full_spec: &Path) -> Option<(&Package<R>, &Module)> {
        let (pkg_path, spec) = match full_spec.components().next() {
            Some(Component::Normal(x)) if x.to_string_lossy().starts_with('@') => {
                let mut c = full_spec.components();
                let scope = c.next()?;
                let package = c.next()?;
                let spec = c.as_path();

                let scope_path: &Path = scope.as_ref();
                let package_path: &Path = package.as_ref();

                Some((scope_path.to_path_buf().join(package_path), spec))
            },
            Some(Component::Normal(_)) => {
                let mut c = full_spec.components();
                let package = c.next()?;
                let spec = c.as_path();

                let package_path: &Path = package.as_ref();

                Some((package_path.to_path_buf(), spec))
            },
            _ => None,
        }?;

        let package = self.resolve_package(&pkg_path.to_string_lossy())?;
        let module = package.resolve_absolute(spec)?;

        Some((package, module))
    }
}

/// Builder for [`PackageResolver`].
pub struct PackageResolverBuilder<R: ModuleResolver> {
    packages: HashMap<String, Package<R>>,
}

impl<R> Default for PackageResolverBuilder<R>
where
    R: ModuleResolver,
{
    fn default() -> Self {
        Self { packages: Default::default() }
    }
}

impl<R> PackageResolverBuilder<R>
where
    R: ModuleResolver,
{
    /// Inserts the specified package in the resolver.
    pub fn with_package<S: Into<String>>(mut self, k: S, v: Package<R>) -> Self {
        self.packages.insert(k.into(), v);
        self
    }

    /// Builds the value.
    pub fn build(self) -> PackageResolver<R> {
        PackageResolver { packages: self.packages }
    }
}
