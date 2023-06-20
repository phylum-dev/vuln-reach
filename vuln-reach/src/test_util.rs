use std::fs;
use std::path::{Path, PathBuf};

use crate::javascript::module::TarballModuleResolver;
use crate::javascript::package::Package;

/// Retrieve the tarball bytes for a given package and version. Will use the
/// on-disk cache or download the package from npm.
pub async fn get_tarball_bytes(package_name: &str, version: &str) -> Vec<u8> {
    let package_path = tarball_path(package_name, version);

    if package_path.exists() {
        fs::read(package_path).expect("Could not read tarball contents")
    } else {
        download_tarball(package_name, version, &package_path).await
    }
}

pub async fn npm_package(name: &str, version: &str) -> Package<TarballModuleResolver> {
    Package::from_tarball_bytes(get_tarball_bytes(name, version).await).unwrap()
}

// Return the path to the tarball cache. Create the directory if it doesn't
// exist.
fn tarball_cache_path() -> PathBuf {
    let tarball_cache_path = PathBuf::from(env!("OUT_DIR")).join("tarball_cache");
    if !tarball_cache_path.exists() {
        fs::create_dir_all(&tarball_cache_path).expect("Could not create tarball cache directory");
    }

    tarball_cache_path
}

fn tarball_path(package_name: &str, version: &str) -> PathBuf {
    tarball_cache_path().join(format!("{package_name}-{version}.tgz"))
}

async fn download_tarball(full_package_name: &str, version: &str, package_path: &Path) -> Vec<u8> {
    // Turn "@foo/bar" into ("@foo/bar", "bar") and "foo" into ("foo", "foo").
    let (namespace, package_name) = full_package_name
        .split_once('/')
        .map(|(_, b)| (full_package_name, b))
        .unwrap_or_else(|| (full_package_name, full_package_name));

    let package_uri =
        format!("https://registry.npmjs.org/{namespace}/-/{package_name}-{version}.tgz");

    println!("Downloading {full_package_name} {version} to {package_path:?}...");
    let bytes = reqwest::get(package_uri).await.unwrap().bytes().await.unwrap().to_vec();

    // Ensure directory exists for a scoped package.
    if full_package_name.contains('/') {
        fs::create_dir_all(package_path.parent().unwrap())
            .expect("Could not create scope directory in tarball cache directory");
    }

    fs::write(package_path, &bytes).expect("Could not write tarball contents");

    bytes
}
