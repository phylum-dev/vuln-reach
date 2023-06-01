//! Benchmark module loading performance.

use bytes::Bytes;
use vuln_reach::javascript::module::TarballModuleResolver;
use vuln_reach::javascript::package::Package;
use vuln_reach_upstream::javascript::module::TarballModuleResolver as UpstreamTarballModuleResolver;
use vuln_reach_upstream::javascript::package::Package as UpstreamPackage;

const PACKAGES: &str = include_str!("../packages");

#[tokio::main]
async fn main() {
    for package_uri in PACKAGES.lines() {
        // Ignore packages which are commented out.
        if package_uri.starts_with('#') {
            continue;
        }

        println!("Benchmarking {package_uri}:");

        let tarball = reqwest::get(package_uri).await.unwrap().bytes().await.unwrap();

        // Time loading HEAD.
        let package = package(&tarball);

        // Time loading upstream.
        let upstream_package = upstream_package(&tarball);

        // Ensure equivalence.
        assert_eq(upstream_package, package);
    }
}

// Load package for the current revision.
fn package(tarball: &Bytes) -> Package<TarballModuleResolver> {
    let start = std::time::Instant::now();
    let package = Package::from_tarball_bytes(tarball.to_vec()).unwrap();
    println!("  HEAD loaded in {:?}", start.elapsed());

    package
}

// Load package for the upstream revision.
fn upstream_package(tarball: &Bytes) -> UpstreamPackage<UpstreamTarballModuleResolver> {
    let start = std::time::Instant::now();
    let package = UpstreamPackage::from_tarball_bytes(tarball.to_vec()).unwrap();
    println!("  Upstream loaded in {:?}", start.elapsed());

    package
}

// Check for equivalence of upstream/HEAD.
fn assert_eq(
    upstream: UpstreamPackage<UpstreamTarballModuleResolver>,
    head: Package<TarballModuleResolver>,
) {
    let upstream_graph = upstream.cache().graph();
    let graph = head.cache().graph();

    for (key, upstream_value) in upstream_graph {
        let value = match graph.get(key) {
            Some(value) => value,
            None => panic!("Missing key {key:?}"),
        };

        for (key, upstream_value) in upstream_value {
            assert_eq!(value.get(key), Some(upstream_value));
        }
    }
}
