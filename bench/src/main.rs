//! Benchmark module loading performance.

use std::time::Duration;

use bytes::Bytes;
use vuln_reach::javascript::module::TarballModuleResolver;
use vuln_reach::javascript::package::Package;
use vuln_reach_upstream::javascript::module::TarballModuleResolver as UpstreamTarballModuleResolver;
use vuln_reach_upstream::javascript::package::Package as UpstreamPackage;

const PACKAGES: &str = include_str!("../packages");

#[tokio::main]
async fn main() {
    let mut perf_changes: Vec<f64> = Vec::with_capacity(PACKAGES.lines().count());

    for package_uri in PACKAGES.lines() {
        // Ignore packages which are commented out.
        if package_uri.starts_with('#') | package_uri.trim().is_empty() {
            continue;
        }

        println!("Benchmarking {package_uri}:");

        let tarball = reqwest::get(package_uri).await.unwrap().bytes().await.unwrap();

        // Time loading HEAD.
        let (package, elapsed) = package(&tarball);

        // Time loading upstream.
        let (upstream_package, upstream_elapsed) = upstream_package(&tarball);

        // Ensure equivalence.
        assert_eq(upstream_package, package);

        // Compute and store percentage change. Negative numbers mean faster HEAD.
        let elapsed = elapsed.as_secs_f64();
        let upstream_elapsed = upstream_elapsed.as_secs_f64();
        let pct_change = elapsed / upstream_elapsed - 1f64;

        println!(
            "\x1b[{};1m  {:.2}%\x1b[0m {}",
            if pct_change < 0. { 32 } else { 31 },
            pct_change.abs() * 100.,
            if pct_change < 0. { "improvement" } else { "regression" }
        );

        perf_changes.push(pct_change);
    }

    let mean: f64 = perf_changes.iter().copied().sum::<f64>() / perf_changes.len() as f64;
    let std: f64 = (perf_changes.iter().copied().map(|val| (val - mean).powf(2f64)).sum::<f64>()
        / (perf_changes.len() - 1) as f64)
        .sqrt();

    println!(
        "\nMean: {:5.2}% {}\n Std: {:5.2}",
        mean * 100.,
        if mean < 0. { "improvement" } else { "regression" },
        std * 100.
    );
}

// Load package for the current revision.
fn package(tarball: &Bytes) -> (Package<TarballModuleResolver>, Duration) {
    let start = std::time::Instant::now();
    let package = Package::from_tarball_bytes(tarball.to_vec()).unwrap();
    let elapsed = start.elapsed();
    println!("  HEAD loaded in {:?}", elapsed);

    (package, elapsed)
}

// Load package for the upstream revision.
fn upstream_package(tarball: &Bytes) -> (UpstreamPackage<UpstreamTarballModuleResolver>, Duration) {
    let start = std::time::Instant::now();
    let package = UpstreamPackage::from_tarball_bytes(tarball.to_vec()).unwrap();
    let elapsed = start.elapsed();
    println!("  Upstream loaded in {:?}", elapsed);

    (package, elapsed)
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
            None => panic!("Head missing key {key:?}"),
        };

        for (key, upstream_value) in upstream_value {
            assert_eq!(value.get(key), Some(upstream_value));
        }
    }

    assert_eq!(upstream_graph, graph);
}
