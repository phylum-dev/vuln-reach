use std::collections::HashMap;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Result};
use clap::Parser;
use futures::future;
use serde::Deserialize;
use tokio::fs;
use vuln_reach::javascript::package::reachability::{NodePath, VulnerableNode};
use vuln_reach::javascript::package::resolver::PackageResolver;
use vuln_reach::javascript::package::Package;
use vuln_reach::javascript::project::Project;

#[derive(Deserialize)]
struct NpmRegistry {
    versions: HashMap<String, Version>,
}

#[derive(Deserialize)]
struct Version {
    dist: Dist,
}

#[derive(Deserialize)]
struct Dist {
    tarball: String,
}

#[derive(Deserialize, Debug, Hash, PartialEq, Eq)]
struct PackageDef {
    name: String,
    version: String,
}

impl PackageDef {
    fn tarball(&self) -> PathBuf {
        PathBuf::from(format!("{}-{}.tgz", self.name, self.version))
    }

    async fn retrieve(&self, prefix: &Path) -> Result<()> {
        let save_path = prefix.join(self.tarball());

        if save_path.exists() {
            return Ok(());
        }

        println!(
            "Downloading \x1b[36m{}-{}\x1b[0m to \x1b[33m{}\x1b[0m...",
            self.name,
            self.version,
            save_path.display()
        );

        let registry = reqwest::get(format!("https://registry.npmjs.org/{}", self.name))
            .await?
            .json::<NpmRegistry>()
            .await?;

        let tarball_url = &registry
            .versions
            .get(&self.version)
            .ok_or_else(|| anyhow!("{}-{} not found", self.name, self.version))?
            .dist
            .tarball;

        let tarball_data = reqwest::get(tarball_url).await?.bytes().await?;

        fs::create_dir_all(save_path.parent().unwrap()).await?;
        fs::write(save_path, tarball_data).await?;

        Ok(())
    }
}

#[derive(Deserialize, Debug)]
struct ProjectDef {
    name: String,
    tarballs: PathBuf,
    packages: Vec<PackageDef>,
    vuln: Vec<VulnerableNode>,
}

impl ProjectDef {
    async fn sync(&self) -> Result<()> {
        let results = future::join_all(
            self.packages.iter().map(|package| async { package.retrieve(&self.tarballs).await }),
        )
        .await;

        for r in results {
            r?;
        }

        Ok(())
    }

    fn reachability(self) -> Result<()> {
        // Build the package resolver.
        let mut package_resolver = PackageResolver::builder();

        for package_def in &self.packages {
            let tarball_path = self.tarballs.join(package_def.tarball());
            let tarball = Package::from_tarball_path(&tarball_path)
                .map_err(|e| anyhow!("{tarball_path:?}: {e:?}"))?;
            package_resolver = package_resolver.with_package(&package_def.name, tarball);
        }

        let package_resolver = package_resolver.build();
        let packages =
            self.packages.iter().map(|PackageDef { name, .. }| name.clone()).collect::<Vec<_>>();

        // Build the project object.
        let project = Project::new(package_resolver, packages);

        // Compute reachability for each node.
        for node in &self.vuln {
            let reachability = project.reachability(node);

            let path = reachability.find_path(&self.name);

            match path {
                Some(path) => {
                    println!(
                        "\n\x1b[31m  *** Node {}/{}:{}:{} is reachable!\x1b[0m\n",
                        node.package(),
                        node.module(),
                        node.start_row(),
                        node.start_column()
                    );
                    print_path(path);
                },
                None => {
                    println!(
                        "\n\x1b[33m  *** No paths to {}/{}:{}:{} found.\x1b[0m",
                        node.package(),
                        node.module(),
                        node.start_row(),
                        node.start_column()
                    );
                },
            }
        }

        Ok(())
    }
}

#[derive(Deserialize, Debug)]
struct Projects {
    projects: Vec<ProjectDef>,
}

impl Projects {
    async fn sync(&self) -> Result<()> {
        let results = future::join_all(self.projects.iter().map(ProjectDef::sync)).await;
        for r in results {
            r?;
        }

        Ok(())
    }
}

fn print_path(package_path: Vec<(String, Vec<(String, NodePath)>)>) {
    for (package, module_path) in package_path {
        println!("  \x1b[34;1m{package}\x1b[0m:");
        for (module, node_path) in module_path {
            println!("    \x1b[33;1m{module}\x1b[0m:");
            for node_step in node_path {
                let (r, c) = node_step.start();
                println!("      {:>4}:{:<5}  {}", r, c, node_step.symbol(),);
            }
        }
    }
}

#[derive(Parser, Debug)]
struct Cli {
    /// Path to a reachability definition .toml file
    path: String,
}

async fn read_document(path: &str) -> Result<Projects> {
    Ok(toml::from_str::<Projects>(fs::read_to_string(path).await?.as_str())?)
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    let documents = read_document(&cli.path).await?;
    documents.sync().await?;

    for document in documents.projects {
        println!("\n\x1b[46;30m    Reachability for {}    \x1b[0m\n", document.name);
        document.reachability()?;
    }

    Ok(())
}
