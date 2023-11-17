use std::collections::HashMap;
use std::fmt::Display;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Result};
use clap::Parser;
use futures::future;
use serde::de::Error;
use serde::{Deserialize, Deserializer};
use tokio::fs;
use vuln_reach::javascript::package::reachability::{NodePath, VulnerableNode};
use vuln_reach::javascript::package::resolver::PackageResolver;
use vuln_reach::javascript::package::Package;
use vuln_reach::javascript::project::Project;

type StdResult<T, E> = std::result::Result<T, E>;

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
    #[serde(deserialize_with = "deserialize_vulnerable_node")]
    vuln: Vec<VulnerableNode>,
}

#[derive(Default)]
struct NodeValidation {
    start_after_end: Option<((usize, usize), (usize, usize))>,
    zero_value: bool,
}

impl NodeValidation {
    fn new(node: &VulnerableNode) -> Self {
        let start_row = node.start_row();
        let start_column = node.start_column();
        let end_row = node.end_row();
        let end_column = node.end_column();

        let start_after_end =
            if start_row > end_row || (start_row == end_row && start_column > end_column) {
                Some(((start_row, start_column), (end_row, end_column)))
            } else {
                None
            };

        Self {
            start_after_end,
            zero_value: node.start_row() == 0
                || node.end_row() == 0
                || node.start_column() == 0
                || node.end_column() == 0,
        }
    }

    fn is_error(&self) -> bool {
        self.start_after_end.is_some() || self.zero_value
    }
}

impl Display for NodeValidation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid node representation: ")?;

        if let Some(((start_row, start_column), (end_row, end_column))) = self.start_after_end {
            write!(f, "Start position ({start_row}, {start_column}) is after end position ({end_row}, {end_column}); ")?;
        }

        if self.zero_value {
            write!(f, "Zero values are not allowed")?;
        }

        Ok(())
    }
}

fn deserialize_vulnerable_node<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> StdResult<Vec<VulnerableNode>, D::Error> {
    let nodes = Vec::<VulnerableNode>::deserialize(deserializer)?;
    nodes
        .into_iter()
        .map(|node| {
            let validation = NodeValidation::new(&node);
            if validation.is_error() {
                return Err(D::Error::custom(validation.to_string()));
            }

            let start_row = node.start_row();
            let start_column = node.start_column();
            let end_row = node.end_row();
            let end_column = node.end_column();

            Ok(VulnerableNode::new(
                node.package(),
                node.module(),
                start_row.saturating_sub(1),
                start_column.saturating_sub(1),
                end_row.saturating_sub(1),
                end_column.saturating_sub(1),
            ))
        })
        .collect::<StdResult<Vec<VulnerableNode>, D::Error>>()
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

        // Build the project object.
        let project = Project::new(package_resolver);

        // Compute reachability for each node.
        for node in &self.vuln {
            let reachability = project.reachability(node)?;

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
