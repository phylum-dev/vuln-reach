![Vuln Reach Logo](https://github.com/phylum-dev/vuln-reach/raw/main/assets/logo.png)

![GitHub Repo stars](https://img.shields.io/github/stars/phylum-dev/vuln-reach) ![GitHub](https://img.shields.io/github/license/phylum-dev/vuln-reach) ![Discord](https://img.shields.io/discord/1070071012353376387)

---

# Overview
**Vuln Reach** is a library for developing tools that determine if a given vulnerability is reachable. Provided to the open source community by [Phylum](https://phylum.io) to help reduce false positives and increase signal-to-noise for software developers.

![Vuln Reach Demo Video](https://github.com/phylum-dev/vuln-reach/raw/main/assets/vulnreach.webp)

# How does it work?

**Vuln Reach** is a static analysis library written in Rust that leverages [`tree-sitter`](https://tree-sitter.github.io/tree-sitter/) for parsing. 
It currently supports Javascript.

It builds an access graph of the source code of a package and its transitive dependencies, and then uses it to search for a path to a known vulnerable identifier node.

# Usage

Add this to your `Cargo.toml`:
```toml
[dependencies]
vuln-reach = { git = "https://github.com/phylum-dev/vuln-reach" }
```

# Example

Here's an example of how you can find out whether an identifier node in a package is reachable from another package.

```rust
use vuln_reach::javascript::package::reachability::VulnerableNode;
use vuln_reach::javascript::package::resolver::PackageResolver;
use vuln_reach::javascript::package::Package;
use vuln_reach::javascript::project::Project;

// Build a package resolver.
let package_resolver = PackageResolver::builder()
  .with_package("path-scurry", Package::from_tarball_path("./tarballs/path-scurry-1.6.1.tgz"))
  .with_package("lru-cache", Package::from_tarball_path("./tarballs/lru-cache-7.14.1.tgz"))
  .with_package("minipass", Package::from_tarball_path("./tarballs/minipass-4.0.2.tgz"))
  .build();
  
// Build a project from the package resolver.
let project = Project::new(
  package_resolver,
  vec!["path-scurry", "lru-cache", "minipass"]
);

// Define a target node.
let vulnerable_node = VulnerableNode::new("lru-cache", "index.js", 1017, 24);

// Compute the reachability graph.
let reachability = project.reachability(&vulnerable_node);

// Find a path to the vulnerable node, starting from the given package.
let path = reachability.find_path("path-scurry");
```

To find out what the transitive dependencies for your project are, you can use [Phylum](https://phylum.io)!

For a more complete example of usage, check out the [cli](https://github.com/phylum-dev/vuln-reach/tree/main/vuln-reach-cli).

# Contributing

## How do you add support for additional languages?

At the moment, the codebase is relatively tightly coupled to Javascript. Plans are underway to abstract the non-language-specific bits to be used by all languages.

Adding support for a new language requires the following steps:
- Add the relevant tree-sitter parser to [`build.rs`](https://github.com/phylum-dev/vuln-reach/blob/main/vuln-reach/build.rs).
- Create a module directory for your language in the [top level](https://github.com/phylum-dev/vuln-reach/blob/main/vuln-reach/src) of the `vuln-reach` package.
- Implement abstractions for the language's imports and exports.
- Implement [the concept of access](https://github.com/phylum-dev/vuln-reach/blob/main/vuln-reach/src/javascript/lang/accesses.rs) for your language -- this could be as simple as being equivalent to "function call" or as complex as necessary.
