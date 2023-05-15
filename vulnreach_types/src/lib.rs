//! Types for the vulnerability reachability API.

use serde::{Deserialize, Serialize};

/// Identified import vulnerability.
#[derive(Serialize, Deserialize, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug)]
pub struct Vulnerability {
    pub name: String,
    pub summary: String,
    pub date: String,
    pub severity: u8,
    pub description: String,
    /// Array storing the reachability path through each affected dependency.
    ///
    /// # Example:
    ///
    /// ```ignore
    /// // Packages reduced to their name for brevity.
    /// [
    ///     [server, http, vulnerable],
    ///     [client, http, vulnerable],
    /// ]
    /// ```
    pub vulnerable_dependencies: Vec<Vec<Package>>,
}

/// Dependency package.
#[derive(Serialize, Deserialize, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug)]
pub struct Package {
    pub name: String,
    pub version: String,
    /// Path taken through this dependency to reach the next vulnerable node.
    pub path: Vec<Callsite>,
}

/// Import usage location.
#[derive(Serialize, Deserialize, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug)]
pub struct Callsite {
    pub file: String,
    pub start: (usize, usize),
    pub end: (usize, usize),
    pub text: String,
}
