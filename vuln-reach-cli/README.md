# vuln-reach-cli

This tool is intended for easing local research and development, and test case design.

## Building

```
cargo build --release --package vuln-reach-cli
```

## Usage

### Specification file

The specification file format is `toml`.

`vuln-reach-cli` relies on it to retrieve the packages from the 
[npm registry](https://registry.npmjs.com/).

The file must contain a list of `project` objects, structured like this:

```toml
[[projects]]
name = "@redis/client"
tarballs = "./tarballs"
packages = [
  { name = "@redis/client", version = "1.0.6" },
  { name = "cluster-key-slot", version = "1.1.2" },
  { name = "yallist", version = "4.0.0" },
  { name = "generic-pool", version = "3.8.2" },
]
vuln = [
  { package = "generic-pool", module = "lib/Pool.js", start_row = 743, start_column = 17, end_row = 743, end_column = 21 }
]

[[projects]]
name = "path-scurry"
tarballs = "./tarballs"
packages = [
  { name = "path-scurry", version = "1.6.1" },
  { name = "lru-cache", version = "7.14.1" },
  { name = "minipass", version = "4.0.2" },
]
vuln = [
  { package = "lru-cache", module = "index.js", start_row = 1017, start_column = 17, end_row = 1017, end_column = 24 }
]
```

In each of those objects: 
- `packages` is the list of packages, and their version, available in the project.
- `vuln` states that there is a vulnerable node
  in the specified `package`, in the file `module` at position `(row, column)`. Note that
  the position is 0-indexed so what would look like `(10, 8)` in a text editor should be
  specified as `(9, 7)`.

The term "vulnerable node" is used loosely here -- any identifier can be chosen as the
target node that will be searched for.

### Running

```
cargo run --release --bin vuln-reach-cli -- sample.toml
```

All the specifications in `sample.toml` will be analyzed for reachability.
If the node is determined to be reachable, the tool will print the access path that was found.
