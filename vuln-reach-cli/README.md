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
  { package = "generic-pool", module = "lib/Pool.js", start_row = 744, start_column = 18, end_row = 744, end_column = 22 }
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
  { package = "lru-cache", module = "index.js", start_row = 1018, start_column = 18, end_row = 1018, end_column = 25 }
]
```

In each of those objects: 
- `packages` is the list of packages, and their version, available in the project. It must contain
  the elements of the entire _transitive_ dependency tree, not just the first-level dependencies.
  You can find the transitive dependency tree via the [Phylum CLI](https://github.com/phylum-dev/cli):
  ```shell
  $ npm init -y && npm i --save <top level packages>  # for a new project
  $ phylum parse package-lock.json
  ```
- `vuln` indicates a vulnerable node in the specified `package`, in the file
  `module` at position `(row, column)`. Note that, differently from the library,
  the position is 1-indexed so specify these values in the same way they are
  displayed in a text editor.

The term "vulnerable node" is used loosely here -- any identifier can be chosen as the
target node that will be searched for.

### Running

```
cargo run --release --bin vuln-reach-cli -- sample.toml
```

All the specifications in `sample.toml` will be analyzed for reachability.
If the node is determined to be reachable, the tool will print the access path that was found.
