# pathfinder-cli

This tool is intended for easing local research and development, and test case design.

## Building

```
cargo build --release --package pathfinder-cli
```

## Usage

### Specification file

The specification file format is `toml`.

`pathfinder-cli` relies on it to build the resolver which will associate a package specifier
(e.g. `@redis/client`) to the path to the tarball containing the package's release artifacts
(i.e. the tarballs that can be downloaded off of `https://registry.npmjs.com`).

The file must contain a list of `project` objects, structured like this:

```toml
[[projects]]
name = "redis-client"
packages = [
  { name = "@redis/client", path = "../pathfinder/tests/fixtures/redis-client/client-1.0.6.tgz" },
  { name = "cluster-key-slot", path = "../pathfinder/tests/fixtures/redis-client/cluster-key-slot-1.1.2.tgz" },
  { name = "yallist", path = "../pathfinder/tests/fixtures/redis-client/yallist-4.0.0.tgz" },
  { name = "generic-pool", path = "../pathfinder/tests/fixtures/redis-client/generic-pool-3.8.2.tgz" }
]
vuln = [
  { package = "generic-pool", module = "lib/Pool.js", row = 743, column = 17 }
]

[[projects]]
name = "path-scurry"
packages = [
  { name = "path-scurry", path = "../pathfinder/tests/fixtures/path-scurry-1.6.1.tgz" },
  { name = "lru-cache", path = "../pathfinder/tests/fixtures/lru-cache-7.14.1.tgz" },
  { name = "minipass", path = "../pathfinder/tests/fixtures/minipass-4.0.2.tgz" },
]
vuln = [
  { package = "lru-cache", module = "index.js", row = 1017, column = 24 }
]
```

In each of those objects: 
- `package` maps a package name to its tarball path
- `vuln` states that there is a vulnerable node
  in the specified package, in the file `module_name` at position `(row, column)`. Note that
  the position is 0-indexed so what would look like `(10, 8)` in a text editor should be
  specified as `(9, 7)`.

### Running

```
cargo run --release --bin pathfinder-cli -- sample.toml
```

All the specifications in `sample.toml` will be analyzed for reachability.
