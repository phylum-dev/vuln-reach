use std::path::{Component, Path, PathBuf};

/// Normalize a path, removing things like `.` and `..`.
///
/// CAUTION: This does not resolve symlinks (unlike
/// [`std::fs::canonicalize`]). This may cause incorrect or surprising
/// behavior at times. This should be used carefully. Unfortunately,
/// [`std::fs::canonicalize`] can be hard to use correctly, since it can often
/// fail, or on Windows returns annoying device paths. This is a problem Cargo
/// needs to improve on.
///
/// Taken from https://github.com/rust-lang/cargo/blob/efd37336e94e2f98260ad28d89e509e02fe4a556/crates/cargo-util/src/paths.rs
pub fn normalize_path(path: &Path) -> PathBuf {
    let mut components = path.components().peekable();
    let mut ret = if let Some(c @ Component::Prefix(..)) = components.peek().cloned() {
        components.next();
        PathBuf::from(c.as_os_str())
    } else {
        PathBuf::new()
    };

    for component in components {
        match component {
            Component::Prefix(..) => unreachable!(),
            Component::RootDir => {
                ret.push(component.as_os_str());
            },
            Component::CurDir => {},
            Component::ParentDir => {
                ret.pop();
            },
            Component::Normal(c) => {
                ret.push(c);
            },
        }
    }
    ret
}

#[test]
fn test_normalize_path() {
    // Check that traversal is prevented.
    assert_eq!(normalize_path(Path::new("./foo/bar")), PathBuf::from("foo/bar"));
    assert_eq!(normalize_path(Path::new("../foo/bar")), PathBuf::from("foo/bar"));
    assert_eq!(normalize_path(Path::new("../foo/../bar")), PathBuf::from("bar"));
}
