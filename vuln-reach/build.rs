use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn out_dir() -> PathBuf {
    PathBuf::from(env::var("OUT_DIR").unwrap())
}

struct TreeSitterLang {
    lang: &'static str,
    path: PathBuf,
    repo: String,
    tag: Option<&'static str>,
}

impl TreeSitterLang {
    fn new(lang: &'static str, tag: Option<&'static str>) -> Self {
        let path = out_dir().join(format!("tree-sitter-{lang}"));
        let repo = format!("https://github.com/tree-sitter/tree-sitter-{lang}");

        TreeSitterLang { lang, path, repo, tag }
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn repo(&self) -> &str {
        &self.repo
    }

    fn clone_repository(&self) {
        if self.path().exists() {
            return;
        }

        let mut cmd = Command::new("git");

        cmd.current_dir(&out_dir()).arg("clone").arg(self.repo()).arg(self.path());

        if let Some(tag) = self.tag {
            cmd.arg("-b").arg(tag);
        }

        let status = cmd.status().expect("Couldn't run git command");

        if !status.success() {
            panic!("Couldn't clone git repo for {}", self.lang);
        }
    }
}

fn main() {
    let js = TreeSitterLang::new("javascript", None);
    js.clone_repository();

    cc::Build::new()
        .warnings(false)
        .include(js.path().join("src"))
        .file(js.path().join("src/parser.c"))
        .file(js.path().join("src/scanner.c"))
        .compile("tree-sitter-obj");
}
