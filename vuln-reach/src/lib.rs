use std::io;
use std::ops::{Deref, DerefMut};

use lazy_static::lazy_static;
use thiserror::Error;
use tree_sitter::{Language, LanguageError, Node, Parser, Query, QueryError, Tree as TsTree};

pub mod javascript;
pub mod util;

pub use tree_sitter;

extern "C" {
    fn tree_sitter_javascript() -> Language;
}

lazy_static! {
    pub static ref JS: Language = unsafe { tree_sitter_javascript() };
}

pub fn js_parser() -> Parser {
    let mut p = Parser::new();
    p.set_language(*JS).unwrap();
    p
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("language error")]
    LanguageError(#[from] LanguageError),
    #[error("query error")]
    QueryError(#[from] QueryError),
    #[error("i/o error")]
    IoError(#[from] io::Error),
    #[error("generic")]
    Generic(String),
}

impl From<String> for Error {
    fn from(value: String) -> Self {
        Error::Generic(value)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
pub struct Tree {
    buf: String,
    lang: Language,
    tree: TsTree,
}

impl Tree {
    pub fn new(buf: String) -> Result<Self> {
        let mut parser = js_parser();
        parser.set_language(*JS)?;

        Self::with_parser(&mut parser, buf)
    }

    pub fn with_parser(parser: &mut Parser, buf: String) -> Result<Self> {
        let lang = parser
            .language()
            .ok_or_else(|| Error::Generic("Language for parser not specified".to_string()))?;
        let tree = parser
            .parse(&buf, None)
            .ok_or_else(|| Error::Generic("Could not parse source".to_string()))?;

        Ok(Tree { buf, lang, tree })
    }

    pub fn buf(&self) -> &str {
        &self.buf
    }

    pub fn query(&self, text: &str) -> Result<Query> {
        Ok(Query::new(self.lang, text)?)
    }

    pub fn repr_of(&self, node: Node) -> &str {
        &self.buf[node.start_byte()..node.end_byte()]
    }
}

impl Deref for Tree {
    type Target = TsTree;

    fn deref(&self) -> &Self::Target {
        &self.tree
    }
}

impl DerefMut for Tree {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.tree
    }
}
