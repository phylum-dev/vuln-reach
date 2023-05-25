use std::io;
use std::ops::{Deref, DerefMut};

use lazy_static::lazy_static;
use thiserror::Error;
use tree_sitter::{
    Language, LanguageError, Node, Parser, Query, QueryError, Tree as TsTree, TreeCursor,
};

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
    #[error("node does not exist in tree")]
    InvalidNode,
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

/// TODO: Doc
#[derive(Clone)]
pub struct Cursor<'a> {
    cursor: TreeCursor<'a>,
    child: Option<Node<'a>>,
}

impl<'a> Cursor<'a> {
    /// Construct a new cursor and move it to the `node`.
    pub fn new(tree: &'a Tree, node: Node<'a>) -> Result<Self> {
        // Start cursor at the root, so we know all parents.
        let mut cursor = tree.root_node().walk();

        // Iterate through children until we've found the desired node.
        while node != cursor.node() {
            let node_end = node.byte_range().end;
            let child_offset = cursor.goto_first_child_for_byte(node_end);

            // Child does not exist in the tree.
            if child_offset.is_none() {
                return Err(Error::InvalidNode);
            }
        }

        Ok(Self { cursor, child: None })
    }

    /// Move the cursor to the parent node.
    pub fn goto_parent(&mut self) -> Option<Node<'a>> {
        if self.child.take().is_none() && !self.cursor.goto_parent() {
            return None;
        }

        Some(self.cursor.node())
    }

    /// Peek at the node's parent.
    pub fn peek_parent(&mut self) -> Option<Node<'a>> {
        // If we've peeked before, just return the cursor's head.
        let node = self.cursor.node();
        if self.child.is_some() {
            return Some(node);
        }

        // Move cursor to the parent and store our child.
        let parent = self.goto_parent()?;
        self.child = Some(node);

        Some(parent)
    }

    /// Get the cursor's current node.
    pub fn node(&self) -> Node<'a> {
        self.child.unwrap_or_else(|| self.cursor.node())
    }

    /// Get an iterator from the cursor's current node to the tree root.
    pub fn parents(self) -> ParentIterator<'a> {
        ParentIterator { cursor: self }
    }
}

pub struct ParentIterator<'a> {
    cursor: Cursor<'a>,
}

impl<'a> Iterator for ParentIterator<'a> {
    type Item = Node<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor.goto_parent()
    }
}
