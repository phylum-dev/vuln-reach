use std::collections::HashMap;
use std::io;
use std::ops::{Deref, DerefMut};

use lazy_static::lazy_static;
use thiserror::Error;
use tree_sitter::{Language, LanguageError, Node, Parser, Query, QueryError, Tree as TsTree};

pub mod javascript;
#[cfg(test)]
mod test_util;
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
    #[error("tree contains parse errors")]
    ParseError,
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

/// Cache for fast duplication of previously used cursors.
pub struct TreeCursorCache<'a> {
    cursors: HashMap<Node<'a>, Cursor<'a>>,
    tree: &'a Tree,
}

impl<'a> TreeCursorCache<'a> {
    fn new(tree: &'a Tree) -> Self {
        Self { tree, cursors: HashMap::new() }
    }

    fn cursor(&mut self, node: Node<'a>) -> Result<Cursor<'a>> {
        match self.cursors.get(&node) {
            Some(cursor) => Ok(cursor.clone()),
            None => {
                let cursor = Cursor::new(self.tree, node)?;
                self.cursors.insert(node, cursor.clone());
                Ok(cursor)
            },
        }
    }
}

/// Cursor for upwards traversal of a [`treesitter::Tree`].
#[derive(Clone)]
pub struct Cursor<'a> {
    nodes: Vec<Node<'a>>,
}

impl<'a> Cursor<'a> {
    /// Construct a new cursor and move it to the `node`.
    pub fn new(tree: &'a Tree, node: Node<'a>) -> Result<Self> {
        let mut nodes = Vec::new();

        // Start cursor at the root, so we know all parents.
        let mut cursor = tree.root_node().walk();
        nodes.push(cursor.node());

        // Iterate through children until we've found the desired node.
        let node_end = node.end_byte();
        while node != nodes[nodes.len() - 1] {
            let child_offset = cursor.goto_first_child_for_byte(node_end);

            // Child does not exist in the tree.
            if child_offset.is_none() {
                return Err(Error::InvalidNode);
            }

            nodes.push(cursor.node());
        }

        Ok(Self { nodes })
    }

    /// Move the cursor to the parent node.
    pub fn goto_parent(&mut self) -> Option<Node<'a>> {
        (self.nodes.len() > 1).then(|| {
            self.nodes.pop();
            self.node()
        })
    }

    /// Get the cursor's current node.
    pub fn node(&self) -> Node<'a> {
        self.nodes[self.nodes.len() - 1]
    }

    /// Get the node's parent.
    pub fn parent(&mut self) -> Option<Node<'a>> {
        (self.nodes.len() > 1).then(|| self.nodes[self.nodes.len() - 2])
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
