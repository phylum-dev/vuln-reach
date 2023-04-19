use tree_sitter::Node;

// Iterates through nodes with a provided "move to next node" function.
pub(crate) struct NodeIterator<'a, F: FnMut(Node<'a>) -> Option<Node<'a>>>(Node<'a>, F);

impl<'a, F> NodeIterator<'a, F>
where
    F: FnMut(Node<'a>) -> Option<Node<'a>>,
{
    pub(crate) fn new(n: Node<'a>, f: F) -> Self {
        Self(n, f)
    }
}

impl<'a, F> Iterator for NodeIterator<'a, F>
where
    F: FnMut(Node<'a>) -> Option<Node<'a>>,
{
    type Item = Node<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0 = self.1(self.0)?;
        Some(self.0)
    }
}

pub(crate) fn parent_iterator(n: Node<'_>) -> impl Iterator<Item = Node<'_>> {
    NodeIterator::new(n, |node| node.parent())
}
