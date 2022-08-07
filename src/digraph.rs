#![allow(dead_code)]

use crate::wdigraph::{IntoIter, Iter, WeightedEdges, WeightedNeighbors};
use crate::WeightedDiGraph;
use std::hash::Hash;

#[allow(unused_imports)]
use crate::{Graph, WeightedGraph};

/// A directed graph implementation.
///
/// To simplify the implementation, nodes are `clone`d when they are inserted.
///
/// This is a thin wrapper around [`WeightedDiGraph`]. This crate also defines
/// [`Graph`] and [`WeightedGraph`].
///
/// # Example
/// ```
/// use rust_dsa::DiGraph;
///
/// // First, we create a new graph.
/// let mut graph = DiGraph::new();
///
/// // Then we can add nodes.
/// graph.insert_node('a');
/// graph.insert_node('b');
/// graph.insert_node('c');
///
/// assert_eq!(graph.len(), 3);
/// assert!(graph.contains_node(&'a'));
/// assert!(graph.contains_node(&'b'));
/// assert!(graph.contains_node(&'c'));
///
/// // And edges between those nodes.
/// graph.insert_edge(&'a', &'b');
/// graph.insert_edge(&'a', &'c');
/// graph.insert_edge(&'c', &'b');
///
/// assert!(graph.contains_edge(&'a', &'b'));
/// assert!(graph.contains_edge(&'a', &'c'));
/// assert!(graph.contains_edge(&'c', &'b'));
///
/// // Missing edge nodes are automatically inserted.
/// graph.insert_edge(&'a', &'z');
///
/// assert!(graph.contains_node(&'z'));
/// assert!(graph.contains_edge(&'a', &'z'));
///
/// // Edges can be removed.
/// graph.remove_edge(&'a', &'z');
///
/// assert!(!graph.contains_edge(&'a', &'z'));
///
/// // Nodes too.
/// graph.remove_node(&'z');
///
/// assert!(!graph.contains_node(&'z'));
///
/// // We can iterate over a node's neighbors.
/// for neighbor in graph.neighbors_of(&'a') {
///     // Prints "b" and "c" in an arbitrary order.
///     println!("{neighbor}");
/// }
///
/// // We can also iterate over all edges in the graph.
/// for (from, to) in graph.edges() {
///     // Prints "a -> b", "a -> c" and "c -> b" in an arbitrary order.
///     println!("{from} -> {to}");
/// }
///
/// // And iterate over all nodes
/// for node in graph {
///     // Prints "a", "b" and "c" in an arbitrary order.
///     println!("{node}");
/// }
/// ```
#[derive(Clone)]
pub struct DiGraph<N> {
    inner: WeightedDiGraph<N, ()>,
}

impl<N> DiGraph<N> {
    /// Creates an empty graph.
    pub fn new() -> DiGraph<N> {
        DiGraph {
            inner: WeightedDiGraph::new(),
        }
    }

    /// Inserts a node into the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::new();
    /// graph.insert_node(1);
    ///
    /// assert!(graph.contains_node(&1));
    /// ```
    pub fn insert_node(&mut self, node: N)
    where
        N: Clone + Hash + Eq,
    {
        self.inner.insert_node(node);
    }

    /// Inserts an edge into the graph.
    ///
    /// The nodes `from` and `to` will be automatically inserted if they are not already
    /// in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::new();
    /// graph.insert_edge(&true, &false);
    ///
    /// assert!(graph.contains_edge(&true, &false));
    /// assert!(graph.contains_node(&true));
    /// assert!(graph.contains_node(&false));
    /// ```
    pub fn insert_edge(&mut self, from: &N, to: &N)
    where
        N: Clone + Hash + Eq,
    {
        self.inner.insert_edge(from, to, ());
    }

    /// Removes a node from the graph. Returns whether the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let foo = "foo".to_string();
    /// let bar = "bar".to_string();
    ///
    /// let mut graph = DiGraph::new();
    /// graph.insert_node(foo.clone());
    /// graph.insert_node(bar.clone());
    ///
    /// assert!(graph.contains_node(&foo));
    ///
    /// assert!(graph.remove_node(&foo));
    ///
    /// assert!(!graph.contains_node(&foo));
    ///
    /// assert!(!graph.remove_node(&foo));
    /// ```
    pub fn remove_node(&mut self, node: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.remove_node(node)
    }

    /// Removes an edge from the graph. Returns `true` if the edge was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::from([(1, 2), (1, 3)]);
    ///
    /// assert!(graph.contains_edge(&1, &2));
    ///
    /// assert!(graph.remove_edge(&1, &2));
    ///
    /// assert!(!graph.contains_edge(&1, &2));
    ///
    /// assert!(!graph.remove_edge(&1, &2));
    /// ```
    pub fn remove_edge(&mut self, from: &N, to: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.remove_edge(from, to).is_some()
    }

    /// Returns `true` if the graph contains `node`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::new();
    ///
    /// graph.insert_node(1);
    ///
    /// assert!(graph.contains_node(&1));
    /// assert!(!graph.contains_node(&2));
    /// ```
    pub fn contains_node(&self, node: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.contains_node(node)
    }

    /// Returns `true` if the graph contains an edge between `from` and `to`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::from([('a', 'b'), ('b', 'c'), ('b', 'd')]);
    ///
    /// assert!(graph.contains_edge(&'b', &'c'));
    /// assert!(!graph.contains_edge(&'c', &'d'));
    /// ```
    pub fn contains_edge(&self, from: &N, to: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.contains_edge(from, to)
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let graph: DiGraph<i32> = (0..42).collect();
    ///
    /// assert_eq!(graph.len(), 42);
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the graph is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph: DiGraph<char> = "abc".chars().collect();
    ///
    /// assert!(!graph.is_empty());
    ///
    /// graph.clear();
    ///
    /// assert!(graph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Clears the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph: DiGraph<char> = "abc".chars().collect();
    ///
    /// assert!(!graph.is_empty());
    ///
    /// graph.clear();
    ///
    /// assert!(graph.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Returns an iterator that visits all of `node`'s neighbors.
    ///
    /// # Panics
    /// Panics if `node` is not present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    /// use std::collections::HashSet;
    ///
    /// let graph = DiGraph::from([
    ///     (1, 2),
    ///     (1, 3),
    ///     (1, 4),
    ///     (4, 3),
    ///     (3, 2),
    /// ]);
    ///
    /// let neighbors: HashSet<&i32> = graph.neighbors_of(&1).collect();
    ///
    /// assert_eq!(
    ///     HashSet::from([&2, &3, &4]),
    ///     neighbors,
    /// );
    /// ```
    pub fn neighbors_of(&self, node: &N) -> Neighbors<'_, N>
    where
        N: Hash + Eq,
    {
        Neighbors {
            inner: self.inner.neighbors_of(node),
        }
    }

    /// Returns an iterator visiting the graph's edges in an arbitrary order.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::new();
    /// graph.insert_edge(&1, &3);
    /// graph.insert_edge(&3, &2);
    ///
    /// for (from, to) in graph.edges() {
    ///     // Prints "1 -> 3" and "3 -> 2" in an arbitrary order
    ///     println!("{from} -> {to}");
    /// }
    /// ```
    pub fn edges(&self) -> Edges<'_, N> {
        Edges {
            inner: self.inner.edges(),
        }
    }
}

impl<N> Default for DiGraph<N> {
    fn default() -> DiGraph<N> {
        DiGraph::new()
    }
}

impl<N> PartialEq for DiGraph<N>
where
    N: Hash + Eq,
{
    /// Returns `true` if the two graphs are equal.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut a = DiGraph::from([(1, 2), (2, 3), (2, 4)]);
    /// let mut b: DiGraph<i32> = (1..=4).collect();
    ///
    /// assert!(a != b);
    ///
    /// b.insert_edge(&1, &2);
    /// b.insert_edge(&2, &3);
    /// b.insert_edge(&4, &2);
    ///
    /// assert!(a != b);
    ///
    /// b.insert_edge(&2, &4);
    ///
    /// assert!(a != b);
    ///
    /// b.remove_edge(&4, &2);
    ///
    /// assert!(a == b);
    ///
    /// a.remove_node(&4);
    /// b.remove_node(&4);
    ///
    /// assert!(a == b);
    /// ```
    fn eq(&self, other: &DiGraph<N>) -> bool {
        self.inner == other.inner
    }
}

impl<N: Eq + Hash> Eq for DiGraph<N> {}

impl<N, const M: usize> From<[(N, N); M]> for DiGraph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N); M]) -> DiGraph<N> {
        let mut graph = DiGraph::new();
        for (from, to) in edges {
            graph.insert_edge(&from, &to);
        }
        graph
    }
}

impl<N> FromIterator<N> for DiGraph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<I: IntoIterator<Item = N>>(iter: I) -> DiGraph<N> {
        DiGraph {
            inner: WeightedDiGraph::from_iter(iter),
        }
    }
}

impl<N> IntoIterator for DiGraph<N> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, N> IntoIterator for &'a DiGraph<N> {
    type IntoIter = Iter<'a, N>;
    type Item = &'a N;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            nodes: self.inner.node_to_id.keys().collect(),
        }
    }
}

pub struct Neighbors<'a, N: 'a> {
    inner: WeightedNeighbors<'a, N, ()>,
}

impl<'a, N> Iterator for Neighbors<'a, N> {
    type Item = &'a N;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(neighbor, _)| neighbor)
    }
}

pub struct Edges<'a, N: 'a> {
    inner: WeightedEdges<'a, N, ()>,
}

impl<'a, N> Iterator for Edges<'a, N> {
    type Item = (&'a N, &'a N);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(from, to, _)| (from, to))
    }
}
