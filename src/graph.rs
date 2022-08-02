#![allow(dead_code)]

use crate::wdigraph::{IntoIter, Iter, WeightedEdges, WeightedNeighbors};
use crate::wgraph::UniqueWeightedEdges;
use crate::WeightedDiGraph;
use std::collections::HashSet;
use std::hash::Hash;

#[allow(unused_imports)]
use crate::{DiGraph, WeightedGraph};

/// A graph implementation.
///
/// To simplify the implementation, nodes are `clone`d when they are inserted.
///
/// This is a thin wrapper around [`WeightedDiGraph`]. This crate also defines
/// [`DiGraph`] and [`WeightedGraph`].
///
/// # Example
/// ```
/// use rust_dsa::Graph;
///
/// // First, we create a new graph.
/// let mut graph = Graph::new();
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
/// assert!(graph.contains_edge(&'b', &'a'));
/// assert!(graph.contains_edge(&'c', &'a'));
/// assert!(graph.contains_edge(&'b', &'c'));
///
/// // Missing edge nodes are automatically inserted.
/// graph.insert_edge(&'a', &'z');
///
/// assert!(graph.contains_node(&'z'));
/// assert!(graph.contains_edge(&'a', &'z'));
/// assert!(graph.contains_edge(&'z', &'a'));
///
/// // Edges can be removed.
/// graph.remove_edge(&'a', &'z');
///
/// assert!(!graph.contains_edge(&'a', &'z'));
/// assert!(!graph.contains_edge(&'z', &'a'));
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
/// for (u, v) in graph.edges() {
///     // Prints "a -> b", "b -> a", "a -> c", "c -> a", "c -> b"
///     // and "b -> c" in an arbitrary order.
///     println!("{u} -> {v}");
/// }
///
/// // Or just the unique edges.
/// for (u, v) in graph.unique_edges() {
///     // Prints "a -> b" or "b -> a", "a -> c" or "c -> a"
///     // and "c -> b" or "b -> c" in an arbitrary order.
///     println!("{u} -> {v}");
/// }
///
/// // And iterate over all nodes
/// for node in graph {
///     // Prints "a", "b" and "c" in an arbitrary order.
///     println!("{node}");
/// }
/// ```
#[derive(Clone)]
pub struct Graph<N> {
    inner: WeightedDiGraph<N, ()>,
}

impl<N> Graph<N> {
    /// Creates an empty graph.
    pub fn new() -> Self {
        Graph {
            inner: WeightedDiGraph::new(),
        }
    }

    /// Inserts a node into the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
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
    /// The nodes `u` and `v` will be automatically inserted if they are not already
    /// in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
    /// graph.insert_edge(&true, &false);
    ///
    /// assert!(graph.contains_edge(&true, &false));
    /// assert!(graph.contains_node(&true));
    /// assert!(graph.contains_node(&false));
    /// ```
    pub fn insert_edge(&mut self, u: &N, v: &N)
    where
        N: Clone + Hash + Eq,
    {
        self.inner.insert_edge(u, v, ());
        self.inner.insert_edge(v, u, ());
    }

    /// Removes a node from the graph. Returns whether the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let foo = "foo".to_string();
    /// let bar = "bar".to_string();
    ///
    /// let mut graph = Graph::new();
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
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::from([(1, 2), (1, 3)]);
    ///
    /// assert!(graph.contains_edge(&1, &2));
    ///
    /// assert!(graph.remove_edge(&1, &2));
    ///
    /// assert!(!graph.contains_edge(&1, &2));
    ///
    /// assert!(!graph.remove_edge(&1, &2));
    /// ```
    pub fn remove_edge(&mut self, u: &N, v: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.remove_edge(u, v);
        self.inner.remove_edge(v, u).is_some()
    }

    /// Returns `true` if the graph contains `node`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
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

    /// Returns `true` if the graph contains an edge between `u` and `v`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::from([('a', 'b'), ('b', 'c'), ('b', 'd')]);
    ///
    /// assert!(graph.contains_edge(&'b', &'c'));
    /// assert!(!graph.contains_edge(&'c', &'d'));
    /// ```
    pub fn contains_edge(&self, u: &N, v: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.contains_edge(u, v)
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let graph: Graph<i32> = (0..42).collect();
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
    /// use rust_dsa::Graph;
    ///
    /// let mut graph: Graph<char> = "abc".chars().collect();
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
    /// use rust_dsa::Graph;
    ///
    /// let mut graph: Graph<char> = "abc".chars().collect();
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
    /// use rust_dsa::Graph;
    /// use std::collections::HashSet;
    ///
    /// let graph = Graph::from([
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
    /// Each edge appears twice: once in either direction.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
    /// graph.insert_edge(&1, &3);
    /// graph.insert_edge(&3, &2);
    ///
    /// for (u, v) in graph.edges() {
    ///     // Prints "1 -> 3", "3 -> 1", "3 -> 2" and
    ///     // "2 -> 3" in an arbitrary order.
    ///     println!("{u} -> {v}");
    /// }
    /// ```
    pub fn edges(&self) -> Edges<'_, N> {
        Edges {
            inner: self.inner.edges(),
        }
    }

    /// Returns an interator visiting each of the graph's unique edges in an
    /// arbitrary order.
    ///
    /// The direction of the edge is also arbitrary.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
    /// graph.insert_edge(&1, &3);
    /// graph.insert_edge(&3, &2);
    ///
    /// for (u, v) in graph.unique_edges() {
    ///     // Prints "1 -> 3" or "3 -> 1" and "3 -> 2" or "2 -> 3"
    ///     // in an arbitrary order.
    ///     println!("{u} -> {v}");
    /// }
    /// ```
    pub fn unique_edges(&self) -> UniqueEdges<'_, N>
    where
        N: Hash + Eq,
    {
        UniqueEdges {
            inner: UniqueWeightedEdges {
                inner: self.inner.edges(),
                seen: HashSet::new(),
            },
        }
    }
}

impl<N> Default for Graph<N> {
    fn default() -> Self {
        Graph::new()
    }
}

impl<N> PartialEq for Graph<N>
where
    N: Hash + Eq,
{
    /// Returns `true` if the two graphs are equal.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut a = Graph::new();
    /// a.insert_edge(&1, &2);
    /// a.insert_edge(&3, &2);
    /// a.insert_edge(&1, &2);
    /// a.remove_edge(&2, &1);
    ///
    /// let mut b: Graph<i32> = [1, 2, 3].into_iter().collect();
    /// b.insert_edge(&2, &3);
    ///
    /// assert!(a == b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<N: Eq + Hash> Eq for Graph<N> {}

impl<N, const M: usize> From<[(N, N); M]> for Graph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N); M]) -> Self {
        let mut graph = Graph::new();
        for (from, to) in edges {
            graph.insert_edge(&from, &to);
        }
        graph
    }
}

impl<N> FromIterator<N> for Graph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<T: IntoIterator<Item = N>>(iter: T) -> Self {
        Graph {
            inner: WeightedDiGraph::from_iter(iter),
        }
    }
}

impl<N> IntoIterator for Graph<N> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, N> IntoIterator for &'a Graph<N> {
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

pub struct UniqueEdges<'a, N: 'a> {
    inner: UniqueWeightedEdges<'a, N, ()>,
}

impl<'a, N> Iterator for UniqueEdges<'a, N>
where
    N: Hash + Eq,
{
    type Item = (&'a N, &'a N);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(u, v, _)| (u, v))
    }
}
