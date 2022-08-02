#![allow(dead_code)]

use crate::wdigraph::{IntoIter, Iter, WeightedDiGraph, WeightedEdges, WeightedNeighbors};
use std::{collections::HashSet, hash::Hash};

#[allow(unused_imports)]
use crate::{DiGraph, Graph};

/// A weighted graph implementation.
///
/// To simplify the implementation, nodes and edges `clone`d when they are inserted.
///
/// This is a thin wrapper around [`WeightedDiGraph`]. This crate also defines
/// [`Graph`] and [`DiGraph`].
///
/// # Example
/// ```
/// use rust_dsa::WeightedGraph;
///
/// // First, we create a new graph.
/// let mut graph = WeightedGraph::new();
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
/// graph.insert_edge(&'a', &'b', 5);
/// graph.insert_edge(&'a', &'c', 1);
/// graph.insert_edge(&'c', &'b', 4);
///
/// assert_eq!(graph.get_edge(&'a', &'b'), Some(&5));
/// assert_eq!(graph.get_edge(&'a', &'c'), Some(&1));
/// assert_eq!(graph.get_edge(&'c', &'b'), Some(&4));
///
/// // Missing edge nodes are automatically inserted.
/// graph.insert_edge(&'a', &'z', -1);
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
/// for (neighbor, weight) in graph.neighbors_of(&'a') {
///     // Prints "b (5)" and "c (1)" in an arbitrary order.
///     println!("{neighbor} ({weight})");
/// }
///
/// // We can also iterate over all edges in the graph.
/// for (from, to, weight) in graph.edges() {
///     // Prints "a -> b (5)", "b -> a (5)", "a -> c (1)", "c -> a (1)",
///     // "c -> b (4)" and "b -> c (4)" in an arbitrary order.
///     println!("{from} -> {to} ({weight})");
/// }
///
/// // Or just the unique edges.
/// for (from, to, weight) in graph.unique_edges() {
///     // Prints "a -> b (5)" or "b -> a (5)", "a -> c (1)" or "c -> a (1)"
///     // and "c -> b (4)" or "b -> c (4)" in an arbitrary order.
///     println!("{from} -> {to} ({weight})");
/// }
///
/// // And iterate over all nodes
/// for node in graph {
///     // Prints "a", "b" and "c" in an arbitrary order.
///     println!("{node}");
/// }
/// ```
#[derive(Clone)]
pub struct WeightedGraph<N, E> {
    inner: WeightedDiGraph<N, E>,
}

impl<N, E> WeightedGraph<N, E> {
    /// Creates an empty graph.
    pub fn new() -> Self {
        WeightedGraph {
            inner: WeightedDiGraph::new(),
        }
    }

    /// Inserts a node into the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph: WeightedGraph<i32, bool> = WeightedGraph::new();
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
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph = WeightedGraph::new();
    /// graph.insert_edge(&true, &false, 'a');
    ///
    /// assert!(graph.contains_edge(&true, &false));
    /// assert!(graph.contains_node(&true));
    /// assert!(graph.contains_node(&false));
    /// ```
    pub fn insert_edge(&mut self, u: &N, v: &N, weight: E)
    where
        N: Clone + Hash + Eq,
        E: Clone,
    {
        self.inner.insert_edge(u, v, weight.clone());
        self.inner.insert_edge(v, u, weight);
    }

    /// Removes a node from the graph. Returns whether the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let foo = "foo".to_string();
    /// let bar = "bar".to_string();
    ///
    /// let mut graph: WeightedGraph<String, i32> = WeightedGraph::new();
    /// graph.insert_node(foo.clone());
    /// graph.insert_node(bar.clone());
    ///
    /// assert!(graph.contains_node(&foo));
    ///
    /// graph.remove_node(&foo);
    ///
    /// assert!(!graph.contains_node(&foo));
    /// ```
    pub fn remove_node(&mut self, node: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.inner.remove_node(node)
    }

    /// Removes an edge from the graph. Returns the weight if the edge was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph = WeightedGraph::from([(1, 2, 'a'), (1, 3, 'b')]);
    ///
    /// assert!(graph.contains_edge(&1, &2));
    ///
    /// assert_eq!(graph.remove_edge(&1, &2), Some('a'));
    ///
    /// assert!(!graph.contains_edge(&1, &2));
    ///
    /// assert_eq!(graph.remove_edge(&1, &2), None);
    /// ```
    pub fn remove_edge(&mut self, u: &N, v: &N) -> Option<E>
    where
        N: Hash + Eq,
    {
        self.inner.remove_edge(u, v);
        self.inner.remove_edge(v, u)
    }

    /// Returns `true` if the graph contains `node`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph: WeightedGraph<i32, f64> = WeightedGraph::new();
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
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph = WeightedGraph::from([
    ///     ('a', 'b', true),
    ///     ('b', 'c', true),
    ///     ('b', 'd', true),
    /// ]);
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

    /// Returns a reference to the edge's weight if the graph contains an edge between `u` and `v`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph = WeightedGraph::from([
    ///     ('a', 'b', 1),
    ///     ('b', 'c', 2),
    ///     ('b', 'd', 3),
    /// ]);
    ///
    /// assert_eq!(graph.get_edge(&'c', &'b'), Some(&2));
    /// assert_eq!(graph.get_edge(&'c', &'d'), None);
    /// ```
    pub fn get_edge(&self, u: &N, v: &N) -> Option<&E>
    where
        N: Hash + Eq,
    {
        self.inner.get_edge(u, v)
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let graph: WeightedGraph<i32, u8> = (0..42).collect();
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
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph: WeightedGraph<char, i32> = "abc".chars().collect();
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
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph: WeightedGraph<char, i32> = "abc".chars().collect();
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
    /// use rust_dsa::WeightedGraph;
    /// use std::collections::HashSet;
    ///
    /// let graph = WeightedGraph::from([
    ///     (1, 2, 'a'),
    ///     (1, 3, 'b'),
    ///     (1, 4, 'c'),
    ///     (4, 3, 'd'),
    ///     (3, 2, 'z'),
    /// ]);
    ///
    /// let neighbors: HashSet<(&i32, &char)> = graph.neighbors_of(&1).collect();
    ///
    /// assert_eq!(
    ///     HashSet::from([(&2, &'a'), (&3, &'b'), (&4, &'c')]),
    ///     neighbors,
    /// );
    /// ```
    pub fn neighbors_of(&self, node: &N) -> WeightedNeighbors<'_, N, E>
    where
        N: Hash + Eq,
    {
        self.inner.neighbors_of(node)
    }

    /// Returns an iterator visiting the graph's edges in an arbitrary order.
    ///
    /// Each edge appears twice: once in either direction.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph = WeightedGraph::new();
    /// graph.insert_edge(&1, &3, 'a');
    /// graph.insert_edge(&3, &2, 'b');
    ///
    /// for (from, to, weight) in graph.edges() {
    ///     // Prints "1 -> 3 (a)", "3 -> 1 (a)", "3 -> 2 (b)" and
    ///     // "2 -> 3 (b)" in an arbitrary order.
    ///     println!("{from} -> {to} ({weight})");
    /// }
    /// ```
    pub fn edges(&self) -> WeightedEdges<'_, N, E> {
        self.inner.edges()
    }

    /// Returns an interator visiting each of the graph's edges once in an
    /// arbitrary order.
    ///
    /// The direction of the edge is also arbitrary.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut graph = WeightedGraph::new();
    /// graph.insert_edge(&1, &3, 'a');
    /// graph.insert_edge(&3, &2, 'b');
    ///
    /// for (from, to, weight) in graph.edges() {
    ///     // Prints "1 -> 3 (a)" or "3 -> 1 (a)" and "3 -> 2 (b)" or "2 -> 3 (b)"
    ///     // in an arbitrary order.
    ///     println!("{from} -> {to} ({weight})");
    /// }
    /// ```
    pub fn unique_edges(&self) -> UniqueWeightedEdges<'_, N, E>
    where
        N: Hash + Eq,
    {
        UniqueWeightedEdges {
            inner: self.edges(),
            seen: HashSet::new(),
        }
    }
}

impl<N, E> Default for WeightedGraph<N, E> {
    fn default() -> Self {
        WeightedGraph::new()
    }
}

impl<N, E> PartialEq for WeightedGraph<N, E>
where
    N: Hash + Eq,
    E: PartialEq,
{
    /// Returns `true` if the two graphs are equal.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedGraph;
    ///
    /// let mut a = WeightedGraph::new();
    /// a.insert_edge(&1, &2, 'a');
    /// a.insert_edge(&3, &2, 'b');
    /// a.remove_edge(&2, &1);
    ///
    /// let mut b: WeightedGraph<i32, char> = [1, 2, 3].into_iter().collect();
    /// b.insert_edge(&3, &2, 'b');
    ///
    /// assert!(a == b);
    ///
    /// let mut c = WeightedGraph::new();
    /// c.insert_node(1);
    /// c.insert_edge(&3, &2, 'b');
    /// c.insert_node(4);
    ///
    /// assert!(a != c);
    ///
    /// c.remove_node(&4);
    ///
    /// assert!(a == c);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<N: Eq + Hash, E: Eq> Eq for WeightedGraph<N, E> {}

impl<N, E> From<Vec<(N, N, E)>> for WeightedGraph<N, E>
where
    N: Clone + Hash + Eq,
    E: Clone,
{
    /// Creates a graph from an edge list.
    fn from(edges: Vec<(N, N, E)>) -> Self {
        let mut graph = WeightedGraph::new();
        for (from, to, weight) in edges {
            graph.insert_edge(&from, &to, weight);
        }
        graph
    }
}

impl<N, E, const M: usize> From<[(N, N, E); M]> for WeightedGraph<N, E>
where
    N: Clone + Hash + Eq,
    E: Clone,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N, E); M]) -> Self {
        let mut graph = WeightedGraph::new();
        for (from, to, weight) in edges {
            graph.insert_edge(&from, &to, weight);
        }
        graph
    }
}

impl<N, E> FromIterator<N> for WeightedGraph<N, E>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<T: IntoIterator<Item = N>>(iter: T) -> Self {
        WeightedGraph {
            inner: WeightedDiGraph::from_iter(iter),
        }
    }
}

impl<N, E> IntoIterator for WeightedGraph<N, E> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, N, E> IntoIterator for &'a WeightedGraph<N, E> {
    type IntoIter = Iter<'a, N>;
    type Item = &'a N;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            nodes: self.inner.node_to_id.keys().collect(),
        }
    }
}

pub struct UniqueWeightedEdges<'a, N: 'a, E: 'a> {
    pub(crate) inner: WeightedEdges<'a, N, E>,
    pub(crate) seen: HashSet<(&'a N, &'a N)>,
}

impl<'a, N, E> Iterator for UniqueWeightedEdges<'a, N, E>
where
    N: Hash + Eq,
{
    type Item = (&'a N, &'a N, &'a E);
    fn next(&mut self) -> Option<Self::Item> {
        for (from, to, weight) in self.inner.by_ref() {
            if !self.seen.contains(&(to, from)) {
                self.seen.insert((from, to));
                return Some((from, to, weight));
            }
        }
        None
    }
}
