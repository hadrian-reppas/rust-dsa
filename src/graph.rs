use crate::digraph::{DiGraph, IntoIter, Iter};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A weighted graph.
///
/// See also: [`DiGraph`].
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
/// graph.insert_edge(&'a', &'b', 5);
/// graph.insert_edge(&'a', &'c', 1);
/// graph.insert_edge(&'c', &'b', 4);
///
/// assert_eq!(graph.get_edge(&'a', &'b'), Some(&5));
/// assert_eq!(graph.get_edge(&'a', &'c'), Some(&1));
/// assert_eq!(graph.get_edge(&'c', &'b'), Some(&4));
///
/// // Edges and nodes can be inserted at the same time.
/// graph.insert_edge_by_value('a', 'z', -1);
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
pub struct Graph<N, E> {
    inner: DiGraph<N, usize>,
    weights: HashMap<usize, E>,
    counter: usize,
}

impl<N, E> Graph<N, E> {
    /// Creates an empty graph.
    pub fn new() -> Graph<N, E> {
        Graph {
            inner: DiGraph::new(),
            weights: HashMap::new(),
            counter: 0,
        }
    }

    /// Inserts a node into the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph: Graph<_, bool> = Graph::new();
    /// graph.insert_node(1);
    ///
    /// assert!(graph.contains_node(&1));
    /// ```
    pub fn insert_node(&mut self, node: N)
    where
        N: Hash + Eq,
    {
        self.inner.insert_node(node);
    }

    /// Inserts an edge into the graph.
    ///
    /// Returns the old weight if the graph already contained the edge.
    ///
    /// # Panics
    /// Panics if `u` or `v` is not in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph: Graph<_, _> = [true, false].into_iter().collect();
    /// graph.insert_edge(&true, &false, 'a');
    ///
    /// assert!(graph.contains_edge(&true, &false));
    /// assert!(graph.contains_edge(&false, &true));
    /// ```
    pub fn insert_edge(&mut self, u: &N, v: &N, weight: E) -> Option<E>
    where
        N: Hash + Eq,
    {
        if !self.contains_node(u) {
            panic!("node `u` is not in the graph");
        }
        if !self.contains_node(v) {
            panic!("node `v` is not in the graph");
        }

        let old_weight_id = self.inner.insert_edge(u, v, self.counter);
        self.inner.insert_edge(v, u, self.counter);
        self.weights.insert(self.counter, weight);
        self.counter += 1;
        old_weight_id.and_then(|id| self.weights.remove(&id))
    }

    /// Inserts an edge into the graph. The nodes are inserted if they are not already
    /// present in the graph.
    ///
    /// Returns the old weight if the graph already contained the edge.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
    ///
    /// graph.insert_edge_by_value('a', 'b', 1);
    ///
    /// assert_eq!(graph.get_edge(&'a', &'b'), Some(&1));
    /// assert!(graph.contains_node(&'a'));
    /// assert!(graph.contains_node(&'b'));
    /// ```
    pub fn insert_edge_by_value(&mut self, u: N, v: N, weight: E) -> Option<E>
    where
        N: Hash + Eq,
    {
        let u_id = self.inner.insert_node_internal(u);
        let v_id = self.inner.insert_node_internal(v);
        let old_weight_id = self.inner.insert_edge_by_id(u_id, v_id, self.counter);
        self.inner.insert_edge_by_id(v_id, u_id, self.counter);
        self.weights.insert(self.counter, weight);
        self.counter += 1;
        old_weight_id.and_then(|id| self.weights.remove(&id))
    }

    /// Removes a node from the graph. Returns `true` if the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let foo = "foo".to_string();
    /// let bar = "bar".to_string();
    ///
    /// let mut graph: Graph<_, i32> = Graph::new();
    /// graph.insert_node(foo.clone());
    /// graph.insert_node(bar);
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
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::from([(1, 2, 'a'), (1, 3, 'b')]);
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
        self.inner
            .remove_edge(v, u)
            .and_then(|id| self.weights.remove(&id))
    }

    /// Returns `true` if the graph contains `node`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph: Graph<_, f64> = Graph::new();
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
    /// let graph = Graph::from([
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
    /// use rust_dsa::Graph;
    ///
    /// let graph = Graph::from([
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
        self.inner
            .get_edge(u, v)
            .and_then(|id| self.weights.get(id))
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let graph: Graph<_, u8> = (0..42).collect();
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
    /// let mut graph: Graph<_, i32> = "abc".chars().collect();
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
    /// let mut graph: Graph<_, i32> = "abc".chars().collect();
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
    ///     (1, 2, 'a'),
    ///     (1, 3, 'b'),
    ///     (1, 4, 'c'),
    ///     (4, 3, 'd'),
    ///     (3, 2, 'z'),
    /// ]);
    ///
    /// let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();
    ///
    /// assert_eq!(
    ///     HashSet::from([(&2, &'a'), (&3, &'b'), (&4, &'c')]),
    ///     neighbors,
    /// );
    /// ```
    pub fn neighbors_of(&self, node: &N) -> Neighbors<'_, N, E>
    where
        N: Hash + Eq,
    {
        let mut neighbors = Vec::new();
        for (neighbor, weight_id) in self.inner.neighbors_of(node) {
            neighbors.push((neighbor, self.weights.get(weight_id).unwrap()));
        }
        Neighbors { neighbors }
    }

    /// Returns the number of neighbors `node` has.
    ///
    /// # Panics
    /// Panics if `node` is not present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let graph = Graph::from([
    ///     (1, 2, 'a'),
    ///     (1, 3, 'b'),
    ///     (1, 4, 'c'),
    ///     (4, 3, 'd'),
    ///     (3, 2, 'e'),
    /// ]);
    ///
    /// assert_eq!(graph.count_neighbors_of(&1), 3);
    /// ```
    pub fn count_neighbors_of(&self, node: &N) -> usize
    where
        N: Hash + Eq,
    {
        self.inner.count_neighbors_of(node)
    }

    /// Returns an interator visiting each of the graph's edges in an
    /// arbitrary order.
    ///
    /// The direction of the edge is also arbitrary.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::new();
    /// graph.insert_edge_by_value(1, 3, 'a');
    /// graph.insert_edge_by_value(3, 2, 'b');
    ///
    /// for (from, to, weight) in graph.edges() {
    ///     // Prints "1 -> 3 (a)" or "3 -> 1 (a)" and "3 -> 2 (b)" or "2 -> 3 (b)"
    ///     // in an arbitrary order.
    ///     println!("{from} -> {to} ({weight})");
    /// }
    /// ```
    pub fn edges(&self) -> Edges<'_, N, E>
    where
        N: Hash + Eq,
    {
        let mut edges = Vec::new();
        let mut seen = HashSet::new();
        for (from, to, weight_id) in self.inner.edges() {
            if !seen.contains(from) {
                edges.push((from, to, self.weights.get(weight_id).unwrap()));
                seen.insert(to);
            }
        }
        Edges { edges }
    }

    /// Returns the number of edges in the graph
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let mut graph = Graph::from([
    ///     (1, 2, ()),
    ///     (2, 3, ()),
    ///     (2, 1, ()),
    ///     (3, 4, ())
    /// ]);
    /// graph.remove_edge(&3, &4);
    ///
    /// assert_eq!(graph.count_edges(), 2);
    /// ```
    pub fn count_edges(&self) -> usize {
        self.weights.len()
    }
}

impl<N, E> Default for Graph<N, E> {
    fn default() -> Graph<N, E> {
        Graph::new()
    }
}

impl<N, E> PartialEq for Graph<N, E>
where
    N: Hash + Eq,
    E: PartialEq,
{
    /// Returns `true` if the two graphs are equal.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Graph;
    ///
    /// let graph: Graph<_, _> = [1, 2, 3].into_iter().collect();
    ///
    /// let mut a = graph.clone();
    /// a.insert_edge(&1, &2, 'a');
    /// a.insert_edge(&3, &2, 'b');
    /// a.remove_edge(&2, &1);
    ///
    /// let mut b = graph.clone();
    /// b.insert_edge(&3, &2, 'b');
    ///
    /// assert!(a == b);
    ///
    /// let mut c = graph.clone();
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
    fn eq(&self, other: &Graph<N, E>) -> bool {
        let self_nodes: HashSet<_> = self.inner.iter().collect();
        let other_nodes: HashSet<_> = other.inner.iter().collect();
        if self_nodes != other_nodes {
            return false;
        }
        if self.count_edges() != other.count_edges() {
            return false;
        }
        for (u, v, weight) in self.edges() {
            if other.get_edge(u, v) != Some(weight) {
                return false;
            }
        }
        true
    }
}

impl<N, E> Eq for Graph<N, E>
where
    N: Eq + Hash,
    E: Eq,
{
}

impl<N, E> Clone for Graph<N, E>
where
    N: Clone + Eq + Hash,
    E: Clone,
{
    fn clone(&self) -> Graph<N, E> {
        Graph {
            inner: self.inner.clone(),
            weights: self.weights.clone(),
            counter: self.counter,
        }
    }
}

impl<N, E, const M: usize> From<[(N, N, E); M]> for Graph<N, E>
where
    N: Clone + Hash + Eq,
    E: Clone,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N, E); M]) -> Graph<N, E> {
        let mut graph = Graph::new();
        for (from, to, weight) in edges {
            graph.insert_edge_by_value(from, to, weight);
        }
        graph
    }
}

impl<N, E> FromIterator<N> for Graph<N, E>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<I: IntoIterator<Item = N>>(iter: I) -> Graph<N, E> {
        Graph {
            inner: DiGraph::from_iter(iter),
            weights: HashMap::new(),
            counter: 0,
        }
    }
}

impl<N, E> IntoIterator for Graph<N, E> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, N, E> IntoIterator for &'a Graph<N, E> {
    type IntoIter = Iter<'a, N>;
    type Item = &'a N;
    fn into_iter(self) -> Self::IntoIter {
        (&self.inner).into_iter()
    }
}

pub struct Edges<'a, N: 'a, E: 'a> {
    edges: Vec<(&'a N, &'a N, &'a E)>,
}

impl<'a, N, E> Iterator for Edges<'a, N, E>
where
    N: Hash + Eq,
{
    type Item = (&'a N, &'a N, &'a E);
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.pop()
    }
}

pub struct Neighbors<'a, N: 'a, E: 'a> {
    neighbors: Vec<(&'a N, &'a E)>,
}

impl<'a, N, E> Iterator for Neighbors<'a, N, E> {
    type Item = (&'a N, &'a E);
    fn next(&mut self) -> Option<Self::Item> {
        self.neighbors.pop()
    }
}
