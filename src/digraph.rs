#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A struct representing a directed graph.
///
/// To simplify the implementation, nodes are `clone`d when they are inserted.
///
/// # Example
/// ```
/// use rust_dsa::DiGraph;
///
/// // First, we create a new graph.
/// let mut graph = DiGraph::new();
///
/// // Then we can add nodes.
/// graph.insert_node(4);
/// graph.insert_node(1);
/// graph.insert_node(3);
///
/// assert_eq!(graph.len(), 3);
/// assert!(graph.contains_node(&4));
/// assert!(graph.contains_node(&1));
/// assert!(graph.contains_node(&3));
///
/// // And edges between those nodes.
/// graph.insert_edge(&4, &1);
/// graph.insert_edge(&4, &3);
/// graph.insert_edge(&1, &3);
///
/// assert!(graph.contains_edge(&4, &1));
/// assert!(graph.contains_edge(&4, &3));
/// assert!(graph.contains_edge(&1, &3));
///
/// // Missing edge nodes are automatically inserted.
/// graph.insert_edge(&4, &10);
///
/// assert!(graph.contains_node(&10));
/// assert!(graph.contains_edge(&4, &10));
///
/// // Edges can be removed.
/// graph.remove_edge(&4, &10);
///
/// assert!(!graph.contains_edge(&4, &10));
///
/// // Nodes too.
/// graph.remove_node(&10);
///
/// assert!(!graph.contains_node(&10));
///
/// // We can iterate over a node's neighbors.
/// for neighbor in graph.neighbors_of(&4) {
///     // prints 1 and 3 in an arbitrary order
///     println!("{neighbor}");
/// }
///
/// // We can also iterate over all edges in the graph.
/// for (from, to) in graph.edges() {
///     // prints "4 -> 1", "4 -> 3" and "1 -> 3" in an arbitrary order
///     println!("{from} -> {to}");
/// }
///
/// // And iterate over all node
/// for node in graph {
///     // prints 1, 3 and 4 in an arbitrary order
///     println!("{node}");
/// }
/// ```
pub struct DiGraph<N> {
    // first, map each node to an id
    node_to_id: HashMap<N, usize>,
    id_to_node: HashMap<usize, N>,

    // then represent the graph with adjacency lists of ids
    neighbors: HashMap<usize, HashSet<usize>>,

    counter: usize,
}

impl<N> DiGraph<N> {
    /// Creates en empty graph.
    pub fn new() -> Self {
        DiGraph {
            neighbors: HashMap::new(),
            node_to_id: HashMap::new(),
            id_to_node: HashMap::new(),
            counter: 0,
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
        if !self.contains_node(&node) {
            self.node_to_id.insert(node.clone(), self.counter);
            self.id_to_node.insert(self.counter, node);
            self.neighbors.insert(self.counter, HashSet::new());
            self.counter += 1;
        }
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
    /// assert!(graph.contains_node(&true));
    /// ```
    pub fn insert_edge(&mut self, from: &N, to: &N)
    where
        N: Clone + Hash + Eq,
    {
        if !self.contains_node(from) {
            self.insert_node(from.clone());
        }
        if !self.contains_node(to) {
            self.insert_node(to.clone());
        }

        let from_id = self.node_to_id[from];
        let to_id = self.node_to_id[to];
        self.neighbors.get_mut(&from_id).unwrap().insert(to_id);
    }

    /// Removes a node from the graph. Returns whether the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let s = "node".to_string();
    ///
    /// let mut graph = DiGraph::new();
    /// graph.insert_node(s.clone());
    ///
    /// assert!(graph.contains_node(&s));
    ///
    /// graph.remove_node(&s);
    ///
    /// assert!(!graph.contains_node(&s));
    /// ```
    pub fn remove_node(&mut self, node: &N) -> bool
    where
        N: Hash + Eq,
    {
        // We don't actually update `self.neighbors`, we just invalidate some
        // of the ids contained in it. If there's an id in `self.neighbors` that
        // doesn't exist in `self.id_to_node`, it can be ignored.
        //
        // This means that `self.neighbors` never decreases in size. Maybe we can
        // write a function that removes inavlid ids from `self.neighbors` (sort
        // of like Vec::shrink_to_fit).
        if let Some(id) = self.node_to_id.get(node) {
            self.id_to_node.remove(id);
            self.node_to_id.remove(node);
            true
        } else {
            false
        }
    }

    /// Removes an edge from the graph. Returns whether the edge was present in the graph.
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
        if self.contains_node(from) && self.contains_node(to) {
            let from_id = self.node_to_id[from];
            let to_id = self.node_to_id[to];
            self.neighbors.get_mut(&from_id).unwrap().remove(&to_id)
        } else {
            false
        }
    }

    /// Returns `true` if the graph contains `node`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph = DiGraph::new();
    ///
    /// graph.insert_node(Some('a'));
    ///
    /// assert!(graph.contains_node(&Some('a')));
    /// assert!(!graph.contains_node(&Some('b')));
    /// ```
    pub fn contains_node(&self, node: &N) -> bool
    where
        N: Hash + Eq,
    {
        self.node_to_id.contains_key(node)
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
        if let (Some(from_id), Some(to_id)) = (self.node_to_id.get(from), self.node_to_id.get(to)) {
            self.neighbors[from_id].contains(to_id)
        } else {
            false
        }
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let graph: DiGraph<_> = (0..5).collect();
    ///
    /// assert_eq!(graph.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.node_to_id.len()
    }

    /// Returns `true` if the graph is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph: DiGraph<_> = "abc".chars().collect();
    ///
    /// assert!(!graph.is_empty());
    ///
    /// graph.clear();
    ///
    /// assert!(graph.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::DiGraph;
    ///
    /// let mut graph: DiGraph<_> = "abc".chars().collect();
    ///
    /// assert!(!graph.is_empty());
    ///
    /// graph.clear();
    ///
    /// assert!(graph.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.node_to_id.clear();
        self.id_to_node.clear();
        self.neighbors.clear();
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
    /// let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();
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
        let node_id = self.node_to_id[node];
        let neighbor_ids = &self.neighbors[&node_id];
        Neighbors {
            neighbors: neighbor_ids
                .iter()
                .filter(|id| self.id_to_node.contains_key(id))
                .map(|id| &self.id_to_node[id])
                .collect(),
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
    ///     // prints "1 -> 3" and "3 -> 2" in an arbitrary order
    ///     println!("{from} -> {to}");
    /// }
    /// ```
    pub fn edges(&self) -> Edges<'_, N>
    where
        N: Hash + Eq,
    {
        let mut edges = Vec::new();
        for (node_id, neighbor_ids) in &self.neighbors {
            if !self.id_to_node.contains_key(node_id) {
                continue;
            }
            for neighbor_id in neighbor_ids {
                if self.id_to_node.contains_key(neighbor_id) {
                    edges.push((&self.id_to_node[node_id], &self.id_to_node[neighbor_id]));
                }
            }
        }
        Edges { edges }
    }
}

impl<N> Default for DiGraph<N> {
    fn default() -> Self {
        DiGraph::new()
    }
}

impl<N> From<Vec<(N, N)>> for DiGraph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: Vec<(N, N)>) -> Self {
        let mut graph = DiGraph::new();
        for (from, to) in edges {
            graph.insert_edge(&from, &to);
        }
        graph
    }
}

impl<N, const M: usize> From<[(N, N); M]> for DiGraph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N); M]) -> Self {
        let mut graph = DiGraph::new();
        for (from, to) in edges {
            graph.insert_edge(&from, &to);
        }
        graph
    }
}

impl<N> IntoIterator for DiGraph<N> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: self.node_to_id.into_keys().collect(),
        }
    }
}

pub struct IntoIter<N> {
    nodes: Vec<N>,
}

impl<N> Iterator for IntoIter<N> {
    type Item = N;
    fn next(&mut self) -> Option<Self::Item> {
        self.nodes.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.nodes.len(), Some(self.nodes.len()))
    }
}

impl<N> FromIterator<N> for DiGraph<N>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<T: IntoIterator<Item = N>>(iter: T) -> Self {
        let mut counter = 0;
        let mut node_to_id = HashMap::new();
        let mut id_to_node = HashMap::new();
        for node in iter {
            node_to_id.insert(node.clone(), counter);
            id_to_node.insert(counter, node);
            counter += 1;
        }
        DiGraph {
            node_to_id,
            id_to_node,
            neighbors: HashMap::new(),
            counter,
        }
    }
}

pub struct Neighbors<'a, N: 'a> {
    neighbors: Vec<&'a N>,
}

impl<'a, N> Iterator for Neighbors<'a, N> {
    type Item = &'a N;
    fn next(&mut self) -> Option<Self::Item> {
        self.neighbors.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.neighbors.len(), Some(self.neighbors.len()))
    }
}

pub struct Edges<'a, N: 'a> {
    edges: Vec<(&'a N, &'a N)>,
}

impl<'a, N> Iterator for Edges<'a, N> {
    type Item = (&'a N, &'a N);
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.edges.len(), Some(self.edges.len()))
    }
}
