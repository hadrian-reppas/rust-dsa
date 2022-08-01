#![allow(dead_code)]

use std::collections::HashMap;
use std::hash::Hash;

#[allow(unused_imports)]
use crate::{DiGraph, Graph, WeightedGraph};

/// A weighted directed graph implementation.
///
/// To simplify the implementation, nodes are `clone`d when they are inserted.
///
/// This crate also defines [`DiGraph`], [`Graph`] and [`WeightedGraph`].
///
/// # Example
/// ```
/// use rust_dsa::WeightedDiGraph;
///
/// // First, we create a new graph.
/// let mut graph = WeightedDiGraph::new();
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
///     // Prints "a -> b (5)", "a -> c (1)" and "c -> b (4)"
///     // in an arbitrary order.
///     println!("{from} -> {to} ({weight})");
/// }
///
/// // And iterate over all nodes
/// for node in graph {
///     // Prints "a", "b" and "c" in an arbitrary order.
///     println!("{node}");
/// }
/// ```
pub struct WeightedDiGraph<N, E> {
    // first, map each node to an id
    pub(crate) node_to_id: HashMap<N, usize>,
    pub(crate) id_to_node: HashMap<usize, N>,

    // then represent the graph with adjacency lists of ids
    pub(crate) edges: HashMap<usize, HashMap<usize, E>>,

    counter: usize,
}

impl<N, E> WeightedDiGraph<N, E> {
    /// Creates an empty graph.
    pub fn new() -> Self {
        WeightedDiGraph {
            edges: HashMap::new(),
            node_to_id: HashMap::new(),
            id_to_node: HashMap::new(),
            counter: 0,
        }
    }

    /// Inserts a node into the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<i32, ()> = WeightedDiGraph::new();
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
            self.edges.insert(self.counter, HashMap::new());
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
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::new();
    /// graph.insert_edge(&true, &false, 1);
    ///
    /// assert!(graph.contains_edge(&true, &false));
    /// assert!(graph.contains_node(&true));
    /// assert!(graph.contains_node(&false));
    /// ```
    pub fn insert_edge(&mut self, from: &N, to: &N, weight: E)
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
        self.edges.get_mut(&from_id).unwrap().insert(to_id, weight);
    }

    /// Removes a node from the graph. Returns whether the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let foo = "foo".to_string();
    /// let bar = "bar".to_string();
    ///
    /// let mut graph = WeightedDiGraph::from([(foo.clone(), bar.clone(), 2)]);
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
        // We don't actually update `self.edges`, we just invalidate some
        // of the ids contained in it. If there's an id in `self.edges` that
        // doesn't exist in `self.id_to_node`, it can be ignored.
        //
        // This means that `self.edges` never decreases in size. Maybe we can
        // write a function that removes inavlid ids from `self.edges` (sort
        // of like Vec::shrink_to_fit).
        if let Some(id) = self.node_to_id.get(node) {
            self.id_to_node.remove(id);
            self.node_to_id.remove(node);
            true
        } else {
            false
        }
    }

    /// Removes an edge from the graph. Returns the weight if the edge was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::from([(1, 2, true), (1, 3, false)]);
    ///
    /// assert!(graph.contains_edge(&1, &2));
    ///
    /// assert_eq!(graph.remove_edge(&1, &2), Some(true));
    ///
    /// assert!(!graph.contains_edge(&1, &2));
    ///
    /// assert_eq!(graph.remove_edge(&1, &2), None);
    /// ```
    pub fn remove_edge(&mut self, from: &N, to: &N) -> Option<E>
    where
        N: Hash + Eq,
    {
        if self.contains_node(from) && self.contains_node(to) {
            let from_id = self.node_to_id[from];
            let to_id = self.node_to_id[to];
            self.edges.get_mut(&from_id).unwrap().remove(&to_id)
        } else {
            None
        }
    }

    /// Returns `true` if the graph contains `node`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<i32, ()> = WeightedDiGraph::new();
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
        self.node_to_id.contains_key(node)
    }

    /// Returns `true` if the graph contains an edge between `from` and `to`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::from([
    ///     ('a', 'b', 1),
    ///     ('b', 'c', 2),
    ///     ('b', 'd', 3),
    /// ]);
    ///
    /// assert!(graph.contains_edge(&'b', &'c'));
    /// assert!(!graph.contains_edge(&'c', &'d'));
    /// ```
    pub fn contains_edge(&self, from: &N, to: &N) -> bool
    where
        N: Hash + Eq,
    {
        if self.contains_node(from) && self.contains_node(to) {
            let from_id = self.node_to_id[from];
            let to_id = self.node_to_id[to];
            self.edges[&from_id].contains_key(&to_id)
        } else {
            false
        }
    }

    /// Returns a reference to the edge's weight if the graph contains an edge between `from` and `to`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::from([
    ///     ('a', 'b', 1),
    ///     ('b', 'c', 2),
    ///     ('b', 'd', 3),
    /// ]);
    ///
    /// assert_eq!(graph.get_edge(&'b', &'c'), Some(&2));
    /// assert_eq!(graph.get_edge(&'c', &'d'), None);
    /// ```
    pub fn get_edge(&self, from: &N, to: &N) -> Option<&E>
    where
        N: Hash + Eq,
    {
        if self.contains_node(from) && self.contains_node(to) {
            let from_id = self.node_to_id[from];
            let to_id = self.node_to_id[to];
            self.edges[&from_id].get(&to_id)
        } else {
            None
        }
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let graph: WeightedDiGraph<i32, ()> = (0..42).collect();
    ///
    /// assert_eq!(graph.len(), 42);
    /// ```
    pub fn len(&self) -> usize {
        self.node_to_id.len()
    }

    /// Returns `true` if the graph is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<char, ()> = "abc".chars().collect();
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
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<char, ()> = "abc".chars().collect();
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
        self.edges.clear();
    }

    /// Returns an iterator that visits all of `node`'s neighbors.
    ///
    /// # Panics
    /// Panics if `node` is not present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    /// use std::collections::HashSet;
    ///
    /// let graph = WeightedDiGraph::from([
    ///     (1, 2, 'a'),
    ///     (1, 3, 'b'),
    ///     (1, 4, 'c'),
    ///     (4, 3, 'd'),
    ///     (3, 2, 'a'),
    /// ]);
    ///
    /// let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();
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
        let node_id = self.node_to_id[node];
        let neighbor_ids = &self.edges[&node_id];
        WeightedNeighbors {
            neighbors: neighbor_ids
                .iter()
                .filter(|(id, _)| self.id_to_node.contains_key(id))
                .map(|(id, edge)| (&self.id_to_node[id], edge))
                .collect(),
        }
    }

    /// Returns an iterator visiting the graph's edges in an arbitrary order.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::new();
    /// graph.insert_edge(&1, &3, 'a');
    /// graph.insert_edge(&3, &2, 'b');
    ///
    /// for (from, to, weight) in graph.edges() {
    ///     // Prints "1 -> 3 (a)" and "3 -> 2 (b)" in an arbitrary order
    ///     println!("{from} -> {to} ({weight})");
    /// }
    /// ```
    pub fn edges(&self) -> WeightedEdges<'_, N, E> {
        let mut edges = Vec::new();
        for (node_id, neighbor_ids) in &self.edges {
            if !self.id_to_node.contains_key(node_id) {
                continue;
            }
            for (neighbor_id, weight) in neighbor_ids {
                if self.id_to_node.contains_key(neighbor_id) {
                    edges.push((
                        &self.id_to_node[node_id],
                        &self.id_to_node[neighbor_id],
                        weight,
                    ));
                }
            }
        }
        WeightedEdges { edges }
    }
}

impl<N, E> Default for WeightedDiGraph<N, E> {
    fn default() -> Self {
        WeightedDiGraph::new()
    }
}

impl<N, E> PartialEq for WeightedDiGraph<N, E>
where
    N: Eq + Hash,
    E: PartialEq,
{
    /// Returns `true` if the two graphs are equal.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut a = WeightedDiGraph::new();
    /// a.insert_edge(&1, &2, 'a');
    /// a.insert_edge(&3, &2, 'b');
    /// a.insert_edge(&2, &1, 'c');
    /// a.remove_edge(&1, &2);
    ///
    /// let mut b: WeightedDiGraph<i32, char> = [1, 2, 3].into_iter().collect();
    /// b.insert_edge(&3, &2, 'b');
    /// b.insert_edge(&2, &1, 'c');
    ///
    /// assert!(a == b);
    ///
    /// let mut c = WeightedDiGraph::new();
    /// c.insert_edge(&1, &2, 'a');
    /// c.insert_edge(&3, &2, 'b');
    /// c.insert_edge(&2, &1, 'c');
    ///
    /// assert!(a != c);
    /// assert!(b != c);
    ///
    /// let mut d = WeightedDiGraph::new();
    /// d.insert_edge(&1, &2, 'a');
    /// d.insert_edge(&3, &2, 'b');
    /// d.insert_edge(&2, &1, 'z');
    ///
    /// assert!(c != d);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            // different number of nodes in `other`
            return false;
        }

        for (node, id) in &self.node_to_id {
            if let Some(other_id) = other.node_to_id.get(node) {
                let edges = self.edges.get(id).unwrap();
                let other_edges = other.edges.get(other_id).unwrap();
                if edges
                    .iter()
                    .filter(|(id, _)| self.id_to_node.contains_key(id))
                    .count()
                    != other_edges
                        .iter()
                        .filter(|(id, _)| other.id_to_node.contains_key(id))
                        .count()
                {
                    // different number of edges out of `node`
                    return false;
                }
                for (neighbor_id, weight) in edges {
                    if let Some(neighbor) = self.id_to_node.get(neighbor_id) {
                        if let Some(other_neighbor_id) = other.node_to_id.get(neighbor) {
                            if let Some(other_weight) = other_edges.get(other_neighbor_id) {
                                if weight != other_weight {
                                    // weight between `node` and `neighbor` in `self` does not
                                    // equal weight between `node` and `neighbor` in `other`
                                    return false;
                                }
                            } else {
                                // no edge between `node` and `neighbor` in `other`
                                return false;
                            }
                        } else {
                            // `neighbor` not in `other`
                            return false;
                        }
                    }
                }
            } else {
                // `node` not in `other`
                return false;
            }
        }
        true
    }
}

impl<N: Eq + Hash, E: Eq> Eq for WeightedDiGraph<N, E> {}

impl<N, E> From<Vec<(N, N, E)>> for WeightedDiGraph<N, E>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: Vec<(N, N, E)>) -> Self {
        let mut graph = WeightedDiGraph::new();
        for (from, to, weight) in edges {
            graph.insert_edge(&from, &to, weight);
        }
        graph
    }
}

impl<N, E, const M: usize> From<[(N, N, E); M]> for WeightedDiGraph<N, E>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N, E); M]) -> Self {
        let mut graph = WeightedDiGraph::new();
        for (from, to, weight) in edges {
            graph.insert_edge(&from, &to, weight);
        }
        graph
    }
}

impl<N, E> FromIterator<N> for WeightedDiGraph<N, E>
where
    N: Clone + Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<T: IntoIterator<Item = N>>(iter: T) -> Self {
        let mut counter = 0;
        let mut node_to_id = HashMap::new();
        let mut id_to_node = HashMap::new();
        let mut edges = HashMap::new();
        for node in iter {
            node_to_id.insert(node.clone(), counter);
            id_to_node.insert(counter, node);
            edges.insert(counter, HashMap::new());
            counter += 1;
        }
        WeightedDiGraph {
            node_to_id,
            id_to_node,
            edges,
            counter,
        }
    }
}

impl<N, E> IntoIterator for WeightedDiGraph<N, E> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: self.node_to_id.into_keys().collect(),
        }
    }
}

impl<'a, N, E> IntoIterator for &'a WeightedDiGraph<N, E> {
    type IntoIter = Iter<'a, N>;
    type Item = &'a N;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            nodes: self.node_to_id.keys().collect(),
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

pub struct Iter<'a, N: 'a> {
    pub(crate) nodes: Vec<&'a N>,
}

impl<'a, N> Iterator for Iter<'a, N> {
    type Item = &'a N;
    fn next(&mut self) -> Option<Self::Item> {
        self.nodes.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.nodes.len(), Some(self.nodes.len()))
    }
}

pub struct WeightedNeighbors<'a, N: 'a, E: 'a> {
    neighbors: Vec<(&'a N, &'a E)>,
}

impl<'a, N, E> Iterator for WeightedNeighbors<'a, N, E> {
    type Item = (&'a N, &'a E);
    fn next(&mut self) -> Option<Self::Item> {
        self.neighbors.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.neighbors.len(), Some(self.neighbors.len()))
    }
}

pub struct WeightedEdges<'a, N: 'a, E: 'a> {
    edges: Vec<(&'a N, &'a N, &'a E)>,
}

impl<'a, N, E> Iterator for WeightedEdges<'a, N, E> {
    type Item = (&'a N, &'a N, &'a E);
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.edges.len(), Some(self.edges.len()))
    }
}
