use crate::BiMap;
use std::collections::{HashMap, HashSet};
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
/// // Edges and nodes can be inserted together.
/// graph.insert_edge_by_value('a', 'z', -1);
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
    map: BiMap<N, usize>,

    // then represent the graph with adjacency lists of ids
    edges: HashMap<usize, HashMap<usize, E>>,
    edges_inv: HashMap<usize, HashSet<usize>>,

    counter: usize,
}

impl<N, E> WeightedDiGraph<N, E> {
    /// Creates an empty graph.
    pub fn new() -> WeightedDiGraph<N, E> {
        WeightedDiGraph {
            map: BiMap::new(),
            edges: HashMap::new(),
            edges_inv: HashMap::new(),
            counter: 0,
        }
    }

    /// Inserts a node into the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<_, ()> = WeightedDiGraph::new();
    /// graph.insert_node(1);
    ///
    /// assert!(graph.contains_node(&1));
    /// ```
    pub fn insert_node(&mut self, node: N)
    where
        N: Hash + Eq,
    {
        self.insert_node_internal(node);
    }

    fn insert_node_internal(&mut self, node: N) -> usize
    where
        N: Hash + Eq,
    {
        if let Some(&id) = self.map.get_by_left(&node) {
            id
        } else {
            self.map.insert(node, self.counter);
            self.edges.insert(self.counter, HashMap::new());
            self.edges_inv.insert(self.counter, HashSet::new());
            self.counter += 1;
            self.counter - 1
        }
    }

    /// Inserts an edge into the graph.
    ///
    /// Returns the old weight if the graph already contained the edge.
    ///
    /// # Panics
    /// Panics if `from` or `to` is not in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<_, _> = [true, false].into_iter().collect();
    /// graph.insert_edge(&true, &false, 1);
    ///
    /// assert!(graph.contains_edge(&true, &false));
    /// ```
    pub fn insert_edge(&mut self, from: &N, to: &N, weight: E) -> Option<E>
    where
        N: Hash + Eq,
    {
        let from_id = self
            .map
            .get_by_left(from)
            .expect("node `from` is not in the graph");
        let to_id = self
            .map
            .get_by_left(to)
            .expect("node `to` is not in the graph");
        self.edges_inv.get_mut(to_id).unwrap().insert(*from_id);
        self.edges.get_mut(from_id).unwrap().insert(*to_id, weight)
    }

    /// Inserts an edge into the graph. The nodes are inserted if they are not already
    /// present in the graph.
    ///
    /// Returns the old weight if the graph already contained the edge.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::new();
    ///
    /// graph.insert_edge_by_value('a', 'b', 1);
    ///
    /// assert_eq!(graph.get_edge(&'a', &'b'), Some(&1));
    /// assert!(graph.contains_node(&'a'));
    /// assert!(graph.contains_node(&'b'));
    /// ```
    pub fn insert_edge_by_value(&mut self, from: N, to: N, weight: E) -> Option<E>
    where
        N: Hash + Eq,
    {
        let from_id = self.insert_node_internal(from);
        let to_id = self.insert_node_internal(to);
        self.edges_inv.get_mut(&to_id).unwrap().insert(from_id);
        self.edges.get_mut(&from_id).unwrap().insert(to_id, weight)
    }

    /// Removes a node from the graph. Returns `true` if the node was present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let foo = "foo".to_string();
    /// let bar = "bar".to_string();
    ///
    /// let mut graph = WeightedDiGraph::from([(foo.clone(), bar, 2)]);
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
        if let Some((_, ref id)) = self.map.remove_by_left(node) {
            for neighbor_id in &self.edges_inv[id] {
                self.edges.get_mut(neighbor_id).unwrap().remove(id);
            }
            self.edges.remove(id);
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
        if let (Some(from_id), Some(to_id)) = (self.map.get_by_left(from), self.map.get_by_left(to))
        {
            self.edges_inv.get_mut(to_id).unwrap().remove(from_id);
            self.edges.get_mut(from_id).unwrap().remove(to_id)
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
    /// let mut graph: WeightedDiGraph<_, f64> = WeightedDiGraph::new();
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
        self.map.contains_left(node)
    }

    /// Returns `true` if the graph contains an edge between `from` and `to`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let graph = WeightedDiGraph::from([
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
        if let (Some(from_id), Some(to_id)) = (self.map.get_by_left(from), self.map.get_by_left(to))
        {
            self.edges[from_id].contains_key(to_id)
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
    /// let graph = WeightedDiGraph::from([
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
        if let (Some(from_id), Some(to_id)) = (self.map.get_by_left(from), self.map.get_by_left(to))
        {
            self.edges[from_id].get(to_id)
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
    /// let graph: WeightedDiGraph<_, ()> = (0..42).collect();
    ///
    /// assert_eq!(graph.len(), 42);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the graph is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph: WeightedDiGraph<_, bool> = "abc".chars().collect();
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
    /// let mut graph: WeightedDiGraph<_, u8> = "abc".chars().collect();
    ///
    /// assert!(!graph.is_empty());
    ///
    /// graph.clear();
    ///
    /// assert!(graph.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
        self.edges.clear();
        self.edges_inv.clear();
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
        let node_id = self
            .map
            .get_by_left(node)
            .expect("`node` is not in the graph");
        let neighbor_ids = &self.edges[node_id];
        WeightedNeighbors {
            neighbors: neighbor_ids
                .iter()
                .map(|(id, edge)| (self.map.get_by_right(id).unwrap(), edge))
                .collect(),
        }
    }

    /// Returns the number of neighbors `node` has.
    ///
    /// # Panics
    /// Panics if `node` is not present in the graph.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let graph = WeightedDiGraph::from([
    ///     (1, 2, 'a'),
    ///     (1, 3, 'b'),
    ///     (1, 4, 'c'),
    ///     (4, 3, 'd'),
    ///     (3, 2, 'a'),
    /// ]);
    ///
    /// assert_eq!(graph.count_neighbors_of(&1), 3);
    /// ```
    pub fn count_neighbors_of(&self, node: &N) -> usize
    where
        N: Hash + Eq,
    {
        let node_id = self
            .map
            .get_by_left(node)
            .expect("`node` is not in the graph");
        self.edges[node_id].len()
    }

    /// Returns an iterator visiting the graph's edges in an arbitrary order.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::WeightedDiGraph;
    ///
    /// let mut graph = WeightedDiGraph::new();
    /// graph.insert_edge_by_value(1, 3, 'a');
    /// graph.insert_edge_by_value(3, 2, 'b');
    ///
    /// for (from, to, weight) in graph.edges() {
    ///     // Prints "1 -> 3 (a)" and "3 -> 2 (b)" in an arbitrary order
    ///     println!("{from} -> {to} ({weight})");
    /// }
    /// ```
    pub fn edges(&self) -> WeightedEdges<'_, N, E> {
        let mut edges = Vec::new();
        for (node_id, neighbor_ids) in &self.edges {
            for (neighbor_id, weight) in neighbor_ids {
                edges.push((
                    self.map.get_by_right(node_id).unwrap(),
                    self.map.get_by_right(neighbor_id).unwrap(),
                    weight,
                ));
            }
        }
        WeightedEdges { edges }
    }
}

impl<N, E> Default for WeightedDiGraph<N, E> {
    fn default() -> WeightedDiGraph<N, E> {
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
    /// let graph: WeightedDiGraph<_, _> = [1, 2, 3].into_iter().collect();
    ///
    /// let mut a = graph.clone();
    /// a.insert_edge(&1, &2, 'a');
    /// a.insert_edge(&3, &2, 'b');
    /// a.insert_edge(&2, &1, 'c');
    /// a.remove_edge(&1, &2);
    ///
    /// let mut b = graph.clone();
    /// b.insert_edge(&3, &2, 'b');
    /// b.insert_edge(&2, &1, 'c');
    ///
    /// assert!(a == b);
    ///
    /// let mut c = graph.clone();
    /// c.insert_edge(&1, &2, 'a');
    /// c.insert_edge(&3, &2, 'b');
    /// c.insert_edge(&2, &1, 'c');
    ///
    /// assert!(a != c);
    /// assert!(b != c);
    ///
    /// let mut d = graph.clone();
    /// d.insert_edge(&1, &2, 'a');
    /// d.insert_edge(&3, &2, 'b');
    /// d.insert_edge(&2, &1, 'z');
    ///
    /// assert!(c != d);
    /// ```
    fn eq(&self, other: &WeightedDiGraph<N, E>) -> bool {
        if self.len() != other.len() {
            // different number of nodes in `other`
            return false;
        }

        for node in self {
            if !other.contains_node(node) {
                return false;
            }
            if self.count_neighbors_of(node) != other.count_neighbors_of(node) {
                return false;
            }
            for (neighbor, weight) in self.neighbors_of(node) {
                if other.get_edge(node, neighbor) != Some(weight) {
                    return false;
                }
            }
        }
        true
    }
}

impl<N, E> Eq for WeightedDiGraph<N, E>
where
    N: Eq + Hash,
    E: Eq,
{
}

impl<N, E> Clone for WeightedDiGraph<N, E>
where
    N: Clone + Hash + Eq,
    E: Clone,
{
    fn clone(&self) -> WeightedDiGraph<N, E> {
        WeightedDiGraph {
            map: self.map.clone(),
            edges: self.edges.clone(),
            edges_inv: self.edges_inv.clone(),
            counter: self.counter,
        }
    }
}

impl<N, E, const M: usize> From<[(N, N, E); M]> for WeightedDiGraph<N, E>
where
    N: Hash + Eq,
{
    /// Creates a graph from an edge list.
    fn from(edges: [(N, N, E); M]) -> WeightedDiGraph<N, E> {
        let mut graph = WeightedDiGraph::new();
        for (from, to, weight) in edges {
            graph.insert_edge_by_value(from, to, weight);
        }
        graph
    }
}

impl<N, E> FromIterator<N> for WeightedDiGraph<N, E>
where
    N: Hash + Eq,
{
    /// Creates a graph with the elements of the iterator. The graph does not
    /// contain any edges.
    fn from_iter<I: IntoIterator<Item = N>>(iter: I) -> WeightedDiGraph<N, E> {
        let mut counter = 0;
        let mut map = BiMap::new();
        let mut edges = HashMap::new();
        let mut edges_inv = HashMap::new();
        for node in iter {
            map.insert(node, counter);
            edges.insert(counter, HashMap::new());
            edges_inv.insert(counter, HashSet::new());
            counter += 1;
        }
        WeightedDiGraph {
            map,
            edges,
            edges_inv,
            counter,
        }
    }
}

impl<N, E> IntoIterator for WeightedDiGraph<N, E> {
    type IntoIter = IntoIter<N>;
    type Item = N;
    /// Creates an iterator over the nodes in the graph.
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: self.map.into_lefts(),
        }
    }
}

impl<'a, N, E> IntoIterator for &'a WeightedDiGraph<N, E> {
    type IntoIter = Iter<'a, N>;
    type Item = &'a N;
    /// Creates an iterator over the nodes in the graph.
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            nodes: self.map.lefts(),
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
}

pub struct Iter<'a, N: 'a> {
    nodes: Vec<&'a N>,
}

impl<'a, N> Iterator for Iter<'a, N> {
    type Item = &'a N;
    fn next(&mut self) -> Option<Self::Item> {
        self.nodes.pop()
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
}

pub struct WeightedEdges<'a, N: 'a, E: 'a> {
    edges: Vec<(&'a N, &'a N, &'a E)>,
}

impl<'a, N, E> Iterator for WeightedEdges<'a, N, E> {
    type Item = (&'a N, &'a N, &'a E);
    fn next(&mut self) -> Option<Self::Item> {
        self.edges.pop()
    }
}
