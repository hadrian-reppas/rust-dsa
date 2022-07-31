#![allow(dead_code)]

use crate::DiGraph;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// Returns a [topological sort](http://en.wikipedia.org/wiki/Topological_sorting)
/// of the graph, if one exists.
///
/// If the graph contains one or more directed cycles, `None` is returned.
///
/// # Example
/// ```
/// use rust_dsa::{DiGraph, topological_sort};
///
/// //    +---+      +---+      +---+
/// //    |'a'| ---> |'b'| ---> |'c'|
/// //    +---+      +---+      +---+
/// let no_cycle = DiGraph::from([('a', 'b'), ('b', 'c')]);
///
/// assert_eq!(
///     topological_sort(&no_cycle),
///     Some(vec![&'a', &'b', &'c'])
/// );
///
///
/// //    +---+      +---+
/// //    | 1 | ---> | 2 |
/// //    +---+      +---+
/// //      ^          |
/// //      |          v
/// //      |        +---+      +---+
/// //      +------- | 3 | ---> | 4 |
/// //               +---+      +---+
/// let with_cycle = DiGraph::from([
///     (1, 2),
///     (2, 3),
///     (3, 4),
///     (3, 1),
/// ]);
///
/// // `with_cycle` contains a cycle so `topological_sort` returns `None`
/// assert_eq!(
///     topological_sort(&with_cycle),
///     None
/// );
///
/// use rust_dsa::is_topological_sort;
///
/// let big_graph = DiGraph::from([
///     (1, 2),
///     (2, 3),
///     (4, 3),
///     (3, 5),
///     (5, 6),
///     (6, 7),
///     (7, 8),
///     (5, 9),
///     (9, 10),
///     (5, 10),
///     (10, 11),
///     (10, 8),
///     (5, 12),
///     (12, 13),
///     (12, 14),
///     (12, 8),
///     (8, 15),
/// ]);
///
/// // `big_graph` is acyclic
/// let sort = topological_sort(&big_graph).unwrap();
///
/// assert!(is_topological_sort(&big_graph, sort));
/// ```
///
/// # Runtime complexity
/// This function implements [Kahn's algorithm](https://en.wikipedia.org/wiki/Topological_sorting#Kahn's_algorithm),
/// so it runs in *O*(*N* + *E*) time where *N* is the number of nodes and *E* is the number of edges.
pub fn topological_sort<N>(graph: &DiGraph<N>) -> Option<Vec<&N>>
where
    N: Hash + Eq,
{
    let mut sorted = Vec::new();
    let mut neighbor_map = get_neighbor_map(graph);
    let mut indegrees = get_indegrees(&neighbor_map);
    let mut indegree_zero: Vec<_> = indegrees
        .iter()
        .filter(|(_, &count)| count == 0)
        .map(|(node, _)| *node)
        .collect();

    while let Some(node) = indegree_zero.pop() {
        sorted.push(node);
        for neighbor in neighbor_map[node].clone() {
            neighbor_map.get_mut(node).unwrap().remove(neighbor);
            *indegrees.get_mut(neighbor).unwrap() -= 1;
            if indegrees[neighbor] == 0 {
                indegree_zero.push(neighbor);
            }
        }
    }

    if indegrees.into_values().all(|indegree| indegree == 0) {
        Some(sorted)
    } else {
        None
    }
}

fn get_neighbor_map<N>(graph: &DiGraph<N>) -> HashMap<&N, HashSet<&N>>
where
    N: Hash + Eq,
{
    graph
        .into_iter()
        .map(|node| (node, graph.neighbors_of(node).collect()))
        .collect()
}

fn get_indegrees<'a, N>(neighbor_map: &HashMap<&'a N, HashSet<&'a N>>) -> HashMap<&'a N, usize>
where
    N: Hash + Eq,
{
    let mut indegrees: HashMap<_, _> = neighbor_map
        .keys()
        .cloned()
        .zip(std::iter::repeat(0))
        .collect();

    for neighbors in neighbor_map.values() {
        for neighbor in neighbors {
            *indegrees.get_mut(neighbor).unwrap() += 1;
        }
    }

    indegrees
}

/// Returns `true` if the ordering is a topological sort for the graph.
///
/// Returns `false` if the ordering is *not* a topological sort or if the graph contains cycles.
///
/// # Panics
/// Panics if any element of `sort` is not contained in `graph` of if there are
/// duplicate elemnts in `sort`.
///
/// # Example
/// ```
/// use rust_dsa::{DiGraph, is_topological_sort};
///
/// //    +---+      +---+      +---+
/// //    |'a'| ---> |'b'| ---> |'c'|
/// //    +---+      +---+      +---+
/// let graph = DiGraph::from([('a', 'b'), ('b', 'c')]);
///
/// assert!(is_topological_sort(
///     &graph,
///     vec![&'a', &'b', &'c']
/// ));
///
/// assert!(!is_topological_sort(
///     &graph,
///     vec![&'b', &'a', &'c']
/// ));
/// ```
pub fn is_topological_sort<N>(graph: &DiGraph<N>, sort: Vec<&N>) -> bool
where
    N: Hash + Eq,
{
    let sort_inv: HashMap<_, _> = sort
        .iter()
        .enumerate()
        .map(|(i, node)| (*node, i))
        .collect();
    if sort_inv.len() < sort.len() {
        panic!("duplicate elemnts in `sort`");
    }

    for (from, to) in graph.edges() {
        if sort_inv[from] > sort_inv[to] {
            return false;
        }
    }

    true
}
