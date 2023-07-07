use std::cmp::min;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::DiGraph;

/// Returns a cycle in the graph, if one exists.
///
/// # Example
/// ```
/// use rust_dsa::{DiGraph, find_cycle};
///
/// let no_cycle = DiGraph::from([('a', 'b', ()), ('b', 'c', ())]);
/// assert!(find_cycle(&no_cycle).is_none());
///
/// let with_cycle = DiGraph::from([
///     (1, 2, ()),
///     (2, 3, ()),
///     (3, 4, ()),
///     (3, 1, ()),
/// ]);
/// let cycle = find_cycle(&with_cycle);
/// assert!(
///     cycle == Some(vec![&1, &2, &3])
///         || cycle == Some(vec![&2, &3, &1])
///         || cycle == Some(vec![&3, &1, &2])
/// );
/// ```
pub fn find_cycle<N, E>(graph: &DiGraph<N, E>) -> Option<Vec<&N>>
where
    N: Hash + Eq,
{
    let mut preorder: HashMap<&N, usize> = HashMap::new();
    let mut lowlink: HashMap<&N, usize> = HashMap::new();
    let mut scc_found: HashSet<&N> = HashSet::new();
    let mut scc_queue = Vec::new();
    let mut index = 0;
    let mut neighbors: HashMap<_, _> = graph
        .into_iter()
        .map(|v| (v, graph.neighbors_of(v)))
        .collect();
    for source in graph {
        if scc_found.contains(source) {
            continue;
        }
        let mut queue = vec![source];
        while let Some(v) = queue.last().copied() {
            if !preorder.contains_key(v) {
                index += 1;
                preorder.insert(v, index);
            }
            let mut done = true;
            while let Some((w, _)) = neighbors.get_mut(v).unwrap().next() {
                if !preorder.contains_key(w) {
                    queue.push(w);
                    done = false;
                    break;
                }
            }
            if done {
                lowlink.insert(v, preorder[v]);
                for (w, _) in graph.neighbors_of(v) {
                    if !scc_found.contains(w) {
                        if preorder[w] > preorder[v] {
                            lowlink.insert(v, min(lowlink[v], lowlink[w]));
                        } else {
                            lowlink.insert(v, min(lowlink[v], preorder[w]));
                        }
                    }
                }
                queue.pop();
                if lowlink[v] == preorder[v] {
                    let mut scc = vec![v];
                    while let Some(k) = scc_queue.last().copied() {
                        if preorder[k] <= preorder[v] {
                            break;
                        }
                        let k = scc_queue.pop().unwrap();
                        scc.push(k);
                    }
                    scc_found.extend(scc.iter().cloned());
                    if scc.len() > 1 {
                        return Some(scc);
                    }
                } else {
                    scc_queue.push(v);
                }
            }
        }
    }

    None
}
