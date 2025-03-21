# Data Structures and Algorithms in Rust

Some interesting data structures and algorithms implemented in Rust. Docs are hosted [here](https://hadrian-reppas.github.io/rust-dsa/rust_dsa/index.html).

## Testing

The doctests are *very* slow, so you can run `test.py` to copy all doctests
into `src/tests.rs` and run them. This makes them run around 100x faster.

## TODO

Most entries on this list were taken directly from Keith Schwarz's
[Archive of Interesting Code](https://keithschwarz.com/interesting/) and
[TODO list](https://keithschwarz.com/interesting/todo.html).

|          | Name                                 | File                               | Description |
| -------- | ------------------------------------ | ---------------------------------- | ----------- |
| &#9989;  | Binary Heap                          | [src/heap.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/heap.rs) | A [priority queue](https://en.wikipedia.org/wiki/Priority_queue) implementation backed by a [binary heap](https://en.wikipedia.org/wiki/Binary_heap). |
| &#9989;  | Topological Sort                     | [src/toposort.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/toposort.rs) | An algorithm for finding a [topological ordering](https://en.wikipedia.org/wiki/Topological_sorting) of a [DAG](https://en.wikipedia.org/wiki/Directed_acyclic_graph). |
| &#9989;  | Graph                                | [src/graph.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/graph.rs) | An implementation of a weighted [graph](https://en.wikipedia.org/wiki/Graph_(abstract_data_type)). |
| &#9989;  | Directed Graph                       | [src/digraph.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/digraph.rs) | An implementation of a weighted, [directed graph](https://en.wikipedia.org/wiki/Directed_graph). |
| &#9989;  | VList                                | [src/vlist.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/vlist.rs) | A dynamic array implementation backed by a [VList](https://rosettacode.org/wiki/VList). |
| &#9989;  | Immutable Vector                     | [src/ivector.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/ivector.rs) | An immutable vector implementation with efficient edits/clones. |
| &#9989;  | Interval Heap                        | [src/iheap.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/iheap.rs) | An implementation of a [double-ended priority queue](https://en.wikipedia.org/wiki/Double-ended_priority_queue) backed by an [interval heap](https://en.wikipedia.org/wiki/Double-ended_priority_queue#Interval_heaps). |
| &#9989;  | Quickselect                          | [src/quickselect.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/quickselect.rs) | An implementation of the [quickselect](https://en.wikipedia.org/wiki/Quickselect) algorithm. |
| &#9989;  | Union-Find                           | [src/unionfind.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/unionfind.rs) | An implementation of a [disjoint-set data structure](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) using a disjoint set forest. |
| &#9989;  | Insertion Sort                       | [src/insertion_sort.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/insertion_sort.rs) | An implementation of the [insertion sort](https://en.wikipedia.org/wiki/Insertion_sort) algorithm. |
| &#9989;  | Radix Sort                           | [src/radix_sort.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/radix_sort.rs) | An implementation of the [radix sort](https://en.wikipedia.org/wiki/Radix_sort) algorithm. |
| &#9989;  | Quicksort                            | [src/quicksort.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/quicksort.rs) | An implementation of the [quicksort](https://en.wikipedia.org/wiki/Quicksort) algorithm. |
| &#9989;  | Mergesort                            | [src/mergesort.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/mergesort.rs) | An implementation of the [merge sort](https://en.wikipedia.org/wiki/Merge_sort) algorithm. |
| &#9989;  | Heapsort                             | [src/heapsort.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/heapsort.rs) | An implementation of the [heapsort](https://en.wikipedia.org/wiki/Heapsort) algorithm. |
| &#10060; | Timsort                              | *TODO*                             | An implementation of the [Timsort](https://en.wikipedia.org/wiki/Timsort) algorithm. |
| &#9989;  | MJRTY                                | [src/mjrty.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/mjrty.rs) | A fast, linear-time algorithm for finding the [majority element](https://www.cs.utexas.edu/~moore/best-ideas/mjrty/) of a data set. |
| &#9989;  | Bidirectional Map                    | [src/bimap.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/bimap.rs) | An implementation of a [bidirectional map](https://en.wikipedia.org/wiki/Bidirectional_map). |
| &#9989;  | Bump Allocator                       | [src/bumpalloc.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/bumpalloc.rs) | A bump allocator. |
| &#10060; | Quickhull                            | *TODO*                             | An implementation of the [quickhull](https://en.wikipedia.org/wiki/Quickhull) algorithm. |
| &#9989;  | Binomial Heap                        | [src/binomialheap.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/binomialheap.rs) | A [priority queue](https://en.wikipedia.org/wiki/Priority_queue) implementation backed by a [binomial heap](https://en.wikipedia.org/wiki/Binomial_heap). |
| &#10060; | Extendible Array                     | *TODO*                             | A dynamic array implementation with O(1) worst-case lookup and append. |
| &#10060; | Hashed Array Tree                    | *TODO*                             | A dynamic array implementation backed by a [hashed array tree](https://en.wikipedia.org/wiki/Hashed_array_tree). |
| &#9989;  | Fibonacci Heap                       | [src/fibheap.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/fibheap.rs) | A priority queue implementation backed by a [Fibonacci heap](https://en.wikipedia.org/wiki/Fibonacci_heap). |
| &#10060; | Dijkstra's Algorithm                 | *TODO*                             | An implementation of [Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra's_algorithm) for single-source shortest paths. |
| &#10060; | Prim's Algorithm                     | *TODO*                             | An implementation of [Prim's algorithm](https://en.wikipedia.org/wiki/Prim's_algorithm) for finding [minimum spanning trees](https://en.wikipedia.org/wiki/Minimum_spanning_tree). |
| &#10060; | Kruskal's Algorithm                  | *TODO*                             | An implementation of [Kruskal's algorithm](https://en.wikipedia.org/wiki/Kruskal%27s_algorithm) for finding [minimum spanning trees](https://en.wikipedia.org/wiki/Minimum_spanning_tree). |
| &#9989;  | Levenshtein Distance                 | [src/levenshtein.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/levenshtein.rs) | An implementation of the [Wagner–Fischer algorithm](https://en.wikipedia.org/wiki/Wagner%E2%80%93Fischer_algorithm) for finding the [Levenshtein distance](https://en.wikipedia.org/wiki/Levenshtein_distance) between two slices. |
| &#9989;  | Bloom Filter                         | [src/bloom.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/bloom.rs) | An implementation of a [Bloom filter](https://en.wikipedia.org/wiki/Bloom_filter). |
| &#10060; | Cuckoo Map                           | *TODO*                             | An [associative array](https://en.wikipedia.org/wiki/Associative_array) implementation using [cuckoo hashing](https://en.wikipedia.org/wiki/Cuckoo_hashing). |
| &#10060; | Treap                                | *TODO*                             | A sorted associative array implementation backed by a [treap](https://en.wikipedia.org/wiki/Treap). |
| &#10060; | Floyd-Warshall Algorithm             | *TODO*                             | An implementation of the [Floyd-Warshall algorithm](https://en.wikipedia.org/wiki/Floyd-Warshall_algorithm) for all-pairs shortest paths in a graph. |
| &#10060; | Edmonds's Matching Algorithm         | *TODO*                             | An implementation of [Edmonds's matching algorithm](https://en.wikipedia.org/wiki/Edmonds's_matching_algorithm) for finding [maximum matchings](https://en.wikipedia.org/wiki/Matching_(graph_theory)#Maximum_matchings) in undirected graphs. |
| &#9989;  | Fenwick Tree                         | [src/fenwick.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/fenwick.rs) | A [Fenwick tree](https://en.wikipedia.org/wiki/Fenwick_tree) implementation. |
| &#9989;  | DiGraph Cycles                       | [src/cycle.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/cycle.rs) | An algorithm for finding [cycles](https://en.wikipedia.org/wiki/Cycle_(graph_theory)) in a directed graph. |
| &#10060; | Kosaraju's Algorithm                 | *TODO*                             | An implementation of [Kosaraju's algorithm](https://en.wikipedia.org/wiki/Kosaraju's_algorithm) for finding [strongly connected components](https://en.wikipedia.org/wiki/Strongly_connected_component) of a directed graph. |
| &#10060; | Bellman-Ford Algorithm               | *TODO*                             | An implementation of the [Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm) for single-source shortest paths. |
| &#9989;  | Graham's Scan                        | [src/graham.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/graham.rs) | An implementation of [Graham's scan](https://en.wikipedia.org/wiki/Graham_scan) for finding convex hulls in 2D space. |
| &#10060; | Johnson's Algorithm                  | *TODO*                             | An implementation of [Johnson's algorithm](https://en.wikipedia.org/wiki/Johnson's_algorithm) for all-pairs shortest paths. |
| &#10060; | Deflate                              | *TODO*                             | An implementation of the [Deflate](https://en.wikipedia.org/wiki/Deflate) algorithm |
| &#9989;  | Ring Buffer-Backed Deque             | [src/deque.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/deque.rs) | An implementation of a [deque](https://en.wikipedia.org/wiki/Double-ended_queue) using a [ring buffer](https://en.wikipedia.org/wiki/Circular_buffer). |
| &#10060; | Rabin-Karp Algorithm                 | *TODO*                             | An implementation of the [Rabin-Karp algorithm](https://en.wikipedia.org/wiki/Rabin%E2%80%93Karp_string_search_algorithm) for string matching. |
| &#9989;  | Any Stack                            | [src/anystack.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/anystack.rs) | An implementation of a [stack](https://en.wikipedia.org/wiki/Stack_(abstract_data_type)) that can contain values of any type |
| &#9989;  | Min-Stack                            | [src/minstack.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/minstack.rs) | An implementation of a [LIFO stack](https://en.wikipedia.org/wiki/Stack_(abstract_data_type)) that supports O(1) push, pop and find-minimum. |
| &#9989;  | Min-Queue                            | [src/minqueue.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/minqueue.rs) | An implementation of a [FIFO queue](https://en.wikipedia.org/wiki/Queue_(data_structure)) that supports O(1) push, pop and find-minimum. |
| &#10060; | Suffix Automaton                     | *TODO*                             | An implementation of a [suffix automaton](https://en.wikipedia.org/wiki/Suffix_automaton). |
| &#10060; | Fortune's Algorithm                  | *TODO*                             | [Fortune's algorithm](https://en.wikipedia.org/wiki/Fortune%27s_algorithm) for generating [Voronoi diagrams](https://en.wikipedia.org/wiki/Voronoi_diagram). |
| &#9989;  | Median Heap                          | [src/medianheap.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/medianheap.rs) | A data structure for efficiently calculating a running median. |
| &#10060; | Aho–Corasick Algorithm               | *TODO*                             | An implementation of the [Aho–Corasick algorithm](https://en.wikipedia.org/wiki/Aho%E2%80%93Corasick_algorithm) for string-searching. |
| &#10060; | Soft Heap                            | *TODO*                             | A [soft heap](https://en.wikipedia.org/wiki/Soft_heap) implementation. |
| &#10060; | Link/Cut Tree                        | *TODO*                             | A [link/cut tree](https://en.wikipedia.org/wiki/Link/cut_tree) implementation. |
| &#10060; | Rope                                 | *TODO*                             | An implementation of a [rope](https://en.wikipedia.org/wiki/Rope_(data_structure)) for efficient string manipulation. |
| &#10060; | GADDAG                               | *TODO*                             | A [GADDAG](https://en.wikipedia.org/wiki/GADDAG) implementation. |
| &#10060; | Burrows–Wheeler Transform            | *TODO*                             | An implementation of the [Burrows-Wheeler transform](https://en.wikipedia.org/wiki/Burrows%E2%80%93Wheeler_transform). |
| &#10060; | Seam Carving                         | *TODO*                             | An implementation of the [seam carving](https://en.wikipedia.org/wiki/Seam_carving) algorithm. |
| &#10060; | Bounded Priority Queue               | *TODO*                             | An implementation of a [priority queue](https://en.wikipedia.org/wiki/Priority_queue) with a fixed upper limit to its size. |
| &#10060; | Fast Fourier Transform               | *TODO*                             | An implementation of the [fast Fourier transform](https://en.wikipedia.org/wiki/Fast_Fourier_transform) algorithm. |
| &#10060; | Brodal Queue                         | *TODO*                             | A [Brodal queue](https://en.wikipedia.org/wiki/Brodal_queue) implementation for use as a priority queue. |
| &#10060; | Chan's Algorithm                     | *TODO*                             | An implementation of [Chan's algorithm](https://en.wikipedia.org/wiki/Chan%27s_algorithm). |
| &#10060; | Christofide's Algorithm              | *TODO*                             | An implementation of [Christofide's algorithm](https://en.wikipedia.org/wiki/Chan%27s_algorithm) for approximating [TSP](https://en.wikipedia.org/wiki/Travelling_salesman_problem) solutions. |
| &#9989;  | Trie                                 | [src/trie.rs](https://github.com/hadrian-reppas/rust-dsa/blob/main/src/trie.rs) | A [trie](https://en.wikipedia.org/wiki/Trie) implementation. |
| &#10060; | Radix Tree                           | *TODO*                             | A [radix tree](https://en.wikipedia.org/wiki/Radix_tree) implementation. |
| &#10060; | Ukkonen's Algorithm                  | *TODO*                             | An implementation of [Ukkonen's algorithm](https://en.wikipedia.org/wiki/Ukkonen%27s_algorithm) for constructing [suffix trees](https://en.wikipedia.org/wiki/Suffix_tree). |
| &#10060; | k-d Tree                             | *TODO*                             | A [k-d tree](https://en.wikipedia.org/wiki/K-d_tree) implementation. |
| &#10060; | Finger Tree                          | *TODO*                             | A [finger tree](https://en.wikipedia.org/wiki/Finger_tree) implementation. |
| &#10060; | Interval Tree                        | *TODO*                             | An [interval tree](https://en.wikipedia.org/wiki/Interval_tree) implementation. |
| &#10060; | Hough Transform                      | *TODO*                             | An implementation of the [Hough transform](https://en.wikipedia.org/wiki/Hough_transform). |
| &#10060; | BSP Tree                             | *TODO*                             | An implementation of a [BSP tree](https://en.wikipedia.org/wiki/Binary_space_partitioning). |
| &#10060; | Pairing Heap                         | *TODO*                             | A [pairing heap](https://en.wikipedia.org/wiki/Pairing_heap) implementation. |
| &#10060; | Fusion Tree                          | *TODO*                             | An [associative array](https://en.wikipedia.org/wiki/Associative_array) implementation backed by a [fusion tree](https://en.wikipedia.org/wiki/Fusion_tree). |
| &#10060; | Push–Relabel Algorithm               | *TODO*                             | An implementation of the [push–relabel maximum flow algorithm](https://en.wikipedia.org/wiki/Push%E2%80%93relabel_maximum_flow_algorithm). |
| &#10060; | Apostolico–Giancarlo Algorithm       | *TODO*                             | An implementation of the [Apostolico–Giancarlo algorithm](https://en.wikipedia.org/wiki/Apostolico%E2%80%93Giancarlo_algorithm). |
| &#10060; | PQ Tree                              | *TODO*                             | A [PQ tree](https://en.wikipedia.org/wiki/PQ_tree) implementation. |
| &#10060; | Bitap Algorithm                      | *TODO*                             | An implementation of the [bitap algorithm](https://en.wikipedia.org/wiki/Bitap_algorithm). |
| &#10060; | NFA                                  | *TODO*                             | An implementation of a [nondeterministic finite automaton](https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton). |
| &#10060; | DFA                                  | *TODO*                             | An implementation of a [deterministic finite automaton](https://en.wikipedia.org/wiki/Deterministic_finite_automaton). |
| &#10060; | NFA to DFA Conversion                | *TODO*                             | An implementation of the [subset construction algorithm](https://en.wikipedia.org/wiki/Subset_construction_algorithm) for conversion from [NFA](https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton) to [DFA](https://en.wikipedia.org/wiki/Deterministic_finite_automaton). |
| &#10060; | Polygon Triangulation                | *TODO*                             | *TODO* |
| &#10060; | Planarity Testing                    | *TODO*                             | *TODO* |
