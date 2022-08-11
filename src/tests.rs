#[test]
fn minstack_rs_15() {
    use crate::MinStack;

    // First, we create a new stack.
    let mut stack = MinStack::new();

    // We can push elements.
    stack.push(2);
    stack.push(3);
    stack.push(6);
    stack.push(1);

    // We can get the minimum element.
    assert_eq!(stack.get_min(), Some(&1));

    // We can peek and pop as usual.
    assert_eq!(stack.peek(), Some(&1));
    assert_eq!(stack.pop(), Some(1));

    // The min element reflects the stack's new state.
    assert_eq!(stack.get_min(), Some(&2));

    // We can iterate over the stack.
    for x in stack {
        // Prints 6, 3 and 2.
        println!("{x}");
    }

    // We can also create stacks from arrays.
    let a = MinStack::from(['s', 't', 'a', 'c', 'k']);

    // And iterators.
    let b: MinStack<_> = "stack".chars().collect();

    assert!(a == b);
}

#[test]
fn minstack_rs_74() {
    use crate::MinStack;

    let mut stack = MinStack::new();
    stack.push(5);

    assert_eq!(stack.pop(), Some(5));
    assert_eq!(stack.pop(), None);
}

#[test]
fn minstack_rs_101() {
    use crate::MinStack;

    let mut stack = MinStack::from([5]);

    assert_eq!(stack.pop(), Some(5));
    assert_eq!(stack.pop(), None);
}

#[test]
fn minstack_rs_116() {
    use crate::MinStack;

    let mut stack = MinStack::from(['a']);

    assert_eq!(stack.peek(), Some(&'a'));

    stack.pop();

    assert_eq!(stack.peek(), None);
}

#[test]
fn minstack_rs_134() {
    use crate::MinStack;

    let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);

    assert_eq!(stack.get_min(), Some(&1));

    stack.pop();

    assert_eq!(stack.get_min(), Some(&2));

    stack.clear();

    assert_eq!(stack.get_min(), None);
}

#[test]
fn minstack_rs_160() {
    use crate::MinStack;

    let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);

    assert_eq!(stack.len(), 7);

    stack.clear();

    assert_eq!(stack.len(), 0);
}

#[test]
fn minstack_rs_178() {
    use crate::MinStack;

    let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);

    assert!(!stack.is_empty());

    stack.clear();

    assert!(stack.is_empty());
}

#[test]
fn minstack_rs_196() {
    use crate::MinStack;

    let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);

    assert!(!stack.is_empty());

    stack.clear();

    assert!(stack.is_empty());
}

#[test]
fn vlist_rs_8() {
    use crate::VList;

    // First, we create a new list.
    let mut list = VList::new();

    // Then we can push values.
    list.push(4);
    list.push(1);
    list.push(3);

    // We can get values.
    assert_eq!(list.get(0), Some(&4));
    assert_eq!(list.get(1), Some(&1));
    assert_eq!(list.last(), Some(&3));

    // And pop from them off.
    assert_eq!(list.pop(), Some(3));
    assert_eq!(list.pop(), Some(1));
    assert_eq!(list.pop(), Some(4));

    assert!(list.is_empty());

    // We can also crate lists from arrays.
    let list_a = VList::from(['v', 'l', 'i', 's', 't']);

    // And iterators.
    let list_b: VList<_> = "vlist".chars().collect();

    // We can iterate over a list.
    for (a, b) in std::iter::zip(list_a, list_b) {
        assert_eq!(a, b);
    }
}

#[test]
fn vlist_rs_60() {
    use crate::VList;

    let mut list = VList::new();

    list.push(5);

    assert_eq!(list.last(), Some(&5));
}

#[test]
fn vlist_rs_87() {
    use crate::VList;

    let mut list = VList::new();

    list.push(5);

    assert_eq!(list.pop(), Some(5));
    assert_eq!(list.pop(), None);
}

#[test]
fn vlist_rs_115() {
    use crate::VList;

    let mut list = VList::from([5]);

    assert_eq!(list.last(), Some(&5));

    list.pop();

    assert_eq!(list.last(), None);
}

#[test]
fn vlist_rs_137() {
    use crate::VList;

    let list = VList::from(['a', 'b', 'c', 'd']);

    assert_eq!(list.get(0), Some(&'a'));
    assert_eq!(list.get(1), Some(&'b'));
    assert_eq!(list.get(2), Some(&'c'));
    assert_eq!(list.get(3), Some(&'d'));
    assert_eq!(list.get(4), None);
}

#[test]
fn vlist_rs_160() {
    use crate::VList;

    let full: VList<_> = (0..10).collect();
    assert_eq!(full.len(), 10);

    let empty: VList<i32> = VList::new();
    assert_eq!(empty.len(), 0);
}

#[test]
fn vlist_rs_176() {
    use crate::VList;

    let mut list = VList::from([5, 6, 4, 2, 8]);

    assert!(!list.is_empty());

    list.clear();

    assert!(list.is_empty());
}

#[test]
fn vlist_rs_194() {
    use crate::VList;

    let mut list = VList::from([5, 6, 4, 2, 8]);

    assert!(!list.is_empty());

    list.clear();

    assert!(list.is_empty());
}

#[test]
fn vlist_rs_225() {
    use crate::VList;

    let mut ints: VList<_> = (0..100_000).collect();

    for i in (0..100_000).rev() {
        assert_eq!(ints.get(i), Some(&i));
        assert_eq!(ints.pop(), Some(i));
    }
}

#[test]
fn insertion_sort_rs_7() {
    use crate::insertion_sort;

    let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
    insertion_sort(&mut ints);
    assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);

    let mut food = ["banana", "eggplant", "dragonfruit", "apple", "carrot"];
    insertion_sort(&mut food);
    assert_eq!(
        &food,
        &["apple", "banana", "carrot", "dragonfruit", "eggplant"]
    );

    let mut random: Vec<i64> = (0..1_000).map(|_| rand::random()).collect();
    insertion_sort(&mut random);
    for i in 1..random.len() {
        assert!(random[i - 1] <= random[i]);
    }
}

#[test]
fn quicksort_rs_8() {
    use crate::quicksort;

    let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
    quicksort(&mut ints);
    assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);

    let mut food = ["banana", "eggplant", "dragonfruit", "apple", "carrot"];
    quicksort(&mut food);
    assert_eq!(
        &food,
        &["apple", "banana", "carrot", "dragonfruit", "eggplant"]
    );

    let mut random: Vec<i64> = (0..100_000).map(|_| rand::random()).collect();
    quicksort(&mut random);
    for i in 1..random.len() {
        assert!(random[i - 1] <= random[i]);
    }
}

#[test]
fn graph_rs_18() {
    use crate::Graph;

    // First, we create a new graph.
    let mut graph = Graph::new();

    // Then we can add nodes.
    graph.insert_node('a');
    graph.insert_node('b');
    graph.insert_node('c');

    assert_eq!(graph.len(), 3);
    assert!(graph.contains_node(&'a'));
    assert!(graph.contains_node(&'b'));
    assert!(graph.contains_node(&'c'));

    // And edges between those nodes.
    graph.insert_edge(&'a', &'b');
    graph.insert_edge(&'a', &'c');
    graph.insert_edge(&'c', &'b');

    assert!(graph.contains_edge(&'a', &'b'));
    assert!(graph.contains_edge(&'a', &'c'));
    assert!(graph.contains_edge(&'c', &'b'));

    assert!(graph.contains_edge(&'b', &'a'));
    assert!(graph.contains_edge(&'c', &'a'));
    assert!(graph.contains_edge(&'b', &'c'));

    // Missing edge nodes are automatically inserted.
    graph.insert_edge(&'a', &'z');

    assert!(graph.contains_node(&'z'));
    assert!(graph.contains_edge(&'a', &'z'));
    assert!(graph.contains_edge(&'z', &'a'));

    // Edges can be removed.
    graph.remove_edge(&'a', &'z');

    assert!(!graph.contains_edge(&'a', &'z'));
    assert!(!graph.contains_edge(&'z', &'a'));

    // Nodes too.
    graph.remove_node(&'z');

    assert!(!graph.contains_node(&'z'));

    // We can iterate over a node's neighbors.
    for neighbor in graph.neighbors_of(&'a') {
        // Prints "b" and "c" in an arbitrary order.
        println!("{neighbor}");
    }

    // We can also iterate over all edges in the graph.
    for (u, v) in graph.edges() {
        // Prints "a -> b", "b -> a", "a -> c", "c -> a", "c -> b"
        // and "b -> c" in an arbitrary order.
        println!("{u} -> {v}");
    }

    // Or just the unique edges.
    for (u, v) in graph.unique_edges() {
        // Prints "a -> b" or "b -> a", "a -> c" or "c -> a"
        // and "c -> b" or "b -> c" in an arbitrary order.
        println!("{u} -> {v}");
    }

    // And iterate over all nodes
    for node in graph {
        // Prints "a", "b" and "c" in an arbitrary order.
        println!("{node}");
    }
}

#[test]
fn graph_rs_107() {
    use crate::Graph;

    let mut graph = Graph::new();
    graph.insert_node(1);

    assert!(graph.contains_node(&1));
}

#[test]
fn graph_rs_128() {
    use crate::Graph;

    let mut graph = Graph::new();
    graph.insert_edge(&true, &false);

    assert!(graph.contains_edge(&true, &false));
    assert!(graph.contains_node(&true));
    assert!(graph.contains_node(&false));
}

#[test]
fn graph_rs_149() {
    use crate::Graph;

    let foo = "foo".to_string();
    let bar = "bar".to_string();

    let mut graph = Graph::new();
    graph.insert_node(foo.clone());
    graph.insert_node(bar);

    assert!(graph.contains_node(&foo));

    assert!(graph.remove_node(&foo));

    assert!(!graph.contains_node(&foo));

    assert!(!graph.remove_node(&foo));
}

#[test]
fn graph_rs_177() {
    use crate::Graph;

    let mut graph = Graph::from([(1, 2), (1, 3)]);

    assert!(graph.contains_edge(&1, &2));

    assert!(graph.remove_edge(&1, &2));

    assert!(!graph.contains_edge(&1, &2));

    assert!(!graph.remove_edge(&1, &2));
}

#[test]
fn graph_rs_201() {
    use crate::Graph;

    let mut graph = Graph::new();

    graph.insert_node(1);

    assert!(graph.contains_node(&1));
    assert!(!graph.contains_node(&2));
}

#[test]
fn graph_rs_221() {
    use crate::Graph;

    let graph = Graph::from([('a', 'b'), ('b', 'c'), ('b', 'd')]);

    assert!(graph.contains_edge(&'b', &'c'));
    assert!(!graph.contains_edge(&'c', &'d'));
}

#[test]
fn graph_rs_239() {
    use crate::Graph;

    let graph: Graph<_> = (0..42).collect();

    assert_eq!(graph.len(), 42);
}

#[test]
fn graph_rs_253() {
    use crate::Graph;

    let mut graph: Graph<_> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn graph_rs_271() {
    use crate::Graph;

    let mut graph: Graph<_> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn graph_rs_292() {
    use crate::Graph;
    use std::collections::HashSet;

    let graph = Graph::from([(1, 2), (1, 3), (1, 4), (4, 3), (3, 2)]);

    let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();

    assert_eq!(HashSet::from([&2, &3, &4]), neighbors,);
}

#[test]
fn graph_rs_325() {
    use crate::Graph;

    let mut graph = Graph::new();
    graph.insert_edge(&1, &3);
    graph.insert_edge(&3, &2);

    for (u, v) in graph.edges() {
        // Prints "1 -> 3", "3 -> 1", "3 -> 2" and
        // "2 -> 3" in an arbitrary order.
        println!("{u} -> {v}");
    }
}

#[test]
fn graph_rs_350() {
    use crate::Graph;

    let mut graph = Graph::new();
    graph.insert_edge(&1, &3);
    graph.insert_edge(&3, &2);

    for (u, v) in graph.unique_edges() {
        // Prints "1 -> 3" or "3 -> 1" and "3 -> 2" or "2 -> 3"
        // in an arbitrary order.
        println!("{u} -> {v}");
    }
}

#[test]
fn graph_rs_389() {
    use crate::Graph;

    let mut a = Graph::new();
    a.insert_edge(&1, &2);
    a.insert_edge(&3, &2);
    a.insert_edge(&1, &2);
    a.remove_edge(&2, &1);

    let mut b: Graph<_> = [1, 2, 3].into_iter().collect();
    b.insert_edge(&2, &3);

    assert!(a == b);
}

#[test]
fn deque_rs_10() {
    use crate::Deque;

    // First, we create a new deque.
    let mut deque = Deque::new();

    // Then we can push values onto the front or back.
    deque.push_back(4);
    deque.push_back(1);
    deque.push_front(3);

    // And pop from the front or back.
    assert_eq!(deque.pop_back(), Some(1));
    assert_eq!(deque.pop_front(), Some(3));
    assert_eq!(deque.pop_front(), Some(4));

    // We can also crate deques from arrays.
    let deque_a = Deque::from(['d', 'e', 'q', 'u', 'e']);

    // And iterators.
    let deque_b: Deque<_> = "deque".chars().collect();

    // We can iterate over a deque.
    for (a, b) in std::iter::zip(deque_a, deque_b) {
        assert_eq!(a, b);
    }

    let mut deque = Deque::from([1, 2, 3, 4, 5]);
    for i in 0..1_000_000 {
        deque.pop_front();
        deque.push_back(i);
    }
    // After pushing and poping a million elements,
    // the capacity is still 5.
    assert_eq!(deque.capacity(), 5);

    assert_eq!(
        deque.into_iter().collect::<Vec<_>>(),
        vec![999_995, 999_996, 999_997, 999_998, 999_999]
    );
}

#[test]
fn deque_rs_82() {
    use crate::Deque;

    let deque: Deque<u8> = Deque::with_capacity(10);

    assert_eq!(deque.capacity(), 10);
}

#[test]
fn deque_rs_101() {
    use crate::Deque;

    let mut deque = Deque::new();

    deque.push_back(5);

    assert_eq!(deque.peek_back(), Some(&5));
}

#[test]
fn deque_rs_123() {
    use crate::Deque;

    let mut deque = Deque::new();

    deque.push_front(5);

    assert_eq!(deque.peek_front(), Some(&5));
}

#[test]
fn deque_rs_145() {
    use crate::Deque;

    let mut deque = Deque::from([1, 2, 3]);

    assert_eq!(deque.pop_back(), Some(3));
    assert_eq!(deque.pop_back(), Some(2));
    assert_eq!(deque.pop_back(), Some(1));
    assert_eq!(deque.pop_back(), None);
}

#[test]
fn deque_rs_170() {
    use crate::Deque;

    let mut deque = Deque::from([1, 2, 3]);

    assert_eq!(deque.pop_front(), Some(1));
    assert_eq!(deque.pop_front(), Some(2));
    assert_eq!(deque.pop_front(), Some(3));
    assert_eq!(deque.pop_front(), None);
}

#[test]
fn deque_rs_195() {
    use crate::Deque;

    let deque = Deque::from(['a', 'b', 'c']);

    assert_eq!(deque.peek_back(), Some(&'c'));

    let empty: Deque<u8> = Deque::new();
    assert_eq!(empty.peek_back(), None);
}

#[test]
fn deque_rs_218() {
    use crate::Deque;

    let deque = Deque::from(['a', 'b', 'c']);

    assert_eq!(deque.peek_front(), Some(&'a'));

    let empty: Deque<u8> = Deque::new();
    assert_eq!(empty.peek_front(), None);
}

#[test]
fn deque_rs_243() {
    use crate::Deque;

    let mut deque = Deque::from(['a', 'b', 'c']);

    assert_eq!(deque.get(1), Some(&'b'));

    deque.pop_front();
    assert_eq!(deque.get(1), Some(&'c'));

    deque.pop_front();
    assert_eq!(deque.get(1), None);
}

#[test]
fn deque_rs_276() {
    use crate::Deque;

    let mut deque: Deque<_> = ('a'..='z').collect();

    let mut drain = deque.drain(1..25);
    assert_eq!(drain.next(), Some('b'));
    assert_eq!(drain.next(), Some('c'));
    // etc...

    // Now, deque is just ['a', 'z']
    assert_eq!(deque.pop_front(), Some('a'));
    assert_eq!(deque.pop_front(), Some('z'));
    assert_eq!(deque.pop_front(), None);
}

#[test]
fn deque_rs_315() {
    use crate::Deque;

    let full: Deque<_> = (0..10).collect();
    assert_eq!(full.len(), 10);

    let empty: Deque<bool> = Deque::new();
    assert_eq!(empty.len(), 0);
}

#[test]
fn deque_rs_331() {
    use crate::Deque;

    let empty: Deque<bool> = Deque::new();
    assert!(empty.is_empty());

    let full: Deque<_> = (0..10).collect();
    assert!(!full.is_empty());
}

#[test]
fn deque_rs_347() {
    use crate::Deque;

    let mut deque = Deque::from([1, 2, 3]);

    assert!(!deque.is_empty());

    deque.clear();

    assert!(deque.is_empty());
}

#[test]
fn deque_rs_365() {
    use crate::Deque;

    let mut deque = Deque::with_capacity(10);
    deque.push_back("foo");
    deque.push_back("bar");

    assert_eq!(deque.capacity(), 10);
    assert_eq!(deque.len(), 2);

    deque.shrink_to_fit();

    assert_eq!(deque.capacity(), 2);
    assert_eq!(deque.len(), 2);
}

#[test]
fn deque_rs_388() {
    use crate::Deque;

    let mut deque = Deque::with_capacity(10);

    assert_eq!(deque.capacity(), 10);

    for i in 0..20 {
        deque.push_back(i);
    }

    assert!(deque.capacity() > 10);
}

#[test]
fn heap_rs_11() {
    use crate::BinaryHeap;

    // First, we create a new heap.
    let mut heap = BinaryHeap::new();

    // Then we can add items in any order.
    heap.insert(4);
    heap.insert(1);
    heap.insert(3);

    // We can peek at the minimum item.
    assert_eq!(heap.peek(), Some(&1));

    // And pop them off in ascending order.
    assert_eq!(heap.pop(), Some(1));
    assert_eq!(heap.pop(), Some(3));
    assert_eq!(heap.pop(), Some(4));
    assert_eq!(heap.pop(), None);

    // We can also create heaps from arrays.
    let mut heap = BinaryHeap::from([2, 6, 2]);

    // And heaps can contain duplicate items.
    assert_eq!(heap.pop(), Some(2));
    assert_eq!(heap.pop(), Some(2));

    assert_eq!(heap.len(), 1);
}

#[test]
fn heap_rs_63() {
    use crate::BinaryHeap;

    let mut heap = BinaryHeap::new();
    heap.insert(4);
    heap.insert(1);
    heap.insert(3);

    assert_eq!(heap.len(), 3);
    assert_eq!(heap.peek(), Some(&1));
}

#[test]
fn heap_rs_85() {
    use crate::BinaryHeap;

    let mut heap = BinaryHeap::from([2, 1]);
    assert_eq!(heap.peek(), Some(&1));

    heap.clear();
    assert_eq!(heap.peek(), None);
}

#[test]
fn heap_rs_102() {
    use crate::BinaryHeap;

    let mut heap = BinaryHeap::from([4, 1, 3]);

    assert_eq!(heap.pop(), Some(1));
    assert_eq!(heap.pop(), Some(3));
    assert_eq!(heap.pop(), Some(4));
    assert_eq!(heap.pop(), None);
}

#[test]
fn heap_rs_128() {
    use crate::BinaryHeap;

    let mut heap = BinaryHeap::from([1, 2, 3]);
    assert_eq!(heap.len(), 3);

    heap.clear();
    assert_eq!(heap.len(), 0);
}

#[test]
fn heap_rs_144() {
    use crate::BinaryHeap;

    let mut heap = BinaryHeap::from([1, 2]);
    assert!(!heap.is_empty());

    heap.clear();
    assert!(heap.is_empty());
}

#[test]
fn heap_rs_160() {
    use crate::BinaryHeap;

    let mut heap = BinaryHeap::from([1, 2]);

    heap.clear();
    assert!(heap.is_empty());
}

#[test]
fn heap_rs_225() {
    use crate::BinaryHeap;

    let heap = BinaryHeap::from([4, 2, 3, 1]);

    for x in heap {
        // prints 1, 2, 3, 4
        println!("{x}");
    }
}

#[test]
fn toposort_rs_11() {
    use crate::{topological_sort, DiGraph};

    //    +---+      +---+      +---+
    //    |'a'| ---> |'b'| ---> |'c'|
    //    +---+      +---+      +---+
    let no_cycle = DiGraph::from([('a', 'b'), ('b', 'c')]);

    assert_eq!(topological_sort(&no_cycle), Some(vec![&'a', &'b', &'c']));

    //    +---+      +---+
    //    | 1 | ---> | 2 |
    //    +---+      +---+
    //      ^          |
    //      |          v
    //      |        +---+      +---+
    //      +------- | 3 | ---> | 4 |
    //               +---+      +---+
    let with_cycle = DiGraph::from([(1, 2), (2, 3), (3, 4), (3, 1)]);

    // `with_cycle` contains a cycle so `topological_sort` returns `None`
    assert_eq!(topological_sort(&with_cycle), None);

    use crate::is_topological_sort;

    let big_graph = DiGraph::from([
        (1, 2),
        (2, 3),
        (4, 3),
        (3, 5),
        (5, 6),
        (6, 7),
        (7, 8),
        (5, 9),
        (9, 10),
        (5, 10),
        (10, 11),
        (10, 8),
        (5, 12),
        (12, 13),
        (12, 14),
        (12, 8),
        (8, 15),
    ]);

    // `big_graph` is acyclic
    let sort = topological_sort(&big_graph).unwrap();

    assert!(is_topological_sort(&big_graph, sort));
}

#[test]
fn toposort_rs_146() {
    use crate::{is_topological_sort, DiGraph};

    //    +---+      +---+      +---+
    //    |'a'| ---> |'b'| ---> |'c'|
    //    +---+      +---+      +---+
    let graph = DiGraph::from([('a', 'b'), ('b', 'c')]);

    assert!(is_topological_sort(&graph, vec![&'a', &'b', &'c']));

    assert!(!is_topological_sort(&graph, vec![&'b', &'a', &'c']));
}

#[test]
fn ivector_rs_13() {
    use crate::ImmutableVector;

    let vector = ImmutableVector::new();

    // Each time we push a value, the original vector doesn't change.
    let vector1 = vector.push(1);
    let vector2 = vector1.push(2);
    let vector3 = vector2.push(3);

    assert_eq!(vector, ImmutableVector::from([]));
    assert_eq!(vector1, ImmutableVector::from([1]));
    assert_eq!(vector2, ImmutableVector::from([1, 2]));
    assert_eq!(vector3, ImmutableVector::from([1, 2, 3]));

    // We can also remove elements.
    let vector4 = vector3.remove(1);
    assert_eq!(vector4, ImmutableVector::from([1, 3]));

    // And join two vectors.
    let vector5 = vector4.join(&vector2);
    assert_eq!(vector5, ImmutableVector::from([1, 3, 1, 2]));

    // We can iterate over vectors.
    for x in vector5 {
        // x has type Rc<i32>
        println!("{x}");
    }

    for x in &vector4 {
        // x has type &i32
        println!("{x}");
    }

    // And create vectors from iterators.
    let vector6: ImmutableVector<_> = ('a'..='z').collect();
    assert_eq!(vector6.len(), 26);
}

#[test]
fn ivector_rs_77() {
    use crate::ImmutableVector;

    let vector = ImmutableVector::from([1, 2, 3, 4, 5, 6, 7]);

    assert_eq!(vector.get(3), Some(&4));
    assert_eq!(vector.get(10), None);
}

#[test]
fn ivector_rs_96() {
    use crate::ImmutableVector;

    let racecar: ImmutableVector<_> = "racecar".chars().collect();
    let car: ImmutableVector<_> = "car".chars().collect();

    assert_eq!(racecar.range(4..), car);
}

#[test]
fn ivector_rs_117() {
    use crate::ImmutableVector;
    use std::rc::Rc;

    let vector = ImmutableVector::from([1, 2, 3, 4, 5, 6, 7]);

    assert_eq!(vector.get_rc(3), Some(Rc::new(4)));
    assert_eq!(vector.get_rc(10), None);
}

#[test]
fn ivector_rs_133() {
    use crate::ImmutableVector;

    let vector = ImmutableVector::new();
    let vector = vector.push(1);
    let vector = vector.push(2);
    let vector = vector.push(3);

    assert_eq!(vector, ImmutableVector::from([1, 2, 3]));
}

#[test]
fn ivector_rs_155() {
    use crate::ImmutableVector;

    let feast: ImmutableVector<_> = "feast".chars().collect();

    let east = feast.remove(0);

    assert_eq!(east, ImmutableVector::from(['e', 'a', 's', 't']));
}

#[test]
fn ivector_rs_179() {
    use crate::ImmutableVector;

    let unseasonably: ImmutableVector<_> = "unseasonably".chars().collect();
    let unreasonably: ImmutableVector<_> = "unreasonably".chars().collect();

    assert_eq!(unseasonably.replace(2, 'r'), unreasonably);
}

#[test]
fn ivector_rs_200() {
    use crate::ImmutableVector;

    let fruits = ImmutableVector::from(["apple", "banana"]);
    let veggies = ImmutableVector::from(["asparagus", "broccoli"]);

    let both = fruits.join(&veggies);

    assert_eq!(
        both,
        ImmutableVector::from(["apple", "banana", "asparagus", "broccoli"])
    );
}

#[test]
fn ivector_rs_225() {
    use crate::ImmutableVector;

    let empty: ImmutableVector<bool> = ImmutableVector::new();
    let forty: ImmutableVector<_> = (0..40).collect();

    assert_eq!(empty.len(), 0);
    assert_eq!(forty.len(), 40);
}

#[test]
fn ivector_rs_241() {
    use crate::ImmutableVector;

    let empty: ImmutableVector<bool> = ImmutableVector::new();
    let forty: ImmutableVector<_> = (0..40).collect();

    assert!(empty.is_empty());
    assert!(!forty.is_empty());
}

#[test]
fn wgraph_rs_15() {
    use crate::WeightedGraph;

    // First, we create a new graph.
    let mut graph = WeightedGraph::new();

    // Then we can add nodes.
    graph.insert_node('a');
    graph.insert_node('b');
    graph.insert_node('c');

    assert_eq!(graph.len(), 3);
    assert!(graph.contains_node(&'a'));
    assert!(graph.contains_node(&'b'));
    assert!(graph.contains_node(&'c'));

    // And edges between those nodes.
    graph.insert_edge(&'a', &'b', 5);
    graph.insert_edge(&'a', &'c', 1);
    graph.insert_edge(&'c', &'b', 4);

    assert_eq!(graph.get_edge(&'a', &'b'), Some(&5));
    assert_eq!(graph.get_edge(&'a', &'c'), Some(&1));
    assert_eq!(graph.get_edge(&'c', &'b'), Some(&4));

    // Missing edge nodes are automatically inserted.
    graph.insert_edge(&'a', &'z', -1);

    assert!(graph.contains_node(&'z'));
    assert!(graph.contains_edge(&'a', &'z'));

    // Edges can be removed.
    graph.remove_edge(&'a', &'z');

    assert!(!graph.contains_edge(&'a', &'z'));

    // Nodes too.
    graph.remove_node(&'z');

    assert!(!graph.contains_node(&'z'));

    // We can iterate over a node's neighbors.
    for (neighbor, weight) in graph.neighbors_of(&'a') {
        // Prints "b (5)" and "c (1)" in an arbitrary order.
        println!("{neighbor} ({weight})");
    }

    // We can also iterate over all edges in the graph.
    for (from, to, weight) in graph.edges() {
        // Prints "a -> b (5)", "b -> a (5)", "a -> c (1)", "c -> a (1)",
        // "c -> b (4)" and "b -> c (4)" in an arbitrary order.
        println!("{from} -> {to} ({weight})");
    }

    // Or just the unique edges.
    for (from, to, weight) in graph.unique_edges() {
        // Prints "a -> b (5)" or "b -> a (5)", "a -> c (1)" or "c -> a (1)"
        // and "c -> b (4)" or "b -> c (4)" in an arbitrary order.
        println!("{from} -> {to} ({weight})");
    }

    // And iterate over all nodes
    for node in graph {
        // Prints "a", "b" and "c" in an arbitrary order.
        println!("{node}");
    }
}

#[test]
fn wgraph_rs_98() {
    use crate::WeightedGraph;

    let mut graph: WeightedGraph<_, bool> = WeightedGraph::new();
    graph.insert_node(1);

    assert!(graph.contains_node(&1));
}

#[test]
fn wgraph_rs_119() {
    use crate::WeightedGraph;

    let mut graph = WeightedGraph::new();
    graph.insert_edge(&true, &false, 'a');

    assert!(graph.contains_edge(&true, &false));
    assert!(graph.contains_node(&true));
    assert!(graph.contains_node(&false));
}

#[test]
fn wgraph_rs_141() {
    use crate::WeightedGraph;

    let foo = "foo".to_string();
    let bar = "bar".to_string();

    let mut graph: WeightedGraph<_, i32> = WeightedGraph::new();
    graph.insert_node(foo.clone());
    graph.insert_node(bar);

    assert!(graph.contains_node(&foo));

    graph.remove_node(&foo);

    assert!(!graph.contains_node(&foo));
}

#[test]
fn wgraph_rs_167() {
    use crate::WeightedGraph;

    let mut graph = WeightedGraph::from([(1, 2, 'a'), (1, 3, 'b')]);

    assert!(graph.contains_edge(&1, &2));

    assert_eq!(graph.remove_edge(&1, &2), Some('a'));

    assert!(!graph.contains_edge(&1, &2));

    assert_eq!(graph.remove_edge(&1, &2), None);
}

#[test]
fn wgraph_rs_191() {
    use crate::WeightedGraph;

    let mut graph: WeightedGraph<_, f64> = WeightedGraph::new();

    graph.insert_node(1);

    assert!(graph.contains_node(&1));
    assert!(!graph.contains_node(&2));
}

#[test]
fn wgraph_rs_211() {
    use crate::WeightedGraph;

    let graph = WeightedGraph::from([('a', 'b', true), ('b', 'c', true), ('b', 'd', true)]);

    assert!(graph.contains_edge(&'b', &'c'));
    assert!(!graph.contains_edge(&'c', &'d'));
}

#[test]
fn wgraph_rs_233() {
    use crate::WeightedGraph;

    let graph = WeightedGraph::from([('a', 'b', 1), ('b', 'c', 2), ('b', 'd', 3)]);

    assert_eq!(graph.get_edge(&'c', &'b'), Some(&2));
    assert_eq!(graph.get_edge(&'c', &'d'), None);
}

#[test]
fn wgraph_rs_255() {
    use crate::WeightedGraph;

    let graph: WeightedGraph<_, u8> = (0..42).collect();

    assert_eq!(graph.len(), 42);
}

#[test]
fn wgraph_rs_269() {
    use crate::WeightedGraph;

    let mut graph: WeightedGraph<_, i32> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn wgraph_rs_287() {
    use crate::WeightedGraph;

    let mut graph: WeightedGraph<_, i32> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn wgraph_rs_308() {
    use crate::WeightedGraph;
    use std::collections::HashSet;

    let graph = WeightedGraph::from([
        (1, 2, 'a'),
        (1, 3, 'b'),
        (1, 4, 'c'),
        (4, 3, 'd'),
        (3, 2, 'z'),
    ]);

    let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();

    assert_eq!(
        HashSet::from([(&2, &'a'), (&3, &'b'), (&4, &'c')]),
        neighbors,
    );
}

#[test]
fn wgraph_rs_339() {
    use crate::WeightedGraph;

    let mut graph = WeightedGraph::new();
    graph.insert_edge(&1, &3, 'a');
    graph.insert_edge(&3, &2, 'b');

    for (from, to, weight) in graph.edges() {
        // Prints "1 -> 3 (a)", "3 -> 1 (a)", "3 -> 2 (b)" and
        // "2 -> 3 (b)" in an arbitrary order.
        println!("{from} -> {to} ({weight})");
    }
}

#[test]
fn wgraph_rs_362() {
    use crate::WeightedGraph;

    let mut graph = WeightedGraph::new();
    graph.insert_edge(&1, &3, 'a');
    graph.insert_edge(&3, &2, 'b');

    for (from, to, weight) in graph.edges() {
        // Prints "1 -> 3 (a)" or "3 -> 1 (a)" and "3 -> 2 (b)" or "2 -> 3 (b)"
        // in an arbitrary order.
        println!("{from} -> {to} ({weight})");
    }
}

#[test]
fn wgraph_rs_400() {
    use crate::WeightedGraph;

    let mut a = WeightedGraph::new();
    a.insert_edge(&1, &2, 'a');
    a.insert_edge(&3, &2, 'b');
    a.remove_edge(&2, &1);

    let mut b: WeightedGraph<_, _> = [1, 2, 3].into_iter().collect();
    b.insert_edge(&3, &2, 'b');

    assert!(a == b);

    let mut c = WeightedGraph::new();
    c.insert_node(1);
    c.insert_edge(&3, &2, 'b');
    c.insert_node(4);

    assert!(a != c);

    c.remove_node(&4);

    assert!(a == c);
}

#[test]
fn trie_rs_7() {
    use crate::GenericTrie;

    // First, we create a new trie.
    let mut trie = GenericTrie::new();

    // Then we can insert keys and items.
    trie.insert(&[1, 2, 3], "foo");
    trie.insert(&[1, 2, 4], "bar");
    trie.insert(&[1, 2, 4, 0], "baz");

    assert!(trie.contains_key(&[1, 2, 3]));
    assert!(trie.contains_key(&[1, 2, 4]));
    assert!(trie.contains_key(&[1, 2, 4, 0]));

    // We can get the values.
    assert_eq!(trie.get(&[1, 2, 3]), Some(&"foo"));
    assert_eq!(trie.get(&[1, 2, 4]), Some(&"bar"));
    assert_eq!(trie.get(&[1, 2]), None);

    // We can iterate over the values with a given prefix.
    use std::collections::HashSet;
    let get_prefix: HashSet<_> = trie.get_prefix(&[1, 2, 4]).collect();
    assert_eq!(get_prefix, HashSet::from([&"bar", &"baz"]));

    // We can remove values.
    let removed = trie.remove(&[1, 2, 3]);

    assert_eq!(removed, Some("foo"));
    assert!(!trie.contains_key(&[1, 2, 3]));

    assert_eq!(trie.len(), 2);
}

#[test]
fn trie_rs_59() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();

    trie.insert(&['c', 'a', 'b'], 0);
    trie.insert(&['c', 'a', 'r'], 0);
    trie.insert(&['c'], 0);

    assert!(trie.contains_key(&['c', 'a', 'b']));
    assert!(trie.contains_key(&['c', 'a', 'r']));
    assert!(trie.contains_key(&['c']));
}

#[test]
fn trie_rs_96() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();

    trie.insert(&['c', 'a', 'b'], 1);
    trie.insert(&['c', 'a', 'r'], 2);

    assert_eq!(trie.get(&['c', 'a', 'b']), Some(&1));
    assert_eq!(trie.get(&['c', 'a', 'r']), Some(&2));
    assert_eq!(trie.get(&['c', 'a', 't']), None);
}

#[test]
fn trie_rs_121() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();

    trie.insert(&[1, 2, 3], 'a');
    trie.insert(&[1, 2, 4], 'b');

    assert_eq!(trie.get(&[1, 2, 3]), Some(&'a'));
    assert_eq!(trie.get(&[1, 2, 4]), Some(&'b'));

    let removed = trie.remove(&[1, 2, 3]);

    assert_eq!(removed, Some('a'));
    assert!(!trie.contains_key(&[1, 2, 3]));
}

#[test]
fn trie_rs_153() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();

    trie.insert(&[1, 2, 3], 'a');
    trie.insert(&[1, 2, 3, 4], 'b');
    trie.insert(&[1, 2], 'c');
    trie.insert(&[1], 'd');

    use std::collections::HashSet;
    assert_eq!(
        trie.get_prefix(&[1, 2]).collect::<HashSet<_>>(),
        HashSet::from([&'a', &'b', &'c'])
    );
}

#[test]
fn trie_rs_186() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();
    trie.insert(&[true, true, false], 0);

    assert!(trie.contains_key(&[true, true, false]));
    assert!(!trie.contains_key(&[true, false]));
}

#[test]
fn trie_rs_212() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();
    trie.insert(&[true, true, false], 0);

    assert!(trie.contains_prefix(&[true, true, false]));
    assert!(trie.contains_prefix(&[true, true]));
    assert!(trie.contains_prefix(&[true]));
    assert!(!trie.contains_prefix(&[false]));
    assert!(!trie.contains_prefix(&[true, false]));
}

#[test]
fn trie_rs_243() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();
    trie.insert(&[1, 2, 3], 'a');
    trie.insert(&[1, 2], 'b');
    trie.insert(&[1, 2, 3], 'c');

    assert_eq!(trie.len(), 2);

    trie.remove(&[1, 2]);

    assert_eq!(trie.len(), 1);
}

#[test]
fn trie_rs_268() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();
    trie.insert(&[1, 2, 3], 'a');
    trie.insert(&[1, 2], 'b');

    assert!(!trie.is_empty());

    trie.clear();

    assert!(trie.is_empty());
}

#[test]
fn trie_rs_288() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();
    trie.insert(&[1, 2, 3], 'a');
    trie.insert(&[1, 2], 'b');

    assert!(!trie.is_empty());

    trie.clear();

    assert!(trie.is_empty());
}

#[test]
fn trie_rs_309() {
    use crate::GenericTrie;

    let mut trie = GenericTrie::new();

    trie.insert(&[1, 2, 3], 'a');
    trie.insert(&[1, 2, 3, 4], 'b');
    trie.insert(&[1, 2], 'c');
    trie.insert(&[1], 'd');

    use std::collections::HashSet;
    assert_eq!(
        trie.values().collect::<HashSet<_>>(),
        HashSet::from([&'a', &'b', &'c', &'d'])
    );
}

#[test]
fn trie_rs_355() {
    use crate::GenericTrie;

    let mut a = GenericTrie::new();
    a.insert(&['a', 'b', 'c'], 1);
    a.insert(&['a', 'x'], 2);

    let mut b = GenericTrie::new();
    b.insert(&['a', 'b', 'c'], 1);
    b.insert(&['a', 'x'], 2);
    b.insert(&['z'], 3);

    assert!(a != b);

    b.remove(&['z']);

    assert!(a == b);
}

#[test]
fn trie_rs_435() {
    use crate::Trie;

    // First, we create a new trie.
    let mut trie = Trie::new();

    // Then we can insert keys and items.
    trie.insert("foo", 1);
    trie.insert("bar", 2);
    trie.insert("ba", 3);

    assert!(trie.contains_key("foo"));
    assert!(trie.contains_key("bar"));
    assert!(trie.contains_key("ba"));

    // We can get the values.
    assert_eq!(trie.get("foo"), Some(&1));
    assert_eq!(trie.get("bar"), Some(&2));
    assert_eq!(trie.get("ba"), Some(&3));
    assert_eq!(trie.get("baz"), None);

    // We can iterate over the values with a given prefix.
    use std::collections::HashSet;
    let get_prefix: HashSet<_> = trie.get_prefix("ba").collect();
    assert_eq!(get_prefix, HashSet::from([&2, &3]));

    // We can remove values.
    let removed = trie.remove("ba");

    assert_eq!(removed, Some(3));
    assert!(!trie.contains_key("ba"));

    assert_eq!(trie.len(), 2);
}

#[test]
fn trie_rs_486() {
    use crate::Trie;

    let mut trie = Trie::new();

    trie.insert("cab", 0);
    trie.insert("car", 0);
    trie.insert("c", 0);

    assert!(trie.contains_key("cab"));
    assert!(trie.contains_key("car"));
    assert!(trie.contains_key("c"));
}

#[test]
fn trie_rs_507() {
    use crate::Trie;

    let mut trie = Trie::new();

    trie.insert("cab", 1);
    trie.insert("car", 2);

    assert_eq!(trie.get("cab"), Some(&1));
    assert_eq!(trie.get("car"), Some(&2));
    assert_eq!(trie.get("cat"), None);
}

#[test]
fn trie_rs_527() {
    use crate::Trie;

    let mut trie = Trie::new();

    trie.insert("foo", 1);
    trie.insert("bar", 2);

    assert_eq!(trie.get("foo"), Some(&1));
    assert_eq!(trie.get("bar"), Some(&2));

    let removed = trie.remove("foo");

    assert_eq!(removed, Some(1));
    assert!(!trie.contains_key("foo"));
}

#[test]
fn trie_rs_551() {
    use crate::Trie;

    let mut trie = Trie::new();

    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("ab", 3);
    trie.insert("a", 4);

    use std::collections::HashSet;
    assert_eq!(
        trie.get_prefix("ab").collect::<HashSet<_>>(),
        HashSet::from([&1, &2, &3])
    );
}

#[test]
fn trie_rs_575() {
    use crate::Trie;

    let mut trie = Trie::new();
    trie.insert("cat", 0);

    assert!(trie.contains_key("cat"));
    assert!(!trie.contains_key("ca"));
}

#[test]
fn trie_rs_592() {
    use crate::Trie;

    let mut trie = Trie::new();
    trie.insert("xyz", 0);

    assert!(trie.contains_prefix("xyz"));
    assert!(trie.contains_prefix("xy"));
    assert!(trie.contains_prefix("x"));
    assert!(!trie.contains_prefix("y"));
    assert!(!trie.contains_prefix("xz"));
}

#[test]
fn trie_rs_612() {
    use crate::Trie;

    let mut trie = Trie::new();
    trie.insert("abc", 1);
    trie.insert("ab", 2);
    trie.insert("abc", 3);

    assert_eq!(trie.len(), 2);

    trie.remove("ab");

    assert_eq!(trie.len(), 1);
}

#[test]
fn trie_rs_633() {
    use crate::Trie;

    let mut trie = Trie::new();
    trie.insert("abc", 1);
    trie.insert("ab", 2);

    assert!(!trie.is_empty());

    trie.clear();

    assert!(trie.is_empty());
}

#[test]
fn trie_rs_653() {
    use crate::Trie;

    let mut trie = Trie::new();
    trie.insert("abc", 1);
    trie.insert("ab", 2);

    assert!(!trie.is_empty());

    trie.clear();

    assert!(trie.is_empty());
}

#[test]
fn trie_rs_673() {
    use crate::Trie;

    let mut trie = Trie::new();

    trie.insert("abc", 1);
    trie.insert("abcd", 2);
    trie.insert("ab", 3);
    trie.insert("a", 4);

    use std::collections::HashSet;
    assert_eq!(
        trie.values().collect::<HashSet<_>>(),
        HashSet::from([&1, &2, &3, &4])
    );
}

#[test]
fn trie_rs_714() {
    use crate::Trie;

    let trie = Trie::from([("foo", 1), ("bar", 2), ("baz", 3)]);
    assert_eq!(trie.get("foo"), Some(&1));
    assert_eq!(trie.get("bar"), Some(&2));
    assert_eq!(trie.get("baz"), Some(&3));
    assert_eq!(trie.get("boo"), None);
}

#[test]
fn graham_rs_19() {
    use crate::graham_scan;

    let points = [
        (6, 0),
        (-4, 10),
        (-9, -6),
        (-15, -6),
        (15, 14),
        (1, -16),
        (3, -19),
        (17, 11),
        (5, -7),
        (2, 3),
        (10, 3),
        (20, 3),
        (-8, 1),
        (20, -13),
        (-10, 1),
        (8, 16),
    ];
    let expected_hull = [
        (3, -19),
        (20, -13),
        (20, 3),
        (17, 11),
        (15, 14),
        (8, 16),
        (-4, 10),
        (-15, -6),
    ];

    assert_eq!(graham_scan(&points), expected_hull.to_vec());

    let points = [(0, 0), (1, 2), (4, 0), (2, 4), (0, 8)];
    let expected_hull = [(0, 0), (4, 0), (0, 8)];

    assert_eq!(graham_scan(&points), expected_hull.to_vec());
}

#[test]
fn unionfind_rs_10() {
    use crate::UnionFind;

    // First, we create a new structure.
    let mut uf = UnionFind::new();

    // Then we can insert values.
    uf.insert(1);
    uf.insert(2);
    uf.insert(3);
    uf.insert(4);
    uf.insert(5);

    // And union some of the elements.
    uf.union(&1, &2);
    uf.union(&2, &4);
    uf.union(&3, &5);

    // Now, we can query to see if elements are in the same set.
    assert_eq!(uf.find(&1), uf.find(&2));
    assert_eq!(uf.find(&2), uf.find(&4));
    assert_eq!(uf.find(&4), uf.find(&1));
    assert_eq!(uf.find(&3), uf.find(&5));
    assert_eq!(uf.find(&5), uf.find(&3));

    assert_ne!(uf.find(&1), uf.find(&3));
    assert_ne!(uf.find(&5), uf.find(&4));

    // We can also create `UnionFind`s from arrays.
    let uf = UnionFind::from(["foo", "bar"]);

    assert!(!uf.friends(&"foo", &"bar").unwrap());

    // And iterators.
    let uf: UnionFind<_> = "string".chars().collect();

    assert!(!uf.friends(&'s', &'t').unwrap());
}

#[test]
fn unionfind_rs_76() {
    use crate::UnionFind;

    let mut uf = UnionFind::new();

    uf.insert('a');
    uf.insert('b');

    assert!(uf.contains(&'a'));
    assert!(uf.contains(&'b'));
}

#[test]
fn unionfind_rs_108() {
    use crate::UnionFind;

    let mut uf = UnionFind::from([1, 2, 3]);
    uf.union(&1, &2);

    assert_eq!(uf.find(&1), uf.find(&2));
    assert_ne!(uf.find(&1), uf.find(&3));
}

#[test]
fn unionfind_rs_144() {
    use crate::UnionFind;

    let mut uf = UnionFind::from([1, 2, 3]);
    uf.union(&1, &2);

    assert_eq!(uf.static_find(&1), uf.static_find(&2));
    assert_ne!(uf.static_find(&1), uf.static_find(&3));
}

#[test]
fn unionfind_rs_172() {
    use crate::UnionFind;

    let mut uf = UnionFind::from(['x', 'y', 'z']);

    assert_eq!(uf.union(&'x', &'y'), Some(true));

    // Returns `Some(false)` if we try again.
    assert_eq!(uf.union(&'x', &'y'), Some(false));

    assert!(uf.friends(&'x', &'y').unwrap());
    assert!(!uf.friends(&'y', &'z').unwrap());
}

#[test]
fn unionfind_rs_220() {
    use crate::UnionFind;

    let mut uf = UnionFind::from([1, 2, 3]);

    uf.union(&1, &2);

    assert_eq!(uf.friends(&1, &2), Some(true));
    assert_eq!(uf.friends(&1, &3), Some(false));
    assert_eq!(uf.friends(&1, &999), None);
}

#[test]
fn unionfind_rs_241() {
    use crate::UnionFind;

    let mut uf = UnionFind::new();

    uf.insert('a');
    uf.insert('b');

    assert!(uf.contains(&'a'));
    assert!(uf.contains(&'b'));
}

#[test]
fn unionfind_rs_262() {
    use crate::UnionFind;

    let mut uf: UnionFind<_> = (0..42).collect();

    assert_eq!(uf.len(), 42);

    uf.clear();

    assert_eq!(uf.len(), 0);
}

#[test]
fn unionfind_rs_280() {
    use crate::UnionFind;

    let mut uf: UnionFind<_> = "chars".chars().collect();

    assert!(!uf.is_empty());

    uf.clear();

    assert!(uf.is_empty());
}

#[test]
fn unionfind_rs_298() {
    use crate::UnionFind;

    let mut uf: UnionFind<_> = "chars".chars().collect();

    assert!(!uf.is_empty());

    uf.clear();

    assert!(uf.is_empty());
}

#[test]
fn wdigraph_rs_14() {
    use crate::WeightedDiGraph;

    // First, we create a new graph.
    let mut graph = WeightedDiGraph::new();

    // Then we can add nodes.
    graph.insert_node('a');
    graph.insert_node('b');
    graph.insert_node('c');

    assert_eq!(graph.len(), 3);
    assert!(graph.contains_node(&'a'));
    assert!(graph.contains_node(&'b'));
    assert!(graph.contains_node(&'c'));

    // And edges between those nodes.
    graph.insert_edge(&'a', &'b', 5);
    graph.insert_edge(&'a', &'c', 1);
    graph.insert_edge(&'c', &'b', 4);

    assert_eq!(graph.get_edge(&'a', &'b'), Some(&5));
    assert_eq!(graph.get_edge(&'a', &'c'), Some(&1));
    assert_eq!(graph.get_edge(&'c', &'b'), Some(&4));

    // Missing edge nodes are automatically inserted.
    graph.insert_edge(&'a', &'z', -1);

    assert!(graph.contains_node(&'z'));
    assert!(graph.contains_edge(&'a', &'z'));

    // Edges can be removed.
    graph.remove_edge(&'a', &'z');

    assert!(!graph.contains_edge(&'a', &'z'));

    // Nodes too.
    graph.remove_node(&'z');

    assert!(!graph.contains_node(&'z'));

    // We can iterate over a node's neighbors.
    for (neighbor, weight) in graph.neighbors_of(&'a') {
        // Prints "b (5)" and "c (1)" in an arbitrary order.
        println!("{neighbor} ({weight})");
    }

    // We can also iterate over all edges in the graph.
    for (from, to, weight) in graph.edges() {
        // Prints "a -> b (5)", "a -> c (1)" and "c -> b (4)"
        // in an arbitrary order.
        println!("{from} -> {to} ({weight})");
    }

    // And iterate over all nodes
    for node in graph {
        // Prints "a", "b" and "c" in an arbitrary order.
        println!("{node}");
    }
}

#[test]
fn wdigraph_rs_100() {
    use crate::WeightedDiGraph;

    let mut graph: WeightedDiGraph<_, ()> = WeightedDiGraph::new();
    graph.insert_node(1);

    assert!(graph.contains_node(&1));
}

#[test]
fn wdigraph_rs_126() {
    use crate::WeightedDiGraph;

    let mut graph = WeightedDiGraph::new();
    graph.insert_edge(&true, &false, 1);

    assert!(graph.contains_edge(&true, &false));
    assert!(graph.contains_node(&true));
    assert!(graph.contains_node(&false));
}

#[test]
fn wdigraph_rs_155() {
    use crate::WeightedDiGraph;

    let foo = "foo".to_string();
    let bar = "bar".to_string();

    let mut graph = WeightedDiGraph::from([(foo.clone(), bar, 2)]);

    assert!(graph.contains_node(&foo));

    graph.remove_node(&foo);

    assert!(!graph.contains_node(&foo));
}

#[test]
fn wdigraph_rs_192() {
    use crate::WeightedDiGraph;

    let mut graph = WeightedDiGraph::from([(1, 2, true), (1, 3, false)]);

    assert!(graph.contains_edge(&1, &2));

    assert_eq!(graph.remove_edge(&1, &2), Some(true));

    assert!(!graph.contains_edge(&1, &2));

    assert_eq!(graph.remove_edge(&1, &2), None);
}

#[test]
fn wdigraph_rs_221() {
    use crate::WeightedDiGraph;

    let mut graph: WeightedDiGraph<_, f64> = WeightedDiGraph::new();

    graph.insert_node(1);

    assert!(graph.contains_node(&1));
    assert!(!graph.contains_node(&2));
}

#[test]
fn wdigraph_rs_241() {
    use crate::WeightedDiGraph;

    let graph = WeightedDiGraph::from([('a', 'b', 1), ('b', 'c', 2), ('b', 'd', 3)]);

    assert!(graph.contains_edge(&'b', &'c'));
    assert!(!graph.contains_edge(&'c', &'d'));
}

#[test]
fn wdigraph_rs_269() {
    use crate::WeightedDiGraph;

    let graph = WeightedDiGraph::from([('a', 'b', 1), ('b', 'c', 2), ('b', 'd', 3)]);

    assert_eq!(graph.get_edge(&'b', &'c'), Some(&2));
    assert_eq!(graph.get_edge(&'c', &'d'), None);
}

#[test]
fn wdigraph_rs_297() {
    use crate::WeightedDiGraph;

    let graph: WeightedDiGraph<_, ()> = (0..42).collect();

    assert_eq!(graph.len(), 42);
}

#[test]
fn wdigraph_rs_311() {
    use crate::WeightedDiGraph;

    let mut graph: WeightedDiGraph<_, bool> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn wdigraph_rs_329() {
    use crate::WeightedDiGraph;

    let mut graph: WeightedDiGraph<_, u8> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn wdigraph_rs_352() {
    use crate::WeightedDiGraph;
    use std::collections::HashSet;

    let graph = WeightedDiGraph::from([
        (1, 2, 'a'),
        (1, 3, 'b'),
        (1, 4, 'c'),
        (4, 3, 'd'),
        (3, 2, 'a'),
    ]);

    let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();

    assert_eq!(
        HashSet::from([(&2, &'a'), (&3, &'b'), (&4, &'c')]),
        neighbors,
    );
}

#[test]
fn wdigraph_rs_389() {
    use crate::WeightedDiGraph;

    let mut graph = WeightedDiGraph::new();
    graph.insert_edge(&1, &3, 'a');
    graph.insert_edge(&3, &2, 'b');

    for (from, to, weight) in graph.edges() {
        // Prints "1 -> 3 (a)" and "3 -> 2 (b)" in an arbitrary order
        println!("{from} -> {to} ({weight})");
    }
}

#[test]
fn wdigraph_rs_435() {
    use crate::WeightedDiGraph;

    let mut a = WeightedDiGraph::new();
    a.insert_edge(&1, &2, 'a');
    a.insert_edge(&3, &2, 'b');
    a.insert_edge(&2, &1, 'c');
    a.remove_edge(&1, &2);

    let mut b: WeightedDiGraph<_, _> = [1, 2, 3].into_iter().collect();
    b.insert_edge(&3, &2, 'b');
    b.insert_edge(&2, &1, 'c');

    assert!(a == b);

    let mut c = WeightedDiGraph::new();
    c.insert_edge(&1, &2, 'a');
    c.insert_edge(&3, &2, 'b');
    c.insert_edge(&2, &1, 'c');

    assert!(a != c);
    assert!(b != c);

    let mut d = WeightedDiGraph::new();
    d.insert_edge(&1, &2, 'a');
    d.insert_edge(&3, &2, 'b');
    d.insert_edge(&2, &1, 'z');

    assert!(c != d);
}

#[test]
fn digraph_rs_16() {
    use crate::DiGraph;

    // First, we create a new graph.
    let mut graph = DiGraph::new();

    // Then we can add nodes.
    graph.insert_node('a');
    graph.insert_node('b');
    graph.insert_node('c');

    assert_eq!(graph.len(), 3);
    assert!(graph.contains_node(&'a'));
    assert!(graph.contains_node(&'b'));
    assert!(graph.contains_node(&'c'));

    // And edges between those nodes.
    graph.insert_edge(&'a', &'b');
    graph.insert_edge(&'a', &'c');
    graph.insert_edge(&'c', &'b');

    assert!(graph.contains_edge(&'a', &'b'));
    assert!(graph.contains_edge(&'a', &'c'));
    assert!(graph.contains_edge(&'c', &'b'));

    // Missing edge nodes are automatically inserted.
    graph.insert_edge(&'a', &'z');

    assert!(graph.contains_node(&'z'));
    assert!(graph.contains_edge(&'a', &'z'));

    // Edges can be removed.
    graph.remove_edge(&'a', &'z');

    assert!(!graph.contains_edge(&'a', &'z'));

    // Nodes too.
    graph.remove_node(&'z');

    assert!(!graph.contains_node(&'z'));

    // We can iterate over a node's neighbors.
    for neighbor in graph.neighbors_of(&'a') {
        // Prints "b" and "c" in an arbitrary order.
        println!("{neighbor}");
    }

    // We can also iterate over all edges in the graph.
    for (from, to) in graph.edges() {
        // Prints "a -> b", "a -> c" and "c -> b" in an arbitrary order.
        println!("{from} -> {to}");
    }

    // And iterate over all nodes
    for node in graph {
        // Prints "a", "b" and "c" in an arbitrary order.
        println!("{node}");
    }
}

#[test]
fn digraph_rs_91() {
    use crate::DiGraph;

    let mut graph = DiGraph::new();
    graph.insert_node(1);

    assert!(graph.contains_node(&1));
}

#[test]
fn digraph_rs_112() {
    use crate::DiGraph;

    let mut graph = DiGraph::new();
    graph.insert_edge(&true, &false);

    assert!(graph.contains_edge(&true, &false));
    assert!(graph.contains_node(&true));
    assert!(graph.contains_node(&false));
}

#[test]
fn digraph_rs_132() {
    use crate::DiGraph;

    let foo = "foo".to_string();
    let bar = "bar".to_string();

    let mut graph = DiGraph::new();
    graph.insert_node(foo.clone());
    graph.insert_node(bar);

    assert!(graph.contains_node(&foo));

    assert!(graph.remove_node(&foo));

    assert!(!graph.contains_node(&foo));

    assert!(!graph.remove_node(&foo));
}

#[test]
fn digraph_rs_160() {
    use crate::DiGraph;

    let mut graph = DiGraph::from([(1, 2), (1, 3)]);

    assert!(graph.contains_edge(&1, &2));

    assert!(graph.remove_edge(&1, &2));

    assert!(!graph.contains_edge(&1, &2));

    assert!(!graph.remove_edge(&1, &2));
}

#[test]
fn digraph_rs_183() {
    use crate::DiGraph;

    let mut graph = DiGraph::new();

    graph.insert_node(1);

    assert!(graph.contains_node(&1));
    assert!(!graph.contains_node(&2));
}

#[test]
fn digraph_rs_203() {
    use crate::DiGraph;

    let graph = DiGraph::from([('a', 'b'), ('b', 'c'), ('b', 'd')]);

    assert!(graph.contains_edge(&'b', &'c'));
    assert!(!graph.contains_edge(&'c', &'d'));
}

#[test]
fn digraph_rs_221() {
    use crate::DiGraph;

    let graph: DiGraph<_> = (0..42).collect();

    assert_eq!(graph.len(), 42);
}

#[test]
fn digraph_rs_235() {
    use crate::DiGraph;

    let mut graph: DiGraph<_> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn digraph_rs_253() {
    use crate::DiGraph;

    let mut graph: DiGraph<_> = "abc".chars().collect();

    assert!(!graph.is_empty());

    graph.clear();

    assert!(graph.is_empty());
}

#[test]
fn digraph_rs_274() {
    use crate::DiGraph;
    use std::collections::HashSet;

    let graph = DiGraph::from([(1, 2), (1, 3), (1, 4), (4, 3), (3, 2)]);

    let neighbors: HashSet<_> = graph.neighbors_of(&1).collect();

    assert_eq!(HashSet::from([&2, &3, &4]), neighbors,);
}

#[test]
fn digraph_rs_305() {
    use crate::DiGraph;

    let mut graph = DiGraph::new();
    graph.insert_edge(&1, &3);
    graph.insert_edge(&3, &2);

    for (from, to) in graph.edges() {
        // Prints "1 -> 3" and "3 -> 2" in an arbitrary order
        println!("{from} -> {to}");
    }
}

#[test]
fn digraph_rs_337() {
    use crate::DiGraph;

    let mut a = DiGraph::from([(1, 2), (2, 3), (2, 4)]);
    let mut b: DiGraph<_> = (1..=4).collect();

    assert!(a != b);

    b.insert_edge(&1, &2);
    b.insert_edge(&2, &3);
    b.insert_edge(&4, &2);

    assert!(a != b);

    b.insert_edge(&2, &4);

    assert!(a != b);

    b.remove_edge(&4, &2);

    assert!(a == b);

    a.remove_node(&4);
    b.remove_node(&4);

    assert!(a == b);
}

#[test]
fn minqueue_rs_10() {
    use crate::MinQueue;

    // First, we create a new queue.
    let mut queue = MinQueue::new();

    // We can push elements.
    queue.push(1);
    queue.push(6);
    queue.push(2);
    queue.push(3);

    // We can get the minimum element.
    assert_eq!(queue.get_min(), Some(&1));

    // We can peek and poll as usual.
    assert_eq!(queue.peek(), Some(&1));
    assert_eq!(queue.poll(), Some(1));

    // The min element reflects the queue's new state.
    assert_eq!(queue.get_min(), Some(&2));

    // We can iterate over the queue.
    for x in queue {
        // Prints 6, 2 and 3.
        println!("{x}");
    }

    // We can also create queues from arrays.
    let a = MinQueue::from(['q', 'u', 'e', 'u', 'e']);

    // And iterators.
    let b: MinQueue<_> = "queue".chars().collect();

    assert!(a == b);
}

#[test]
fn minqueue_rs_72() {
    use crate::MinQueue;

    let mut queue = MinQueue::new();
    queue.push(5);

    assert_eq!(queue.poll(), Some(5));
    assert_eq!(queue.poll(), None);
}

#[test]
fn minqueue_rs_91() {
    use crate::MinQueue;

    let mut queue = MinQueue::from([5]);

    assert_eq!(queue.poll(), Some(5));
    assert_eq!(queue.poll(), None);
}

#[test]
fn minqueue_rs_114() {
    use crate::MinQueue;

    let mut queue = MinQueue::from(['a']);

    assert_eq!(queue.peek(), Some(&'a'));

    queue.poll();

    assert_eq!(queue.peek(), None);
}

#[test]
fn minqueue_rs_132() {
    use crate::MinQueue;

    let mut queue = MinQueue::from([1, 5, 3, 4, 8, 2, 6]);

    assert_eq!(queue.get_min(), Some(&1));

    queue.poll();

    assert_eq!(queue.get_min(), Some(&2));

    queue.clear();

    assert_eq!(queue.get_min(), None);
}

#[test]
fn minqueue_rs_168() {
    use crate::MinQueue;

    let mut queue = MinQueue::from([1, 5, 3, 4, 8, 2, 6]);

    assert_eq!(queue.len(), 7);

    queue.clear();

    assert_eq!(queue.len(), 0);
}

#[test]
fn minqueue_rs_186() {
    use crate::MinQueue;

    let mut queue = MinQueue::from([1, 5, 3, 4, 8, 2, 6]);

    assert!(!queue.is_empty());

    queue.clear();

    assert!(queue.is_empty());
}

#[test]
fn minqueue_rs_204() {
    use crate::MinQueue;

    let mut queue = MinQueue::from([5, 3, 4, 8, 2, 6, 1]);

    assert!(!queue.is_empty());

    queue.clear();

    assert!(queue.is_empty());
}

#[test]
fn levenshtein_rs_7() {
    use crate::edit_distance;

    let a = [9, 4, 8, 5, 9, 3, 8, 5];
    let b = [1, 9, 4, 8, 3, 5];
    assert_eq!(edit_distance(&a, &b), 4);

    let kitten = ['k', 'i', 't', 't', 'e', 'n'];
    let sitting = ['s', 'i', 't', 't', 'i', 'n', 'g'];
    assert_eq!(edit_distance(&kitten, &sitting), 3);

    let x = ["foo", "bar", "baz", "baz"];
    let y = ["baz", "foo", "bar", "baz"];
    assert_eq!(edit_distance(&x, &y), 2);
}

#[test]
fn levenshtein_rs_52() {
    use crate::str_distance;

    assert_eq!(str_distance("kitten", "sitting"), 3);

    assert_eq!(str_distance("intention", "execution"), 5);

    assert_eq!(str_distance("sail", "wail"), 1);

    assert_eq!(str_distance("Levenshtein", "Levenshtein"), 0);

    assert_eq!(str_distance("", "foo"), 3);
}

#[test]
fn mjrty_rs_9() {
    use crate::majority_element;

    let ints = vec![1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 1];
    let winner = majority_element(ints.into_iter());
    assert_eq!(winner, Some(1));

    let strs = vec!["a", "c", "b", "a"];
    let winner = majority_element(strs.into_iter());
    assert_eq!(winner, None);
}

#[test]
fn quickselect_rs_12() {
    use crate::select;

    let nums = [80, 61, 36, 70, 53, 54, 59, 17, 76, 49];

    assert_eq!(select(&nums, 4), &54);
    assert_eq!(select(&nums, 6), &61);
    assert_eq!(select(&nums, 0), &17);
    assert_eq!(select(&nums, 9), &80);

    let strs = ["foo", "bar", "baz"];

    assert_eq!(select(&strs, 0), &"bar");
    assert_eq!(select(&strs, 1), &"baz");
    assert_eq!(select(&strs, 2), &"foo");
}

#[test]
fn quickselect_rs_45() {
    use crate::select_in_place;

    let mut nums = [80, 61, 36, 70, 53, 54, 59, 17, 76, 49];

    assert_eq!(select_in_place(&mut nums, 4), &54);
    assert_eq!(select_in_place(&mut nums, 6), &61);
    assert_eq!(select_in_place(&mut nums, 0), &17);
    assert_eq!(select_in_place(&mut nums, 9), &80);

    let mut strs = ["foo", "bar", "baz"];

    assert_eq!(select_in_place(&mut strs, 0), &"bar");
    assert_eq!(select_in_place(&mut strs, 1), &"baz");
    assert_eq!(select_in_place(&mut strs, 2), &"foo");
}

#[test]
fn quickselect_rs_97() {
    use crate::partition;

    let mut nums = [4, 10, 3, 0, 2, 6, 7, 1, 5, 8, 9];

    let pivot_index = partition(&mut nums, 0);

    assert_eq!(pivot_index, 4);

    for &num in &nums[..pivot_index] {
        assert!(num < nums[pivot_index]);
    }

    for &num in &nums[(pivot_index + 1)..] {
        assert!(nums[pivot_index] <= num);
    }

    let mut nums: Vec<i32> = (0..10_000).map(|_| rand::random()).collect();

    let pivot_index = partition(&mut nums, 0);
    let pivot = nums[pivot_index];

    for &num in &nums[0..pivot_index] {
        assert!(num < pivot);
    }

    for &num in &nums[(pivot_index + 1)..] {
        assert!(num >= pivot);
    }

    let mut single = [1];
    assert_eq!(partition(&mut single, 0), 0);
}

#[test]
fn iheap_rs_7() {
    use crate::IntervalHeap;

    // First, we create a new heap.
    let mut heap = IntervalHeap::new();

    // Then we can add values in any order.
    heap.insert(4);
    heap.insert(1);
    heap.insert(3);
    heap.insert(6);

    // We can peek at the min and max values.
    assert_eq!(heap.peek_min(), Some(&1));
    assert_eq!(heap.peek_max(), Some(&6));

    // And pop them off from both ends.
    assert_eq!(heap.pop_min(), Some(1));
    assert_eq!(heap.pop_min(), Some(3));
    assert_eq!(heap.pop_max(), Some(6));
    assert_eq!(heap.pop_min(), Some(4));
    assert_eq!(heap.pop_min(), None);

    // We can also create heaps from arrays.
    let mut heap = IntervalHeap::from([2, 6, 2]);

    // And heaps can contain duplicate items.
    assert_eq!(heap.pop_min(), Some(2));
    assert_eq!(heap.pop_min(), Some(2));

    assert_eq!(heap.len(), 1);
}

#[test]
fn iheap_rs_64() {
    use crate::IntervalHeap;

    let mut heap = IntervalHeap::new();

    heap.insert('h');
    heap.insert('n');

    assert_eq!(heap.peek_min(), Some(&'h'));
    assert_eq!(heap.peek_max(), Some(&'n'));
}

#[test]
fn iheap_rs_104() {
    use crate::IntervalHeap;

    let mut heap = IntervalHeap::from([4, 3, 6]);

    assert_eq!(heap.pop_min(), Some(3));
    assert_eq!(heap.pop_min(), Some(4));
    assert_eq!(heap.pop_min(), Some(6));
    assert_eq!(heap.pop_min(), None);
}

#[test]
fn iheap_rs_146() {
    use crate::IntervalHeap;

    let mut heap = IntervalHeap::from([4, 3, 6]);

    assert_eq!(heap.pop_max(), Some(6));
    assert_eq!(heap.pop_max(), Some(4));
    assert_eq!(heap.pop_max(), Some(3));
    assert_eq!(heap.pop_max(), None);
}

#[test]
fn iheap_rs_188() {
    use crate::IntervalHeap;

    let mut heap = IntervalHeap::from(['a', 'b', 'c']);

    assert_eq!(heap.peek_min(), Some(&'a'));

    heap.clear();

    assert_eq!(heap.peek_min(), None);
}

#[test]
fn iheap_rs_210() {
    use crate::IntervalHeap;

    let mut heap = IntervalHeap::from(['a', 'b', 'c']);

    assert_eq!(heap.peek_max(), Some(&'c'));

    heap.clear();

    assert_eq!(heap.peek_min(), None);
}

#[test]
fn iheap_rs_232() {
    use crate::IntervalHeap;

    let mut heap: IntervalHeap<_> = (0..42).collect();

    assert_eq!(heap.len(), 42);

    heap.pop_max();

    assert_eq!(heap.len(), 41);

    heap.clear();

    assert_eq!(heap.len(), 0);
}

#[test]
fn iheap_rs_258() {
    use crate::IntervalHeap;

    let mut heap: IntervalHeap<_> = ('a'..='z').collect();

    assert!(!heap.is_empty());

    heap.clear();

    assert!(heap.is_empty());
}

#[test]
fn iheap_rs_276() {
    use crate::IntervalHeap;

    let mut heap: IntervalHeap<_> = ('a'..='z').collect();

    assert!(!heap.is_empty());

    heap.clear();

    assert!(heap.is_empty());
}

#[test]
fn iheap_rs_418() {
    use crate::IntervalHeap;

    let random: Vec<i32> = (0..10_000).map(|_| rand::random()).collect();

    let mut sorted = random.clone();
    sorted.sort();
    let mut iter = sorted.into_iter();

    let mut heap: IntervalHeap<_> = random.into_iter().collect();

    for _ in 0..10_001 {
        if rand::random() {
            assert_eq!(heap.pop_min(), iter.next());
        } else {
            assert_eq!(heap.pop_max(), iter.next_back());
        }
    }
}

#[test]
fn radix_sort_rs_5() {
    use crate::radix_sort;

    let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
    radix_sort(&mut ints);
    assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);

    let mut random: Vec<_> = (0..100_000).map(|_| rand::random()).collect();
    radix_sort(&mut random);
    for i in 1..random.len() {
        assert!(random[i - 1] <= random[i]);
    }
}
