searchState.loadedDescShard("rust_dsa", 0, "A stack that can hold arbitrary types.\nA bidirectional map.\nA priority queue implementation backed by a binary heap.\nA priority queue implementation backed by a binomial heap.\nA Bloom filter.\nA bump allocator for type <code>T</code>.\nA deque implementation backed by a ring buffer.\nA weighted, directed graph.\nA Fenwick tree specialized for primitive integers and …\nA priority queue implementation backed by a Fibonacci heap.\nA Fenwick tree that is generic over any type <code>T</code> and …\nA trie for mapping sequences of keys to values.\nA weighted graph.\nAn immutable vector implementation with efficient …\nAn interval heap implementation for use as a double-ended …\nAn enum representing the median in a <code>MedianHeap</code>.\nA data structure for efficiently calculating a running …\nA FIFO queue that supports O(1) push, pop and find-minimum.\nA LIFO stack that supports <em>O</em>(1) push, pop and find-minimum.\nAn enum representing the items removed from a <code>BiMap</code>.\nA trie for mapping <code>str</code>s to values.\nA disjoint-set data structure backed by a disjoint set …\nA dynamic array implementation backed by a VList.\nAllocates a slot, if one is available.\nReturns an interator over the currently allocated pointers.\nEstimates the number of items in this Bloom filter based …\nReturns the number of available slots that can be …\nReturns <code>true</code> if <code>BumpAlloc::alloc</code> will return <code>Some</code>.\nReturns the number of elements the deque can hold without …\nRemoves all values from the stack.\nClears the map.\nClears the heap.\nClears the graph.\nClears the heap.\nClears the graph.\nClears the trie.\nClears the trie.\nClears the <code>UnionFind</code> structure.\nSets all the bits to zero.\nClears the deque.\nEmpties the tree.\nEmpties the tree.\nClears the binary heap.\nClears the heap.\nClears the heap.\nClears the queue.\nClears the stack.\nClears the list.\nConsolidates the heap so no two nodes have the same rank.\nReturns <code>true</code> if the value is in the <code>UnionFind</code> structure.\nReturns <code>true</code> if the graph contains an edge between <code>from</code> …\nReturns <code>true</code> if the graph contains an edge between <code>u</code> and <code>v</code>.\nReturns <code>true</code> if the trie contains <code>key</code>.\nReturns <code>true</code> if the trie contains <code>key</code>.\nReturns <code>true</code> if the map contains the left value.\nReturns <code>true</code> if the graph contains <code>node</code>.\nReturns <code>true</code> if the graph contains <code>node</code>.\nReturns <code>true</code> if the trie contains a key with the given …\nReturns <code>true</code> if the trie contains a key with the given …\nReturns <code>true</code> if the map contains the right value.\nReturns the number of edges in the graph.\nReturns the number of edges in the graph\nReturns the number of neighbors <code>node</code> has.\nReturns the number of neighbors <code>node</code> has.\nCounts the number of set bits in the Bloom filter.\nRemoves the specified range from the deque, returning all …\nReturns an iterator visiting the graph’s edges in an …\nReturns an interator visiting each of the graph’s edges …\nReturns the Levenshtein distance between two slices.\nEstimates the false positive rate of this Bloom filter if …\nReturns <code>true</code> if the two graphs are equal.\nReturns <code>true</code> if the two graphs are equal.\nReturns <code>true</code> if the tries are equal.\nInserts the elements from annother heap into this one.\nInserts the elements from annother heap into this one.\nEstimates the false positive rate of this Bloom filter …\nReturns a <code>usize</code> representing the set that contains <code>value</code> …\nReturns a cycle in the graph, if one exists.\nFrees a slot.\nFrees all the currently allocated pointers.\nReturns <code>Some(true)</code> if <code>a</code> and <code>b</code> are members of the same set …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCreates a graph from an edge list.\nReturns the argument unchanged.\nCreates a graph from an edge list.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCreates a trie from an array of key value pairs.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nUses the heapify algorithm to create a BinaryHeap in <em>O</em>(<em>n</em>) …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCreates a Fenwick tree from an array in linear time.\nCreates a heap from an iterator.\nCreates a graph with the elements of the iterator. The …\nCreates a heap from an iterator.\nCreates a graph with the elements of the iterator. The …\nUses the heapify algorithm to create a BinaryHeap in <em>O</em>(<em>n</em>) …\nExample\nReturns a reference to the value associated with the key, …\nReturns a reference to the value associated with the key, …\nReturns a reference to the element in position <code>index</code> if …\nReturns a reference to the value at position <code>index</code> if one …\nReturns the value at position <code>index</code> if one exists.\nReturns a reference to the element at <code>index</code> or None if out …\nReturns a reference to the value at position <code>index</code> if one …\nReturns a reference to the right value based on the left …\nReturns a reference to the left value based on the right …\nReturns a reference to the edge’s weight if the graph …\nReturns a reference to the edge’s weight if the graph …\nReturns the smallest element in the queue or <code>None</code> if the …\nReturns the smallest element on the stack or <code>None</code> if the …\nReturns an iterator over the values whose associated keys …\nReturns an iterator over the values whose associated keys …\nReturns an <code>Rc</code> that contains to the element at <code>index</code> or …\nReturns a subset of the input points representing their …\nAn implementation of the heapsort algorithm.\nInserts a pair into the map. Returns the removed items.\nInserts a value into the heap.\nInserts a value into the heap.\nInserts the key value pair into the trie, cloning each …\nInserts the key value pair into the trie.\nInserts a value into the <code>UnionFind</code> structure.\nInserts a value into the Bloom filter.\nInserts an item into the binary heap.\nInserts a value into the heap.\nInserts a new value into the heap.\nInserts an edge into the graph.\nInserts an edge into the graph.\nInserts an edge into the graph. The nodes are inserted if …\nInserts an edge into the graph. The nodes are inserted if …\nInserts a node into the graph.\nInserts a node into the graph.\nAn implementation of the insertion sort algorithm.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreates an iterator that iterates over the heap’s items …\nCreates an iterator over the nodes in the graph.\nCreates an iterator over the nodes in the graph.\nCreates an iterator that iterates over the heap’s items …\nCreates an iterator that iterates over the heap’s items …\nReturns the left values in the map.\nReturns right values in the map.\nReturns <code>true</code> if the stack is empty.\nReturns <code>true</code> if the map is empty.\nReturns <code>true</code> if the heap is empty.\nReturns <code>true</code> if the graph is empty.\nReturns <code>true</code> if the heap is empty.\nReturns <code>true</code> if the graph is empty.\nReturns <code>true</code> if the trie is empty.\nReturns <code>true</code> if the trie is empty.\nReturns <code>true</code> if the <code>UnionFind</code> structure is empty.\nChecks if a Bloom filter is empty (i.e., if all the bits …\nReturns <code>true</code> if the deque is empty.\nReturns <code>true</code> if the tree is empty.\nReturns <code>true</code> if the tree is empty.\nReturns <code>true</code> if the binary heap is empty.\nReturns <code>true</code> if the heap is empty.\nReturns <code>true</code> if the vector is empty.\nReturns <code>true</code> if the heap is empty.\nReturns <code>true</code> if the queue is empty.\nReturns <code>true</code> if the stack is empty.\nReturns <code>true</code> if the list is empty.\nReturns <code>true</code> if the ordering is a topological sort for the …\nReturns an iterator over the items in the map.\nReturns an iterator over the nodes in the graph.\nReturns an iterator over the nodes in the graph.\nReturns a <em>new</em> vector that contains the elements in <code>self</code> …\nReturns a reference to the last value in the tree, or <code>None</code> …\nReturns the last value in the tree, or <code>None</code> if the tree is …\nReturns a reference to value at the end of the list, or …\nReturns the left values in the map.\nReturns the length of the stack.\nReturns the number of pairs in the map.\nReturns the number of elements in the heap.\nReturns the number of nodes in the graph.\nReturns the number of elements in the heap.\nReturns the number of nodes in the graph.\nReturns the number of elements in the trie.\nReturns the number of elements in the trie.\nReturns the number of elements in the <code>UnionFind</code> structure.\nReturns the length of the deque.\nReturns the number of values in the tree.\nReturns the number of values in the tree.\nReturns the length of the binary heap.\nReturns the number of elements in the heap.\nReturns the length of the vector.\nReturns the number of elements in the heap.\nReturns the number of elements in the queue.\nReturns the number of elements on the stack.\nReturns the length of the list.\nReturns the majority element of an iterator, if one exists.\nQueries the Bloom filter for a given value.\nReturns one or two median values in the heap, or <code>None</code> if …\nAn implementation of the mergesort algorithm.\nReturns an iterator that visits all of <code>node</code>’s neighbors.\nReturns an iterator that visits all of <code>node</code>’s neighbors.\nCreates a new stack.\nCreates a new map.\nCreates a new heap.\nCreates a new allocator.\nCreates an empty graph.\nCreates a new heap.\nCreates an empty graph.\nCreates a new trie.\nCreates a new trie.\nCreates a new <code>UnionFind</code> structure.\nCreates an empty Bloom filter.\nCreates an empty deque.\nCreates a Fenwick tree.\nCreates a Fenwick tree.\nCreates an empty binary heap.\nCreates an empty heap.\nCreates an empty vector.\nCreates an empty queue.\nCreates an empty stack.\nCreates an empty list.\nPartitions the slice around the element at <code>pivot_index</code>.\nTries to peek a value of type <code>T</code> from the top of the stack.\nReturns the smallest item in the heap, or <code>None</code> if the heap …\nReturns the smallest item in the heap, or <code>None</code> if the heap …\nReturns the smallest item in the binary heap, or <code>None</code> if …\nReturns a reference the next element in the queue or <code>None</code> …\nReturns a reference the last element on the stack or <code>None</code> …\nPeeks the value at the back of the deque.\nPeeks the value at the front of the deque.\nReturns a reference to the largest value in the heap, or …\nReturns a reference to the smallest value in the heap, or …\nRemoves the next element in the queue and returns it or …\nTries to pop a value of type <code>T</code> from the stack.\nRemoves and returns the smallest item in the heap, or …\nRemoves and returns the smallest item in the heap, or …\nRemoves and returns the last value in the tree, or <code>None</code> if …\nRemoves and returns the last value in the tree, or returns …\nRemoves and returns the smallest item in the binary heap, …\nPops the median element from the heap.\nRemoves the last element on the stack and returns it or …\nRemoves and returns the value at the end of the list, or …\nPops a value from the back of the deque.\nPops a value from the front of the deque.\nRemoves and returns the largest value in the heap, or <code>None</code> …\nRemoves and returns the smallest value in the heap, or <code>None</code>…\nPushes a value onto the stack.\nPushes a value onto the end of the tree.\nPushes a value onto the end of the tree.\nReturns a <em>new</em> vector with the value appended.\nPushes an element into the queue.\nPushes an element onto the top of the stack.\nPushes a value onto the end of the list.\nPushes a value onto the back of the deque.\nPushes a value onto the front of the deque.\nAn implementation of the quicksort algorithm.\nAn implementation of the radix sort algorithm.\nReturns a new vector that contains the elements in the …\nRemoves and returns the value associated with the key, if …\nRemoves and returns the value associated with the key, if …\nReturns a <em>new</em> vector without the value at <code>index</code>.\nRemoves a pair from the map based on the left value.\nRemoves a pair from the map based on the right value.\nRemoves an edge from the graph. Returns the weight if the …\nRemoves an edge from the graph. Returns the weight if the …\nRemoves a node from the graph. Returns <code>true</code> if the node …\nRemoves a node from the graph. Returns <code>true</code> if the node …\nReturns a <em>new</em> vector with <code>value</code> at position <code>index</code>.\nReturns right values in the map.\nReturns a reference to the <code>k</code>th smallest element in the …\nReturns a reference to the <code>k</code>th smallest element in the …\nSets the value at <code>index</code>.\nShrinks the capacity of the buffer if possible.\nCreates a heap with a single element.\nReturns a <code>usize</code> representing the set that contains <code>value</code> …\nReturns the Levenshtein distance between two <code>str</code>s.\nReturns the sum of the values with indices in <code>range</code>.\nReturns the associative operation <code>f</code> applied to the values …\nReturns the sum of the values with indices in the range …\nReturns <code>true</code> if the top of the stack has type <code>T</code>.\nReturns a topological sort of the graph, if one exists.\nReturns the associative operation <code>f</code> applied to all values …\nReturns sum of all values in the tree.\nJoins the two sets containing <code>a</code> and <code>b</code>. Returns <code>None</code> if <code>a</code> …\nUpdates the value at <code>index</code>.\nUpdates the value at <code>index</code>.\nReturns an iterator over the trie’s values.\nReturns an iterator over the trie’s values.\nCreates a new map with the given capacity.\nCreates a new <code>UnionFind</code> structure with the specified …\nCreates an empty deque with the given capacity.\nCreates an empty queue with the specified capacity.\nCreates an empty stack with the specified capacity.\nCreates an empty Bloom filter which will use the given …")