# Using the library
1. The GraphBasics lab is old, we need to use **-impredicative-set** option to launch.
    - in vscoq, you need to add "coqtop.args"
    - It may cause inconsistency?  see "https://github.com/coq/coq/wiki/Impredicative-Set".
2. Using make to build the ".vo" files.
3. You need to use **From GraphBasics Require Export xxx** instead of just require export. 
    - It may cause inconsistency, see "https://github.com/coq/coq/wiki/Impredicative-Set".
    - I don't know whether it's okey, or need to rewrite it.


# Algorithm (function.v)
1. Siyuan wrote the "functions.v", Ke did with the definition. "function.v" need to import some definitions, but we're just pretending the definitions are there.
2. Siyuan rewrite some functions in the original algorithm into recursive format. 
3. There're still many things need to be changed...
4. We need to work further on the definitions.

# Spec (code.v)
The current input for this algorithm is **g : Graph** a graph, **ind : Edge -> nat** an indexing for edges in the graph. 

is_valid_indexing asserts that, intuitively, every pathway is a continuous line that does not intersect itself. More specifically, the number of nodes that is attached to exactly 1 edge of some specific taxiway is 2 (endpoints), other nodes can have either 0 or 2 edges attached to it that is part of the taxiway.

TODO: write gen_graph(adjacency_list) -> graph

TODO: This is an initial design. Fully implement the spec after checking the correctness.