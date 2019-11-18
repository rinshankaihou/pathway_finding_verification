# The algorithm modified for spec-free
1. The algorithm is modified on the original system, and is expected to have the same output without setting the following steps:
    - No loop
    - At most two neighbours on a given taxiway

## only drop loop spec
1. The idea is to modify the call function, and using recursive way to deal with the neighbours
    - the recursive will only ends when it finds the aim
    - maybe we need to use a checker node
2. We need to insert a node list indicating the previous nodes to detect whether there's a loop\
    - if cur_node in prev_node_list, then it's a loop
3. In the previous algorithm, we use source-node in the returned list as a checker, and this time we can directly get it in the prev_node_list
    - when call, give {source} 
4. **We're still assuming that one node can have at most two neighbors on a given taxiway**

## Important Change if drop the two-neighbor assumption
1. Since we no-longer can imagine at most-two neighbors, we need to call the method for every neighbor except the previous one. We should select the right result from all these calls, and return to the caller.
2. This is a TODO thing.
    - This maybe helping prove, but I don't sure.
    - This implement will need no assumption.