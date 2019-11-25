# The new structure (see code)
0. Using **state:= {List Vertex, List Taxiway}** to indicate the data structure
1. We'll use step-by-step instead of using a complete recursion. 
    - Arrange a list of the pairs we're going to explore like a stack/queue
    - For each pair we explore, if the neighbors are possible, i.e. on the current taxiway or next taxiway, we insert the pair into the list.
    - If the pair reaches the final output, we insert into the result list
2. This algorithm is expected to be easier to prove.

# Stregedy
## get neighbors
1. Results are strictly on the taxiway
2. Number is at most 2

## filter/pack neighbor
1. Result will not be the previous node
    - this is important in showing the fixpoint will stop
    - or saying **in every step we decrease unchecked states**
2. The next states are one-step from current state
3. The packed states are correct

## The fixpoint will stop
1. prove unchecked states(vertices) are monotonous decrease
2. We checked all states possible

# Goals(please ignore)

## $\forall~ p$  we find is a valid path
1. p starts at s and ends at e
2.  $\forall~ \text{vertice} ~v_i\in p =[v_1,\dots,v_m] , \exists \text{ taxiway } T, \text{s.t.}  [v_i :: v_{i+1}] $ is a sub-list of $T$.
    - p is a valid path in the graph.
    - equivalent to $p = [e_1, \dots, e_m],~ \forall i\in[1,m-1], \text{end}(e_i)=\text{start}(e_{i+1})$, and $e_1,\dots,e_m$ are edges on the graph
    - since we don't use the edges any more, we need to rewrite it
3. $\forall~ \text{taxiway }T\in\text{ATC}$, $\exists~l: \text{list}$, s.t. $l$ is a sub-list of $T$ \\/ $l\neq []$ 
    - names of taxiway need to be the form: $ABC$, indicating $A^+B^+C$.
    - Alternatively, we can prove that every taxiway is coresponding to some nodes

**Explain**: by 1 we can validate the start and the end. By 3 we can prove every taxiway of ATC comman is used, and by 2 we can say that every vertice is in the ATC taxiway (aka the path is continuous).
