# ALgorithm
The current algorithm is in https://github.com/rinshankaihou/pathway_finding_ver/blob/master/GraphBasics/dfs_directed.v. 

Definitions:

        string represents taxiway names.

        Vertex: a vertex in the graph
        
        State_type : Type := V_list * list string.
            - V_list is the previous visited node, in reverse order
            - list string is the rest ATC

        Node_type : Type :=           Vertex * string
            - see Edge_type

        Edge_type : Type := Vertex * (Vertex * string)
            - the edge
            - (cur_vertex, (connected-to vertex, taxiway between them))

        Graph_type : Type := list Edge_type.

We use **state** (list Node_type, list string) to represent the current search state
    - fst is a list of vertices that previously visited, head is current 
    - snd is the remaining taxiways from the ATC command, head is current. Using *ATC* to denote the rest taxiways. 

For each **state**:

1. If last node in **state** is the end_vertex and ATC has length 1 and 
       last node is on the taxiway that last ATC, we return this **state**.
2. If the length of the remaining taxiway is no greater than 1 we terminate.
 This is because we only consume the current taxiway in ATC if we move to the next taxiway.
3. Then we get all nodes it points to, and drop the most recently visited node, as well as all the nodes not on current/next taxiway.
4. For each remaining neighbor node, we append it to the current **state**,
       and drop the head of the ATC command if the neighbor node is on the next
       taxiway. Then we recursively search these new **state**s.

# Specification
(start with 1., do 2 and 3 later)
1. If I get a result for an ATC instruction, then this result is valid. For example, if the ATC instruction is “ACB”, the result I get is:
   1. correct start & end points; 
   2. valid path in the graph;
   3. its ‘signature’ is of the form A+C+B+.

   **any_path_in_output_is_valid** states these properties. 1.1 corresponds to **start_correct** and **end_correct**. 1.2 corresponds to **connected**. 1.3 corresponds to **path_valid**. Note that **connected** should be able to reduce to **path_valid**.
2. If the algorithm is returning a result, there is no other valid result.
3. If a taxiway is too small for the aircraft, then not part of the result should include this taxiway.
