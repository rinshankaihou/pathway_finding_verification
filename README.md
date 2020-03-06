# Dependency
CoqHammer with at least Vampire and Eprover installed. (Otherwise trust the hammer tactic works at its every occurrence) https://github.com/princeton-vl/CoqGym/tree/master/ASTactic/coqhammer

mathcomp.

# Algorithm
The current algorithm is in https://github.com/rinshankaihou/pathway_finding_ver/blob/master/GraphBasics/dfs_complete_paper.v.
Top level function: find_path_wrapper.

Definitions and Conventions:

     Vertex: index nat
     
     Node_type : (Vertex * Vertex)
       a node in the complete graph. (current, from)
        
    Taxiway_type : string

    Edge_type : (Node_type * Node_type) * Taxiway_type
                ((end1, end2), taxiway_name)

    Graph_type : list Edge_type
    
    State_type : State (list Edge_type) Taxiway_type (list Taxiway_type) (list Taxiway_type) 
                       cur_path         atc_h  atc_t         atc_used
                       
    atc_*: atc commands, Taxiway_type or (list Taxiway_type)
    
    p | path: a path, list Edges
    
    s | n_s | state: a State_type

    D: a Directed graph
    
    start_v, end_v: starting/ending vertex
    
    [(((start_v, input), (start_v, input)), atc_h)]: initial cur_path with one edge


# Specification
1. If I get a result for an ATC instruction, then this result is valid. For example, if the ATC instruction is “ACB”, the result I get is:
   1. correct start & end points; 
   2. valid path in the graph; ( *find_path_conn* )(**DONE**)
   3. its ‘signature’ is of the form A+C+B+. (*output_path_follow_atc*)(**DONE**)
   4. every edge is in the graph.

2. If the algorithm is returning a result, there is no other valid result. (completeness)
3. If a taxiway is too small for the aircraft, then not part of the result should include this taxiway.

# Notes
Thoughts for completeness. WTS: for (p: Path), SomeProp p -> In p output.
Then this SomeProp guarantees a program execution path that produces p. 

Consider using reflection since our soundness spec sounds very deterministic.
https://softwarefoundations.cis.upenn.edu/vfa-current/Decide.html

# ToDo
1. Admire Ke Du
2. Write a wrapper for find_path (or further for the whole algorithm, it's similar), then 
     - Check the ATC command is valid (i.e. not empty or in the graph... check later)
     - Check the result has only one path (if exists), maybe write a new type for return
3. edge in directed graph -> Arc_type, edge in undirected graph -> Edge_type
