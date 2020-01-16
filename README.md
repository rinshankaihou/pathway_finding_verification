# Dependency
CoqHammer with at least Vampire and Eprover installed. (Otherwise trust the hammer tactic works at its every occurance)https://github.com/princeton-vl/CoqGym/tree/master/ASTactic/coqhammer

ssreflect : only for computing examples. Safe to delete.

# Algorithm
The current algorithm is in https://github.com/rinshankaihou/pathway_finding_ver/blob/master/GraphBasics/dfs_complete_paper.v.



Definitions:

     Node_type : (Vertex * Vertex)
        (current, from)
    taxiway : string

    Edge_type : (Node_type * Node_type) * string
        ((end1, end2), taxiway)

    Graph_type : list Edge_type


    State_type : ((list Edge_type * string) * list string)
                 ((cur_path, cur_taxiway), rest_ATC)



# Specification
(start with 1., do 2 and 3 later)
1. If I get a result for an ATC instruction, then this result is valid. For example, if the ATC instruction is “ACB”, the result I get is:
   1. correct start & end points; 
   2. valid path in the graph; (connected basically done; see *find_path_conn*; shall we check if every edge is in the graph?)
   3. its ‘signature’ is of the form A+C+B+. (*output_path_follow_atc*)

2. If the algorithm is returning a result, there is no other valid result.
3. If a taxiway is too small for the aircraft, then not part of the result should include this taxiway.
