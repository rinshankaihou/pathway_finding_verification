# Dependency
coqc 8.10.1 (Feb 2020) with Ocaml 4.07.1


CoqHammer 1.1.1. (Otherwise trust the hammer tactic works at its every occurrence) https://github.com/princeton-vl/CoqGym/tree/master/ASTactic/coqhammer

CoqHammer requires 4 ATPs, the versions we are using are:
   
      CVC4 1.7
      Z3_tptp 4.8.8.0
      vampire 4.2.2
      Eprover 2.4

mathcomp-ssreflect 1.10.0.

# File Organization
The algorithm is implemented in *Implementation.v*. 
Type definitions are in *Type.v*. Some examples on the Ann Arbor airport is in *Example.v*. Run *Extraction.v* to extract the algorithm to Ocaml.

Top level function: find_path_wrapper.

We provide a ```makefile```. Note that *Extraction.v* is not included in the make list, so you have to manually run it.
   - ```make```: compile all targets
   - ```make clean```: delete compiled files and temporary files

# Correctness
We prove correctness of the algorithm in
If I get a result for an ATC instruction, then this result is valid. For example, if the ATC instruction is “ACB”, the result I get is:
   1. correct start & end points; (*output_path_start_correct*; *output_path_end_correct*)
   2. valid path in the graph; ( *find_path_conn* )
   3. its ‘signature’ is of the form A+C+B+. (*output_path_follow_atc*)
   4. every edge is in the graph. (*output_path_in_graph*)
   
The proof is in *correctness.v*, top level theorem is *corectness*.

# Reference
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
