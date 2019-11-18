(* 
    Here is the implements of the functions in the pesudocode_functions.py of the algorithm
    TODO: use notations, local definition/variables for easier read
        now since definition changes frequently, so I let them verbose...
*)



Require Export definitions_taxi.
(*
    This should be the definitions, currently done by Ke,
    suppose we have:
    Types:
        Node
        Node_list
        Graph
        Taxiway := nat
    Functions:
        get_neighbors: return all neighbours of node n on given taxiway
            (Node -> nat -> Graph) -> Node_list
        is_on_taxiway: return whether node n is on taxiway
            (Node -> nat -> Graph) -> boolean
        last_node: return the list of last node in a node_list, return [] when empty
            (Node_list) -> Node_list
        drop_last: return the list without last node (imaging not empty)
            (Node_list) -> Node_list
*)


(*================ get_last_segment ====================*)

Fixpoint last_segment (source_node : Node) (pre_node : Node) (cur_node : Node) (end_node : Node) (taxiway : nat) (g : Graph) (neighbor_nodes : Node_list) : Node_list :=
    match neighbor_nodes with
        | [] => []
        | x :: l => match x with
            | pre_node => last_segment source_node pre_node cur_node end_node taxiway g l
            | end_node => x :: [source_node]
            | _ => x :: last_segment source_node cur_node x end_node taxiway g (get_neighbors x taxiway g)
            end
        end.
      
        
Fixpoint get_last_segment (cur_node : Node) (end_node : Node) (taxiway : nat) (g : Graph) : Node_list :=
    match last_node (last_segment cur_node cur_node cur_node end_node taxiway g (last_node (get_neighbors cur_node taxiway g))) with
        | [] => []
        | [source_node] => drop_last (last_segment cur_node cur_node cur_node end_node taxiway g (last_node (get_neighbors cur_node taxiway g)))
        | [_] => drop_last (last_segment cur_node cur_node cur_node end_node taxiway g (drop_last (get_neighbors cur_node taxiway g)))
        end.
      
(*============= get_intermediate_nodes ====================*)


Fixpoint intermediate_nodes (source_node : Node) (pre_node : Node) (cur_node : Node) (cur_taxi : nat) (next_taxi : nat) (g:Graph) (neighbor_nodes : Node_list) : Node_list :=
    match neighbor_nodes with
        | [] => []
        | x :: l => match x with
            | pre_node => intermediate_nodes source_node pre_node cur_node cur_taxi next_taxi g l
            | a => match  (is_on_taxiway x next_taxi g) with
                | true => a :: [source_node]
                | _ => a :: intermediate_nodes source_node cur_node x cur_taxi next_taxi g (get_neighbors x cur_taxi g)
                end
            end
        end.
      
Definition get_intermediate_nodes (cur_node : Node) (cur_taxi : nat) (next_taxi : nat) (g:Graph) : Node_list :=
    match last_node (intermediate_nodes cur_node cur_node cur_node cur_taxi next_taxi g (last_node (get_neighbors cur_node cur_taxi g))) with
        | [] => []
        | [source_node] => drop_last (intermediate_nodes cur_node cur_node cur_node cur_taxi next_taxi g (last_node (get_neighbors cur_node cur_taxi g)))
        | [_] => drop_last (intermediate_nodes cur_node cur_node cur_node cur_taxi next_taxi g (drop_last (get_neighbors cur_node cur_taxi g)))
        end.

      
      
(*=================== find_path =========================*)  

(*It's done very early, I can't check the correctness now...*)
Fixpoint find_path (start_node : Node) (end_node : Node) (taxiway_names : list nat) (g : Graph) : Node_list :=
    match taxiway_names with
    | [] => None
    | a::[] => match get_last_segment start_node end_node a with
        | [] => None
        | last_seg => last_seg
        end
    | a::b::rest => match (get_intermediate_nodes start_node a b g) with
        | [] => None
        | None => None (*??? why did I write this*)
        | path_seg => path_seg::(find_path (last_node path_seg) end_node b::rest g)
        end
    end.
      
Definition find_path_wrapper (start_node : Node) (end_node : Node) (taxiway_names : nat) (g : Graph) : Node_list :=
     start_node::(find_path start_node end_node taxiway_names).
      
      