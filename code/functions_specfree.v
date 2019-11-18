(*
    Using the new definitions:
        Node
        List Node =: V_List
        Edge := (Node, Node)
        Taxiway := List Edge

    Assuming these functions:
        get_neighbors: return a V_List type of all the neighbors in a taxiway
            Node -> Taxiway -> V_List
        is_on_taxiway: return whether a given node is on a taxiway
            Node -> Taxiway -> Boolean
        node_find: return whether a node is in a list of node
            Node -> V_List -> Boolean
        
        last_node: return the last node of a node list
            V_List -> Node
        drop_last: return the list except for last node
            V_List -> V_List
        
        head: return the first node in a node list
            V_List -> Node
        tail: return the rest of a list
            V_List -> V_List
*)



Require Export taxi_definitions.



(*       get_last_segment       *)

Fixpoint last_segment (pre_node_list : V_List) (cur_node : Node) (aim_node : Node) (taxiway : Taxiway) (neighbors : V_List) : V_List :=
    match neighbors with
    |   [] => []
    |   x :: _ => if node_find cur_node pre_node_list then [] else 
        match x with
        |   aim_node => cur_node :: [last_node pre_node_list]
        |   _ => match last_node (last_segment (cur_node :: pre_node_list) x aim_node taxiway (get_neighbors x taxiway)) with
                |   last_node pre_node_list => cur_node :: (last_segment (cur_node :: pre_node_list) x aim_node taxiway (get_neighbors x taxiway))
                |   _ => last_segment pre_node_list cur_node aim_node taxiway (tail neighbors)
                end
        end
    end.


Definition get_last_segment (source_node : Node) (aim_node : Node) (taxiway : Taxiway) : V_List := 
    tail (drop_last (last_segment [] source_node aim_node taxiway (get_neighbors source_node taxiway))).



(*         get_intermediate_notes       *)

Fixpoint intermediate_nodes (pre_node_list : V_List) (cur_node : Node) (cur_taxi : Taxiway) (next_taxi : Taxiway) (neighbors : V_List) : V_List :=
    match neighbors with
    |   [] => []
    |   x :: _ => if node_find cur_node_list then [] else
        if is_on_taxiway x next_taxi then cur_node :: [last_node pre_node_list] else
        match last_node (intermediate_nodes (cur_node :: pre_node_list) x cur_taxi nex_taxi (get_neighbors x cur_taxi)) with 
        |   last_node pre_node_list => cur_node :: (intermediate_nodes (cur_node :: pre_node_list) x cur_taxi nex_taxi (get_neighbors x cur_taxi))
        |   _ => intermediate_nodes pre_node_list cur_node cur_taxi next_taxi (tail neighbors)
        end
    end.

Definition get_intermediate_nodes (source_node : Node) (cur_taxi : Taxiway) (next_taxi : Taxiway) : V_List :=
    tail (drop_last (intermediate_nodes [] source_node cur_taxi next_taxi (get_neighbors source_node cur_taxi))).


 (* top level *)   
    (*It's done very early, I can't check the correctness now...*)
Fixpoint find_path (start_node : Node) (end_node : Node) (taxiway_names : nat) (g : Graph) : Node_list :=
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
      