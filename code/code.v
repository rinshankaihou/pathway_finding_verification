From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.


(* The definitions:
    Node
    Edge
    Node_list
    Edge_list *)

(* To do later. first touch fish *)

Print Vertex.
(* Inductive Vertex : Set :=  index : nat -> Vertex *)
Definition Node : Type := Vertex. (* alias *)
Print Edge.
Definition _Node_list : Type := list Node.
Definition Edge_list : Type := list Edge.
Inductive Node_list : Type :=
  | Some (n : Node_list)
  | None.
Definition Indexing : Type := Edge -> nat.
Notation "{ x }" := (Indexing x). (* where x is an edge*)
(* '~' defines an equivalence relation *)
(* Notation " x ~ y " :=  eq_nat (indexing x) (indexing y).*) (* where x,y are edges*)

(* input to this algorithm is a GV_list and adjacency_list, where the former  
   is to ensure termination *)
(*is this function infinite?*)
(*abr. as AL *)
Definition adjacency_list : Type :=
  list Vertex * (list Vertex * nat).
 (*maps a node to adjacent nodes, along with the pathwaynames that connect them*)
(* '*' return the product type *) 

(*Definition gen_graph (AL : adjacency_list): Graph *)

(*nat is the index of taxiway. indexing models giving name to taxiway names*)
(* return the number of edges that has taxiway_name name attached to it *)
Fixpoint taxiway_degree (z : Node) (taxiway : nat) (edges : Edge_list) (indexing : Edge -> nat) : nat :=
  match edges with
  | [] => 0
  | e::l => if In z e /\ ({e} = nat)(* if z is an end point of edge e*) then S (taxiway_degree z nat l indexing)
                else (taxiway_degree z nat l indexing)
  end.
  
Fixpoint taxiway_degree (z : Node) (taxiway : nat) (edges : Edge_list) (indexing : Edge -> nat) : nat :=
  match edges with
  | [] => 0
  | e::l => if In z e /\ ({e} = nat)(* if z is an end point of edge e*) then S (taxiway_degree z nat l indexing)
                else (taxiway_degree z nat l indexing)
  end.

(*input: all edge in the graph, indexing function that represents taxiway names*)
(* SPEC of the input. there are two distinct edges x, y in the graph*)
Definition is_valid_indexing (g : Graph) (indexing : Edge -> nat)  : Prop :=
  match g with 
  | Graph nodes edges => 
  forall taxiway, exists g -> In g Graph -> {g} = taxiway -> (* For any taxiway in the graph, there existss    *)
  exists x, exists y,                                        (* distinct nodes x, y in the graph s.t.,         *)
  x != y -> In x nodes -> In y nodes ->                      (* x, y are end points of taxiway, and            *)                              
    (taxiway_degree x taxiway edges indexing) = 1 /\     
    (taxiway_degree y taxiway edges indexing) = 1 /\                       
    forall z, In z nodes -> z!=x -> z!=y ->                  (* for other nodes z, the number of taxiways that,  
                                                                has name _taxiway_ and are attached to z,      *)
      (taxiway_degree z taxiway edges indexing) = 0 \/       (* is either 0                                    *)
      (taxiway_degree z taxiway edges indexing) = 2.         (* or 2.                                          *)
end.

(*find all neighbors of n on the taxiway taxi_way, there should be at most two nodes*)
Definition get_neighbors (n : Node) (taxi_way : nat) (g : graph) : Node_list:=
  Admitted.


(*return true if n is on taxiway*)
Definition is_on_taxiway (n:Node) (taxiway : nat) (g:graph) : bool :=
    Admitted.





(*===============================get_last_segment function================================
    need get_neighbors: return all neighbours of node n on given taxiway
*)



(*last_segment(pre_node, aim_node, taxiway, neighbors, node_list):
    if neighbors == [] return []
    else if head(heighbors) == pre_nodes, return last_segment(pre_node, aim_node, taxiway, rest(neighbors), node_list) #for
    else if head(neighbors) == node2: #(should be only one(if exists))
        # we're assuming that it exists, or it will be done in ==[]
        # for this case, it's done
        return node_list
    else if head(neighbors) != pre_node or node2
        return head(neighbors) :: last_segment(head(neighbors), aim_node, taxiway, neighbor(head(neighbors), []))*)



Fixpoint last_segment  (pre_node : Node) (cur_node : Node) (end_node : Node) (taxiway : nat)  (g : Graph) (neighbor_nodes : Node_list) (node_list : Node_list): Node_list :=
  match neighbor_nodes with
    | [] => []
    | x :: l => match x with
        | pre_node => last_segment pre_node cur_node end_node taxiway g l node_list
        | end_node => node_list
        | _ => x :: last_segment cur_node x end_node taxiway g (get_neighbors x taxiway g) []
        end
    end.

(*As a function caller, to do for*)    
Definition get_last_segment : (cur_node : Node) (end_node : Node) (e : Edge) (g : Graph) : Node_list :=
    last_segment  cur_node cur_node end_node e g (get_neighbors cur_node e g) [].
(*return path_seg = (cur_node, next_node] via taxiway e,  or [] if there is no such*)



(*==============================get_intermediate_nodes funtion============================================
    need get_neighbors: return all neighbours of node n on given taxiway
    need is_on_taxiway: return whether node n is on taxiway
*)


(*
get_intermediate_nodes(node1, cur_taxi, next_taxi):
    intermediate_nodes(node1,node1, cur_taxi, next_taxi, neighbors = neighbor(node1, taxiway), [])

intermediate_nodes(pre_node, cur_node,cur_taxi, next_taxi, neighbors, node_list):
    if neighbors == [] return []
    else if head(heighbors) == pre_nodes, return intermediate_nodes(pre_node,cur_node, cur_taxi, next_taxi, rest(neighbors), node_list)
    else:
        if is_on_taxiway(head(neighbors),next_taxi) == true: 
        return node_list
        else
        return head(neighbors) :: intermediate_nodes(cur_nodes, head(neighbors), cur_taxi, next_taxi, neighbor(head(neighbors), []))

*)


Definition intermediate_nodes : (pre_node :Node) (cur_node:Node) (cur_taxi : nat) (next_taxi : nat) (g:Graph) (neighbor_nodes : Node_list) (node_list : Node_list): Node_list :
    match neighbor_nodes with
        | [] => []
        | x :: l => match x with
            | pre_node => intermediate_nodes pre_node cur_node cur_taxi next_taxi g l node_list
            | _ => match  (is_on_taxiway x next_taxi g) with
                | true => node_list
                | _ => a :: intermediate_nodes cur_node x cur_taxi next_taxi g (get_neighbors x cur_taxi g) []
                end
            end
        end.

Definition get_intermediate_nodes (cur_node : Node) (a : nat) (b : nat) (g:Graph) (neighbor_nodes : Node_list): Node_list :=
    intermediate_nodes cur_node cur_node a b g (get_neighbors cur_node a g) [].
(*return path_seg = (cur_node, next_node], where next_node is an intersection of pathway a and b.
  or [] if there is no such path*)



(*=========================find_path function ==========================================================*)

  
  Definition last_item{T : Type} (lst : List T) : T :=
  Admitted.
(*return last item of the list*)


Fixpoint find_path (start_node : Node) (end_node : Node) (taxiway_names : Edge_list) (g : Graph) : Node_list :=
  match taxiway_names with
  | [] => None
  | a::[] => match get_last_segment start_node end_node a with
             | [] => None
             | last_seg => last_seg
             end
  | a::b::rest => match (get_intermediate_nodes start_node a b g) with
                  | [] => None
                  | None => None ??? why did I write this
                  | path_seg => path_seg::(find_path (last_item path_seg) end_node b::rest g)
                  end
  end.

Definition find_path_wrapper (start_node : Node) (end_node : Node) (taxiway_names : Edge_list) (g : Graph) : Node_list :=
  start_node::(find_path start_node end_node taxiway_names).

