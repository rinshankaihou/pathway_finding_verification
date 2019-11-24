
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.



Definition all_neighbors (v : Vertex) (taxiway_names : list V_list) : V_list .


(*
Using the basic pair (V_list, list V_list)
    - fst is the vertice lists that previously visited, the first is current 
    - snd is the remaining ATC commend, first is this one

Whenever we deal with a pair, we get all its neighbors, and only consider the vertices having taxiway name
    - this taxiway => push into the stack
    - next taxiway => delete snd's first element, and push into the stack
meanwhile adding the node to the previous node list

not using option type, or none
*)


(*
    push_stack accepts a pair, and return as list of pairs with requirements of the pair
    find_path acts like while(not empty), and when accepting the push_stack, check if there's valid path 
*)


Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Fixpoint eqv_list (vlst1 : V_list) (vlst2 : V_list) : bool :=
  match vlst1, vlst2 with
  | v1::r1, v2::r2 => if eqv v1 v2 then eqv_list r1 r2 else false
  | [], [] => true
  | _, _ => false
  end.


(* return sublist after v, or [] *)
Fixpoint list_after_v (v : Vertex) (taxiway : V_list) {struct taxiway}: V_list :=
  match taxiway with  
  | a::rest => if eqv a v then rest else list_after_v v rest
  | _ => []
  end.

(* TODO should return option Vertex *)
(* return [next_elem] after v, or [] *)
Definition next_neighbor (v : Vertex) (taxiway : V_list) : V_list :=
  match list_after_v v taxiway with
  | next_elem::rest => [next_elem]
  | _ => []
  end.


(* easy to prove that at most 2 elements, 
using property of list, will drop which on the pre_list*)
(*todo: don't accept cur_V, but accept taxiway, if not on taxiway, next_neighbor will return []*)
Definition neighbors_on_the_taxiway (cur_v : V_list * list V_list) : list Vertex :=
    match next_neighbor (head fst cur_v) (head snd cur_v) ++ next_neighbor (head fst cur_v) (head rev snd cur_v) with
    | [] => []
    | a :: nil => if a In fst cur_v then [] else [a]
    | a :: b :: nil => if a In fst cur_v then 
                            if b In fst cur_v then [] else [b]
                        else 
                            if b In fst cur_v then [a] else [a;b]
    | a :: b :: l => [] (*will not encounter*)
    end.


(* match neighbor_on_this, 
    - if [a]
        - if a on next_ATC == true
            return ..a
        - else return ..a
    - if [a,b], match (a on next_ATC, b on next_ATC):
        - (true, true) ...
        - (true, false) ...
        - (false, true) ...
        - (false, false) ...'

TODO: if a neighbor is either on current or next ATC, we push next neighbor
so which means we check neighbors for 2 taxiways 
*)
Fixpoint push_stack (cur_v : V_list * list V_list) :  list (V_list * list V_list) :=



Fixpoint find_path (cur_stack : list (V_list * list V_list)) (end_v : Vertex) 



Definition find_path_wapper (start_v : Vertex) (end_v : Vertex) (taxiway_names : list V_list) : list V_list :=
    match 
(* The definitions imported GraphBasics.Vertices:
     Vertex: nat->Vertex, indexed by nat
     V_list = list Vertex
   New definitions:
     taxiway : V_list, an ordered list of all vertices on the taxiway. 
                       There is no name for a taxiway. 
                       
     taxiways : list taxiway, a list of all taxiways. order does not matter.
                              TODO Consider using string->V_list to replace taxiways.
   taxiways represents all information in the graph for now
   ATC Command is: (start_vertex, end_vertex, taxiway_names)
   Entry point (top level function) find_path_wrapper.
*)
Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Fixpoint eqv_list (vlst1 : V_list) (vlst2 : V_list) : bool :=
  match vlst1, vlst2 with
  | v1::r1, v2::r2 => if eqv v1 v2 then eqv_list r1 r2 else false
  | [], [] => true
  | _, _ => false
  end.

(* a state of searching, a pair of current partial path and the remaining taxiway names *)
Definition state : Type := V_list * (list V_list).


Definition stepping (partial_path : V_list) (taxiway_names : list V_list): list V_list :=
  match partial_path with
  | [] => []
  | cur_vertex::rest_partial_path => V_list 
 
Print map.
Fixpoint dfs (cur_stack : list V_list) (end_vtx : Vertex) (taxiway_names : list V_list): list V_list :=
  match cur_stack with
  | [] => []
  | partial_path::rest_cur_stack => step partial_path ++ (dfs rest_cur_stack

Fixpoint dfs_wrapper (start_vtx : Vertex) (end_vtx : Vertex) (taxiway_names : list V_list): list V_list :=
  dfs [[start_vtx]] end_vtx taxiway_names. 