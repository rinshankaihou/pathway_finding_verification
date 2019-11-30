Require Import Coq.Strings.String.
Open Scope string_scope.

From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
Require Import Coq.Lists.List Coq.Bool.Bool.


(* string library will overlap vertex (the ctor index), import it first  *)

(*
Using state (V_list, list string) to represent a 
    - fst is a list of vertices that previously visited, first is current 
    - snd is the remaining ATC commend, first is current

For each state, we:
    1. get all nodes it points to
    2. drop the most recently visited node
    3. drop all the nodes not on current/next taxiway in ATC command
    4. pack the rest for further check (recursively or iteratively)

We should be using the None type, since we need map vertex to it's edges
But...It seems we don't need option type...

    Basic Type: 
        Taxiway Name: string
        Vertex: Vertex or string (it's just an indicator)
        Graph: list (Vertex * (Vertex * string))
            - it's a list of (current vertex, (connected-to vertex, taxiway of connected-to))
            - i.e. the set of edges (directed)
            - it's consistent with the input csv

        State_type : Type := V_list * list string.
            - V_list is the previous visited node, in reverse order
            - list string is the rest ATC

        Node_type : Type := Vertex * string
            - the information pair of a vertex

        Edge_type : Type := Vertex * (Vertex * string)
            - the edge
            - (cur_vertex, (connected-to vertex, taxiway between them))

        Graph_type : Type := list Edge_type.
            - contains every edges


    Key functions:
        vertex_connect_to: Vertex -> Graph -> list Node_type
            - accept current vertex and graph, return the edge lists of it
            - will filter those not on current taxiway
            - map the vertex to all nodes it connects to
            - using list filter for the fst, check the equality
        
        v2e_map : Vertex -> Graph -> list Edge_type
            - used to implement vertex_connect_to
            - we can skip it, but maybe for future use

        get_next_states: State_type -> Graph -> list State_type
            - accept current state, return a list of next possible states


based on naive graph, if want to change to complete graph, just change Vertex to (Vertex, Vertex),
indicating (current, from)
*)

Definition Node_type : Type := Vertex * string.
Definition State_type : Type := V_list * list string.
Definition Edge_type : Type := Vertex * (Vertex * string).
Definition Graph_type : Type := list Edge_type.

Example AA3 := index 1.
Example AB := index 2.
Example AC := index 3.
Example AA1 := index 4.
Example Ch := index 5.
Example BC := index 6.
Example A3r := index 7.
Example A2r := index 8.
Example A1r := index 9.

Example tA := "A".
Example tB := "B".
Example tC := "C".
Example tA1 := "A1".
Example tA2 := "A2".
Example tA3 := "A3".



Example ann_arbor : Graph_type := [
    (Ch, (BC, tC));
    (A3r, (AA3, tA3));
    (A2r, (AB, tA2));
    (A1r, (AA1, tA1));
    (AA3, (A3r, tA3)); (AA3, (AB, tA));
    (AB, (A2r, tA2)); (AB, (AA3, tA)); (AB, (BC, tB)); (AB, (AC, tA));
    (AC, (AA1, tA)); (AC, (BC, tC)); (AC, (AB, tA));
    (AA1, (A1r, tA1)); (AA1, (AC, tA));
    (BC, (Ch, tC)); (BC, (AC, tC)); (BC, (AB, tB))
].


(* basic functions, copy form last file*)
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

Fixpoint v_in_vlist (v : Vertex) (vlst : V_list) : bool :=
  match vlst with
  | [] => false
  | a :: rst => if eqv a v then true else v_in_vlist v rst
  end.


(* the map function, using list filter *)

Definition v2e_map_filter (cur_v : Vertex) (edge : Edge_type) : bool :=
    eqv cur_v (fst edge).

(*for flat_map way*)
(* Definition v2e_map_filter (cur_v : Vertex) (edge : Edge_type) : list Edge_type :=
    match eqv cur_v (fst edge) with
    | true => [edge]
    | false => []
    end. *)

Eval vm_compute in v2e_map_filter AB (AB, (AC, tA)).


Definition v2e_map (cur_v : Vertex) (graph : Graph_type) : list Edge_type :=
    filter (v2e_map_filter cur_v) graph.

Eval vm_compute in v2e_map AB ann_arbor.

(* if node (should be a neighbor) is on this/next taxiway *)
Definition if_valid_neighbor (cur_s : State_type) (node : Node_type) : bool :=
    match snd cur_s with
    | [] => false       (*won't happen*)
    | a :: nil => a =? snd node
    | a :: b :: _ => (a =? snd node) || (b =? snd node)
    end.

(* if the most recent vertex in cur_s is not node *)
Definition not_last_node (cur_s : State_type) (node : Node_type) : bool :=
    match head (tail (fst cur_s)) with
    | None => true (*won't happen*)
    | Some a => if eqv a (fst node) then false else true
    end.

(* return a list of neighbor nodes that are 1.reachable with current ATC 2.not the most recently visited node *)
Definition vertex_connect_to (cur_s : State_type) (graph : Graph_type) : list Node_type :=
    match head (fst cur_s) with
    | None => []    (*will never encounter*)
    | Some v => filter (not_last_node cur_s) (filter (if_valid_neighbor cur_s) (map snd (v2e_map v graph)))
    end.    


Eval vm_compute in vertex_connect_to ([BC; Ch], [tC;tB]) ann_arbor.




(* get the next states of a given taxiway *)


(* if node is on next taxiway *)
Definition if_on_next_taxi (node : Node_type) (cur_s : State_type) : bool :=
    match snd cur_s with
    | [] => false       (*won't happen*)
    | _ :: nil => false
    | a :: b :: _ => b =? (snd node)
    end.

(* Check if a node is valid, and pack it to state*)
(* After dropping last node, filtering taixway, the result should be a state*)
Definition neighbor_packer (cur_s : State_type) (node : Node_type) : list State_type :=
    if if_on_next_taxi node cur_s then [((fst node)::(fst cur_s), tail (snd cur_s))] else [((fst node)::(fst cur_s), snd cur_s)].


Eval vm_compute in neighbor_packer ([BC;Ch], [tC;tB]) (AB, tB).


Definition get_next_states (cur_s : State_type) (graph : Graph_type) : list State_type :=
    flat_map (neighbor_packer cur_s) (vertex_connect_to cur_s graph).

Eval vm_compute in get_next_states ([BC;Ch], [tC;tB]) ann_arbor.





(* find path *)

Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match head (fst cur_s) with
    | None => false (* never encounter *)
    | Some a => eqv a end_v && (length (snd cur_s) == 1)
    end.


Fixpoint find_path (end_v : Vertex) (graph : Graph_type) (round_bound : nat) (cur_s : State_type) : list V_list :=
    match round_bound with
    | 0 => []
    | S n => 
        ((if if_reach_endpoint cur_s end_v 
         then [rev (fst cur_s)]
         else [])
         ++ (flat_map (find_path end_v graph n) (get_next_states cur_s graph)))
    end
    
.    

Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (taxiway : list string) (graph : Graph_type) : list V_list :=
    find_path end_v graph 100 ([start_v], taxiway).


Eval vm_compute in find_path_wrapper A3r A1r [tA3; tA; tA1] ann_arbor.

Example eg_find_path_1 : find_path_wrapper Ch AB [tC] ann_arbor= [].
Proof. reflexivity. Qed.
    
Example eg_find_path_2 : find_path_wrapper Ch BC [tC] ann_arbor= [[Ch; BC]].
Proof. reflexivity. Qed.
    
Example eg_find_path_3 : find_path_wrapper Ch AA3 [tC;tB;tA] ann_arbor= [[Ch; BC; AB; AA3]].
Proof. reflexivity. Qed.
    
Example eg_find_path_4 : find_path_wrapper AA3 AA1 [tA;tB;tC;tA] ann_arbor= [[AA3; AB; BC; AC; AA1]].
Proof. reflexivity. Qed.
    
Example eg_find_path_5 : find_path_wrapper A3r A1r [tA3; tA; tA1] ann_arbor= [[A3r; AA3; AB; AC; AA1; A1r]].
Proof. reflexivity. Qed.
    
Example eg_find_path_6 : find_path_wrapper Ch Ch [tC; tB; tA; tC; tB; tA; tC] ann_arbor= [[Ch; BC; AB; AC; BC; AB; AC; BC; Ch]].
Proof. reflexivity. Qed.


(* The recursive version of find_path *)

