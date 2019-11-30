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
Definition State_type : Type := (list Node_type) * (list string).
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

(* return true if v is the endpoint of the edge *)
Definition edge_endwith_v (cur_v : Vertex) (edge : Edge_type) : bool :=
    eqv cur_v (fst edge).

(*for flat_map way*)
(* Definition v2e_map_filter (cur_v : Vertex) (edge : Edge_type) : list Edge_type :=
    match eqv cur_v (fst edge) with
    | true => [edge]
    | false => []
    end. *)

Eval vm_compute in edge_endwith_v AB (AB, (AC, tA)).

 (* maps cur_v to neighbors, which is a list of (vertex, taixway) *)
Definition v2e_map (cur_v : Vertex) (graph : Graph_type) : list Edge_type :=
    filter (edge_endwith_v cur_v) graph.

Eval vm_compute in v2e_map AB ann_arbor.

(* if node is on next taxiway *)
Definition if_on_next_taxi (cur_s : State_type) (node : Node_type) : bool :=
    match snd cur_s with
    | [] => false       (*won't happen*)
    | _ :: nil => false
    | a :: b :: _ => b =? (snd node)
    end.

(* if node is on this (current) taxiway *)
Definition if_on_this_taxi (cur_s : State_type) (node : Node_type) : bool :=
    match snd cur_s with
    | [] => false       (*won't happen*)
    | a :: _ => a =? snd node
end.

(* if node (should be a neighbor) is on this/next taxiway *)
Definition if_valid_neighbor (cur_s : State_type) (node : Node_type) : bool :=
    orb (if_on_next_taxi cur_s node)  (if_on_this_taxi cur_s node).

(* if the most recent vertex in cur_s is not node *)
Definition not_last_node (cur_s : State_type) (node : Node_type) : bool :=
    match head (tail (fst cur_s)) with
    | None => true (*won't happen*)
    | Some a => if eqv (fst a) (fst node) then false else true
    end.

(* return a list of neighbor nodes that are 
   1.valid neighbors (see if_valid_neighbor)
   2.not the last visited node *)
Definition vertex_connect_to (cur_s : State_type) (graph : Graph_type) : list Node_type :=
    match head (fst cur_s) with
    | None => []    (*will never encounter*)
    | Some v => filter (not_last_node cur_s) (filter (if_valid_neighbor cur_s) (map snd (v2e_map (fst v) graph)))
    end.    


Eval vm_compute in vertex_connect_to ([(BC, tC); (Ch, tC)], [tC;tB]) ann_arbor.


(* This section are funcs that get the next states of a given taxiway *)


(* Check if a node is valid, and pack it to state *)
(* After dropping last node, filtering taxiway, the result should be a state *)
Definition neighbor_packer (cur_s : State_type) (node : Node_type) : State_type :=
    if if_on_next_taxi cur_s node 
    then (node::(fst cur_s), tail (snd cur_s))
    else (node::(fst cur_s), snd cur_s).

Eval vm_compute in neighbor_packer ([(BC, tC); (Ch, tC)], [tC;tB]) (AB, tB).

Definition get_next_states (cur_s : State_type) (graph : Graph_type) : list State_type :=
    map (neighbor_packer cur_s) (vertex_connect_to cur_s graph).

Eval vm_compute in get_next_states ([(BC, tC); (Ch, tC)], [tC;tB]) ann_arbor.


(* This section are funcs for finding path *)


Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match head (fst cur_s) with
    | None => false (* never encounter *)
    | Some a => eqv (fst a) end_v && (length (snd cur_s) == 1)
    end.


Fixpoint find_path (end_v : Vertex) (graph : Graph_type) (round_bound : nat) (cur_s : State_type) : list (list Node_type) :=
    match round_bound with
    | 0 => []
    | S n => 
        ((if if_reach_endpoint cur_s end_v 
         then [rev (fst cur_s)]
         else [])
         ++ (flat_map (find_path end_v graph n) (get_next_states cur_s graph)))
    end
.

Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (taxiways : list string) 
(graph : Graph_type) : list (list Node_type) :=
    find_path end_v graph 100 ([(start_v, "tC")], taxiways).

(* turn paths in (list (list Node_type)) into V_list. Only for testing. *) 
Definition extract_path (paths : list (list Node_type)): list V_list :=
    map (map fst) paths.

Eval vm_compute in (find_path_wrapper A3r A1r [tA3; tA; tA1] ann_arbor).

Example eg_find_path_1 : extract_path (find_path_wrapper Ch AB [tC] ann_arbor) = [].
Proof. reflexivity. Qed.
    
Example eg_find_path_2 : extract_path (find_path_wrapper Ch BC [tC] ann_arbor) = [[Ch; BC]].
Proof. reflexivity. Qed.
    
Example eg_find_path_3 : extract_path (find_path_wrapper Ch AA3 [tC;tB;tA] ann_arbor) = [[Ch; BC; AB; AA3]].
Proof. reflexivity. Qed.
    
Example eg_find_path_4 : extract_path (find_path_wrapper AA3 AA1 [tA;tB;tC;tA] ann_arbor) = [[AA3; AB; BC; AC; AA1]].
Proof. reflexivity. Qed.
    
Example eg_find_path_5 : extract_path (find_path_wrapper A3r A1r [tA3; tA; tA1] ann_arbor) = [[A3r; AA3; AB; AC; AA1; A1r]].
Proof. reflexivity. Qed.
    
Example eg_find_path_6 : extract_path (find_path_wrapper Ch Ch [tC; tB; tA; tC; tB; tA; tC] ann_arbor) 
                         = [[Ch; BC; AB; AC; BC; AB; AC; BC; Ch]].
Proof. reflexivity. Qed.


(* PROOF FOR SOUNDNESS *)

(* path_valid returns true only if one can traverse the path and follow the atc commands.
   more specifically, it returns true only if:
   for every step to the next node (Vertex, string) in the path,
   the associated taxiway exists, and is either the current or the next taxiway. *)
Fixpoint path_valid_bool (n1 : Node_type) (rest_path : list Node_type) (g : Graph_type) (taxiways : list string) : bool :=
    match rest_path with
    | n2::n_rest =>
        (* if v2 is on current taxiway *)
        if (if_on_this_taxi ([n1;n2], taxiways) (n2))
        then path_valid_bool n2 n_rest g taxiways
        else 
        if (if_on_next_taxi ([n1;n2], taxiways) (n2))
        then path_valid_bool n2 n_rest g (tail taxiways)
        else false (* if n2 is neither on this_taxi nor on next_taxi *)
    | [] => if eqn 1 (length taxiways) then true else false (* the last taxiway will not be consumed *) 
    end
.

Definition path_valid_wrapper (path : list Node_type) (g : Graph_type) (taxiways : list string) : bool :=
    match path with
    | [] => true
    | f::l => path_valid_bool f l g taxiways
    end.

Example path_valid_test : 
forall path, 
(In path (find_path_wrapper Ch Ch [tC; tB; tA; tC; tB; tA; tC] ann_arbor)) ->
(path_valid_wrapper path ann_arbor [tC; tB; tA; tC; tB; tA; tC] = true).
Proof. intros path H. simpl in H. destruct H. 
- rewrite <-H. unfold path_valid_wrapper. unfold path_valid_bool.  reflexivity. 
- contradiction.
Qed.

Definition start_correct (start_v : Vertex) (path : list Node_type) : Prop :=
    match path with
    | [] => False
    | f::r => start_v = (fst f)
    end.

Definition end_correct (end_v : Vertex) (path : list Node_type) : Prop :=
    match rev path with
    | [] => False
    | f::r => end_v = (fst f)
    end.

Definition head_is {T : Type} (elem : T)(l : list T) : Prop :=
    match l with
    | [] => False
    | h::r => elem = h
    end.

Definition n1_n2_connected (n1 n2 : Node_type) (graph : Graph_type) : Prop :=
    In n2 (map snd (v2e_map n1.1 graph)).

Example test_conn : (n1_n2_connected (Ch, tC) (BC, tC) ann_arbor).
Proof. unfold n1_n2_connected. simpl. left. reflexivity. Qed.

(* path is connected *) 
Inductive connected : (list Node_type) -> Graph_type -> Prop :=
| conn_base
     (g : Graph_type):  
     connected [] g
| conn_induct 
     (n1 n2 : Node_type) (nodes : list Node_type) (g : Graph_type)
     (Hconn : n1_n2_connected n1 n2 g)
     (Hnodes_start_with_n2 : head_is n2 nodes)
     (IH : connected nodes g) : 
         connected (n1::nodes) g.


Theorem any_path_in_output_is_valid:
forall start_v end_v taxiways graph path,
In path (find_path_wrapper start_v end_v taxiways graph) ->
start_correct start_v path /\
end_correct start_v path /\
path_valid_wrapper path graph taxiways /\
connected path graph.

