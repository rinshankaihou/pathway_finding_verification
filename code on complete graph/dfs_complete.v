Require Import Coq.Strings.String.
Open Scope string_scope.

From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
Require Import Coq.Lists.List Coq.Bool.Bool.



(*
    Node_type : (Vertex * Vertex)
        (current, from)
    taxiway : string

    Edge_type : (Node_type * Node_type) * string
        ((end1, end2), taxiway)

    Graph_type : list Edge_type


    State_type : ((list Edge_type * string) * list string)
        ((results, current_taxiway), rest_ATC)

    Result : option (list Edge_type)
*)



Definition Node_type : Type := (Vertex * Vertex).
Definition Edge_type : Type := (Node_type * Node_type) * string.
Definition Graph_type : Type := list Edge_type.


Inductive Result_type : Type :=
    | CANNOT_FIND
    | TOO_MANY_PATH
    | ATC_ERROR
    | SOME_P (result: (list Node_type)).
(* EXAMPLES *)

Example input := index 0.
(* input should be a node meaningless, but only indicate it's input *)

Example AA3 := index 1.
Example AB := index 2.
Example AC := index 3.
Example AA1 := index 4.
Example Ch := index 5.
Example BC := index 6.
Example A3r := index 7.
Example A2r := index 8.
Example A1r := index 9.

Example A := "A".
Example B := "B".
Example C := "C".
Example A1 := "A1".
Example A2 := "A2".
Example A3 := "A3".

Example ann_arbor : Graph_type :=[
    (((Ch, input), (BC, Ch)), C);
    (((A3r, input), (AA3, A3r)), A3);
    (((A2r, input), (AB, A2r)), A2);
    (((A1r, input), (AA1, A1r)), A1);
    (((AA3, A3r), (AB, AA3)), A);
    (((AA3, AB), (A3r, AA3)), A3);
    (((AB, A2r), (AA3, AB)), A);
    (((AB, A2r), (AC, AB)), A);
    (((AB, A2r), (BC, AB)), B);
    (((AB, AA3), (A2r, AB)), A2);
    (((AB, AA3), (AC, AB)), A);
    (((AB, AA3), (BC, AB)), B);
    (((AB, BC), (A2r, AB)), A2);
    (((AB, BC), (AA3, AB)), A);
    (((AB, BC), (AC, AB)), A);
    (((AB, AC), (A2r, AB)), A2);
    (((AB, AC), (AA3, AB)), A);
    (((AB, AC), (BC, AB)), B);
    (((AC, AB), (AA1, AC)), A);
    (((AC, AB), (BC, AC)), C);
    (((AC, AA1), (AB, AC)), A);
    (((AC, AA1), (BC, AC)), C);
    (((AC, BC), (AB, AC)), A);
    (((AC, BC), (AA1, AC)), A);
    (((AA1, A1r), (AC, AA1)), A);
    (((AA1, AC), (A1r, AA1)), A1);
    (((BC, Ch), (AB, BC)), B);
    (((BC, Ch), (AC, BC)), C);
    (((BC, AB), (Ch, BC)), C);
    (((BC, AB), (AC, BC)), C);
    (((BC, AC), (Ch, BC)), C);
    (((BC, AC), (AB, BC)), B)
].


(* =========== find_edge =============*)
Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Definition edge_filter (current : Node_type) (e : Edge_type) : bool :=
    (eqv current.1 e.1.1.1) && (eqv current.2 e.1.1.2).

Definition find_edge (current : Node_type) (D : Graph_type) : list Edge_type :=
    filter (edge_filter current) D.


Definition State_type : Type :=  ((list Node_type) * string) * list string.

(* ============ helper functions ============*)
    
Definition is_on_next_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    match head cur_s.2 with
    | None => false
    | Some t => t =? e.2
    end.
    
Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match head cur_s.1.1 with
    | None => false (*will never reach*)
    | Some n => (eqv n.1 end_v) && (eqn (length cur_s.2) 0)
    end.  
    
    
(* =================  state handler functions ==============*)
(*
    for each edge starts from current:
        if on same taxiway => return [new state]
        else if on next taxiway => return [new state]
        else => return []
    
    using flat_map to operate on all edges 
    
    since (prev, current) won't connect back, so don't need to check back
    the edge in complete graph is naturally valid, so don't to check valid 
*)
    
    
(* The function to pack a edge into a state *)
(* Original Name: neighbor_packer *)
Definition packer (cur_s : State_type) (e : Edge_type) : list State_type :=
    if cur_s.1.2 =? e.2 (* on the same taxiway *)
    then [((e.1.2 ::cur_s.1.1, cur_s.1.2), cur_s.2)]
    else if is_on_next_taxiway cur_s e (* on the next taxiway *)
    then [((e.1.2 ::cur_s.1.1, e.2), tail cur_s.2)]
    else [].
    
    
(* the function to handle a state, to insert possible destinations*)
(* Original Name: get_next_state *)
Definition state_handle (cur_s : State_type) (D : Graph_type) : list State_type :=
    match head cur_s.1.1 with
    | None => []
    | Some n => flat_map (packer cur_s) (find_edge n D)
    end.
    
    
    
(* ================= main function ===============*)
(* we return list list edges as results, it can be map to other type*)
(* 
    The design is that in initial state, edge can't be empty
    Put the initial edge as: ()
*)
Fixpoint find_path (end_v : Vertex) (D : Graph_type) (round_bound : nat) (cur_s : State_type) : list (list Node_type) :=
    match round_bound with
    | 0 => []
    | S n =>
        (if if_reach_endpoint cur_s end_v  (*reach endpoint*)
        then [rev cur_s.1.1]
        else []) ++
        (flat_map (find_path end_v D n) (state_handle cur_s D))
    end.
    
    
Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Node_type)) :=
    match ATC with
    | [] => None (* ATC error *)
    | t :: rest => Some (find_path end_v D 100 (([(start_v, input)], t), rest))
    end.
    
(* 
    This function try to deliver the result, or potential error 
    This function is to replace find_path_wrapper
        1. if only one path, give the result
        2. if two or more path, return too_many_path error
        3. if no result returns, give cannot_find error
        4. if ATC is empty, or we can't start, give atc_error
    It means if we have wrong ATC command such as from Ch->BC, but ATC=A,
        the error will be cannot_find error, since we assume atc is correct
*)

Definition find_path_caller (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : Result_type :=
    match ATC with
    | [] => ATC_ERROR
    | t :: rest => match find_path end_v D 100 (([(start_v, input)], t), rest) with
        | [] => CANNOT_FIND
        | a :: nil => SOME_P a
        | a :: b :: _ => TOO_MANY_PATH
        end
    end.


    
Example eg_find_path_1 : find_path_caller Ch AB [C] ann_arbor = CANNOT_FIND.
Proof. reflexivity. Qed.
    
Example eg_find_path_2 : find_path_caller Ch BC [C] ann_arbor = SOME_P [(Ch, input); (BC, Ch)].
Proof. reflexivity. Qed.
    
Example eg_find_path_3 : find_path_caller Ch AA3 [C;B;A] ann_arbor = SOME_P [(Ch, input); (BC, Ch); (AB, BC); (AA3, AB)].
Proof. reflexivity. Qed.
    
Example eg_find_path_4 : find_path_caller AA3 AA1 [A;B;C;A] ann_arbor = SOME_P [(AA3, input); (AB, AA3); (BC, AB); (AC, BC); (AA1, AC)].
Proof. Abort. (* It's good because AA3 is not a input*)
    
Example eg_find_path_5 : find_path_caller A3r A1r [A3; A; A1] ann_arbor = SOME_P [(A3r, input); (AA3, A3r); (AB, AA3); (AC, AB); (AA1, AC); (A1r, AA1)].
Proof. reflexivity. Qed.
    
Example eg_find_path_6 : find_path_caller Ch Ch [C; B; A; C; B; A; C] ann_arbor
                         = SOME_P [(Ch, input); (BC, Ch); (AB, BC); (AC, AB); (BC, AC); (AB, BC); (AC, AB); (BC, AC); (Ch, BC)].
Proof. reflexivity. Qed.





(* ==================================================================*)
(* ===================== Old Attempts ===============================*)
(* ==================================================================*)

(*
    In this attempt, we store edge in state, but the problem is
        1. we don't need edge, since we already store current taxiway in state
        2. it's not intuitive, since the structure is complex
        3. We can reconstruct list edge from list node
    So we turn to use node


Definition State_type : Type :=  ((list Edge_type) * string) * list string.

(* ============ helper functions ============*)

Definition is_on_next_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    match head cur_s.2 with
    | None => false
    | Some t => t =? e.2
    end.

Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match head cur_s.1.1 with
    | None => false (*will never reach*)
    | Some e => (eqv e.1.2.1 end_v) && (eqn (length cur_s.2) 0)
    end.  


(* =================  state handler functions ==============*)
(*
    for each edge starts from current:
        if on same taxiway => return [new state]
        else if on next taxiway => return [new state]
        else => return []

    using flat_map to operate on all edges 

    since (prev, current) won't connect back, so don't need to check back
    the edge in complete graph is naturally valid, so don't to check valid 
*)


(* The function to pack a edge into a state *)
(* Original Name: neighbor_packer *)
Definition packer (cur_s : State_type) (e : Edge_type) : list State_type :=
    if cur_s.1.2 =? e.2 (* on the same taxiway *)
    then [((e::cur_s.1.1, cur_s.1.2), cur_s.2)]
    else if is_on_next_taxiway cur_s e (* on the next taxiway *)
    then [((e::cur_s.1.1, e.2), tail cur_s.2)]
    else [].


(* the function to handle a state, to insert possible destinations*)
(* Original Name: get_next_state *)
Definition state_handle (cur_s : State_type) (D : Graph_type) : list State_type :=
    match head cur_s.1.1 with
    | None => []
    | Some n => flat_map (packer cur_s) (find_edge n.1.2 D)
    end.



(* ================= main function ===============*)
(* we return list list edges as results, it can be map to other type*)
(* 
    The design is that in initial state, edge can't be empty
    Put the initial edge as: ()
*)
Fixpoint find_path (end_v : Vertex) (D : Graph_type) (round_bound : nat) (cur_s : State_type) : list (list Edge_type) :=
    match round_bound with
    | 0 => []
    | S n =>
        (if if_reach_endpoint cur_s end_v  (*reach endpoint*)
        then [rev cur_s.1.1]
        else []) ++
        (flat_map (find_path end_v D n) (state_handle cur_s D))
    end.


Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Edge_type)) :=
    match ATC with
    | [] => None (* ATC error *)
    | t :: rest => Some (find_path end_v D 100 (([(((start_v, input), (start_v, input)), t)], t), rest))
    end.


(* ============ Map to other result  =========== *)

(* pick the endpoint2 of edge *)
Definition e2n_helper (e : Edge_type) : Node_type := e.1.2.

Definition edge_2_node (le : list Edge_type) : list Node_type :=
    map (e2n_helper) le.

Definition node_result_wrapper (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Node_type)) :=
    match find_path_wrapper start_v end_v ATC D with
    | None => None
    | Some x => Some (map edge_2_node x)
    end.


*)