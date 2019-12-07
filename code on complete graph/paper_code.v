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


    State_type : ((list Edge_type * string), list string)
        ((results, current_taxiway), rest_ATC)

    Result : option (list Edge_type)
*)



Definition Node_type : Type := (Vertex * Vertex).
Definition Edge_type : Type := (Node_type * Node_type) * string.
Definition Graph_type : Type := list Edge_type.

Inductive Result_type : Type :=
    | M_NONE
    | M_ERROR
    | M_SOME (result: (list Edge_type)).
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


(* implementation of find_edge *)
Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Definition edge_filter (current : Node_type) (e : Edge_type) : bool :=
    (eqv current.1 e.1.1.1) && (eqv current.2 e.1.1.2).

Definition find_edge (current : Node_type) (D : Graph_type) : list Edge_type :=
    filter (edge_filter current) D.



(* Small functions *)
Definition name (e : Edge_type) : string :=
    snd e.

(* add M_NONE to Results won't change Results*)
(* the order doesn't matter *)
Definition add (res : Result_type) (Results : Result_type) : Result_type :=
    match Results with
    | M_ERROR => M_ERROR    (* pass M_ERROR whenever*)
    | M_SOME _ => match res with
                | M_ERROR => M_ERROR
                | M_NONE => Results
                | M_SOME _ => M_ERROR
                end
    | M_NONE => match res with
                | M_ERROR => M_ERROR
                | M_NONE => Results
                | M_SOME _ => res
                end
    end.


Definition condition_if (current_taxiway_name : option string) (name_e : string) : bool :=
    match current_taxiway_name with
    | None => false
    | Some x => (x =? name_e)
    end.





(* Version directly translated from the paper*)

Fixpoint INNER_FOREACH (edges : list Edge_type) (results : Result_type) (D : Graph_type) (current : Node_type) (destination : Vertex) (taxiway_names : list string) (current_taxiway_name : option string) : Result_type :=
    match edges with
    | [] => M_NONE    (*add M_NONE to result won't change result*)
    | e :: rest =>  add (add (INNER_FOREACH (tail edges) results D current destination taxiway_names current_taxiway_name) (* the iteration *)
                        (if (condition_if current_taxiway_name (name e)) then (*the first if, case b*)
                            (FIND_PATH_AUX D (e.1.2) destination taxiway_names current_taxiway_name) else M_NONE ))  (* M_NONE won't influence the result*)
                        (if condition_if (head taxiway_names) (name e)  then (*assume case c, case b won't both happen*)
                            (FIND_PATH_AUX D (e.1.2) destination (tail taxiway_names) (head taxiway_names)) else M_NONE)
    end.
                    

Fixpoint FIND_PATH_AUX (D : Graph_type) (current : Node_type) (destination : Vertex) (taxiway_names : list string) (current_taxiway_name : option string) : Result_type :=
    add 
        (if taxiway_names==[] & (eqv current.2 destination then [] else M_NONE)) 
        INNER_FOREACH (find_edge current D) M_NONE D current destination taxiway_names current_taxiway_name.


Definition FIND_PATH (D : Graph_type) (start : Vertex) (destination : Vertex) (ATC : list string) : option (list Edge_type) :=
    match FIND_PATH_AUX D (start, input) destination ATC M_NONE with
    | M_NONE => M_NONE
    | M_ERROR => M_NONE
    | Some res => res
    end.
