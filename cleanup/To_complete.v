(*
    This file describes the function to expand a naive graph into a complete graph.
    We need to prove that it's reasonable to expand -> run algorithm -> downward

    TODO: May use List.incl to write F f = id
    TODO: rewrite the expansion (if necessary)
*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Coq.Program.Tactics.

From Taxiway Require Import Types.
From Taxiway Require Import Example. 

Definition Edge_inv (edge : Edge_type) : Edge_type := 
    ((edge.1.2, edge.1.1), edge.2).

    (* add inverse of every edge, subtract the reversed input edge *)
Definition undirect_to_bidirect (ng : N_Graph_type) : N_Graph_type := 
    filter (fun x => negb (eqv x.1.1 input)) (flat_map (fun edge => [edge; Edge_inv edge]) ng).

(* every edge that goes to cur.1.2 except (Edge_inv cur) *)
(* NOTE ng must be bidirected *)
Definition previous_edges (cur : Edge_type) (bg : N_Graph_type) : list Edge_type :=
    filter (fun x => (eqv x.1.1 cur.1.2) && negb (eqv x.1.2 cur.1.1)) bg.

(* NOTE bg must be bidirected *)
(* geenrate edges in complete graph related to a single edge (input) *)
Definition generate_edges (bg : N_Graph_type) (edge : Edge_type) : list Arc_type :=
    map (fun x => ((x.1, edge.1), edge.2)) (previous_edges edge bg).

Definition to_C (ng : N_Graph_type) : C_Graph_type :=
    let bg := undirect_to_bidirect ng in
        flat_map (generate_edges bg) bg.


(* examples *)
Example A: Vertex := index 1.
Example B: Vertex := index 2.
Example C: Vertex := index 3.
Example D: Vertex := index 4.
Example E: Vertex := index 5.


Example AB: Edge_type := (A, B, "x").
Example BA: Edge_type := (B, A, "x").
(* ========== testcase ========== *)
(*
    A testcase for the to_C function on ann arbor case.
*)
(* Definition eqe (e1 :Arc_type) (e2:Arc_type) : bool :=
    (eqv e1.1.1.1 e2.1.1.1) &&
    (eqv e1.1.1.2 e2.1.1.2) &&
    (eqv e1.1.2.1 e2.1.2.1) &&
    (eqv e1.1.2.2 e2.1.2.2) &&
    (e1.2 =? e2.2).

Fixpoint in_list_b (e : Arc_type) (le : list Arc_type) : bool :=
    match le with
    | [] => false
    | h::t => if eqe h e then true else in_list_b e t
    end.

Fixpoint two_list_inclusion (l1 : list Arc_type) (l2 : list Arc_type) : bool :=
    match l1 with
    | [] => true
    | h::t => (in_list_b h l2) && two_list_inclusion t l2
    end.

Eval compute in two_list_inclusion ann_arbor (to_C naive_ann_arbor) 
    && two_list_inclusion (to_C naive_ann_arbor) ann_arbor. *)

