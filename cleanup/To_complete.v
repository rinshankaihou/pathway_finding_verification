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

Definition arc_inv (arc : Arc_type) : Arc_type := 
    ((arc.1.2, arc.1.1), arc.2).

Definition undirect_to_bidirect (ng : N_Graph_type) : N_Graph_type := 
    filter (fun x => negb (eqv x.1.1 input)) (flat_map (fun arc => [arc; arc_inv arc]) ng).

Definition previous_arcs (cur : Arc_type) (ng : N_Graph_type) : list Arc_type :=
    filter (fun x => (eqv x.1.1 cur.1.2) && negb (eqv x.1.2 cur.1.1)) ng.

Definition generate_edges (ng : N_Graph_type) (arc : Arc_type) : list Edge_type :=
    map (fun x => ((x.1, arc.1), arc.2)) (previous_arcs arc ng).

Definition to_C (ng : N_Graph_type) : C_Graph_type :=
    flat_map (generate_edges (undirect_to_bidirect ng)) (undirect_to_bidirect ng).

(* ========== testcase ========== *)
(*
    A testcase for the to_C function on ann arbor case.
*)
(* Definition eqe (e1 :Edge_type) (e2:Edge_type) : bool :=
    (eqv e1.1.1.1 e2.1.1.1) &&
    (eqv e1.1.1.2 e2.1.1.2) &&
    (eqv e1.1.2.1 e2.1.2.1) &&
    (eqv e1.1.2.2 e2.1.2.2) &&
    (e1.2 =? e2.2).

Fixpoint in_list_b (e : Edge_type) (le : list Edge_type) : bool :=
    match le with
    | [] => false
    | h::t => if eqe h e then true else in_list_b e t
    end.

Fixpoint two_list_inclusion (l1 : list Edge_type) (l2 : list Edge_type) : bool :=
    match l1 with
    | [] => true
    | h::t => (in_list_b h l2) && two_list_inclusion t l2
    end.

Eval compute in two_list_inclusion ann_arbor (to_C naive_ann_arbor) 
    && two_list_inclusion (to_C naive_ann_arbor) ann_arbor. *)

