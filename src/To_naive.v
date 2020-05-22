(*
    This file descirbes the funtion downward from complete path(arcs) to naive path(edges)
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

From Hammer Require Import Hammer.

(* default is 10, default may cause "Fail to Reconstruct Proof" for low performance CPUs *)
Set Hammer ReconstrLimit 20.

(* ========== downward function ========== *)

(* Define a equivalent relation for Edge_type *)
Definition eq_e (e1:Edge_type) (e2:Edge_type) : bool :=
    (eqv e1.1.1 e2.1.1) && (eqv e1.1.2 e2.1.2) && (e1.2 =? e2.2).

(* eqe is an equivalence relation *)
Lemma eqe_eq:
    forall e1 e2, (eq_e e1 e2 = true) <-> (e1=e2).
Proof. intros. split.
    - intros. unfold eq_e in H. hammer.
    - intros. rewrite H. unfold eq_e. hammer.
Qed.

(* equality of edge is decidable *)
Definition dec_Edge : forall (a b : Edge_type), {a = b} + {a <> b}.
Proof. intros. destruct (eq_e a b) eqn :H.
    - left. hammer.
    - right. hammer.
Defined.

(* the map from an edge to an arc *)
Definition c_to_n : Arc_type -> Edge_type :=
    fun ce => (ce.1.2, ce.2).

(* abandoned *)
Definition to_N_nodup (le : list Arc_type) : list Edge_type := 
    nodup dec_Edge (map c_to_n le).


(* Since we can't apply nodup to path, 
    because we might encounter cases going through on edge multiple times*)
Definition to_N (le : list Arc_type) : list Edge_type :=
    map c_to_n le.


