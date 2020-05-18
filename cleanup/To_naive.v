(*
    This file descirbes the funtion downward from path(arc) to path(edge)
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

(* default is 10, default may cause "Fail to Reconstruct Proof" in make for low performance CPU *)
Set Hammer ReconstrLimit 20.

(* ========== downward function ========== *)
(* Locate " {} + {}". *)


(* unnecessary for arc *)

(* Definition eq_a (a1 : Arc_type) (a2 : Arc_type) : bool :=
    (eq_n a1.1.1 a2.1.1) && (eq_n a1.1.2 a2.1.2) && (a1.2 =? a2.2).

Lemma eqa_eq :
    forall a1 a2, (eq_a a1 a2 = true) <-> (a1=a2).
Proof. intros. split.
    - intros. unfold eq_a in H. hammer.
    - intros. rewrite H. unfold eq_a. hammer.
Qed.   


Definition dec_Arc : forall (a b : Arc_type), {a = b} + {a <> b}.
Proof. intros. destruct (eq_a a b) eqn :H.
    - left. hammer.
    - right. hammer.
Defined. *)

(* Define a equivalent relation for Edge_type *)
Definition eq_e (e1:Edge_type) (e2:Edge_type) : bool :=
    (eqv e1.1.1 e2.1.1) && (eqv e1.1.2 e2.1.2) && (e1.2 =? e2.2).

(* the lemma for bool and Prop relation *)
Lemma eqe_eq:
    forall e1 e2, (eq_e e1 e2 = true) <-> (e1=e2).
Proof. intros. split.
    - intros. unfold eq_e in H. hammer.
    - intros. rewrite H. unfold eq_e. hammer.
Qed.

(* decidable *)
Definition dec_Edge : forall (a b : Edge_type), {a = b} + {a <> b}.
Proof. intros. destruct (eq_e a b) eqn :H.
    - left. hammer.
    - right. hammer.
Defined.

(* the map from an edge to an arc *)
Definition c_to_n : Arc_type -> Edge_type :=
    fun ce => (ce.1.2, ce.2).

(* abandon now *)
Definition to_N_nodup (le : list Arc_type) : list Edge_type := 
    nodup dec_Edge (map c_to_n le).


(* Since we can't apply nodup to path, 
    because we might encounter cases going through on edge multiple times*)
Definition to_N (le : list Arc_type) : list Edge_type :=
    map c_to_n le.


