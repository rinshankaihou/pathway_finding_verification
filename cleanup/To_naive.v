(*
    This file descirbes the funtion and proofs for the properties still hold downward
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
(* From Taxiway Require Import Example. *)

From Hammer Require Import Hammer.
Hammer_cleanup.
(* ========== downward function ========== *)
Locate " {} + {}".

(* Definition dec_Vertex_Type : forall (a b : Vertex), {a = b} + {a <> b}.
Proof. intros. destruct (eqv a b) eqn : H.
    - left. hammer.
    - right. hammer.
Defined. *)


(* Definition eq_n (n1 : Node_type) (n2 : Node_type) : bool :=
    (eqv n1.1 n2.1) && (eqv n1.2 n2.2).

Lemma eqn_eq : 
    forall n1 n2, (eq_n n1 n2 = true) <-> (n1=n2).
Proof. intros. split.
    - intros. unfold eq_n in H. hammer.
    - hammer.
Qed. *)


(* Definition dec_Node_Type : forall (a b : Node_type), {a = b} + {a <> b}.
Proof. intros. destruct (eq_n a b) eqn : H.
    - left. hammer.
    - right. hammer.
Defined. *)

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


Definition eq_e (e1:Edge_type) (e2:Edge_type) : bool :=
    (eqv e1.1.1 e2.1.1) && (eqv e1.1.2 e2.1.2) && (e1.2 =? e2.2).

Lemma eqe_eq:
    forall e1 e2, (eq_e e1 e2 = true) <-> (e1=e2).
Proof. intros. split.
    - intros. unfold eq_e in H. hammer.
    - intros. rewrite H. unfold eq_e. hammer.
Qed.

Definition dec_Edge : forall (a b : Edge_type), {a = b} + {a <> b}.
Proof. intros. destruct (eq_e a b) eqn :H.
    - left. hammer.
    - right. hammer.
Defined.


(* we allow replicants in to_N *)
Definition to_N (le : list Arc_type) : list Edge_type := 
    map (fun ce => (ce.1.2, ce.2)) le.


(* Since we can't apply nodup to path, 
    because we might encounter cases going through on edge multiple times*)
(* Thus to_N_path coincide with to_N, which is desired because it may ease the proof. *)
Definition to_N_path (le : list Arc_type) : list Edge_type :=
    map (fun ce => (ce.1.2, ce.2)) le.


(* Eval compute in to_N [(((Ch, BC), (Ch, AA3)), B); (((Ch, BC), (Ch, AA3)), B)].
Example xm : to_N [(((Ch, BC), (Ch, AA3)), B); (((Ch, BC), (Ch, AA3)), B)] = [((Ch, AA3), B)].
Proof. compute. reflexivity. Qed. *)