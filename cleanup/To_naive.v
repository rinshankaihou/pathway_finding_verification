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
From Taxiway Require Import Example.

From Hammer Require Import Hammer.
(* ========== downward function ========== *)
Locate " {} + {}".

Definition dec_Vertex_Type : forall (a b : Vertex), {a = b} + {a <> b}.
Proof. intros. destruct (eqv a b) eqn : H.
    - left. hammer.
    - right. hammer.
Defined.

Definition dec_Node_Type : forall (a b : Node_type), {a = b} + {a <> b}.
Proof. intros. Admitted.

Definition dec_Arc : forall (a b : Arc_type), {a = b} + {a <> b}.
Proof. intros. Print C_Edge_type. Admitted.

Definition to_N (le : list Edge_type) : list Arc_type := 
    nodup dec_Arc (map (fun ce => (ce.1.2, ce.2)) le).

Eval compute in to_N [(((Ch, BC), (Ch, AA3)), B); (((Ch, BC), (Ch, AA3)), B)].
Example xm : to_N [(((Ch, BC), (Ch, AA3)), B); (((Ch, BC), (Ch, AA3)), B)] = [((Ch, AA3), B)].
Proof. compute. reflexivity. Qed.