(*
    This file proves the theorem related to expansion and downward
*)
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Coq.Program.Tactics.
From Taxiway Require Import To_complete.
From Taxiway Require Import To_naive.

(* ========== downward properties ========== *)

(*
    we'll have five properties, the form should be

    (In Cp CG -> properties holds for Cp in CG) ->
        In Np (to_N CG) -> properties holds for Np in (to_N CG).
    
    The properties need to be rewrited for naive graph
*)


(* ========== identity property ========== *)

Theorem toC_toN_id : forall G, 
    incl (to_N (to_C G)) G.