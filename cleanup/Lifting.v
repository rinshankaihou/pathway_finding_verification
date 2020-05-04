(*
    This file proves the theorem related to expansion and downward
*)
From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
From Taxiway Require Import To_complete To_naive Types.
From Hammer Require Import Hammer.

Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Setoid.
Require Import Relations.
Require Import Compare_dec.
Require Import ArithRing. 
Require Import Omega.
Require Import Coq.Program.Tactics.
(* ========== downward properties ========== *)

(*
    we'll have five properties, the form should be

    (In Cp CG -> properties holds for Cp in CG) ->
        In Np (to_N CG) -> properties holds for Np in (to_N CG).
    
    The properties need to be rewrited for naive graph
*)


(* ========== identity property ========== *)
Locate ".1".
Theorem toC_toN_id : forall G,
    (forall ne, In ne G -> 
        ne.1.1 <> ne.1.2) -> (* no self loop *)
    (forall ne, In ne G -> 
        exists prev_ne, In prev_ne (previous_edges ne (undirect_to_bidirect G))) (* any edge has a previous edge *)
    -> incl G (to_N (to_C G)).

Proof. intros G Hno_self_loop Hexist_prev.
remember (undirect_to_bidirect G) as bg.
unfold incl. intros ne H.
(* WTS In ne G'', where G'' = (toN toC G'), where G' = [ne, prev_ne] *)
assert (Hexist_prev_ne: exists prev_ne, 
    In prev_ne (previous_edges ne (undirect_to_bidirect G))). {
    hammer.
}
destruct Hexist_prev_ne as [prev_ne Hprev_ne].
clear Hexist_prev.
remember (to_N (to_C [ne; prev_ne] )) as G''.
destruct ne as [neEndStart neTaxi] eqn:Hne1.
destruct neEndStart as [neEnd neStart] eqn:Hne2.
assert (Hne3: (eqv neStart neEnd) = false). {
    apply Hno_self_loop in H; simpl in H.
    admit. (* TODO can do better *)
}
assert (Hne3_equiv: (eqv neEnd neStart) = false). {
    rewrite <- Hne3.
    admit.  (* TODO can do better *)
}
assert (Hne4: (eqv neStart neStart)) by admit.
assert (Hne5: (eqv neEnd neEnd)) by admit.
assert (In ne G''). {
    (* 4 situations, whether ne_start/end ?= Types.input *)
    destruct (negb (Types.eqv neEnd Types.input)) eqn: Hend.
    + destruct (negb (Types.eqv neStart Types.input)) eqn: Hstart.
        - 
        rewrite -> HeqG'. rewrite <- Hne1. unfold to_C. 
        remember (undirect_to_bidirect [ne; prev_ne ]) as b_G' eqn: Hbg_ne. (* bidirected graph from [ne] *)
        rewrite -> Hne1 in Hbg_ne. rewrite <- Hbg_ne.
        (* eval bg_ne *)
        unfold undirect_to_bidirect in Hbg_ne. simpl in Hbg_ne.
        rewrite -> Hend in Hbg_ne; rewrite -> Hstart in Hbg_ne; simpl in Hbg_ne.
        unfold Edge_inv in Hbg_ne; simpl in Hbg_ne.
        (* eval (generate_edges bg_ne) *)
        unfold generate_edges, previous_edges. simpl.
        rewrite -> Hbg_ne. simpl.
        try rewrite -> Hne3; try rewrite -> Hne3_equiv; try rewrite -> Hne4; try rewrite -> Hne5; simpl.
        rewrite -> Hend; rewrite -> Hstart; simpl.
}


unfold generate_edges. unfold to_N.
