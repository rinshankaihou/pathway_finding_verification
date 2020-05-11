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

(* outputs in (previous_edges ne bg) are in bg *)
Lemma prev_edge_in_bi_G: forall G ne prev_ne,
    In ne G ->
    In prev_ne (previous_edges ne (undirect_to_bidirect G)) ->
    In prev_ne (undirect_to_bidirect G).
Proof.
intros.
unfold previous_edges in H0.
remember (undirect_to_bidirect G) as bg.
apply filter_In in H0. destruct H0. assumption.
Qed.

Lemma prev_edge_prop: forall prev_ne ne G,
    In ne G ->
    In prev_ne (previous_edges ne (undirect_to_bidirect G)) ->
    prev_ne.1.1 =v= ne.1.2 /\ prev_ne.1.2 >v< ne.1.1.
Proof.
intros. unfold previous_edges in H0. apply filter_In in H0. destruct H0. apply andb_true_iff in H1. easy.
Qed.
(* undirect_to_bidirect preserve original edges *)
Lemma undirect_edge_in_bi_G: forall G undir_e,
    In undir_e G ->
    undir_e.1.1 >v< input ->
    In undir_e (undirect_to_bidirect G).
Proof. intros. unfold undirect_to_bidirect. apply filter_In. split.
- apply in_flat_map. exists undir_e. split. intuition. intuition. 
- intuition.
Qed.

Definition no_self_loop (G: N_Graph_type) : Prop :=  (forall ne, In ne G -> ne.1.1 <> ne.1.2).



Lemma no_self_loop_in_bg: 
    forall G,
    no_self_loop G -> no_self_loop (undirect_to_bidirect G).
Proof.
intros G H. unfold no_self_loop. intros. unfold undirect_to_bidirect in *.
apply filter_In in H0. destruct H0. apply in_flat_map in H0. destruct H0 as [e hyp]; destruct hyp.
unfold no_self_loop in H. 
simpl in H2. destruct H2.
- hammer.
- hammer.
Qed.

Definition no_input_vertex (G: N_Graph_type) : Prop :=  
    (forall ne, In ne G -> (ne.1.1 >v< input) /\ (ne.1.2 >v< input)).

Lemma no_input_vertex_in_bg:
    forall G,
    no_input_vertex G -> no_input_vertex (undirect_to_bidirect G).
Proof. intros. unfold no_input_vertex. intros. unfold undirect_to_bidirect in H0.
apply filter_In in H0. destruct H0. apply in_flat_map in H0. destruct H0 as [e hyp]; destruct hyp.
unfold no_self_loop in H. 
simpl in H2. destruct H2.
- hammer.
- hammer.
Qed.

Lemma negb_veq_refl:
    forall v1 v2, v1 >v< v2 <-> v2 >v< v1.
Proof. hammer. Qed.

(* ========== identity property ========== *)
Theorem toC_toN_id : forall (ne: Edge_type) (G: N_Graph_type),
    no_self_loop G -> (* no self loop *)
    In ne G ->
    (exists prev_ne, In prev_ne (previous_edges ne (undirect_to_bidirect G))) -> (* ne has a previous edge in the bidirect graph *)
    (forall ne, In ne G ->
        (ne.1.1 >v< input) /\ (ne.1.2 >v< input)) -> (* input vertex should not appear in any naive graph *)
    In ne (to_N (to_C G)).

Proof. intros ne G Hno_self_loop Hne_in_G Hexist_prev Hno_input.
unfold to_C. 
remember (undirect_to_bidirect G) as bg.
unfold generate_edges.
destruct Hexist_prev as [prev_ne Hprev_ne].

remember (to_N (to_C [ne; prev_ne] )) as G''.
destruct ne as [neEndStart neTaxi] eqn:Hne1.
destruct neEndStart as [neEnd neStart] eqn:Hne2.
assert (Hne3: neStart >v< neEnd). {
    apply Hno_self_loop in Hne_in_G; simpl in Hne_in_G.
    apply eqv_inv. hammer. 
}
(* properties about ne and prev_ne *)
assert (Hne6: (ne.1.1 >v< input) /\ (ne.1.2 >v< input)) by hammer.
rewrite -> Hne1 in Hne6; simpl in Hne6.
destruct Hne6 as [Hne6 Hne7].

assert(Hprev_ne_in_bg: In prev_ne bg). {
    rewrite -> Heqbg.
    apply prev_edge_in_bi_G with (ne:= ne). hammer.
    hammer.
}
assert (Hprev_ne1: (prev_ne.1.1 >v< input) /\ (prev_ne.1.2 >v< input)). {
    assert (Hprev_ne1_equiv: no_input_vertex (undirect_to_bidirect G)). {
        apply no_input_vertex_in_bg. unfold no_input_vertex. easy.
    }
    rewrite <- Heqbg in Hprev_ne1_equiv. 
    unfold no_input_vertex in Hprev_ne1_equiv. apply Hprev_ne1_equiv.
    assumption.
}
destruct Hprev_ne1 as [Hprev_ne1 Hprev_ne2].
assert (Hprev_ne3: prev_ne.1.1 =v= ne.1.2 /\ prev_ne.1.2 >v< ne.1.1). {
    apply prev_edge_prop with (G:=G). hammer. hammer.
}
rewrite -> Hne1 in Hprev_ne3; simpl in Hprev_ne3.
destruct Hprev_ne3 as [Hprev_ne3 Hprev_ne4].
assert (Hprev_ne5: (prev_ne.1.1 >v< prev_ne.1.2)). {
    rewrite -> Heqbg in Hprev_ne_in_bg.
    apply no_self_loop_in_bg in Hprev_ne_in_bg.
    apply eqv_inv.
    assumption.
    assumption.
}

assert  (Hprev_ne6: (prev_ne.1.2 =v= neStart) = false). {
    apply eqv_eq in Hprev_ne3. rewrite Hprev_ne3 in Hprev_ne5.
    clear - Hprev_ne5. apply eqv_rewrite_2 in Hprev_ne5.
    destruct (prev_ne.1.2 =v= neStart) eqn: Htemp.
    - apply eqv_eq in Htemp. symmetry in Htemp. apply eqv_eq in Htemp. rewrite Hprev_ne5 in Htemp. intuition.
    - intuition.           
}

assert (In ne G''). {
    (* 4 situations, whether ne_start/end ?= Types.input *)
    destruct (negb (Types.eqv neEnd Types.input)) eqn: Hend.
    + destruct (negb (Types.eqv neStart Types.input)) eqn: Hstart.
        - 
        rewrite -> HeqG''. rewrite <- Hne1. unfold to_C. 
        remember (undirect_to_bidirect [ne; prev_ne ]) as b_G' eqn: Hbg_ne. (* bidirected graph from [ne] *)
        rewrite -> Hne1 in Hbg_ne.
        (* eval bg_ne *)
        unfold undirect_to_bidirect in Hbg_ne. simpl in Hbg_ne.
        rewrite -> Hend in Hbg_ne; rewrite -> Hstart in Hbg_ne; simpl in Hbg_ne.
        unfold Edge_inv in Hbg_ne; simpl in Hbg_ne.
        rewrite -> Hprev_ne1 in Hbg_ne; rewrite -> Hprev_ne2 in Hbg_ne; simpl in Hbg_ne. 
        (* eval (generate_edges bg_ne) *)
        unfold generate_edges, previous_edges.
        rewrite -> Hbg_ne. simpl.

        Ltac choose_branch term hyp :=
            assert (hyp: term) by hammer; rewrite hyp; simpl.
        assert((neEnd >v< neStart)). {
            apply negb_veq_refl in Hne3. assumption.
        }
        choose_branch ((neEnd =v= neStart) && (neStart >v< neEnd) = false) branch1.
        choose_branch ((neStart =v= neStart) && (neEnd >v< neEnd) = false) branch2.
        choose_branch ((prev_ne.1.1 =v= neStart) && (prev_ne.1.2 >v< neEnd) = true) branch3.
        right.
        
        choose_branch  ((prev_ne.1.2 =v= neStart) && (prev_ne.1.1 >v< neEnd) = false) branch4.
        choose_branch ((neEnd =v= neEnd) && (neStart >v< neStart) = false) branch5.
        choose_branch ((neStart =v= neEnd) && (neEnd >v< neStart) = false) branch6.
        choose_branch ((prev_ne.1.1 =v= neEnd) && (prev_ne.1.2 >v< neStart) = false) branch7.
        choose_branch ((prev_ne.1.2 =v= neEnd) && (prev_ne.1.1 >v< neStart) = false) branch8.
        
        assert ((neEnd =v= prev_ne.1.2) = false). {
            apply negb_veq_refl in Hprev_ne4.
            hammer.
        }
        choose_branch ((neEnd =v= prev_ne.1.2) && (neStart >v< prev_ne.1.1) = false) branch9.
        choose_branch ((neStart =v= prev_ne.1.2) && (neEnd >v< prev_ne.1.1) = false) branch10.
        choose_branch ((prev_ne.1.1 =v= prev_ne.1.2) && (prev_ne.1.2 >v< prev_ne.1.1) = false) branch11.
        choose_branch ((prev_ne.1.2 =v= prev_ne.1.2) && (prev_ne.1.1 >v< prev_ne.1.1) = false) branch12.
        choose_branch ((neEnd =v= prev_ne.1.1) && (neStart >v< prev_ne.1.2) = false) branch13.
        choose_branch ((neStart =v= prev_ne.1.1) && (neEnd >v< prev_ne.1.2) = true) branch14.
        right.
        choose_branch ((prev_ne.1.1 =v= prev_ne.1.1) && (prev_ne.1.2 >v< prev_ne.1.2) = false) branch15.
        choose_branch ((prev_ne.1.2 =v= prev_ne.1.1) && (prev_ne.1.1 >v< prev_ne.1.2) = false) branch16.

}


unfold generate_edges. unfold to_N.
