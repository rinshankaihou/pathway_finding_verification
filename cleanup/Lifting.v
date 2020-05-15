(*
    This file proves the partial identity between expansion map and downward map
    i.e. to_naive (to_complete G) is the subset of G
*)
From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
From Taxiway Require Import To_complete To_naive Types.
From Taxiway Require Import Downward.
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

(* A spec on graph, ensuring that no self-looping *)
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

(* Check if there's "input" vertex *)
Definition no_input_vertex (G: N_Graph_type) : Prop :=  
    (forall ne, In ne G -> (ne.1.1 >v< input) /\ (ne.1.2 >v< input)).

(* a lemma to ensure there's no input vertices left *)
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


(* vertices in the naive graph, ARB *)
(* Example AA3 : Vertex := index 1.
Example AB := index 2.
Example AC := index 3.
Example AA1 := index 4.
Example Ch := index 5.
Example BC := index 6.
Example A3r := index 7.
Example A2r := index 8.
Example A1r := index 9.

(* taxiway name *)
Example A : Taxiway_type := "A".
Example B := "B".
Example C := "C".
Example A1 := "A1".
Example A2 := "A2".
Example A3 := "A3". *)



(* Example G1 : N_Graph_type := [ 
    ((AA1, AC), A);
    ((AA1, A1r), A)
    ].

Theorem toC_toN_id : forall (ne: Edge_type) ,
    no_self_loop G1 -> (* no self loop *)
    In ne G1 ->
    (exists prev_ne, In prev_ne (previous_edges ne (undirect_to_bidirect G1))) -> (* ne has a previous edge in the bidirect graph *)
    (forall ne, In ne G1 ->
        (ne.1.1 >v< input) /\ (ne.1.2 >v< input)) -> (* input vertex should not appear in any naive graph *)
        In ne (to_N (to_C G1)) \/ In (Edge_inv ne) (to_N (to_C G1)).
Proof. intros. simpl in H0. destruct H0.
hammer. hammer. Qed.  *)


(* TODO o put it in types.v *)
Lemma negb_eqv_refl: forall v1 v2, v1 >v< v2 <-> v2 >v< v1.
Proof. intros. split.
- hammer.
- hammer.
Qed.


Lemma negb_eqv_false_equiv: forall v1 v2, (v1 =v= v2) = false -> (v2 =v= v1) = false.
Proof. intros.
apply eqv_rewrite_2. apply negb_eqv_refl. hammer.
Qed.


(* ========== identity property ========== *)

(*  
    We give an specifications on the input undirected graph, while we first expand it to a bi-directional graph.
    The bi-directional graph have the idea of direction, easier for explanation:
    1. No edge is separated alone, i.e. the graph is connected. Or we can't generate a legal arc. 
        Equivalently, every edge can find some previous edges, and exists some previous edge found in bi-directional graph.
    2. there's no self-loop

    We drop all "input" vertices because it's what we hard-coded as extra identifier of some special node. It doesn't effect the graph structure.
*)
Theorem toC_toN_id : forall (ne: Edge_type) (G: N_Graph_type),
    no_self_loop G -> (* no self loop *)
    In ne G ->
    (exists prev_ne, 
    (* ne has a previous edge in the bidirect graph *)
        (In prev_ne (previous_edges ne (undirect_to_bidirect G)) /\ 
    (* exists some previous edge is equivalent to we can find it in the graph G
    WLOG let [ne, prev_ne] be the first two items in bi_G *) 
        exists L, [ne; prev_ne] ++ L = undirect_to_bidirect G)) -> 
    (forall ne, In ne G ->
        (ne.1.1 >v< input) /\ (ne.1.2 >v< input)) -> (* input vertex should not appear in any naive graph *)
    In ne (to_N (to_C G)).

Proof. intros ne G Hno_self_loop Hne_in_G Hexist_prev Hno_input.
unfold to_C. 
remember (undirect_to_bidirect G) as bg.
unfold generate_edges.
destruct Hexist_prev as [prev_ne Hprev_ne].
destruct Hprev_ne as [Hprev_ne Hprev_ne0].

remember (to_N (to_C [ne; prev_ne] )) as G''.
destruct ne as [neEndStart neTaxi] eqn:Hne1.
destruct neEndStart as [neEnd neStart] eqn:Hne2.
assert (Hne3: neStart >v< neEnd). {
    apply Hno_self_loop in Hne_in_G; simpl in Hne_in_G.
    apply eqv_inv. hammer. 
}
assert(Hne4: (neEnd >v< neStart)). {
    apply negb_eqv_refl. assumption.
}
assert(Hne5: (neEnd =v= neStart) = false). {
    hammer.
}
assert(Hne5_2: (neStart =v= neEnd) = false). {
    apply negb_eqv_false_equiv. assumption.
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



assert (lemma: In ne G'' ). {
    (* 4 situations, whether ne_start/end ?= Types.input *)
        rewrite -> HeqG''. rewrite <- Hne1. unfold to_C. 
        remember (undirect_to_bidirect [ne; prev_ne ]) as b_G' eqn: Hbg_ne. (* bidirected graph from [ne] *)
        rewrite -> Hne1 in Hbg_ne.
        (* eval bg_ne *)
        unfold undirect_to_bidirect in Hbg_ne. simpl in Hbg_ne.
        rewrite -> Hne6 in Hbg_ne; rewrite -> Hne7 in Hbg_ne; 
        rewrite -> Hprev_ne1 in Hbg_ne; rewrite -> Hprev_ne2 in Hbg_ne; simpl in Hbg_ne.
        unfold Edge_inv in Hbg_ne; simpl in Hbg_ne.
        (* eval (generate_edges bg_ne) *)
        unfold generate_edges, previous_edges.
        rewrite -> Hbg_ne. simpl.

        Ltac choose_branch term hyp :=
            assert (hyp: term) by hammer; rewrite hyp; simpl.
        choose_branch ((neEnd =v= neStart) && (neStart >v< neEnd) = false) branch1.
        choose_branch ((neStart =v= neStart) && (neEnd >v< neEnd) = false) branch2.
        choose_branch ((prev_ne.1.1 =v= neStart) && (prev_ne.1.2 >v< neEnd) = true) branch3.
        left. unfold c_to_n; simpl. easy.
}

assert(Hne8: (neStart =v= neStart)) by hammer.
assert(Hne9: (neEnd =v= neEnd)) by hammer.
assert (Hprev_ne7: (prev_ne.1.1 =v= neEnd) = false). {
    apply eqv_rewrite_2. apply eqv_inv. apply eqv_eq in Hprev_ne3. rewrite Hprev_ne3.
    apply eqv_inv. assumption.
}

(* eval G''*)
unfold In, to_N, to_C, undirect_to_bidirect, generate_edges, previous_edges in HeqG''; simpl in HeqG''.

Ltac unfold_undir_to_bidir Hprev_ne1 Hprev_ne2 Hne6 Hne7 H :=
    unfold undirect_to_bidirect in H; simpl in H; 
    rewrite -> Hprev_ne1, Hprev_ne2, Hne6, Hne7 in H; simpl. 

Ltac choose_branch_2 term hyp H:=
    assert (hyp: term) by first [apply negb_eqv_false_equiv; easy |  hammer];
    rewrite -> hyp in H; simpl in H.

unfold_undir_to_bidir Hprev_ne1 Hprev_ne2 Hne6 Hne7 HeqG''. 
unfold Edge_inv in HeqG''. simpl in HeqG''.
repeat (
        try rewrite -> Hne3 in HeqG'';
        try rewrite -> Hne4 in HeqG'';
        try rewrite -> Hne5 in HeqG'';
        try rewrite -> Hne5_2 in HeqG'';
        try rewrite -> Hne6 in HeqG'';
        try rewrite -> Hne7 in HeqG'';
        try rewrite -> Hne8 in HeqG'';
        try rewrite -> Hne9 in HeqG'';
        try rewrite -> Hprev_ne1 in HeqG'';
        try rewrite -> Hprev_ne2 in HeqG'';
        try rewrite -> Hprev_ne3 in HeqG'';
        try rewrite -> Hprev_ne4 in HeqG'';
        try rewrite -> Hprev_ne5 in HeqG'';
        try rewrite -> Hprev_ne6 in HeqG'';

        try rewrite -> Hprev_ne7 in HeqG'';
        try rewrite -> Hne1 in HeqG'';
        try unfold Edge_inv in HeqG'';
        try simpl in HeqG''
    ).
choose_branch_2 ((prev_ne.1.2 =v= neEnd) = false) hyp1 HeqG''.
choose_branch_2 ((neEnd =v= prev_ne.1.2) = false) hyp2 HeqG''.
choose_branch_2 ((neStart =v= prev_ne.1.2) = false) hyp3 HeqG''.

assert(hyp4:(prev_ne.1.1 =v= prev_ne.1.2) = false). {
apply eqv_rewrite_2. assumption.
}
rewrite -> hyp4 in HeqG''; simpl in HeqG''.
assert (hyp5: prev_ne.1.1 =v= prev_ne.1.1) by reflexivity.
rewrite -> hyp5 in HeqG''; simpl in HeqG''.
assert (hyp6: prev_ne.1.2 =v= prev_ne.1.2) by reflexivity.
rewrite -> hyp6 in HeqG''; simpl in HeqG''.
choose_branch_2 ( (neEnd =v= prev_ne.1.1) = false) hyp7 HeqG''.
choose_branch_2 ((neStart =v= prev_ne.1.1)) hyp8 HeqG''.
choose_branch_2 ( (prev_ne.1.2 =v= prev_ne.1.1) = false) hyp9 HeqG''.

unfold c_to_n in HeqG''; simpl in HeqG''.


assert(lemma2: In ne (to_N (to_C G))). {
    destruct Hprev_ne0 as [L Hprev_ne0].
    unfold to_C. rewrite <- Heqbg. rewrite <- Hprev_ne0.
     simpl.
    (* evaluate the first generate_edges *)
    Ltac temp Hne1 Hne3 Hne4 Hne5 Hne5_2 Hne6 Hne7 Hne8 Hne9 
    Hprev_ne1 Hprev_ne2 Hprev_ne3 Hprev_ne4 Hprev_ne5 Hprev_ne6 Hprev_ne7 Hprev_ne
    hyp1 hyp2 hyp3 hyp4 hyp5 hyp6 hyp7 hyp8 hyp9:=
        unfold generate_edges at 1; simpl;
        repeat (
            try rewrite -> Hne1;
            try rewrite -> Hne3;
            try rewrite -> Hne4;
            try rewrite -> Hne5;
            try rewrite -> Hne5_2;
            try rewrite -> Hne6;
            try rewrite -> Hne7;
            try rewrite -> Hne8;
            try rewrite -> Hne9;
            try rewrite -> Hprev_ne1;
            try rewrite -> Hprev_ne2;
            try rewrite -> Hprev_ne3;
            try rewrite -> Hprev_ne4;
            try rewrite -> Hprev_ne5;
            try rewrite -> Hprev_ne6;
            try rewrite -> Hprev_ne7;
            try rewrite -> hyp1;
            try rewrite -> hyp2;
            try rewrite -> hyp3;
            try rewrite -> hyp4;
            try rewrite -> hyp5;
            try rewrite -> hyp6;
            try rewrite -> hyp7;
            try rewrite -> hyp8;
            try rewrite -> hyp9;
            try unfold Edge_inv;
            try simpl
        );
        unfold c_to_n; simpl.
    temp Hne1 Hne3 Hne4 Hne5 Hne5_2 Hne6 Hne7 Hne8 Hne9 
        Hprev_ne1 Hprev_ne2 Hprev_ne3 Hprev_ne4 Hprev_ne5 Hprev_ne6 Hprev_ne7 Hprev_ne
        hyp1 hyp2 hyp3 hyp4 hyp5 hyp6 hyp7 hyp8 hyp9.
    left. easy.
}
hammer.
Qed.




(* ========= Make-up for naive_conn ========== *)

(*
    This is a makeup theorem for downward connection property hold for a complete graph generated by to_C
*)


(*  A lemma to ensure that the arc in complete graph follows a consistency
    i.e. in the form ((x, _), (_, x), taxiway)
*)
Lemma to_C_legal: 
    forall (NG: N_Graph_type),
    (forall arc, In arc (to_C NG) -> is_legal_arc arc).
Proof. 
    intros. unfold to_C in H. remember (undirect_to_bidirect NG) as BG.
    unfold generate_edges in H. unfold previous_edges in H.
    apply in_flat_map in H. destruct H as [e H]. destruct H. 
    apply in_map_iff in H0. destruct H0 as [a H0]. destruct H0. 
    apply filter_In in H1. destruct H1. unfold is_legal_arc. 
    unfold undirect_to_bidirect in HeqBG. simpl in HeqBG.    
    assert(a.1.1 =v= e.1.2). hammer. clear H2. 
    hammer.
Qed.



Theorem naive_conn_complete:
    forall (path : list Arc_type) start_v end_v ATC (G : N_Graph_type)  (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (to_C G)) ->
    In path paths ->
    (naive_path_conn (rev (to_N path))).
Proof.
    intros. apply naive_conn with (start_v:=start_v) (end_v:=end_v) (ATC:=ATC) (D:=to_C G) (paths:=paths).
    assumption. assumption.
    assert ((forall arc : Arc_type, In arc (to_C G) -> is_legal_arc arc) -> (forall arc : Arc_type, In arc (tl path) -> is_legal_arc arc)). intros. apply H1. 
    assert (forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    path_in_graph path D). apply output_path_in_graph. unfold path_in_graph in H3. 
    apply H3 with (start_v:=start_v) (end_v:=end_v) (ATC:=ATC) (path:=path) (paths:=paths). assumption. assumption. 
    assumption.
    apply H1. apply to_C_legal with (NG:=G).
Qed.