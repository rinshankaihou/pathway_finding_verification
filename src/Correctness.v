(*
    In this project, we proved the correctness of our implementation.

    Theorem is the five properties, 
    Lemma are lemmas used to prove theorem

    We first prove the result is connected and follows ATC, 
        because we can use the lemmas step_states_properties to easily prove other properties
*)

(* ========== Dependency ==========*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.

From Taxiway Require Import Types.
From Taxiway Require Import Implementation.
(*
    Hammer needs at least Vampire, CVC4 and Eprover installed
    We widely use hammer for trivial cases
*)
From Hammer Require Import Hammer.

Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Coq.Program.Tactics.

(* configure Hintdb *)
Hint Resolve beq_nat_refl.

(* 
    Setoid is included in the List actually
    setoid_rewrite can rewrite subterms inside a function
*)
Require Setoid.

(* ========== Tactics ==========*)

(* Here we declare some tactics to replace duplicated work *)

(* hypothesis with the form In elem (flat_map ..) *)
Ltac split_in_flat_map H1 elem output_H1 output_H2 :=
    apply in_flat_map in H1; destruct H1 as [elem output_H1]; destruct output_H1 as [output_H1 output_H2].

(* 
    H_reach_end : if_reach_endpoint s end_v = true,
    H_path_not_empty:  s @1 = (hd :: tl), evidence that s@1 is not empty
    H_reach_end_1 H_reach_end_2: output hypothesiss
*)
Ltac unpack_if_reach_endpoint H_reach_end H_path_not_empty H_reach_end_1 H_reach_end_2:= 
   unfold if_reach_endpoint in H_reach_end; simpl in H_reach_end; 
   rewrite -> H_path_not_empty in H_reach_end;
   apply andb_true_iff in H_reach_end; destruct H_reach_end as [H_reach_end_1 H_reach_end_2]; 
   apply Nat.eqb_eq in H_reach_end_2; apply length_zero_iff_nil in H_reach_end_2;
   apply eqv_eq in H_reach_end_1.

(* 
    for H that contains find_path_aux, split it into [Hl | Hr], 
    AND INTRODUCES Hl AUTOMATICALLY
    note: Hl is first part (before ++) of find_path_aux 
*)
Ltac unpack_find_path_aux_in_H H Hl Hr := unfold find_path_aux in H; apply in_app_or in H; destruct H as [Hl | Hr].

(*
    for H that contains if_reach_endpoint s end_v = true,
    unpack into two goals that 
        hd.1.2.1 = end_v
        s @3 = []

    Not used in the proof
*)
(* Ltac unpack_if_reach_endpoint_in_goal H_path_not_empty:= 
   unfold if_reach_endpoint; simpl; 
   rewrite -> H_path_not_empty;
   apply andb_true_iff; split; 
   [apply Nat.eqb_eq; apply eqv_eq | apply length_zero_iff_nil]. *)


(*
    Apply lemma (find_path_aux_prop) to goal (output_path_prop).
    Where: 
        lemma has the form:
            forall round (s : State_type) end_v D path,
            s@1 <> [] ->
            In path (find_path_aux end_v D round s) ->
            prop

        goal has the form:
            forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
            Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
            In path paths ->
            prop
*)
Ltac aux_to_output lemma := 
    intros start_v end_v ATC D path paths H H0;
    unfold find_path in H;
    destruct ATC as [|ATC_h ATC_t] eqn:H_ATC;
    [inversion H |
        pose (init_s := (State [(start_v, input, (start_v, input), ATC_h)] ATC_h ATC_t []));
        try (
            assert (H_init_s_not_empty : init_s @1 <> []) by hammer; (* {simpl. congruence. } *)
            try (
                apply lemma with
                (round := 100) (end_v := end_v) (D := D) (path := path) (s := init_s) in H_init_s_not_empty;
                repeat hammer
            );
            try (
                apply lemma with
                (round := 100) (end_v := end_v) (D := D) (path := path) (s := init_s);
                repeat hammer
            )
        )   
    ].


(* ========== The path is a connected path ==========*)

(* function to check whether two edges are connected *)
Definition edge_conn (e1 : Edge_type) (e2 : Edge_type) : Prop :=
    e1.1.1 = e2.1.2.

(* 
    function to check whether a path is connected 
    it requires every edge to be connected

    note that the function checks reverse order, since find_path_aux is reversed
*)
Fixpoint path_conn (path : list Edge_type): Prop :=
    match path with
    | path_f::path_r => match path_r with
        | path_s::path_r_r => (edge_conn path_f path_s) /\ (path_conn path_r)
        | [] => True
        end
    | [] => True (* a path shorter than 2 edges is trivially connected *)
    end.

(* a short example, need import Example.v *)
(* Example path_conn_eg1 : path_conn  [(((Ch, input), (BC, Ch)), C);
    (((BC, Ch), (AA3, A3r)), A3)].
Proof. simpl. unfold edge_conn. simpl. split. reflexivity. reflexivity. Qed. *)

(* 
    find_edge returns a connected result
    if e1 ends at node n, then e2 given by find_edge starts at the same node n 
*)
Lemma find_edge_conn : forall e1 e2 n D, e1.1.2 = n -> In e2 (find_edge n D) -> edge_conn e2 e1.
Proof. intros e1 e2 n D H1 H2. unfold find_edge in H2. apply filter_In in H2. destruct H2.
    unfold edge_conn.
    unfold next_edges in H0. rewrite -> H1. apply andb_true_iff in H0. destruct H0. destruct e2.1.1. destruct n.
    Ltac temp H1 := simpl in H1; apply eqv_eq in H1; rewrite H1.
    temp H0. temp H2. reflexivity.
Qed.

(* 
    step_states returns connected result
*)
Lemma step_states_conn : forall ns s D,
    path_conn s@1 ->
    In ns (step_states s D) ->
    path_conn ns@1.
Proof. intros ns s D IH H. unfold step_states in H. unfold hd_error in H.
    destruct s@1 as [| path_hd path_tail] eqn:Hpath.
    - simpl in H. contradiction.
    - apply in_flat_map in H. elim H. intros n_edge H2. destruct H2 as [H2 H3].
        unfold step_state_by_e in H3. 
        unfold if_on_current_taxiway in H3.
        destruct (s@2 =? n_edge.2) eqn:Heqn.
        + (* n_edge on this taxiway *) 
            simpl in H3.
            destruct H3 as [H3|Contra].
            * rewrite <- H3. simpl. rewrite -> Hpath. split.
                {unfold edge_conn. 
                unfold find_edge in H2. simpl in H2. 
                clear Heqn H3 Hpath IH H. 
                apply filter_In in H2. destruct H2 as [H20 H2]. 
                unfold next_edges in H2. apply andb_true_iff in H2. destruct H2 as [H21 H22].
                apply eqv_eq in H21. apply eqv_eq in H22. 
                destruct n_edge.1.1. destruct path_hd.1.2. simpl in H21. simpl in H22.
                rewrite H21. rewrite H22. reflexivity. }
                {assumption. } 
            * contradiction.
        + unfold if_on_next_taxiway in H3. destruct (hd_error s@3) eqn:Heqn2.
            * unfold hd_error in Heqn2. 
                destruct s@3 as [| s'] eqn:Heqn3 in Heqn2.  
                    {inversion Heqn2. } 
                    {inversion Heqn2. 
                    destruct (s0 =? n_edge.2).
                    (* n_edge on next taxiway *)  
                    (* copy proof in the previous case*)
                    - simpl in H3.
                        destruct H3 as [H3|Contra].
                        + rewrite <- H3. simpl. rewrite -> Hpath. split.
                            {unfold edge_conn. 
                            unfold find_edge in H2. simpl in H2.  
                            clear Heqn H3 Hpath IH H Heqn3 Heqn2 H1.
                            apply filter_In in H2. destruct H2 as [H20 H2].
                            unfold next_edges in H2. apply andb_true_iff in H2. destruct H2 as [H21 H22]. 
                            apply eqv_eq in H21. apply eqv_eq in H22. 
                            destruct n_edge.1.1. destruct path_hd.1.2. simpl in H21. simpl in H22. 
                            rewrite H21. rewrite H22. reflexivity. }
                            {assumption. } 
                        + contradiction. 
                    - simpl in H3. contradiction H3. }
        * contradiction.
Qed.

(* 
    find_path_aux returns connected result if the input state is connected
*)
Lemma find_path_aux_conn:
forall round path end_v D  s res,
    path_conn s@1 ->
    res = (find_path_aux end_v D round s) ->
    In path res ->
    path_conn (rev path).
Proof. intros round. induction round as [| rb  IHrb].
    - intros path end_v D  s res H1 H2 H3.
    (* H1: conn cur_path *)
    unfold find_path_aux in H2. rewrite H2 in H3. simpl in H3. contradiction.
    - intros path end_v D  s res H1 H2 H3.
    unfold find_path_aux in H2. destruct (if_reach_endpoint s end_v).
    + (* reached endpoint *) rewrite -> H2 in H3. simpl in H3. 
        destruct H3 as [H4|H5].
        * (* path is rev s @1 *) rewrite <- H4. assert(rev (rev s @1)=s @1). apply rev_involutive.
        rewrite -> H. apply H1. 
        * (* path is given in recursive call of find_path_aux *) 
            fold find_path_aux in H5. fold find_path_aux in H2.
            apply in_flat_map in H5.
            elim H5. intros ns H6. destruct H6 as [H6 H7]. 
            apply IHrb with (res := find_path_aux end_v D rb ns) (end_v := end_v) (D := D) (s := ns).
                {apply step_states_conn with (s := s) (D := D).
                assumption. assumption. }
                {reflexivity. }
                {assumption. }
    + (* not reached end point yet. proof is similar. Consider refactoring? *)
        fold find_path_aux in H2. simpl in H2.
        rewrite -> H2 in H3. rename H3 into H5. (* so that I can copy proof in the previous case directly *)
            apply in_flat_map in H5.
            elim H5. intros ns H6. destruct H6 as [H6 H7]. 
            apply IHrb with (res := find_path_aux end_v D rb ns) (end_v := end_v) (D := D) (s := ns).
                {apply step_states_conn with (s := s) (D := D).
                assumption. assumption. }
                {reflexivity. }
                {assumption. }
Qed.

(* find_path_aux_conn, but without param 'res' *)
Lemma find_path_aux_conn_alt:
forall round path end_v D s,
    path_conn s@1 ->
    In path (find_path_aux end_v D round s) ->
    path_conn (rev path).
Proof. 
    intros round path end_v D s0 H1 H2. apply find_path_aux_conn with (end_v:=end_v) (round:=round) (D:=D) (s:=s0) 
    (res:=(find_path_aux end_v D round s0)).
    assumption. trivial. assumption.
Qed.



(* the top-level theorem for connection, describing the output is always connected *)
Theorem output_path_conn:
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    path_conn (rev path).
Proof.
aux_to_output find_path_aux_conn_alt.
Qed. 


(* ========== The path follows ATC command ==========*)

(* 
    this function extracts the input ATC command from a state,
        which is the invarient in the state
*)
Definition origin_atc (s : State_type) := (rev s@4) ++ [s@2] ++ s@3.

(* 
    path_coresp_atc extracts a path's corresponding atc 
    INPUT: list Edge_type, 
        eg the taxiway names of each edge is like AACCCB 
    OUTPUT: list strings, 
        eg ACB 
*)
Fixpoint path_coresp_atc (path : list Edge_type) : list string :=
    match path with
    | [] => []
    | a::b => match b with
        | []   => [a.2]
        | c::l => if (a.2 =? c.2) 
        then (path_coresp_atc b)
        else a.2::(path_coresp_atc b)
        end 
    end.

(* path_coresp_atc returns empty only if input is empty *)
Lemma coresp_atc_unit : forall path, path_coresp_atc path = [] -> path = [].
Proof.
    intros. induction path. 
    - reflexivity.
    - simpl in H. destruct path.
        + discriminate.
        + destruct (a.2=?e.2).
            * apply IHpath in H. discriminate.
            * discriminate.
Qed. 

(* 
    start to prove that path_coresp_atc and List.rev are commuatative 
    We have two lemmas in order to prove commutative.
*)
Lemma path_coresp_atc_lemma1 : forall (l : seq.seq Edge_type) (b a : Edge_type),
    (b.2 =? a.2) ->
    path_coresp_atc ((l ++ [b]) ++ [a]) = 
    path_coresp_atc (l ++ [b]).
Proof. intro l. induction l as [|hd tl IH].
    - intros b a H. simpl. rewrite -> H. apply String.eqb_eq in H. rewrite H. reflexivity.
    - intros b a H. apply String.eqb_eq in H as H2.
        assert (H3: path_coresp_atc ((tl ++ [b]) ++ [a])%SEQ = path_coresp_atc (tl ++ [b])%SEQ).
            {apply IH. assumption. }
        destruct (tl ++ [b])%SEQ as [|e1 l1] eqn: Hs1.
            {assert(Hcontra: [] <> ((tl ++ [b])%SEQ) ). apply app_cons_not_nil. 
            rewrite -> Hs1 in Hcontra. contradiction. }
        destruct ((tl ++ [b]) ++ [a])%SEQ as [|e2 l2] eqn: Hs2.
            {assert(Hcontra: [] <> ((tl ++ [b]) ++ [a])%SEQ ). apply app_cons_not_nil. 
            rewrite -> Hs2 in Hcontra. contradiction. }
        simpl. rewrite -> Hs2. rewrite -> Hs1.
        rewrite -> Hs1 in Hs2. rewrite <- app_comm_cons in Hs2. inversion Hs2.
        destruct (hd.2 =? e2.2). 
            - rewrite -> app_comm_cons. rewrite <- H1. rewrite <- Hs1.
                apply IH. assumption.
            - rewrite -> app_comm_cons. rewrite <- H1. rewrite <- Hs1.
        assert(Hgoal: (path_coresp_atc ((tl ++ [b])%SEQ ++ [a])%list = path_coresp_atc (tl ++ [b]))).
        {apply IH. assumption. }
        rewrite -> Hgoal. reflexivity.
Qed.

Lemma path_coresp_atc_lemma2 : forall (l : seq.seq Edge_type) (b a : Edge_type),
    (b.2 =? a.2) = false ->
    path_coresp_atc ((l ++ [b]) ++ [a]) = 
    (path_coresp_atc (l ++ [b])) ++ [a.2].
Proof. intro l. induction l as [|hd tl IH].
    - intros b a H. simpl. rewrite -> H. reflexivity.
    - intros b a H. apply String.eqb_neq in H as H2. simpl. 
        assert (H3: path_coresp_atc ((tl ++ [b]) ++ [a])%SEQ  = 
                    ((path_coresp_atc (tl ++ [b])) ++ [a.2])%SEQ ).
        {apply IH. assumption. }
        destruct ((tl ++ [b]) ++ [a])%SEQ as [|e2 l2] eqn: Hs2.
        {assert(Hcontra: [] <> ((tl ++ [b]) ++ [a])%SEQ ). apply app_cons_not_nil. 
            rewrite -> Hs2 in Hcontra. contradiction. }
        destruct (tl ++ [b])%SEQ as [|e1 l1] eqn: Hs1.
        {assert(Hcontra: [] <> (tl ++ [b])%SEQ ). apply app_cons_not_nil. 
            rewrite -> Hs1 in Hcontra. contradiction. }
        simpl. 
        rewrite <- app_comm_cons in Hs2. inversion Hs2.
        rewrite <- H1.
        destruct (hd.2 =? e1.2) eqn: H5. 
        - destruct l1 as [| l1h l1t] eqn: H6.
            + simpl. hammer.
            + simpl. hammer.
        - simpl.
        assert(Hgoal: (match (l1 ++ [a])%list with
            | [] => [e1.2]
            | c :: _ =>
                if e1.2 =? c.2
                then path_coresp_atc (l1 ++ [a])%list
                else e1.2 :: path_coresp_atc (l1 ++ [a])%list
            end)
            = ((match l1 with
            | [] => [e1.2]
            | (c :: _)%SEQ =>
                if e1.2 =? c.2
                then path_coresp_atc l1
                else (e1.2 :: path_coresp_atc l1)%SEQ
            end ++ [a.2]))).
            destruct l1 as [| l1h l1t] eqn: H6. 
                - simpl. hammer.
                - simpl. hammer.  
            (* here is a case better to use setoid_rewrite*)
            setoid_rewrite -> Hgoal. reflexivity. 
Qed.


(* use the two lemmas above to prove the commutativity*)
Lemma path_follow_atc_rev_comm : forall path, 
    path_coresp_atc (rev path) = rev (path_coresp_atc path).
Proof. 
    assert (Rev_lemma: forall {T} (l1 l2 : list T), rev l1 = l2 <-> l1 = rev l2).
    { intros T l1 l2. split. 
    - intro H. rewrite <- H. rewrite -> rev_involutive. reflexivity. 
    - intro H. rewrite -> H. rewrite -> rev_involutive. reflexivity. }
    intro path. induction path as [| a tl IH].
    (* base case *) { reflexivity. }
    destruct tl as [|b l] eqn: Hb.
    {reflexivity. }
    (* now, path = a::b::l, rev path = ra::rb::rl *)
    Ltac refl H H':= apply String.eqb_eq in H as H'.
    destruct (a.2 =? b.2) eqn: Hab. refl Hab Hab'.
        - (* a.2 =? b.2 *)
        simpl. rewrite -> Hab. simpl in IH. simpl. rewrite <- IH.
        apply path_coresp_atc_lemma1. apply String.eqb_eq. symmetry. assumption.
        - (* (a.2 =? b.2) = false *)
        simpl. rewrite -> Hab. simpl in IH. simpl. rewrite <- IH.
        apply path_coresp_atc_lemma2. rewrite -> String.eqb_sym.  assumption.
Qed.

(* 
    function ensures no consecutive duplicationl

    NOTE: it ensures the case in reality, 
        however we don't need it in prove, hence our theorem is stronger
*)
(* Fixpoint no_conn_dup (lst : list string) : Prop :=
    match lst with
    | [] => True
    | f::l => match l with
        | [] => True
        | s::r => (f <> s) /\ no_conn_dup l
        end
    end. *)


(* the function checks whether extracted ATC is same as input atc*)
Definition path_follow_atc (path : list Edge_type) (atc : list string) : Prop :=
    atc = path_coresp_atc path.

(* an example, need to import Example.v*)
(* Example path_follow_atc_eg1 : path_follow_atc  [(((Ch, input), (BC, Ch)),    C);
    (((A3r, input), (AA3, A3r)), A3);
    (((A3r, input), (AA3, A3r)), A3);
    (((A2r, input), (AB, A2r)),  A2);
    (((A2r, input), (AB, A2r)),  A2)]
    [C; A3; A2].
Proof. reflexivity. Qed. *)

(* a function to check whether a state follows ATC*)
Definition state_follow_atc (state : State_type) : Prop := 
    (path_coresp_atc  (rev (state@1))) = (rev ((state@2) :: (state@4))).

(* an example, need to import Example.v*)
(* Example eg_s := (State  [(((Ch, input), (BC, Ch)), C);
        (((A3r, input), (AA3, A3r)), A3);
        (((A3r, input), (AA3, A3r)), A3);
        (((A2r, input), (AB, A2r)),  A2);
        (((A2r, input), (AB, A2r)),  A2)]
    C
    []
    [A3; A2]).

Example state_follow_atc_eg1 : state_follow_atc eg_s.
    Proof. unfold state_follow_atc. reflexivity. Qed. *)

(* if two lists are equal in reversed form, then they're equal *)
Lemma rev_inversion : forall {T : Type} (l1 l2 : list T), rev l1 = rev l2 -> l1 = l2.
Proof. intros T l1 l2 H. assert (H2: rev (rev l1) = rev (rev l2)). rewrite -> H; reflexivity. rewrite -> rev_involutive in H2.
    rewrite -> rev_involutive in H2. assumption. Qed.

(* 
    the result returned by step_states follows ATC is the input follows ATC
*)
Lemma step_states_follow : forall s D n_s hd tl, (* s is cur_state *)
    (s @1 = hd::tl) -> (* cur_path is hd::tl *)
    (s @2 = hd.2) -> (* head of cur_path on atc_t, current atc *)
    state_follow_atc s ->  (* prev state follow atc *)
    In n_s (step_states s D) -> (* n_s is a new_state *)
    state_follow_atc n_s /\ (exists n_hd n_tl, (n_s @1 = (n_hd::n_tl)) /\ (n_s @2 = n_hd.2)).
    (* then n_s follow atcv, and head of new_path on new_atc_hd *)
Proof. intros s D n_s hd tl Hpath Hhd H1 H2.
    unfold step_states in H2.
    unfold state_follow_atc.
    rewrite -> Hpath in H2.
    simpl.
    apply in_flat_map in H2. destruct H2. destruct H as [H2 H3].
    unfold step_state_by_e in H3. destruct (if_on_current_taxiway s x) eqn: H_on_this_taxi.
    + (* on_this_taxiway *)  
        simpl in H3. destruct H3.
        * unfold state_follow_atc in H1. 
        rewrite -> path_follow_atc_rev_comm.
        rewrite -> path_follow_atc_rev_comm in H1.
        apply rev_inversion in H1.
        rewrite <- H. simpl. rewrite -> Hpath. 
        assert(H4: rev s @4 ++ [s @2] = rev ((s @2)::(s @4))) by auto.
        rewrite -> H4.
        assert (Htemp: x.2 =? hd.2).  {
                apply on_current_taxiway_lemma in H_on_this_taxi.
                rewrite -> Hhd in H_on_this_taxi. assumption.
            }
        assert (H_goal: (if x.2 =? hd.2
                        then path_coresp_atc (hd :: tl)
                        else (x.2 :: path_coresp_atc (hd :: tl))%SEQ)
                        = (s @2 :: s @4)).
        {rewrite <- H1. rewrite -> Hpath. 
            rewrite -> Htemp. reflexivity. }
        rewrite H_goal. split. 
            {reflexivity. }
            {exists x. exists (hd::tl). split. 
                - reflexivity. 
                - rewrite -> Hhd. 
                apply String.eqb_eq in Htemp. auto. }
        * contradiction.
    + destruct (if_on_next_taxiway s x) eqn: H_on_next_taxi.
        - (* on_next_taxiway *) 
        simpl in H3. destruct H3 as [H3l | H3r].
        * simpl. unfold state_follow_atc in H1. rewrite <- H3l. simpl.  
            assert (H3 : ((x.2 =? hd.2) = false) ). {
                unfold if_on_next_taxiway in H_on_next_taxi.
                destruct (s @3) as [| atc_t_h atc_t_t].
                + discriminate H_on_next_taxi.
                + unfold if_on_current_taxiway in H_on_this_taxi. rewrite -> Hhd in H_on_this_taxi.
                    rewrite String.eqb_sym in H_on_this_taxi. assumption.
            }
            assert(H4: rev s @1 ++ [x] = rev (x::s @1)) by auto.
            rewrite -> H4. 
            rewrite -> path_follow_atc_rev_comm.
            rewrite -> path_follow_atc_rev_comm in H1.
            apply rev_inversion in H1.
            assert(H5: (rev s @4 ++ [s @2]) ++ [x.2] = rev ([:: x.2, s @2 & (s @4)])) by auto.
            setoid_rewrite -> H5. clear H5.
            assert (H_goal: path_coresp_atc (x :: s @1)
                            = [:: x.2, s @2 & s @4]).
            {
                rewrite <- H1. rewrite -> Hpath.
                unfold path_coresp_atc. 
                assert (Htemp: (x.2 =? hd.2) = false). {
                    unfold if_on_current_taxiway in H_on_this_taxi.
                    rewrite -> Hhd in H_on_this_taxi. rewrite -> String.eqb_sym. exact H_on_this_taxi.
                }
                rewrite -> Htemp. reflexivity.
            }
            rewrite H_goal. split. 
            {reflexivity. }
            { exists x. exists s@1. split.
                - reflexivity.
                - reflexivity. }
            * contradiction.
    * contradiction.
Qed.

(* facts about tl *)
Lemma tl_app : forall {A : Type} (l : list A) (a : A), l <> [] -> tl (l ++ [a]) = (tl l) ++ [a].
Proof. intros. destruct l eqn: H2.
- contradiction.
- simpl. reflexivity.
Qed. 

(* every edge except for the first edge (input edge, hardcoded in init_state) is in D *)
Definition path_in_graph (path : list Edge_type) (D : list Edge_type) : Prop :=
    forall e, In e (tl (path)) -> In e D.
(*
    step_states_properties proves the step_states preserves invarient,
        if we go one step from s to ns, then:
        1. extracted ATC are same by origin_atc
        2. ns has one more edge than s
        3. Every path is passed from s to ns
*)
Lemma step_states_properties : forall s ns D, 
    (s @1) <> [] -> (* cur_path is not empty *)
    In ns (step_states s D) -> (* ns is a new state derived from s *)
    (origin_atc ns = origin_atc s) /\ (* then the ATC are the same *)
    (tl ns@1 = s@1) /\  (* and ns@1 grows s@1 by 1 edge *)
    (path_in_graph (rev s@1) D -> path_in_graph (rev ns@1) D). (* every edge is in D *)
Proof. intros s ns D H1 H2. unfold step_states in H1.
    destruct (s @1) eqn: H_s. 
    {contradiction. } 
    unfold step_states in H2. rewrite H_s in H2. simpl in H2.
    split_in_flat_map H2 n_e H3_1 H3_2.
    unfold step_state_by_e in H3_2. 
    destruct (if_on_current_taxiway s n_e).
    - simpl in H3_2. destruct H3_2.
        + unfold origin_atc. rewrite <- H. rewrite -> H_s. 
        split. * reflexivity.
        split. * auto.
            * intros H_s_in_D e0 H_e_in_path. simpl in *.
            {
            destruct (rev l ++ [e]).
            - auto.
            - simpl in *. 
            apply in_app_or in H_e_in_path.
            destruct H_e_in_path.
                + auto.
                + simpl in *. assert (H2 : n_e = e0) by tauto. rewrite <- H2.
                clear H_s_in_D H0 H2 H1. hammer. 
            }
        + contradiction.
    - destruct (if_on_next_taxiway s n_e) eqn: H_on_next.
        + simpl in H3_2. destruct H3_2.
            * unfold origin_atc. rewrite <- H. simpl.
                unfold if_on_next_taxiway in H_on_next. 
                destruct (s @3) eqn: H_s3.
                { simpl in H_on_next. discriminate H_on_next. }
                { simpl in H_on_next. rewrite -> String.eqb_eq in H_on_next.
                    rewrite <- H_on_next. simpl. rewrite <- app_assoc. split.
                    - auto.
                    split.
                        + auto.
                        + intros H_s_in_D e0 H_e_in_path. rewrite -> H_s in H_e_in_path.
                        destruct (rev l) eqn : H2.
                            * assert (H3 : l = []) by hammer.
                            rewrite -> H3 in *. simpl in *. hammer.
                            * rewrite -> H_s in *.                 
                            rewrite -> tl_app in H_e_in_path.
                            apply in_app_or in H_e_in_path.
                            destruct H_e_in_path.
                            { apply H_s_in_D. simpl. unfold path_in_graph in *. hammer. } 
                            { simpl in *. assert(H4: n_e = e0) by tauto. rewrite <- H4. 
                            clear - H3_1. hammer. }
                            { hammer. }
                }
            * contradiction.
        + contradiction.
Qed. 

(* separate lemmas from last lemma to not break following proof *)
Lemma step_states_preserve_origin_atc : forall s ns D, 
    (s @1) <> [] -> In ns (step_states s D) -> origin_atc ns = origin_atc s.
Proof. apply step_states_properties. Qed.

Lemma step_states_grow_path_by_1 : forall s ns D, 
    (s @1) <> [] -> In ns (step_states s D) -> 
    tl ns@1 = s@1.
Proof. apply step_states_properties. Qed.

(* an alternative of step_states_grow_path_by_1 *)
Lemma step_states_grow_path_by_1_alt : forall s ns D, 
    (s @1) <> [] -> In ns (step_states s D) -> 
    exists new_edge, ns@1 = new_edge :: s@1.
Proof. 
intros. assert (H1 : tl ns @1 = s @1). { 
    apply step_states_grow_path_by_1 with (ns := ns) (D := D) in H.
    1-2: assumption.
} 
destruct ns@1 eqn: H_ns.
    - hammer.
    - exists e. simpl in H1. rewrite <- H1. reflexivity.
Qed.

(* since each time we adds one edge, so it can't be empty*)
Corollary step_states_new_path_not_empty : forall s ns D, 
    (s @1) <> [] -> In ns (step_states s D) ->
    ns@1 <> [].
Proof. intros.
    apply step_states_grow_path_by_1_alt with (ns := ns) (D := D) in H.
    hammer. hammer.
Qed.

(*
    find_path_aux_follow_atc proves that the result of find_path_aux follows ATC command
        if the input state follows ATC command
    
    We mannually seperate ATC = hd::tl, which ensures that ATC is non-empty
*)
Lemma find_path_aux_follow_atc: forall (rb:nat) (end_v:Vertex) (D:Graph_type) (s:State_type) path hd tl,
    s @2 = hd.2 ->
    s @1 = hd::tl->
    state_follow_atc s ->
    In path (find_path_aux end_v D rb s)->
    path_follow_atc path (origin_atc s).
Proof. intro rb. induction rb as [| rb' IHrb].
    - intros end_v D s path hd tl H_hd_on_atc H_path_not_empty H_s_follow H1.
    simpl in H1. contradiction.
    - intros end_v D s path hd tl H_hd_on_atc H_path_not_empty H_s_follow H1.
    unfold find_path_aux in H1.
    apply in_app_or in H1.
    destruct H1 as [H1l | H1r].
        + (* H1l *)
        destruct (if_reach_endpoint s end_v) eqn: H_reach_end.
            * (* reach endpoint *) simpl in H1l.
            assert (H1l_equiv: rev s @1 = path).
            {destruct H1l as [H1l | H1r]. auto. contradiction. } 
                assert(H_atc_t_emtpy : s @3 = []). {
                    unpack_if_reach_endpoint H_reach_end H_path_not_empty H_reach_end_1 H_reach_end_2.
                    assumption.
            }
            destruct path as [| p_hd p_tl] eqn: Hpath.
                - assert(H_rev_s_1: rev (rev s@1) = rev []). {rewrite -> H1l_equiv; reflexivity. }
                simpl in H_rev_s_1. rewrite -> rev_involutive in H_rev_s_1.
                rewrite -> H_rev_s_1 in H_path_not_empty. discriminate H_path_not_empty.
                -  unfold state_follow_atc in H_s_follow. rewrite -> H1l_equiv in H_s_follow.
                unfold path_follow_atc. unfold state_follow_atc. rewrite -> H_s_follow.
                unfold origin_atc. rewrite -> H_atc_t_emtpy.
                reflexivity.
            * (* not reach endpoint *) contradiction.
        + (* path from second half of find_path_aux *)
        split_in_flat_map H1r n_s H1r1 H1r2.
        fold find_path_aux in H1r2.
        assert (H_n_s_follow: state_follow_atc n_s /\ 
                                (exists n_hd n_tl, (n_s @1 = (n_hd::n_tl)) /\ 
                                                    (n_s @2 = n_hd.2))). {
            apply step_states_follow with (D := D) (hd := hd) (tl := tl) (s := s).
            1-4: assumption.
        }
        destruct H_n_s_follow as [H_n_s_follow1 H_n_s_follow2].
        destruct H_n_s_follow2 as [n_hd H_n_s_follow2].
        destruct H_n_s_follow2 as [n_tl H_n_s_follow2].
        destruct H_n_s_follow2 as [H_n_s_follow2 H_n_s_follow3].
        apply step_states_preserve_origin_atc in H1r1 as H_atc.
        { rewrite <- H_atc.
        apply IHrb with (end_v := end_v) (D := D) (hd := n_hd) (tl := n_tl) (s := n_s) (path := path).
        1-4: assumption.
        }
        {rewrite -> H_path_not_empty. discriminate. }
Qed.

(* 
    the top level theorem of that output follows ATC command
    we manually enforce ATC = atc_h :: atc_t, which means ATC command is non-empty,
        if ATC is empty, the case is trivial because the output is empty
*)
Theorem output_path_follow_atc:
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    path_follow_atc path ATC.
Proof.
aux_to_output find_path_aux_follow_atc.
assert(H1 : origin_atc init_s = ATC_h :: ATC_t) by auto.
rewrite <- H1.
apply find_path_aux_follow_atc with 
    (end_v := end_v) (D := D) (hd := (start_v, input, (start_v, input), ATC_h)) (tl := []) (rb := 100).
1-4: hammer.
Qed. 


(* ========== The path is in the graph D ==========*)

(* the edge that step_states adds to the path is in the graph *)
Lemma step_states_new_edge_in_graph : forall s ns D,
    (s @1) <> [] -> In ns (step_states s D) -> 
    ((forall e, In e (tl (rev s@1)) -> In e D) -> 
     (forall e, In e (tl (rev ns@1)) -> In e D)).
Proof. apply step_states_properties. Qed.

(* if e is an input edge *)
Definition is_input (e : Edge_type) : Prop := e.1.2.1 = input.

(*
    if cur_path is not empty, then 
*)
Lemma find_path_aux_in_graph:
    forall round end_v D path (s : State_type),
    s@1 <> [] -> (* s@1 is not empty *)
    path_in_graph (rev s@1) D -> (* all but the first one in s@1 (cur_path) is in D *)
    In path (find_path_aux end_v D round s) ->
    path_in_graph path D. (* then all but the first one in n_s@1 (cur_path) is in D *)
Proof. intro rb. dependent induction rb.
- intros. simpl in H0. contradiction.
- intros e_v D path s H_s1_not_empty H_s_in_D path_in_find_path n_e H_n_e_in_path.
    assert (s1_not_empty: exists s1_hd s1_tl, s@1 = s1_hd::s1_tl).
    {destruct s@1. -contradiction. -eauto.  }
    destruct_conjs. rename s1_not_empty into s1_hd. rename H into s1_tl. rename H0 into H_s1.
    unpack_find_path_aux_in_H path_in_find_path path_in_find_path_l path_in_find_path_r.
        + (* left part of find_path*)
        destruct (if_reach_endpoint s e_v) eqn: H_if_end.
            * (* reach endpoint *)
            unpack_if_reach_endpoint H_if_end H_s1 H_end H_s3_empty.
            simpl in *. assert(Hpath : rev s @1 = path) by tauto. clear path_in_find_path_l.
            rewrite <- Hpath in H_n_e_in_path.
            apply H_s_in_D in H_n_e_in_path.
            assumption.
            * (* not reach endpoint *) contradiction.
        + (* right part of find_path *)
        split_in_flat_map path_in_find_path_r n_s H3 H4.
            apply IHrb with (end_v := e_v)  (path := path) (s := n_s).  
            * fold find_path_aux in H4. apply step_states_grow_path_by_1 in H3.
            destruct n_s @1 as [| n_path'] eqn: H_n_s1. 
                {auto. } 
                {congruence. }
            rewrite -> H_s1. congruence.
            * {
                intros n_e' H_n_e'. (* n_e' is any edge in n_s *)
                fold find_path_aux in H4.
                apply step_states_new_edge_in_graph with (s:=s) (ns:=n_s).
                1-4:auto.
                }
            1-3:auto.
Qed.

(* every edge in path given by find_path is in the input graph*)
Theorem output_path_in_graph : 
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    path_in_graph path D.
Proof.  aux_to_output find_path_aux_starts_with_s1.
intros.
pose (D' := (((start_v, input), (start_v, input), ATC_h)::D)).
apply find_path_aux_in_graph with (end_v := end_v) (D := D) 
                                  (s := init_s) (round := 100) (path := path).
    + auto.
    + hammer.
    + assert (H_temp : paths = (find_path_aux end_v D 100 init_s)) by hammer.
    +  rewrite <- H_temp. assumption.
Qed.

(* ========== The path starts at the input start node ==========*)

(* 
    a lemma for path in find_path_aux starts with s@1 
    Note that in find_path_aux the path is stored in reverse order,
        hence the first of (rev path) is always start node
*)



Lemma find_path_aux_starts_with_s1:
    forall round (s : State_type) end_v D path,
    s@1 <> [] ->
    In path (find_path_aux end_v D round s) ->
    (exists l, (rev path) = l ++ s @1). 
Proof. intro rb. dependent induction rb.
    - intros. simpl in H0. contradiction. 
    - intros. unpack_find_path_aux_in_H H0 Hl Hr.
        + (* first part of find_path_aux *) destruct (if_reach_endpoint s end_v).
            * simpl in Hl. assert(rev s @1 = path) by tauto. 
            rewrite <- H0. rewrite -> rev_involutive. exists []. reflexivity.
            * contradiction.
        + (* second part of find_path_aux *)
        fold find_path_aux in Hr.
        split_in_flat_map Hr n_s H1 H2.
        assert(H_n_s_not_empty : exists n_edge, n_s@1 = n_edge :: s@1). {
                apply  step_states_grow_path_by_1_alt with (ns := n_s)  (D := D).
                1-2: auto.
        }
        assert(H_lemma : (exists l, rev path = l ++ n_s @1)). {
            apply IHrb with (end_v := end_v) (D := D) (s := n_s).
            - destruct H_n_s_not_empty. rewrite -> H0. congruence.
            - assumption.
        }
        destruct H_lemma as [n_l H_lemma].
        destruct H_n_s_not_empty as [n_edge_s H_n_s_not_empty].
        rewrite -> H_n_s_not_empty in H_lemma.
        exists (n_l ++ [n_edge_s]). rewrite -> H_lemma. clear. hammer.
Qed.

(* A trivial corollary for non-empty output of find_path_aux *)
Corollary find_path_aux_path_not_empty:
    forall (round:nat) (s : State_type) end_v D path,
    s@1 <> [] ->
    In path (find_path_aux end_v D round s) ->
    (exists p_hd p_tl, path = p_hd::p_tl).
Proof. intros. destruct path as [ | p_hd p_tl] eqn: H_p.
    assert (H1 : exists l : seq.seq Edge_type, rev path = l ++ s @1) by 
    (apply find_path_aux_starts_with_s1 with 
    (round := round) (end_v := end_v) (D := D) (path := path) (s := s) in H;
    repeat hammer).
    - hammer.
    - exists p_hd. exists p_tl. reflexivity.
Qed.



(* direct consequence of applying the lemma *)
Lemma output_path_start_correct_alt:
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    (* last edge in path is ((start_v, input), (start_v, input), taxiway_name) *)
    exists taxiway_name, exists l,  rev path = l ++ [((start_v, input), (start_v, input), taxiway_name)].
Proof. 
    aux_to_output find_path_aux_starts_with_s1.
Qed.

(* first edge in path is ((start_v, input), (start_v, input), taxiway_name) *)
Definition path_starts_with_vertex (path : list Edge_type) (start_v : Vertex) : Prop :=
    exists taxiway_name, exists l,  path = ((start_v, input), (start_v, input), taxiway_name)::l.
    
(* 
    Top-level theorem for the result of find_path always starts from correct input edge
    Note that every path returned by find_path is in normal order
*)
Theorem output_path_start_correct:
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    (* last edge in path is ((start_v, input), (start_v, input), taxiway_name) *)
    path_starts_with_vertex path start_v.
Proof.
    unfold path_starts_with_vertex.
    intros.
    assert (H1: exists taxiway_name, exists l,  rev path = l ++ [((start_v, input), (start_v, input), taxiway_name)]).
    { apply output_path_start_correct_alt with (end_v := end_v) (ATC := ATC) (D := D) (path := path) (paths := paths).
    1-2: assumption. }
    destruct H1 as [taxiway_name H1]. destruct H1 as [l H1].
    exists taxiway_name. exists (rev l).
    
    assert (H2: rev (rev path) =
                rev (l ++ [(start_v, input, (start_v, input), taxiway_name)])  ). f_equal; auto.
    rewrite -> rev_involutive in H2. clear - H2.
    hammer.
Qed.



(* ========== The path ends at the input end node ==========*)

(* last edge in path ends at end_v *)
(* last edge in path is ((start_v, input), (start_v, input), taxiway_name) *)
Definition path_ends_with_vertex (path : list Edge_type) (end_v : Vertex) : Prop :=
    exists end_edge, ((hd_error (rev path)) = Some end_edge) /\ end_edge.1.2.1 = end_v.

(* 
    a lemma for path in find_path_aux ends at end_v
    Note that in find_path_aux the path is stored in reverse order,
        hence the first of path is always the last edge points to end_v
*)
Lemma find_path_aux_end_correct:
    forall round (s : State_type) end_v D path,
    s@1 <> [] ->
    In path (find_path_aux end_v D round s) ->
    path_ends_with_vertex path end_v.
Proof. intro round. dependent induction round.
    - intros. simpl in H0. contradiction.
    - intros. 
    assert (H_path_not_empty :  (exists p_hd p_tl, path = p_hd::p_tl)). {
        apply find_path_aux_path_not_empty with 
        (round := round .+1) (end_v := end_v) (D := D) (path := path) (s := s) in H.
        1-2: auto.
    }
    destruct H_path_not_empty as [p_hd H_path_not_empty].
    destruct H_path_not_empty as [p_tl H_path_not_empty].
    unpack_find_path_aux_in_H H0 Hl Hr.
    (* first part of find path *)
    - destruct (if_reach_endpoint s end_v) eqn: H_reach_end. 
        + (* if reach endpoint *) simpl in *.  
        assert(Hl_equiv: rev s @1 = path ) by tauto; clear Hl. 
        destruct (s@1) as [|s1_h s1_t] eqn: Hs1. {contradiction. }
        unfold if_reach_endpoint in H_reach_end; simpl in H_reach_end.
        rewrite -> Hs1 in H_reach_end. simpl in H_reach_end.
        apply andb_true_iff in H_reach_end. destruct H_reach_end as [H_reach_end_1 H_reach_end_2]. 
        apply Nat.eqb_eq in H_reach_end_2. apply length_zero_iff_nil in H_reach_end_2.
        apply eqv_eq in H_reach_end_1.
        assert(H2: rev (rev (s1_h :: s1_t)) = rev path) by hammer.
        rewrite -> rev_involutive in H2.
        exists s1_h. rewrite <- H2. rewrite <- H_reach_end_1. simpl. tauto.
        + contradiction.
    - split_in_flat_map Hr n_s H2 H3. apply IHround with 
            (end_v := end_v) (D := D) (path := path) (s := n_s).
        apply step_states_new_path_not_empty with (s := s) (D := D).
        1-3: auto.
Qed.

(* 
    Top-level theorem for every path returned by find_path always ends at end_v
    Note that the result of find_path returns in normal order
*)
Theorem output_path_end_correct:
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    path_ends_with_vertex path end_v.
Proof. 
    aux_to_output find_path_aux_end_correct.
Qed.

(* ========== Correctness ========== *)

(* collection of correctness properties *)
Theorem correctness:
    forall start_v end_v ATC D (path : list Edge_type) (paths : list (list Edge_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type)) ->
    In path paths ->
    (* if find_path return some paths, then every path has the following properties: *)
    path_conn (rev path) /\
    path_follow_atc path ATC /\
    path_in_graph path D /\
    path_starts_with_vertex path start_v /\
    path_ends_with_vertex path end_v.
Proof. intros.
(* this tactic applys thm to current goal and 
   finds hypothesis from assumption for the theorem *)
Ltac temp_tac thm start_v end_v ATC D path paths :=
    let app_thm := (apply (thm start_v end_v ATC D path paths); (repeat assumption)) in
        match goal with
        | [ |- _ /\ _] => split; [app_thm | ]
        | _ =>  app_thm 
        end.

temp_tac output_path_conn start_v end_v ATC D path paths.
temp_tac output_path_follow_atc start_v end_v ATC D path paths.
temp_tac output_path_in_graph start_v end_v ATC D path paths.
temp_tac output_path_start_correct start_v end_v ATC D path paths.
temp_tac output_path_end_correct start_v end_v ATC D path paths.
Qed.