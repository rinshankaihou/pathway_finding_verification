Require Import Coq.Strings.String.
Open Scope string_scope.

From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
Require Import Coq.Lists.List Coq.Bool.Bool.

From Hammer Require Import Hammer. (*all hammer is replaced*)

(*
    Node_type : (Vertex * Vertex)
        (current, from)
    taxiway : string

    Edge_type : (Node_type * Node_type) * string
        ((end1, end2), taxiway)

    Graph_type : list Edge_type


    State_type : ((list Edge_type * string) * list string)
        ((results, current_taxiway), rest_ATC)

    Result : option (list Edge_type)
*)

Ltac split_in_flat_map H1 elem output_H1 output_H2 :=
    apply in_flat_map in H1; destruct H1 as [elem output_H1]; destruct output_H1 as [output_H1 output_H2].

Definition Node_type : Type := (Vertex * Vertex).
Definition Edge_type : Type := (Node_type * Node_type) * string.
Definition Graph_type : Type := list Edge_type.


Inductive Result_type : Type :=
    | CANNOT_FIND
    | TOO_MANY_PATH
    | ATC_ERROR
    | SOME_P (result: (list Node_type)).
(* EXAMPLES *)

Definition input := index 0.
(* input should be a node meaningless, but only indicate it's input *)

Example AA3 := index 1.
Example AB := index 2.
Example AC := index 3.
Example AA1 := index 4.
Example Ch := index 5.
Example BC := index 6.
Example A3r := index 7.
Example A2r := index 8.
Example A1r := index 9.

Example A := "A".
Example B := "B".
Example C := "C".
Example A1 := "A1".
Example A2 := "A2".
Example A3 := "A3".

Example ann_arbor : Graph_type :=[
    (((Ch, input), (BC, Ch)), C);
    (((A3r, input), (AA3, A3r)), A3);
    (((A2r, input), (AB, A2r)), A2);
    (((A1r, input), (AA1, A1r)), A1);
    (((AA3, A3r), (AB, AA3)), A);
    (((AA3, AB), (A3r, AA3)), A3);
    (((AB, A2r), (AA3, AB)), A);
    (((AB, A2r), (AC, AB)), A);
    (((AB, A2r), (BC, AB)), B);
    (((AB, AA3), (A2r, AB)), A2);
    (((AB, AA3), (AC, AB)), A);
    (((AB, AA3), (BC, AB)), B);
    (((AB, BC), (A2r, AB)), A2);
    (((AB, BC), (AA3, AB)), A);
    (((AB, BC), (AC, AB)), A);
    (((AB, AC), (A2r, AB)), A2);
    (((AB, AC), (AA3, AB)), A);
    (((AB, AC), (BC, AB)), B);
    (((AC, AB), (AA1, AC)), A);
    (((AC, AB), (BC, AC)), C);
    (((AC, AA1), (AB, AC)), A);
    (((AC, AA1), (BC, AC)), C);
    (((AC, BC), (AB, AC)), A);
    (((AA1, A1r), (AC, AA1)), A);
    (((AA1, AC), (A1r, AA1)), A1);
    (((BC, Ch), (AB, BC)), B);
    (((BC, Ch), (AC, BC)), C);
    (((BC, AB), (Ch, BC)), C);
    (((BC, AB), (AC, BC)), C);
    (((BC, AC), (Ch, BC)), C);
    (((BC, AC), (AB, BC)), B)
].


(* =========== find_edge =============*)
Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.




Lemma eqv_true :
    forall v1 v2, (eqv v1 v2 = true) -> (v1 = v2).
Proof. intros. unfold eqv in H. destruct v1 as [n1]. destruct v2 as [n2]. 
    apply (Nat.eqb_eq n1 n2) in H. rewrite H. reflexivity. Qed.


Definition edge_filter (current : Node_type) (e : Edge_type) : bool :=
    (eqv current.1 e.1.1.1) && (eqv current.2 e.1.1.2).

Definition find_edge (current : Node_type) (D : Graph_type) : list Edge_type :=
    filter (edge_filter current) D.

    (* cur_path, atc_h, atc_t, atc_used. ATC= (rev atc_used) ++ [atc_f] ++ atc_t *)
Inductive State_type : Type :=
    | State :  (list Edge_type) -> string -> (list string) -> (list string) -> State_type.

Example eg_state : State_type := State [] "2" ["3"; "4"] ["1"].
Definition s_1 (s : State_type) : (list Edge_type) := match s with | State cur_path _ _ _ => cur_path end.
Definition s_2 (s : State_type) : string := match s with | State _ atc_h _ _ => atc_h end.
Definition s_3 (s : State_type) : (list string) := match s with | State _ _ atc_t _ => atc_t end.
Definition s_4 (s : State_type) : (list string) := match s with | State _ _ _ atc_used => atc_used end.
Notation "S @1" := (s_1 S) (at level 1, no associativity).
Notation "S @2" := (s_2 S) (at level 1, no associativity).
Notation "S @3" := (s_3 S) (at level 1, no associativity).
Notation "S @4" := (s_4 S) (at level 1, no associativity).
Lemma s_notation_sound : forall (s : State_type),
    s = State s@1 s@2 s@3 s@4.
Proof. intro s. destruct s as [s1 s2 s3 s4] eqn:H. reflexivity. Qed.
    
Eval compute in  (eg_state@1, eg_state@2, eg_state@3, eg_state@4).
(* ============ helper functions ============*)

Definition is_on_next_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    match head cur_s@3 with
    | None => false
    | Some t => t =? e.2
    end.


Definition is_on_this_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    cur_s@2 =? e.2.

Lemma on_this_taxiway_lemma : forall s e, 
    is_on_this_taxiway s e ->
    (e.2 =? s@2).
Proof. intros s e H.
unfold is_on_this_taxiway in H. rewrite -> String.eqb_sym. assumption. Qed.

Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match head cur_s@1 with
    | None => false (*will never reach*)
    | Some e => (eqv e.1.2.1 end_v) && (eqn (length cur_s@3) 0)
    end.  

(* =================  state handler functions ==============*)
(*
    for each edge starts from current:
        if on same taxiway => return [new state]
        else if on next taxiway => return [new state]
        else => return []

    using flat_map to operate on all edges 
((start_v, input), (start_v, input))=? 
*)


(* The function to pack a edge into a state *)
(* Original Name: neighbor_packer *)
Definition packer (cur_s : State_type) (e : Edge_type) : list State_type :=
    if is_on_this_taxiway cur_s e
    then [State (e::cur_s@1) cur_s@2 cur_s@3 cur_s@4]
    else if is_on_next_taxiway cur_s e (* on the next taxiway *)
    then [State (e::cur_s@1) e.2 (tail cur_s@3) (cur_s@2 :: cur_s@4)]
    else [].


(* the function to handle a state, to insert possible destinations*)
(* Original Name: get_next_state *)
Definition state_handle (cur_s : State_type) (D : Graph_type) : list State_type :=
    match head cur_s@1 with
    | None => []
    | Some e => flat_map (packer cur_s) (find_edge e.1.2 D)
    end.

Lemma state_handle_preserve_atc_h_if_reach_end : forall s D end_v n_s, 
    if_reach_endpoint s end_v -> In n_s (state_handle s D) -> n_s @2 = s @2.
Proof. intros s D end_v n_s H1. unfold state_handle.
    unfold if_reach_endpoint in H1. destruct (s @1) as [| hd tl] eqn: H2.
    - simpl. intro Hfalse. contradiction. 
    - simpl. intro H3. apply in_flat_map in H3.
        destruct H3 as [e H3]. destruct H3 as [H3 H4].
        simpl in H1.
        apply andb_true_iff in H1. destruct H1.
        unfold packer in H4. destruct (is_on_this_taxiway s e).
        - simpl in H4. destruct H4.
            + rewrite <- H1.  auto.
            + contradiction.
        - destruct  (is_on_next_taxiway s e).
            * simpl in H4. destruct H4.
                { rewrite <- H1.  simpl. give_up.  }
                { contradiction. }
            * contradiction.

Abort. (* this is wrong *)

(* ================= main function ===============*)
(* we return list list edges as results, it can be map to other type*)
(* 
    The design is that in initial state, edge can't be empty
    Put the initial edge as: ()
*)



Fixpoint find_path (end_v : Vertex) (D : Graph_type) (round_bound : nat) (cur_s : State_type) : list (list Edge_type) :=
    match round_bound with
    | 0 => []
    | S n =>
        (if if_reach_endpoint cur_s end_v  (*reach endpoint*)
        then [rev cur_s@1]
        else []) ++
        (flat_map (find_path end_v D n) (state_handle cur_s D))
    end. 


 

Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Edge_type)) :=
    match ATC with
    | [] => None (* ATC error *)
    | t :: rest => Some (find_path end_v D 100 (State [(((start_v, input), (start_v, input)), t)] t rest []))
    end.

(* ============ Map list Edge_type to list Node  =========== *)
(* pick the endpoint1 of edge *)
Definition e2n_helper (e : Edge_type) : Node_type := e.1.2.

Definition edge_2_node (le : list Edge_type) : list Node_type :=
    map (e2n_helper) le.

Definition node_result_wrapper (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Node_type)) :=
    match find_path_wrapper start_v end_v ATC D with
    | None => None
    | Some x => Some (map edge_2_node x)
    end.

Definition node_result_caller (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : Result_type :=
    match ATC with
    | [] => ATC_ERROR
    | t :: rest => match find_path end_v D 100 (State [(((start_v, input), (start_v, input)), t)] t rest []) with
        | [] => CANNOT_FIND
        | a :: nil => SOME_P (map e2n_helper a)
        | a :: b :: _ => TOO_MANY_PATH
        end
    end.



    Example eg_find_path_1 : node_result_caller Ch AB [C] ann_arbor = CANNOT_FIND.
    Proof. reflexivity. Qed.
        
    Example eg_find_path_2 : node_result_caller Ch BC [C] ann_arbor = SOME_P [(Ch, input); (BC, Ch)].
    Proof. reflexivity. Qed.
        
    Example eg_find_path_3 : node_result_caller Ch AA3 [C;B;A] ann_arbor = SOME_P [(Ch, input); (BC, Ch); (AB, BC); (AA3, AB)].
    Proof. reflexivity. Qed.
        
    Example eg_find_path_4 : node_result_caller AA3 AA1 [A;B;C;A] ann_arbor = SOME_P [(AA3, input); (AB, AA3); (BC, AB); (AC, BC); (AA1, AC)].
    Proof. Abort. (* It's good because AA3 is not a input*)
        
    Example eg_find_path_5 : node_result_caller A3r A1r [A3; A; A1] ann_arbor = SOME_P [(A3r, input); (AA3, A3r); (AB, AA3); (AC, AB); (AA1, AC); (A1r, AA1)].
    Proof. reflexivity. Qed.
        
    Example eg_find_path_6 : node_result_caller Ch Ch [C; B; A; C; B; A; C] ann_arbor
                             = SOME_P [(Ch, input); (BC, Ch); (AB, BC); (AC, AB); (BC, AC); (AB, BC); (AC, AB); (BC, AC); (Ch, BC)].
    Proof. reflexivity. Qed. 

(* PROOF FOR SOUNDNESS *)


(* edge_conn AB BC *)
Definition _edge_conn (e1 : Edge_type) (e2 : Edge_type) : Prop :=
    e1.1.2 = e2.1.1.

(* if path is connected, eg (AB BC CD) *)
Fixpoint _path_conn (path : list Edge_type): Prop :=
    match path with
    | path_f::path_r => match path_r with
        | path_s::path_r_r => (_edge_conn path_f path_s) /\ (_path_conn path_r)
        | [] => True
        end
    | [] => True (* a path shorter than 2 edges is trivially connected *)
    end.

Example path_conn_eg1 : _path_conn  [(((Ch, input), (BC, Ch)),    C);
(((BC, Ch), (AA3, A3r)), A3)].
Proof. simpl. unfold _edge_conn. simpl. split. reflexivity. reflexivity. Qed.

(* edge_conn BC AB *)
Definition edge_conn (e1 : Edge_type) (e2 : Edge_type) : Prop :=
    e1.1.1 = e2.1.2.

(* if rev path is connected, eg (CD BC AB) *)
Fixpoint path_conn (path : list Edge_type): Prop :=
    match path with
    | path_f::path_r => match path_r with
        | path_s::path_r_r => (edge_conn path_f path_s) /\ (path_conn path_r)
        | [] => True
        end
    | [] => True (* a path shorter than 2 edges is trivially connected *)
    end.

Lemma eq_vertex : forall v1 v2, eqv v1 v2 <-> v1 = v2.
Proof. intros v1 v2.  split. 
-intros H. destruct v1, v2. unfold eqv in H. apply beq_nat_true in H. auto.
-intros H.  destruct v1, v2. unfold eqv. inversion H. clear H H1. induction n0. auto. auto.
Qed.

(* if e1 ends at node n, then e2 given by find_edge starts at the same node n *)
Lemma find_edge_conn : forall e1 e2 n D, e1.1.2 = n -> In e2 (find_edge n D) -> edge_conn e2 e1.
Proof. intros e1 e2 n D H1 H2. unfold find_edge in H2. apply filter_In in H2. destruct H2.
    unfold edge_conn.
    unfold edge_filter in H0. rewrite -> H1. apply andb_true_iff in H0. destruct H0. destruct e2.1.1. destruct n.
    Ltac temp H1 := simpl in H1; apply eq_vertex in H1; rewrite H1.
    temp H0. temp H2. reflexivity.
Qed.

Lemma state_handle_conn : forall ns s D,
    path_conn s@1 ->
    In ns (state_handle s D) ->
    path_conn ns@1.
Proof. intros ns s D IH H. unfold state_handle in H. unfold hd_error in H.
    destruct s@1 as [| path_hd path_tail] eqn:Hpath.
    - simpl in H. contradiction.
    - apply in_flat_map in H. elim H. intros n_edge H2. destruct H2 as [H2 H3].
        unfold packer in H3. 

        unfold is_on_this_taxiway in H3.
        destruct (s@2 =? n_edge.2) eqn:Heqn.

        + (* n_edge on this taxiway *) 
            simpl in H3.
            destruct H3 as [H3|Contra].
            * rewrite <- H3. simpl. rewrite -> Hpath. split.
                {unfold edge_conn. 
                unfold find_edge in H2. simpl in H2. 
                clear Heqn H3 Hpath IH H. 
                apply filter_In in H2. destruct H2 as [H20 H2]. 
                unfold edge_filter in H2. apply andb_true_iff in H2. destruct H2 as [H21 H22].
                apply eqv_true in H21. apply eqv_true in H22. 
                destruct n_edge.1.1. destruct path_hd.1.2. simpl in H21. simpl in H22.
                rewrite H21. rewrite H22. reflexivity. }
                {assumption. } 
            * contradiction.
        + unfold is_on_next_taxiway in H3. destruct (hd_error s@3) eqn:Heqn2.
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
                            unfold edge_filter in H2. apply andb_true_iff in H2. destruct H2 as [H21 H22]. 
                            apply eqv_true in H21. apply eqv_true in H22. 
                            destruct n_edge.1.1. destruct path_hd.1.2. simpl in H21. simpl in H22. 
                            rewrite H21. rewrite H22. reflexivity. }
                            {assumption. } 
                        + contradiction. 
                    - simpl in H3. contradiction H3. }
            * contradiction.
Qed.


(* if want _path_conn, prove this. current version only uses path_conn *)
(* Lemma path_conn_equiv : forall path, path_conn path -> _path_conn (rev path).
Proof. intros p H. induction p.
- trivial.
Admitted. *)


(* path in the result given by find_path is connected if current path in state is connected *)
 Lemma find_path_conn:
   forall round_bound path end_v D  s res,
   path_conn s@1 ->
   res = (find_path end_v D round_bound s) ->
   In path res ->
   path_conn (rev path).
Proof. intros round_bound. induction round_bound as [| rb  IHrb].
- intros path end_v D  s res H1 H2 H3.
(* H1: conn cur_path *)

 unfold find_path in H2. rewrite H2 in H3. simpl in H3. contradiction.
- intros path end_v D  s res H1 H2 H3.
  unfold find_path in H2. destruct (if_reach_endpoint s end_v).
    + (* reached endpoint *) rewrite -> H2 in H3. simpl in H3. 
        destruct H3 as [H4|H5].
        * (* path is rev s.1.1 *) rewrite <- H4. assert(rev (rev s @1)=s @1). apply rev_involutive.
        rewrite -> H. apply H1. 
        * (* path is given in recursive call of find_path *) 
            fold find_path in H5.
            fold find_path in H2.

            apply in_flat_map in H5.
            elim H5. intros ns H6. destruct H6 as [H6 H7]. 
            apply IHrb with (res := find_path end_v D rb ns) (end_v := end_v) (D := D) (s := ns).
                {apply state_handle_conn with (s := s) (D := D).
                 assumption. assumption. }
                {reflexivity. }
                {assumption. }
    + (* not reached end point yet. proof is similar. Consider refactoring? *)
        fold find_path in H2. simpl in H2.
        rewrite -> H2 in H3. rename H3 into H5. (* so that I can copy proof in the previous case directly *)

            apply in_flat_map in H5.
            elim H5. intros ns H6. destruct H6 as [H6 H7]. 
            apply IHrb with (res := find_path end_v D rb ns) (end_v := end_v) (D := D) (s := ns).
                {apply state_handle_conn with (s := s) (D := D).
                 assumption. assumption. }
                {reflexivity. }
                {assumption. }
Qed.

(* find_path_conn, but without param 'res' *)
Lemma find_path_conn_alt:
    forall round_bound path end_v D s,
    path_conn s@1 ->
    In path (find_path end_v D round_bound s) ->
    path_conn (rev path).
Proof. 
    intros. apply find_path_conn with (end_v:=end_v) (round_bound:=round_bound) (D:=D) (s:=s0) 
    (res:=(find_path end_v D round_bound s0)).
    assumption. trivial. assumption.
Qed.

Theorem output_path_conn:
    forall path start_v end_v D round_bound atc_h atc_t,
    In path (find_path end_v D round_bound (State [(((start_v, input), (start_v, input)), atc_h)] atc_h atc_t []))  ->
    path_conn (rev path).
Proof. intros path s e D rb atc_h atc_t H. 
    apply find_path_conn_alt with (round_bound := rb) (end_v := e) (D := D) 
    (s := (State [(((s, input), (s, input)), atc_h)] atc_h atc_t [])) .
    - simpl. trivial. 
    - exact H.
Qed.    

(* Start Proving find_path_conn *)

(* extract a path's corresponding atc *)
(* INPUT list Edge_type, the pathway names of it is something like AACCCB *)
(* OUTPUT list strings, eg ACB *)
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

Lemma path_follow_atc_rev_comm : forall path, 
    path_coresp_atc (rev path) = rev (path_coresp_atc path).
Proof. Admitted.

(* no consecutive duplication *)
Fixpoint no_conn_dup (lst : list string) : Prop :=
    match lst with
    | [] => True
    | f::l => match l with
        | [] => True
        | s::r => (f <> s) /\ no_conn_dup l
        end
    end.

Fixpoint path_follow_atc (path : list Edge_type) (atc : list string) : Prop :=
    atc = path_coresp_atc path.



(* sanity check*)
Example path_follow_atc_eg1 : path_follow_atc  [(((Ch, input), (BC, Ch)),    C);
                                                (((A3r, input), (AA3, A3r)), A3);
                                                (((A3r, input), (AA3, A3r)), A3);
                                                (((A2r, input), (AB, A2r)),  A2);
                                                (((A2r, input), (AB, A2r)),  A2)]
                                                [C; A3; A2].
Proof. reflexivity. Qed.

Definition state_follow_atc (state : State_type) : Prop := 
    (path_coresp_atc  (rev (state@1))) = (rev ((state@2) :: (state@4))). 

Definition eg_s := (State  [(((Ch, input), (BC, Ch)),    C);
(((A3r, input), (AA3, A3r)), A3);
(((A3r, input), (AA3, A3r)), A3);
(((A2r, input), (AB, A2r)),  A2);
(((A2r, input), (AB, A2r)),  A2)]
C
[]
[A3; A2]).
(* sanity check*)
Example state_follow_atc_eg1 : state_follow_atc eg_s.
Proof. unfold state_follow_atc. reflexivity. Qed.

Lemma rev_inversion : forall {T : Type} (l1 l2 : list T), rev l1 = rev l2 -> l1 = l2.
Proof. intros T l1. induction l1.
Admitted.

Lemma state_handle_follow : forall s D n_s hd tl, (* s is cur_state *)
    (s @1 = hd::tl) -> (* cur_path is hd::tl *)
    (s @2 = hd.2) -> (* head of cur_path on atc_t, current atc *)
    state_follow_atc s ->  (* prev state follow atc *)
    In n_s (state_handle s D) -> (* n_s is a new_state *)
    state_follow_atc n_s /\ (exists n_hd n_tl, (n_s @1 = (n_hd::n_tl)) /\ (n_s @2 = n_hd.2)). 
    (* then n_s follow atc, and head of new_path on new_atc_hd *)
Proof. intros s D n_s hd tl Hpath Hhd H1 H2.

unfold state_handle in H2.
unfold state_follow_atc.
rewrite -> Hpath in H2.
simpl.
apply in_flat_map in H2. destruct H2. destruct H as [H2 H3].
unfold packer in H3. destruct (is_on_this_taxiway s x) eqn: H_on_this_taxi.
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
            apply on_this_taxiway_lemma in H_on_this_taxi.
            rewrite -> Hhd in H_on_this_taxi. assumption.
        }
    assert (H_goal: (if x.2 =? hd.2
                    then path_coresp_atc (hd :: tl)
                    else (x.2 :: path_coresp_atc (hd :: tl))%SEQ)
                    = (s @2 :: s @4)).
    {rewrite <- H1. rewrite -> Hpath. 
        
        rewrite -> Htemp. reflexivity.
    }
    rewrite H_goal. split. 
        {reflexivity. }
        {exists x. exists (hd::tl). split. 
            - reflexivity. 
            rewrite -> Hhd. 
                    apply String.eqb_eq in Htemp. auto. }
    * contradiction.
+ destruct (is_on_next_taxiway s x) eqn: H_on_next_taxi.
    - (* on_next_taxiway *) 
    simpl in H3. destruct H3 as [H3l | H3r].
    * simpl. unfold state_follow_atc in H1. rewrite <- H3l. simpl.  
        assert (H3 : ((x.2 =? hd.2) = false) ). {
            unfold is_on_next_taxiway in H_on_next_taxi.
            destruct (s @3) as [| atc_t_h atc_t_t].
            + discriminate H_on_next_taxi.
            + unfold is_on_this_taxiway in H_on_this_taxi. rewrite -> Hhd in H_on_this_taxi.
                rewrite String.eqb_sym in H_on_this_taxi. assumption.
        }
        assert(H4: rev s @1 ++ [x] = rev (x::s @1)) by auto.
        rewrite -> H4. 
        rewrite -> path_follow_atc_rev_comm.
        rewrite -> path_follow_atc_rev_comm in H1.
        apply rev_inversion in H1.
        assert(H5: (rev s @4 ++ [s @2]) ++ [x.2] = rev ([:: x.2, s @2 & (s @4)])) by auto.
        rewrite -> H5. clear H5.
        assert (H_goal: path_coresp_atc (x :: s @1)
                        = [:: x.2, s @2 & s @4]).
        {
            rewrite <- H1. rewrite -> Hpath.
            unfold path_coresp_atc. 
            assert (Htemp: (x.2 =? hd.2) = false). {
                unfold is_on_this_taxiway in H_on_this_taxi.
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


Definition origin_atc (s : State_type) := (rev s@4) ++ [s@2] ++ s@3.

Lemma state_handle_preserve_origin_atc : forall s ns D, 
    In ns (state_handle s D) -> origin_atc ns = origin_atc s.
Admitted.

Lemma find_path_follow_atc: forall rb end_v D s path hd tl,
    s @2 = hd.2 ->
    s @1 = hd::tl->
    state_follow_atc s ->
    In path (find_path end_v D rb s)->
    path_follow_atc path (origin_atc s).
Proof. intro rb. induction rb as [| rb' IHrb].
- intros end_v D s path hd tl H_hd_on_atc H_path_not_empty H_s_follow H1.
simpl in H1. contradiction.
- intros end_v D s path hd tl H_hd_on_atc H_path_not_empty H_s_follow H1.
    unfold find_path in H1.
    destruct (if_reach_endpoint s end_v) eqn: H_reach_end.
    + (* reach endpoint *) simpl in H1.
        destruct H1 as [H1l | H1r].
        * (* path from second half of find_path *) 
            assert(H_atc_t_emtpy : s @3 = []). {
                unfold if_reach_endpoint in H_reach_end.
                simpl in H_reach_end. rewrite -> H_path_not_empty in H_reach_end.
                 apply andb_true_iff in H_reach_end.
                    destruct H_reach_end. destruct (s @3) as [| s3]. 
                    * reflexivity. 
                    * simpl in H0. discriminate H0.
            }
                
             destruct path as [| p_hd p_tl] eqn: Hpath.
            - assert(H_rev_s_1: rev (rev s@1) = rev []). {rewrite -> H1l; reflexivity. }
                simpl in H_rev_s_1. rewrite -> rev_involutive in H_rev_s_1.
                rewrite -> H_rev_s_1 in H_path_not_empty. discriminate H_path_not_empty.
            -  unfold state_follow_atc in H_s_follow. rewrite -> H1l in H_s_follow.
            unfold path_follow_atc. unfold state_follow_atc. rewrite -> H_s_follow.
            unfold origin_atc. rewrite -> H_atc_t_emtpy.
            reflexivity.

        * (* path from second half of find_path *)
            split_in_flat_map H1r n_s H1r1 H1r2.
            fold find_path in H1r2.
            assert (H_n_s_follow: state_follow_atc n_s /\ 
                                  (exists n_hd n_tl, (n_s @1 = (n_hd::n_tl)) /\ 
                                                     (n_s @2 = n_hd.2))). {
                apply state_handle_follow with (D := D) (hd := hd) (tl := tl) (s := s).
                - assumption.
                - assumption.
                - assumption.
                - assumption.
            }
            destruct H_n_s_follow as [H_n_s_follow1 H_n_s_follow2].
            destruct H_n_s_follow2 as [n_hd H_n_s_follow2].
            destruct H_n_s_follow2 as [n_tl H_n_s_follow2].
            destruct H_n_s_follow2 as [H_n_s_follow2 H_n_s_follow3].
            apply state_handle_preserve_origin_atc in H1r1 as H_atc. rewrite <- H_atc.
            apply IHrb with (end_v := end_v) (D := D) (hd := n_hd) (tl := n_tl) (s := n_s) (path := path).
            - assumption.
            - assumption.
            - assumption.
            - assumption.

    + (* not reach endpoint *)
        split_in_flat_map H1 n_s H1_1 H1_2.
        fold find_path in H1_2.
        assert (H_n_s_follow: state_follow_atc n_s /\ 
                                (exists n_hd n_tl, (n_s @1 = (n_hd::n_tl)) /\ 
                                                    (n_s @2 = n_hd.2))). {
            apply state_handle_follow with (D := D) (hd := hd) (tl := tl) (s := s).
            - assumption.
            - assumption.
            - assumption.
            - assumption.
        }
        destruct H_n_s_follow as [H_n_s_follow1 H_n_s_follow2].
        destruct H_n_s_follow2 as [n_hd H_n_s_follow2].
        destruct H_n_s_follow2 as [n_tl H_n_s_follow2].
        destruct H_n_s_follow2 as [H_n_s_follow2 H_n_s_follow3].
        apply state_handle_preserve_origin_atc in H1_1 as H_atc. rewrite <- H_atc.
        apply IHrb with (end_v := end_v) (D := D) (hd := n_hd) (tl := n_tl) (s := n_s) (path := path).
        - assumption.
        - assumption.
        - assumption.
        - assumption.
Qed.
            


(* atc = atc_f::atc_t *)
Theorem output_path_follow_atc:
    forall round_bound start_v end_v D (atc_h:string) (atc_t:list string) path,
    In path (find_path end_v D round_bound (State [(((start_v, input), (start_v, input)), atc_h)] atc_h atc_t []) ) ->
    no_conn_dup (atc_h::atc_t) ->
    path_follow_atc path (atc_h::atc_t).
(*CHECK POINT *)
Proof. intros rb start_v end_v D atc_f atc_t path.

remember [(((start_v, input), (start_v, input)), atc_f)] as start_edges.
remember ((start_edges, atc_f), atc_t) as start_state.

assert( forall t new_path, ((In new_path (find_path end_v D (t + rb)  ((start_edges, atc_f), atc_t) )) -> 
path_follow_atc new_path (atc_f::atc_t)) ) as H.
Abort.


(* following stuff are defs from an old version *)
        Definition start_correct (start_v : Vertex) (path : list Node_type) : Prop :=
            match path with
            | [] => False
            | f::r => start_v = (fst f)
            end.
            list string.
        Definition end_correct (end_v : Vertex) (path : list Node_type) : Prop :=
            match rev path with
            | [] => False
            | f::r => end_v = (fst f)
            end.
        
        Definition head_is {T : Type} (elem : T)(l : list T) : Prop :=
            match l with
            | [] => False
            | h::r => elem = h
            end.
        
        
        
        Definition any_path_in_output_is_valid : Prop := e
        forall start_v end_v taxiways graph path,
        In path (find_path_wrapper start_v end_v taxiways graph) ->
        start_correct start_v path.
        
        Theorem any_path_in_output_is_valid:
        forall start_v end_v taxiways graph path,
        In path (find_path_wrapper start_v end_v taxiways graph) ->
        start_correct start_v path /\
        end_correct start_v path /\
        path_valid path graph taxiways /\
        connected path graph.
        Proof. 
