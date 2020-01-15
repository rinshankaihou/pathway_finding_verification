Require Import Coq.Strings.String.
Open Scope string_scope.

From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
Require Import Coq.Lists.List Coq.Bool.Bool.

From Hammer Require Import Hammer.


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



Definition Node_type : Type := (Vertex * Vertex).
Definition Edge_type : Type := (Node_type * Node_type) * string.
Definition Graph_type : Type := list Edge_type.


Inductive Result_type : Type :=
    | CANNOT_FIND
    | TOO_MANY_PATH
    | ATC_ERROR
    | SOME_P (result: (list Node_type)).
(* EXAMPLES *)

Example input := index 0.
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
    (((AC, BC), (AA1, AC)), A);
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

Definition edge_filter (current : Node_type) (e : Edge_type) : bool :=
    (eqv current.1 e.1.1.1) && (eqv current.2 e.1.1.2).

Definition find_edge (current : Node_type) (D : Graph_type) : list Edge_type :=
    filter (edge_filter current) D.

Definition State_type : Type :=  ((list Edge_type) * string) * list string.

(* ============ helper functions ============*)

Definition is_on_next_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    match head cur_s.2 with
    | None => false
    | Some t => t =? e.2
    end.


Definition is_on_this_taxiway (cur_s : State_type) (e : Edge_type) : bool :=
    cur_s.1.2 =? e.2.

Definition if_reach_endpoint (cur_s : State_type) (end_v : Vertex) : bool :=
    match head cur_s.1.1 with
    | None => false (*will never reach*)
    | Some e => (eqv e.1.2.1 end_v) && (eqn (length cur_s.2) 0)
    end.  


(* =================  state handler functions ==============*)
(*
    for each edge starts from current:
        if on same taxiway => return [new state]
        else if on next taxiway => return [new state]
        else => return []

    using flat_map to operate on all edges 

    since (prev, current) won't connect back, so don't need to check back
    the edge in complete graph is naturally valid, so don't to check valid 
*)


(* The function to pack a edge into a state *)
(* Original Name: neighbor_packer *)
Definition packer (cur_s : State_type) (e : Edge_type) : list State_type :=
    if is_on_this_taxiway cur_s e
    then [((e::cur_s.1.1, cur_s.1.2), cur_s.2)]
    else if is_on_next_taxiway cur_s e (* on the next taxiway *)
    then [((e::cur_s.1.1, e.2), tail cur_s.2)]
    else [].


(* the function to handle a state, to insert possible destinations*)
(* Original Name: get_next_state *)
Definition state_handle (cur_s : State_type) (D : Graph_type) : list State_type :=
    match head cur_s.1.1 with
    | None => []
    | Some n => flat_map (packer cur_s) (find_edge n.1.2 D)
    end.

    

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
        then [rev cur_s.1.1]
        else []) ++
        (flat_map (find_path end_v D n) (state_handle cur_s D))
    end.


Definition find_path_wrapper (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : option (list (list Edge_type)) :=
    match ATC with
    | [] => None (* ATC error *)
    | t :: rest => Some (find_path end_v D 100 (([(((start_v, input), (start_v, input)), t)], t), rest))
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
Print map.

Definition node_result_caller (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : Graph_type) : Result_type :=
    match ATC with
    | [] => ATC_ERROR
    | t :: rest => match find_path end_v D 100 (([(((start_v, input), (start_v, input)), t)], t), rest) with
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

(* INPUT list Edge_type, the pathway names of it is something like AACCCB *)
(* OUTPUT list strings, eg ACB *)
Fixpoint suppress (path_f : Edge_type) (path_r : list Edge_type) : list string :=
    match path_r with
    | [] => [path_f.2]
    | path_r_f::path_r_r => 
        if (path_f.2 =? path_r_f.2) 
        then (suppress path_r_f path_r_r)
        else path_f.2::(suppress path_r_f path_r_r)
    end.

(* sanity check*)
Example suppress_eg1 : suppress (((Ch, input), (BC, Ch)),     C)
                                [(((Ch, input), (BC, Ch)),    C);
                                 (((A3r, input), (AA3, A3r)), A3);
                                 (((A3r, input), (AA3, A3r)), A3);
                                 (((A2r, input), (AB, A2r)),  A2);
                                 (((A2r, input), (AB, A2r)),  A2)]
                       = [C; A3; A2].
Proof. reflexivity. Qed.

(* path_valid returns true only if one can traverse the path and follow the atc commands.
   more specifically, it returns true only if:
   for every step to the next node (Vertex, string) in the path,
   the associated taxiway exists, and is either the current or the next taxiway. *)
Fixpoint path_follow_atc (cur_path : list Edge_type) (taxiways : list string) : Prop :=
    match cur_path, taxiways with
    | [], [] => True
    | cur_path_f::cur_path_r, _ => (suppress cur_path_f cur_path_r) = taxiways
    | _, _ => False
    end.

(* sanity check*)
Example path_follow_atc_eg1 : path_follow_atc  [(((Ch, input), (BC, Ch)),    C);
                                                (((A3r, input), (AA3, A3r)), A3);
                                                (((A3r, input), (AA3, A3r)), A3);
                                                (((A2r, input), (AB, A2r)),  A2);
                                                (((A2r, input), (AB, A2r)),  A2)]
                                                [C; A3; A2].
Proof. reflexivity. Qed.

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
-intros H.  destruct v1, v2. unfold eqv. inversion H. hammer. (* don't know how to prove (n0 =? n0). gotta hammer *)
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
    path_conn s.1.1 ->
    In ns (state_handle s D) ->
    path_conn ns.1.1.
Proof. intros ns s D IH H. unfold state_handle in H. unfold hd_error in H.
    destruct s.1.1 as [| path_hd path_tail] eqn:Hpath.
    - simpl in H. contradiction.
    - apply in_flat_map in H. elim H. intros n_edge H2. destruct H2 as [H2 H3].
        unfold packer in H3. 

        unfold is_on_this_taxiway in H3.
        destruct (s.1.2 =? n_edge.2) eqn:Heqn.

        + (* n_edge on this taxiway *) 
            simpl in H3.
            destruct H3 as [H3|Contra].
            * rewrite <- H3. simpl. rewrite -> Hpath. split.
                {unfold edge_conn. 
                unfold find_edge in H2. simpl in H2.
                hammer. }
                {assumption. } 
            * contradiction.
        + unfold is_on_next_taxiway in H3. destruct (hd_error s.2) eqn:Heqn2.
            * unfold hd_error in Heqn2. 
                destruct s.2 as [| s'] eqn:Heqn3 in Heqn2.  
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
                            hammer. }
                            {assumption. } 
                        + contradiction. 
                    - simpl in H3. contradiction H3. }
            * contradiction.
Qed.

Lemma path_conn_equiv : forall path, path_conn path -> _path_conn (rev path).
Proof. intros p H. induction p.
- trivial.
Admitted.
(* if want _path_conn, prove this. current version only uses path_conn *)

(* path in the result given by find_path is connected if current path in state is connected *)
Lemma find_path_conn:
   forall round_bound path end_v D  s res,
   path_conn s.1.1 ->
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
        * (* path is rev s.1.1 *) rewrite <- H4 . hammer.
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

(* CHECK POINT *) 




Theorem output_path_follow_atc:
   forall path end_v D round_bound cur_path atc,
   In path (find_path end_v D round_bound (cur_path, atc)) ->
   path_conn path.

   
   Definition start_correct (start_v : Vertex) (path : list Node_type) : Prop :=
      match path with
      | [] => False
      | f::r => start_v = (fst f)
      end.
   
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
   Check any_path_in_output_is_valid.
   QuickChick any_path_in_output_is_valid.
   
   Theorem any_path_in_output_is_valid:
   forall start_v end_v taxiways graph path,
   In path (find_path_wrapper start_v end_v taxiways graph) ->
   start_correct start_v path /\
   end_correct start_v path /\
   path_valid path graph taxiways /\
   connected path graph.
   Proof. hammer.
   Lemma flat_map_conn : forall s prev,
   sta