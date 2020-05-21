(* 
    This file have five theorems indicating the correctness theorems on complete graph preserve downward
    Top level theorem is "correctness_preservation"
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
From Taxiway Require Import To_naive To_complete.
From Taxiway Require Import Find_path.
From Taxiway Require Import Correctness.

From Hammer Require Import Hammer.


(* ======== start correct =========*)

Definition naive_path_starts_with_vertex (path : list Edge_type) (start_v : Vertex) : Prop := 
    exists taxiway_name, exists l, path = ((start_v, input), taxiway_name) :: l.


Theorem naive_start_correct:
    forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    naive_path_starts_with_vertex (to_N path) start_v.
Proof. 
    (* Hint Resolve output_path_start_correct. *)
    intros. unfold naive_path_starts_with_vertex. 
    assert (
        (exists taxiway_name l_c, to_N path = to_N ( (((start_v, input), (start_v, input)), taxiway_name)::l_c ) )->
        exists taxiway_name l, to_N path = (start_v, input, taxiway_name)::l). hammer. 
    apply H1. clear H1.
    assert (
        (exists taxiway_name l_c,
            path = ((start_v, input), (start_v, input), taxiway_name) :: l_c ) ->
        exists taxiway_name l_c,
            to_N path = to_N ((start_v, input, (start_v, input), taxiway_name) :: l_c)
    ). hammer. apply H1. clear H1. 
    apply output_path_start_correct with (start_v := start_v) (end_v := end_v) (ATC := ATC) (D := D) (paths := paths).
    apply H. apply H0.
Qed.
    



(* ========== end correct ===========*)

Lemma hd_error_f : 
    forall (f:Arc_type -> Edge_type) a l,
    hd_error l = Some a -> hd_error (map f l) = Some (f a).
Proof.
    intros. hammer.
Qed.


Definition naive_ends_with_vertex (path : list Edge_type) (end_v : Vertex) : Prop :=
    exists end_Edge,
    ((hd_error (rev path)) = Some end_Edge) /\ end_Edge.1.1 = end_v.


Theorem naive_end_correct:
    forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    naive_ends_with_vertex (to_N path) end_v.
Proof. 
    intros. unfold naive_ends_with_vertex.
    assert (
        rev (to_N path) = to_N (rev path)
    ). unfold to_N. hammer.  rewrite -> H1. 
    
    assert (
        exists end_arc,
            hd_error (rev path) = Some end_arc /\ end_arc.1.2.1 = end_v
    ) as H_original. 
    apply output_path_end_correct with (start_v := start_v) (ATC := ATC) (D:=D) (path:=path) (paths:=paths). assumption. assumption.

    destruct H_original as [v H_2]. destruct H_2 as [H_l H_r].
    exists (c_to_n v). split.
    - unfold to_N. apply hd_error_f with (l:=rev path). assumption.  
    - unfold c_to_n. simpl. assumption.
Qed.    
     




(* ============ in graph ============*) 

Lemma to_N_downward : 
    forall x path, In x path -> 
    forall a, a = c_to_n x -> In a (to_N path).
Proof.
    intros. unfold to_N. hammer.
Qed. 


Definition naive_path_in_graph (path : list Edge_type) (G : list Edge_type) : Prop :=
    forall a, In a (tl (path)) -> In a G.


Theorem naive_in_graph : 
    forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    naive_path_in_graph (to_N path) (to_N D).
Proof. 
    intros. unfold naive_path_in_graph.
    
    assert (
        path_in_graph path D
    ) as H_original. hammer. unfold path_in_graph in H_original.

    assert (
        forall a, In a (tl (to_N path)) <-> In a (to_N (tl path))
    ) as H_tl. intros. split. hammer. hammer.

    assert (
        (forall a : Edge_type,
        (In a (to_N (tl path)) -> In a (to_N D))) -> 
        (forall a : Edge_type,
        (In a (tl (to_N path)) -> In a (to_N D)))
    ). hammer. apply H1. clear H1. clear H_tl.
    
    unfold to_N.
    hammer. 
Qed.




(* ============ connected ===========*)

(* From Taxiway Require Import Example.
Example path_conn_eg1 : path_conn (rev [(((Ch, input), (BC, Ch)), C);
(((BC, Ch), (AA3, A3r)), A3)]).
Proof. simpl. unfold Arc_conn. easy. Qed.  *)


(* an arc is legal if it has the form (from AB to BC), i.e. ((B, A), (C, B)) *)
Definition is_legal_arc (e1 : Arc_type)  : Prop :=
   (e1.1.1.1 = e1.1.2.2).

(* Example is_legal_arc_eg : is_legal_arc (((BC, Ch), (AA3, BC)), ""). *)
(* Proof. unfold is_legal_arc. easy. Qed. *)

(* TWO edges are connected if e1.from = e2.to *)
Definition Edge_conn (e1 : Edge_type) (e2 : Edge_type) : Prop :=
    e1.1.2 = e2.1.1.

(* NOTE the first edge is the later edge, i.e. the path is CH -> BC -> AA3 *)
(* Example Edge_conn_eg: Edge_conn ((AA3, BC), "") ((BC, Ch), "") .
Proof. simpl. unfold Edge_conn. easy. Qed. *)


(*  The function to check whether path(edge) is connected
    Since the edge doesn't contains the "from" information, we need to refer to the neighbor
*)
Fixpoint naive_path_conn (path : list Edge_type): Prop :=
    match path with
    | path_f::path_r => match path_r with
        | path_s::path_r_r => (Edge_conn path_f path_s) /\ (naive_path_conn path_r)
        | [] => True
        end
    | [] => True
    end.

(* 
    The first element in the path is the initial arc assigned by Find_path, which is (((start_v, input), (start_v, input)), t), will violate the property
    We drop the first element in this property

    We further introduce an assumption of the path, however the find_path on generated complete graph will always satisfy the assumption. We leave this part to partial identity.
*)
Theorem naive_conn:
    forall (path : list Arc_type) start_v end_v ATC D  (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    ((forall arc, In arc (tl path) -> is_legal_arc arc) -> naive_path_conn (rev (to_N path))).
Proof.
intros.
        assert (
            path_conn (rev path)
        ) as H_original by hammer. 

        (* TODO put this below to_N *)
        assert (forall path, (rev (to_N path)) = to_N (rev path)) as lemma. {
            intros.
            unfold to_N. unfold c_to_n. rewrite map_rev. reflexivity. 
        }

        (* this assertion should be unrelated to find_path, and quantify over path to make it strong enough *)
        assert (forall rev_path, 
            path_conn (rev_path) ->
            (forall arc, In arc (tl (rev rev_path))%SEQ -> is_legal_arc arc) ->
             naive_path_conn ((to_N (rev_path)))). 
        {
            intro p. dependent induction p.
                + easy.
                + intros. simpl. 
                destruct p eqn:Hp.
                    * easy.
                    * assert (path_conn (a0 :: l)). {
                        hammer.
                    }
                    simpl.
                    assert (rev [:: a, a0 & l] = rev (a0::l) ++ (rev [a])). {
                        rewrite <- rev_app_distr. reflexivity.
                    }
                    split.
                    {
                        assert(H_a_legal: is_legal_arc a). {
                            apply H3.
                           
                            rewrite -> H5. destruct (rev (a0 :: l)) eqn:H7.
                            - assert ((a0 :: l) = rev []). hammer. simpl in H6. discriminate H6.
                            - simpl. intuition.
                        }
                        unfold Edge_conn, c_to_n; simpl.
                        simpl in H2. destruct H2.
                        unfold Arc_conn in H2. rewrite <- H2.
                        (* assert (path' = rev  [:: a, a0 & l]  ). hammer. *)
                        
                        unfold is_legal_arc in H_a_legal. hammer.
                    }
                    
                    
                    {
                    apply IHp in H4.
                    - simpl in H4. assumption.
                    - intros. apply H3. rewrite -> H5.
                    simpl. simpl in H6.
                    remember ((rev l ++ [a0])%list) as l1.
                    destruct l1 eqn: Hl1.
                        + simpl in H6. contradiction.
                        +  simpl in H6. simpl. apply in_rev. apply in_rev in H6.
                        rewrite rev_app_distr. simpl. right. assumption.
                    }
        }

        rewrite -> lemma.
        apply H2. assumption. rewrite rev_involutive. assumption.
Qed.




(* ========== follow ATC =========*)

Fixpoint naive_path_coresp_atc (path : list Edge_type) : list string :=
    match path with
    | [] => []
    | a::b => match b with
        | []   => [a.2]
        | c::l => if (a.2 =? c.2) 
        then (naive_path_coresp_atc b)
        else a.2::(naive_path_coresp_atc b)
        end 
    end.


Definition naive_path_follow_atc (path : list Edge_type) (atc : list string) : Prop :=
    atc = naive_path_coresp_atc path.


Theorem naive_follow_atc:
    forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    naive_path_follow_atc (to_N path) ATC.
Proof.
intros. unfold naive_path_follow_atc.
    
assert (
    path_follow_atc path ATC
) as H_original. hammer. unfold path_follow_atc in H_original.

assert (
    forall path, path_coresp_atc path = naive_path_coresp_atc (to_N path)
) as H_tl. {
    intros. 
    induction path0.
    - easy.
    - simpl.
    hammer.
}
hammer. 
Qed.




(* ========== Correctness Preserve ========== *)

(* collection of correctness properties *)
Theorem correctness_preservation:
    forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path paths ->
    (* if find_path return some paths, then every path has the following properties: *)
    naive_path_follow_atc (to_N path) ATC /\
    naive_path_in_graph (to_N path) (to_N D) /\
    naive_path_starts_with_vertex (to_N path) start_v /\
    naive_ends_with_vertex (to_N path) end_v /\
    (* The assumption always hold for D = to_C G, the complete theorem is in Lifting.v *)
    ((forall arc, In arc (tl path) -> is_legal_arc arc) -> naive_path_conn (rev (to_N path))).
Proof. intros.
(* this tactic applys thm to current goal and 
   finds hypothesis from assumption for the theorem *)
Ltac temp_tac thm start_v end_v ATC D path paths :=
    let app_thm := (apply (thm start_v end_v ATC D path paths); (repeat assumption)) in
        match goal with
        | [ |- _ /\ _] => split; [app_thm | ]
        | _ =>  app_thm 
        end.

temp_tac naive_follow_atc start_v end_v ATC D path paths.
temp_tac naive_in_graph start_v end_v ATC D path paths.
temp_tac naive_start_correct start_v end_v ATC D path paths.
temp_tac naive_end_correct start_v end_v ATC D path paths.
temp_tac naive_conn path start_v end_v ATC D paths.
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


(* a makeup for naive_conn *)
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