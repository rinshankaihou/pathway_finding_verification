(*
    The top-level algorithm with correctness proof. a combination of To_complete, Find_path, To_naive. 
*)

From Taxiway Require Import Types To_complete Find_path To_naive Downward Correctness Lifting.
From Hammer Require Import Hammer.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.

(* top level theorem *)
Definition path_finding_algorithm (start_v : Vertex) (end_v : Vertex) (ATC : list Taxiway_type) (graph : N_Graph_type) : option (list (list Edge_type)) := 
    match find_path start_v end_v ATC (to_C graph) with 
    | None => None
    | Some v => Some (map to_N v)
    end.
    

(* top level correctness theorem. it states that every path in the output has these properties. *)
Theorem total_correctness:
    forall (start_v : Vertex) (end_v :Vertex) (ATC : list Taxiway_type) (G:N_Graph_type) (paths : list (list Edge_type)) (path : list (Edge_type)),
    Some paths = (path_finding_algorithm (start_v : Vertex) (end_v : Vertex) (ATC : list string) G) ->
    In path paths ->
    (naive_path_follow_atc path ATC /\
    naive_path_in_graph path (undirect_to_bidirect G) /\ (* (to_C (to_N G))*)
    naive_path_starts_with_vertex path start_v /\
    naive_ends_with_vertex path end_v /\
    naive_path_conn (rev path)).
Proof. intros.
unfold path_finding_algorithm in H. 
destruct (find_path start_v end_v ATC (to_C G)) eqn:H1.
- inversion H. rewrite H3 in H0. apply in_map_iff in H0. destruct H0 as [p H0]. destruct H0.
    rewrite <- H0.
    remember (to_C G) as D.
    repeat split.
    {
        apply naive_follow_atc with (start_v := start_v) (end_v := end_v) (D:=D) (paths:=l).
        easy. easy.
    }
    {
        assert (naive_path_in_graph (to_N p) (to_N D)). {
            apply naive_in_graph with (start_v := start_v) (end_v := end_v) (D:=D) (paths:=l) (ATC:=ATC).
            easy. easy.
        }
        unfold naive_path_in_graph. intro e. intros.
        unfold naive_path_in_graph in H4. apply H4 in H5.
        assert (incl [e] (to_N (to_C G))) by hammer.
        apply incl_tran with (l:=[e]) (m:= (to_N (to_C G))) (n:=(undirect_to_bidirect G)) in H6.
        - unfold incl in H6. apply H6. hammer.
        - apply toN_toC_G_subset_G.
    }
    {
        apply naive_start_correct with (start_v := start_v) (end_v := end_v) (D:=D) (paths:=l)  (ATC:=ATC).
        easy. easy. 
    }
    {
        apply naive_end_correct with (start_v := start_v) (end_v := end_v) (D:=D) (paths:=l)  (ATC:=ATC).
        easy. easy. 
    }
    {
        apply naive_conn_complete with (start_v := start_v) (end_v := end_v) (G:=G) (paths:=l)  (ATC:=ATC).
        hammer. easy.  
    }
- inversion H.
Qed.