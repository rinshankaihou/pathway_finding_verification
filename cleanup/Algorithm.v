(*
    This file is the top-level algorithm execution, a combination of To_complete, Find_path, To_naive
    We 
*)

From Taxiway Require Import Types.
From Taxiway Require Import To_complete.
From Taxiway Require Import Find_path.
From Taxiway Require Import To_naive.
From Taxiway Require Import Downward Correctness.

Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.


Definition path_finding_algorithm (start_v : Vertex) (end_v : Vertex) (ATC : list Taxiway_type) (graph : N_Graph_type) : option (list (list Edge_type)) := 
    match find_path start_v end_v ATC (to_C graph) with 
    | None => None
    | Some v => Some (map to_N v)
    end.
    

Theorem total_correctness:
    forall (start_v : Vertex) (end_v :Vertex) (ATC : list Taxiway_type) (G:N_Graph_type) (paths : list (list Edge_type)) (path : list (Edge_type)),
    Some paths = (path_finding_algorithm (start_v : Vertex) (end_v : Vertex) (ATC : list string) G) ->
    In path paths ->
    (naive_path_follow_atc path ATC /\
    naive_path_in_graph path G /\ (* (to_C (to_N G))*)
    naive_path_starts_with_vertex path start_v /\
    naive_ends_with_vertex path end_v /\
    naive_path_conn (rev path)).