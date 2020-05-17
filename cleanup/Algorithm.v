(*
    This file is the top-level algorithm execution, a combination of To_complete, Find_path, To_naive
    We 
*)

From Taxiway Require Import Types.
From Taxiway Require Import To_complete.
From Taxiway Require Import Find_path.
From Taxiway Require Import To_naive.
From Taxiway Require Import Example.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.


Definition path_finding_algorithm (start_v : Vertex) (end_v : Vertex) (ATC : list Taxiway_type) (graph : N_Graph_type) : option (list (list Edge_type)) := 
    match find_path start_v end_v ATC (to_C graph) with 
    | None => None
    | Some v => Some (map to_N v)
    end.
    

Example path_finding_example := (path_finding_algorithm Ch A3r [C;A;A3] naive_ann_arbor).
