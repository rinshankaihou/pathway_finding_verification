Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Coq.Program.Tactics.
From Taxiway Require Import To_naive.
From Taxiway Require Import Find_path.
From Taxiway Require Import Correctness.

From Hammer Require Import Hammer.

(* This file have five theorems indicating the theorem of complete graph preserve downward*)

Definition naive_path_starts_with_vertex (path : list Edge_type) (start_v : Vertex) : Prop := 
    exists taxiway_name, exists l, path = ((start_v, input), taxiway_name) :: l.


Theorem naive_start_correct:
    forall start_v end_v ATC D (path : list Arc_type) (paths : list (list Arc_type)),
    Some paths = (find_path (start_v : Vertex) (end_v : Vertex) (ATC : list string) (D : C_Graph_type)) ->
    In path (to_N paths) ->
    naive_path_starts_with_vertex path start_v.