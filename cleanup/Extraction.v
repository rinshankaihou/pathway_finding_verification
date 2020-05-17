(* 
    run this file in order to extract to ocaml
    In default, this file won't be compiled use "make"
*)

(* pure algorithm code *)
From Taxiway Require Export Algorithm.

Require Coq.extraction.Extraction.
Extraction "extraction/path_finding_algorithm.ml" path_finding_algorithm.


(* algorithm with example *)
From Taxiway Require Import Example.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.

Example path_finding_example := (path_finding_algorithm Ch A3r [C;A;A3] naive_ann_arbor).

Extraction "extraction/path_finding_example.ml" path_finding_example.