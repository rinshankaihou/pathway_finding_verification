(* 
    run this file in order to extract to ocaml
    In default, this file won't be compiled use "make"
*)

From Taxiway Require Export Algorithm.

Require Coq.extraction.Extraction.
Extraction "extraction/path_finding_algorithm.ml" path_finding_algorithm.
Extraction "extraction/path_finding_example.ml" path_finding_example.