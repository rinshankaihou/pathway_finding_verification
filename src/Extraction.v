(* 
    run this file in order to extract to ocaml
    In default, this file won't be compiled use "make"
*)

From Taxiway Require Export Implementation.

Require Coq.extraction.Extraction.
Extraction "find_path.ml" find_path.