(* 
    run this file in order to extract to ocaml
    In default, this file won't be compiled use "make"
*)

(* pure algorithm code *)
From Taxiway Require Export Algorithm.

Require Coq.extraction.Extraction.
Extraction "extraction/path_finding_algorithm.ml" path_finding_algorithm.


(* algorithm with example *)
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import Coq.Strings.String.

Import ListNotations.
Import C.Notations.


Open Scope string_scope.
Example print_start := "[".
Example print_end := "]".
Example print_empty := "".
Example print_concat := ";".
Close Scope string_scope.


Definition print_line (s:string) : C.t System.effect unit :=
    System.log (LString.s s ++ LString.s print_concat).

Fixpoint print_path (ls : list string) : C.t System.effect unit :=
    match ls with
        | [] => System.log (LString.s "]")
        | h::t => do! (print_line h) in print_path t 
    end.

Fixpoint print_result (res: list (list string)) : C.t System.effect unit :=
    match res with
        | [] => System.log (LString.s print_empty) 
        | h::t => do! System.log (LString.s print_start) in do! (print_path (h)) in (print_result t)
    end.


From Taxiway Require Import Example.

Definition print_example (argv : list LString.t) : C.t System.effect unit :=
    print_result path_finding_example_string.

Definition main := Extraction.launch print_example.

Extraction "extraction/coq_print" main. 


(* If you don't have IO library, it's an alternative choice*)

(* From Taxiway Require Import Example.
Extraction "extraction/path_finding_example.ml" path_finding_example_string. *)

