(*
    Here is the Example of the Ann Arbor Airport

    Naming Convention
        ARB: Ann Arbor Municipal Airport
        NG: Naive graph
        CG: complete graph
*)

Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
From Taxiway Require Import Types.
From Taxiway Require Import Implementation.

(* ============ vertex ============*)

(* 
    hardcoded input vertex. if a vertex is start_vertex in the naive graph, 
    we encode input Node in the complete graph to be ((start_vertex, input), (start_vertex, input)) 
*)
Example input : Vertex := index 0.

(* vertices in the naive graph, ARB *)
Example AA3 : Vertex := index 1.
Example AB := index 2.
Example AC := index 3.
Example AA1 := index 4.
Example Ch := index 5.
Example BC := index 6.
Example A3r := index 7.
Example A2r := index 8.
Example A1r := index 9.

(* ============ taxiway names ============*)
Example A : Taxiway_type := "A".
Example B := "B".
Example C := "C".
Example A1 := "A1".
Example A2 := "A2".
Example A3 := "A3".

(* ============ graph ============*)
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
    (((AA1, A1r), (AC, AA1)), A);
    (((AA1, AC), (A1r, AA1)), A1);
    (((BC, Ch), (AB, BC)), B);
    (((BC, Ch), (AC, BC)), C);
    (((BC, AB), (Ch, BC)), C);
    (((BC, AB), (AC, BC)), C);
    (((BC, AC), (Ch, BC)), C);
    (((BC, AC), (AB, BC)), B)
].


(* ============ testcases ============*)
Example eg_find_path_aux_1 : find_path Ch AB [C] ann_arbor = Some ([]).
Proof. reflexivity. Qed.
    
Example eg_find_path_aux_2 : find_path Ch BC [C] ann_arbor = 
    Some ([[(((Ch, input), (Ch, input)), C); (((Ch, input), (BC, Ch)), C)]]).
Proof. reflexivity. Qed.
    
Example eg_find_path_aux_3 : find_path Ch AA3 [C;B;A] ann_arbor = 
    Some ([[(((Ch, input), (Ch, input)), C); (((Ch, input), (BC, Ch)), C); (((BC, Ch), (AB, BC)), B); (((AB, BC), (AA3, AB)), A)]]).
Proof. reflexivity. Qed.

(* It works as expected because AA3 is not a input, so there's no edge from (AA3, input)*)    
Example eg_find_path_aux_4 : find_path AA3 AA1 [A;B;C;A] ann_arbor = 
    Some ([]).
Proof. reflexivity. Qed. 
    
Example eg_find_path_aux_5 : find_path A3r A1r [A3; A; A1] ann_arbor = 
    Some ([[(((A3r, input), (A3r, input)), A3); (((A3r, input), (AA3, A3r)), A3); (((AA3, A3r), (AB, AA3)), A);
    (((AB, AA3), (AC, AB)), A); (((AC, AB), (AA1, AC)), A); (((AA1, AC), (A1r, AA1)), A1)]]).
Proof. reflexivity. Qed.

(* This is a loop case*)
Example eg_find_path_aux_6 : find_path Ch Ch [C; B; A; C; B; A; C] ann_arbor = 
    Some ([[(((Ch, input), (Ch, input)), C); (((Ch, input), (BC, Ch)), C); (((BC, Ch), (AB, BC)), B); (((AB, BC), (AC, AB)), A);
    (((AC, AB), (BC, AC)), C); (((BC, AC), (AB, BC)), B); (((AB, BC), (AC, AB)), A); (((AC, AB), (BC, AC)), C); (((BC, AC), (Ch, BC)), C)]]).
Proof. reflexivity. Qed. 