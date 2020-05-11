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
From Taxiway Require Import Find_path To_complete To_naive.

(* ============ vertex ============*)

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
Example ann_arbor : C_Graph_type :=[
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
    (((AC, BC), (AA1, AC)), A);
    (((AA1, A1r), (AC, AA1)), A);
    (((AA1, AC), (A1r, AA1)), A1);
    (((BC, Ch), (AB, BC)), B);
    (((BC, Ch), (AC, BC)), C);
    (((BC, AB), (Ch, BC)), C);
    (((BC, AB), (AC, BC)), C);
    (((BC, AC), (Ch, BC)), C);
    (((BC, AC), (AB, BC)), B)
].

Example naive_ann_arbor : N_Graph_type :=[
    ((Ch, input), "");
    ((A1r, input), "");
    ((A2r, input), "");
    ((A3r, input), "");    
    ((Ch, BC), C);
    ((BC, AB), B);
    ((AB, AA3), A);
    ((AA3, A3r), A3);
    ((AB, A2r), A2);
    ((BC, AC), C);
    ((AB, AC), A);
    ((AC, AA1), A);
    ((AA1, A1r), A1)
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

(* It works as expected because AA3 is not a input, so there's no arc from (AA3, input)*)    
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

Example G1 : N_Graph_type := [ 
    ((AA1, AC), A);
    ((AA1, A1r), A)
    ].



From mathcomp Require Import all_ssreflect.

Theorem toC_toN_id : forall (ne: Edge_type) ,
    no_self_loop G1 -> (* no self loop *)
    In ne G1 ->
    (exists prev_ne, In prev_ne (previous_edges ne (undirect_to_bidirect G1))) -> (* ne has a previous edge in the bidirect graph *)
    (forall ne, In ne G1 ->
        (ne.1.1 >v< input) /\ (ne.1.2 >v< input)) -> (* input vertex should not appear in any naive graph *)
    In ne (to_N (to_C G1)).

    Example complete_G1 : (to_N (to_C G1)) = [].
Proof. simpl.

Eval compute in (to_C naive_ann_arbor).
simpl.  unfold c_to_n. simpl. unfold naive_ann_arbor.


