(*
    Here is the Example of the Ann Arbor Airport

    Naming Convention
        ARB: Ann Arbor Municipal Airport
        NG: Naive graph
        CG: complete graph
*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
From Taxiway Require Import Types Find_path To_complete To_naive Algorithm.


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
    ((BC, input), (Ch, BC), C);
    ((BC, input), (AB, BC), B);
    ((BC, input), (AC, BC), C);
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

(* input edges have taxiway name "" *)
Example naive_ann_arbor : N_Graph_type :=[
    ((Ch, input), "");
    ((A1r, input), "");
    ((A2r, input), "");
    ((A3r, input), "");
    ((BC, input), "");   
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


(* ======== maps to transfer to printable string ======*)

Example ann_arbor_v2s (v:Vertex) : string := 
    match v with 
        | index 0 => "input"
        | index 1 => "AA3"
        | index 2 => "AB"
        | index 3 => "AC"
        | index 4 => "AA1"
        | index 5 => "Ch"
        | index 6 => "BC"
        | index 7 => "A3r"
        | index 8 => "A2r"
        | index 9 => "A1r"
        | _ => "Error Vertex"
    end.


Fixpoint string_list_append (ls : list string) : string :=
    match ls with
        | [] => ""
        | h::t => append h (string_list_append t)
    end.


(* ==========  maps an Edge_type to a string ============= *)
Definition edge_to_string (f:Vertex->string) (e:Edge_type) : string := 
string_list_append ["(from " ; (f e.1.2); " to ";(f e.1.1); " on taxiway "; e.2; ")"].

Example ann_arbor_e2s (le:list Edge_type) : list string :=
    map (edge_to_string ann_arbor_v2s) le.


Example example_result_to_string (res : option (list (list Edge_type))) : list (list string) :=
    match res with
    | None => [["No path found."]]
    | Some(s) => map ann_arbor_e2s s
    end.



(* ========== The example for extraction and print ==========*)
Example path_finding_example := (path_finding_algorithm Ch A3r [C;A;A3] naive_ann_arbor).

Example path_finding_example_string := example_result_to_string path_finding_example.

Eval compute in path_finding_example_string.



(* ============ find_path examples ============*)
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

(* ========= To_naive example =========*)

Example to_n_ex1 : to_N [(((Ch, BC), (Ch, AA3)), B); (((Ch, BC), (Ch, AA3)), B)] = [((Ch, AA3), B); ((Ch, AA3), B)].
Proof. compute. reflexivity. Qed.

Example to_n_ex2 : to_N_nodup [(((Ch, BC), (Ch, AA3)), B); (((Ch, BC), (Ch, AA3)), B)] = [((Ch, AA3), B)].
Proof. compute. reflexivity. Qed.


(* ======== To_complete example ======== *) 

(* This example shows our to_C exactly generate the ann arbor complete graph from naive graph *)

Example to_c_ex : incl (to_C naive_ann_arbor) ann_arbor /\ incl ann_arbor (to_C naive_ann_arbor).
Proof. 
    Ltac incl_tac := tryif (left; assumption || contradiction) then simpl else (right; incl_tac). 
    Ltac incl_tac_repeat H := elim H; [intros | ]; [incl_tac |]; clear H; intros.
    split. 
    - { unfold incl. simpl. intros. 
    repeat incl_tac_repeat H.
    contradiction. }
    - { unfold incl. simpl. intros.
    repeat incl_tac_repeat H.
    contradiction. }
Qed.
    
    
    

    
    
     
    
    
    
    