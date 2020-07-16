(*
    Here is the Example of Wil airport

    Since the Wil airport naming use a same variable on nodes and taxiway, such as "C".
    This is a conflict in Coq, so we had to rename all taxiways names.
    We add "_T" suffix to taxiway variables.
*)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Strings.String Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
From Coq.Arith Require Import Arith EqNat.
Open Scope string_scope.
Open Scope list_scope.
From Taxiway Require Import Types Find_path To_complete To_naive Algorithm.


(* ========== vertex ===========*)

Example GB : Vertex := index 1.
Example G1 := index 2.
Example G2 := index 3.
Example GEH := index 4.
Example E1 := index 5.
Example HD := index 6.
Example DS := index 7.
Example HSB := index 8.
Example B2 := index 9.
Example B1 := index 10.
Example BC := index 11.
Example C := index 12.


(* =========== taxiway names ==========*)

Example G_T : Taxiway_type := "G".
Example C_T := "C".
Example D_T := "D".
Example S_T := "S".
Example H_T := "H".
Example B_T := "B".
Example E1_T := "E1".


(* ======== Naive Graph ======== *)
Example Wil : N_Graph_type := [
    ((GB, input), "");
    ((G1, input), "");
    ((G2, input), "");
    ((E1, input), "");
    ((B2, input), "");
    ((B1, input), "");
    ((BC, input), "");
    ((C, input), "");
    ((GB, G1), G_T);
    ((GB, BC), B_T);
    ((G1, G2), G_T);
    ((G2, GEH), G_T);
    ((GEH, E1), E1_T);
    ((GEH, HD), H_T);
    ((HD, DS), D_T);
    ((HD, HSB), H_T);
    ((DS, HSB), S_T);
    ((HSB, B2), B_T);
    ((B2, B1), B_T);
    ((B1, BC), B_T);
    ((BC, C), C_T)
].

(* ============================
    transfer naming map 
    Most similar in Example.v
   ============================ *)
Example Wil_v2s (v:Vertex) : string := 
    match v with
        | index 0 => "input"
        | index 1 => "GB"
        | index 2 => "G1"
        | index 3 => "G2"
        | index 4 => "GEH"
        | index 5 => "E1"
        | index 6 => "HD"
        | index 7 => "DS"
        | index 8 => "HSB"
        | index 9 => "B2"
        | index 10 => "B1"
        | index 11 => "BC"
        | index 12 => "C"
        | _ => "Error Vertex"
    end.

Fixpoint string_list_append (ls : list string) : string :=
    match ls with
        | [] => ""
        | h::t => append h (string_list_append t)
    end.

Definition edge_to_string (f:Vertex->string) (e:Edge_type) : string := 
    string_list_append ["(from " ; (f e.1.2); " to ";(f e.1.1); " on taxiway "; e.2; ")"].

Example Wil_e2s (le:list Edge_type) : list string :=
    map (edge_to_string Wil_v2s) le.

Example example_result_to_string (res : option (list (list Edge_type))) : list (list string) :=
    match res with
    | None => [["No path found."]]
    | Some(s) => map Wil_e2s s
    end.


(* =========== path finding examples =========== *)
Example path_finding_example_1 := (
    path_finding_algorithm G1 GB [G_T] Wil
).

Example path_finding_example_1_string := example_result_to_string path_finding_example_1.

Eval compute in path_finding_example_1_string.


Example path_finding_example_2 := (
    path_finding_algorithm E1 C [E1_T; H_T; B_T; C_T] Wil
).

Example path_finding_example_2_string := example_result_to_string path_finding_example_2.

Eval compute in path_finding_example_2_string.