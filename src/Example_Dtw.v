(*
    Here is the Example of Dtw airport

    Since the Dtw airport naming use a same variable on nodes and taxiway, such as "Z10".
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

Example A1 : Vertex := index 1.
Example A2 := index 2.
Example A3 := index 3.
Example AR := index 4.
Example A4 := index 5.
Example AV := index 6.
Example A5 := index 7.
Example A6 := index 8.
Example A7 := index 9.
Example VZ := index 10.
Example Z5 := index 11.
Example Z7 := index 12.
Example Z10 := index 13.
Example Y1 := index 14.
Example Y2 := index 15.
Example RY := index 16.
Example Y3 := index 17.
Example Y4 := index 18.
Example YV := index 19.
Example Y5 := index 20.
Example Y7 := index 21.
Example Y9 := index 22.
Example Y10 := index 23.
Example VB := index 24.
Example VF := index 25.
Example V2 := index 26.
Example VG := index 27.
Example VM := index 28.
Example VW := index 29.
Example V1 := index 30.
Example M1 := index 31.
Example MF := index 32.
Example FG := index 33.
Example M5 := index 34.
Example M6 := index 35.
Example T1 := index 36.
Example T2 := index 37.
Example T3 := index 38.
Example T4 := index 39.
Example TW := index 40.
Example T5 := index 41.
Example T6 := index 42.
Example T7 := index 43.
Example T8 := index 44.
Example W1 := index 45.
Example W2 := index 46.
Example W3 := index 47.
Example W4 := index 48.
Example W5 := index 49.
Example W6 := index 50.
Example W7 := index 51.
Example P5 := index 52.
Example P6 := index 53.
Example S1 := index 54.
Example S6 := index 55.
Example FW := index 56.
Example ZY10 := index 57.
Example ZY7 := index 58.
Example ZY5 := index 59.
Example R := index 60.
Example Y9L := index 61.
Example MP5 := index 62.
Example MP6 := index 63.
Example V21R := index 64.
Example V21L := index 65.
Example V22L := index 66.
Example M9L := index 67.
Example WS6 := index 68.
Example WS41 := index 69.
Example W9R := index 70.
Example W9L := index 71.
Example F9L := index 72.
Example FG9L := index 73.
Example T := index 74.


(* =========== taxiway names ==========*)

Example R_T : Taxiway_type := "R".
Example Z10_T := "Z10".
Example Z_T := "Z".
Example Q_T := "Q".
Example M6_T := "M6".
Example Y5_T := "Y5".
Example A_T := "A".
Example P6_T := "P6".
Example T_T := "T".
Example Z7_T := "Z7".
Example Y7_T := "Y7".
Example W_T := "W".
Example P_T := "P".
Example M_T := "M".
Example Y_T := "Y".
Example G_T := "G".
Example W6_T := "W6".
Example S1_T := "S1".
Example M5_T := "M5".
Example PP_T := "PP".
Example P5_T := "P5".
Example S_T := "S".
Example V_T := "V".
Example W4_T := "W4".
Example F_T := "F".
Example Y10_T := "Y10".
Example S6_T := "S6".
Example Z5_T := "Z5".

(* ======== Naive Graph ======== *)

Example Dtw : N_Graph_type := [
    ((A1, input), "");
    ((A2, input), "");
    ((A3, input), "");
    ((A4, input), "");
    ((A5, input), "");
    ((A6, input), "");
    ((A7, input), "");
    ((Z5, input), "");
    ((Z7, input), "");
    ((Z10, input), "");
    ((Y1, input), "");
    ((Y2, input), "");
    ((Y3, input), "");
    ((Y4, input), "");
    ((Y5, input), "");
    ((Y7, input), "");
    ((Y9, input), "");
    ((Y10, input), "");
    ((VB, input), "");
    ((VF, input), "");
    ((V2, input), "");
    ((VG, input), "");
    ((VM, input), "");
    ((VW, input), "");
    ((V1, input), "");
    ((M1, input), "");
    ((MF, input), "");
    ((M5, input), "");
    ((M6, input), "");
    ((T1, input), "");
    ((T2, input), "");
    ((T3, input), "");
    ((T4, input), "");
    ((TW, input), "");
    ((T5, input), "");
    ((T6, input), "");
    ((T7, input), "");
    ((T8, input), "");
    ((W1, input), "");
    ((W2, input), "");
    ((W3, input), "");
    ((W4, input), "");
    ((W5, input), "");
    ((W6, input), "");
    ((W7, input), "");
    ((P5, input), "");
    ((P6, input), "");
    ((S1, input), "");
    ((S6, input), "");
    ((FW, input), "");
    ((ZY10, input), "");
    ((ZY7, input), "");
    ((ZY5, input), "");
    ((R, input), "");
    ((Y9L, input), "");
    ((MP5, input), "");
    ((MP6, input), "");
    ((V21R, input), "");
    ((V21L, input), "");
    ((V22L, input), "");
    ((M9L, input), "");
    ((WS6, input), "");
    ((WS41, input), "");
    ((W9R, input), "");
    ((W9L, input), "");
    ((F9L, input), "");
    ((FG9L, input), "");
    ((T, input), "");
    ((A1, A2), A_T);
    ((A1, Y1), Q_T);
    ((A2, A3), A_T);
    ((A3, AR), A_T);
    ((AR, A4), A_T);
    ((AR, R), R_T);
    ((A4, AV), A_T);
    ((AV, A5), A_T);
    ((AV, VZ), V_T);
    ((A5, A6), A_T);
    ((A6, A7), A_T);
    ((VZ, Z5), Z_T);
    ((VZ, V22L), V_T);
    ((Z5, Z7), Z_T);
    ((Z5, ZY5), Z5_T);
    ((Z7, Z10), Z_T);
    ((Z7, ZY7), Z7_T);
    ((Z10, ZY10), Z10_T);
    ((Y1, Y2), Y_T);
    ((Y1, T8), T_T);
    ((Y2, RY), Y_T);
    ((RY, Y3), Y_T);
    ((RY, R), R_T);
    ((Y3, Y4), Y_T);
    ((Y4, Y9L), Y_T);
    ((YV, Y5), Y_T);
    ((YV, VB), Y_T);
    ((YV, Y9L), Y_T);
    ((YV, V22L), V_T);
    ((Y5, Y7), Y_T);
    ((Y5, ZY5), Y5_T);
    ((Y7, Y9), Y_T);
    ((Y7, ZY7), Y7_T);
    ((Y9, Y10), Y_T);
    ((Y10, ZY10), Y10_T);
    ((VB, VF), V_T);
    ((VF, V2), V_T);
    ((VF, F9L), F_T);
    ((V2, VG), V_T);
    ((VG, VM), V_T);
    ((VG, FG9L), G_T);
    ((VM, M5), M_T);
    ((VM, V21R), V_T);
    ((VM, M9L), M_T);
    ((VW, W7), W_T);
    ((VW, V21R), V_T);
    ((VW, V21L), V_T);
    ((VW, W9L), W_T);
    ((V1, V21L), V_T);
    ((M1, MF), M_T);
    ((MF, FG), M_T);
    ((MF, FW), F_T);
    ((MF, M9L), M_T);
    ((FG, F9L), F_T);
    ((FG, FG9L), G_T);
    ((M5, M6), M_T);
    ((M5, MP5), M5_T);
    ((M6, MP6), M6_T);
    ((T1, T2), T_T);
    ((T2, T3), T_T);
    ((T3, T4), T_T);
    ((T4, T), T_T);
    ((TW, T5), T_T);
    ((TW, W2), W_T);
    ((TW, W9R), W_T);
    ((TW, T), T_T);
    ((T5, T6), T_T);
    ((T5, FW), PP_T);
    ((T6, T7), T_T);
    ((T7, T8), T_T);
    ((W1, W9R), W_T);
    ((W2, W3), W_T);
    ((W3, W4), W_T);
    ((W3, FW), F_T);
    ((W4, W5), W_T);
    ((W4, FW), F_T);
    ((W4, WS41), W4_T);
    ((W5, W6), W_T);
    ((W6, WS6), W6_T);
    ((W6, W9L), W_T);
    ((P5, P6), P_T);
    ((P5, MP5), P5_T);
    ((P6, MP6), P6_T);
    ((S1, S6), S_T);
    ((S1, WS41), S1_T);
    ((S6, WS6), S6_T)
].


(* ============================
    transfer naming map 
    Most similar in Example.v
   ============================ *)

Example Dtw_v2s (v:Vertex) : string :=
    match v with
    | index 0 => "input"
    | index 1 => "A1"
    | index 2 => "A2"
    | index 3 => "A3"
    | index 4 => "AR"
    | index 5 => "A4"
    | index 6 => "AV"
    | index 7 => "A5"
    | index 8 => "A6"
    | index 9 => "A7"
    | index 10 => "VZ"
    | index 11 => "Z5"
    | index 12 => "Z7"
    | index 13 => "Z10"
    | index 14 => "Y1"
    | index 15 => "Y2"
    | index 16 => "RY"
    | index 17 => "Y3"
    | index 18 => "Y4"
    | index 19 => "YV"
    | index 20 => "Y5"
    | index 21 => "Y7"
    | index 22 => "Y9"
    | index 23 => "Y10"
    | index 24 => "VB"
    | index 25 => "VF"
    | index 26 => "V2"
    | index 27 => "VG"
    | index 28 => "VM"
    | index 29 => "VW"
    | index 30 => "V1"
    | index 31 => "M1"
    | index 32 => "MF"
    | index 33 => "FG"
    | index 34 => "M5"
    | index 35 => "M6"
    | index 36 => "T1"
    | index 37 => "T2"
    | index 38 => "T3"
    | index 39 => "T4"
    | index 40 => "TW"
    | index 41 => "T5"
    | index 42 => "T6"
    | index 43 => "T7"
    | index 44 => "T8"
    | index 45 => "W1"
    | index 46 => "W2"
    | index 47 => "W3"
    | index 48 => "W4"
    | index 49 => "W5"
    | index 50 => "W6"
    | index 51 => "W7"
    | index 52 => "P5"
    | index 53 => "P6"
    | index 54 => "S1"
    | index 55 => "S6"
    | index 56 => "FW"
    | index 57 => "ZY10"
    | index 58 => "ZY7"
    | index 59 => "ZY5"
    | index 60 => "R"
    | index 61 => "Y9L"
    | index 62 => "MP5"
    | index 63 => "MP6"
    | index 64 => "V21R"
    | index 65 => "V21L"
    | index 66 => "V22L"
    | index 67 => "M9L"
    | index 68 => "WS6"
    | index 69 => "WS41"
    | index 70 => "W9R"
    | index 71 => "W9L"
    | index 72 => "F9L"
    | index 73 => "FG9L"
    | index 74 => "T"
    | _ => "Error Vertex"
    end.    

Fixpoint string_list_append (ls : list string) : string :=
    match ls with
        | [] => ""
        | h::t => append h (string_list_append t)
    end.

Definition edge_to_string (f:Vertex->string) (e:Edge_type) : string := 
    string_list_append ["(from " ; (f e.1.2); " to ";(f e.1.1); " on taxiway "; e.2; ")"].

Example Dtw_e2s (le:list Edge_type) : list string :=
    map (edge_to_string Dtw_v2s) le.

Example example_result_to_string (res : option (list (list Edge_type))) : list (list string) :=
    match res with
    | None => [["No path found."]]
    | Some(s) => map Dtw_e2s s
    end.


(* ============== Path finding example ===============*)
Example path_finding_example_1 := (
    path_finding_algorithm ZY10 FG9L [Z10_T; Z_T; Z5_T; Y5_T; Y_T; V_T; G_T] Dtw
).

Example path_finding_example_1_string := example_result_to_string path_finding_example_1.

Eval compute in path_finding_example_1_string.

(* a great long path *)
Example path_finding_example_2 := (
    path_finding_algorithm A7 W1 [A_T; R_T; Y_T; V_T; F_T; M_T; F_T; PP_T; T_T; W_T] Dtw
).

Example path_finding_example_2_string := example_result_to_string path_finding_example_2.

Eval compute in path_finding_example_2_string.