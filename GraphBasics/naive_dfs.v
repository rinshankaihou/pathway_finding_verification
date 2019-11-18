
From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
(*From Coq Require Import FSets.FMapInterface.*)
(* The definitions imported:
     Vertex: nat->Vertex, indexed by nat
     Edge: Vertex->Vertex->Edge (not being used currently)
     V_list = list Vertex
     E_list = list Edge
   New definitions:
     taxiway : V_list, an ordered list of all vertices on the taxiway. 
                       There is no name for a taxiway. 
                       
     taxiways : list taxiway, a list of all taxiways. order does not matter.
                              TODO Consider using string->V_list to replace taxiways.
   taxiways represents all information in the graph for now
   ATC Command is: (start_vertex, end_vertex, taxiway_names)
   Entry point (top level function) find_path_wrapper.
*)

Example A1 := index 1.
Example A2 := index 2.
Example A3 := index 3.
Example C1 := index 4.
Example CB := index 5.
Example BA := index 6.
Example CA := index 7.

(* for now we do not use edge *)
Example eg_edge_list : E_list :=
  [E_ends C1 CB;
   E_ends A1 CA;
   E_ends A2 BA;
   E_ends A3 BA;
   E_ends CB C1; E_ends CB BA; E_ends CB CA;
   E_ends BA A2; E_ends BA A3; E_ends BA CA;
   E_ends CA A1; E_ends CA CB; E_ends CA BA].

Definition Indexing : Type := Edge -> nat.


(* use nat to represent taixway name. 
C 1
A1*)

(* use the other def for Taxiway 
Definition _Taxiway := E_list.
(* TODO check if duplicated edges are necessary. *)
Example tC : _Taxiway :=
  [E_ends C1 CB; E_ends CB C1; E_ends CB CA ; E_ends CA CB].
Example tA1 : _Taxiway :=
  [E_ends A1 CA; E_ends CA A1].
Example tA2 : _Taxiway :=
  [E_ends A2 BA; E_ends BA A2].
Example tA : _Taxiway :=
  [E_ends A3 BA; E_ends BA A3;  E_ends BA CA; E_ends CA BA].
Example tB : _Taxiway :=
  [E_ends CB BA; E_ends BA CB].
Example eg_taxiways :=
 [tC; tA1; tA2; tA; tB].
*)


(* define taxiway name as their index in taxiway_names *)


Example nC  := [C1; CB; CA].
Example nA1 := [A1; CA].
Example nA2 := [A2; BA].
Example nA := [A3; BA; CA].
Example nB := [CB; BA].
Example eg_taxiways :=
  [nC; nA1; nA2; nA; nB].
(* abandoned example *)
(* Example eg_indexing (e : Edge) : nat :=
  match e with
  | E_ends C1 CB => tC
  | E_ends A1 CA => tA1
  | E_ends A2 BA => tA2
  | E_ends A3 BA => tA
  | E_ends CB C1 => tC | E_ends CB BA => tB | E_ends CB CA => tC
  | E_ends BA A2 => tA2 | E_ends BA A3 => tA | E_ends BA CB => B | E_ends BA CA => tA
  | E_ends CA A1 => tA1 | E_ends CA CB => tC | E_ends CA BA => tA
  end. *)



Definition eqv (v1 : Vertex) (v2 : Vertex) : bool :=
  match v1, v2 with
  index n1, index n2 => beq_nat n1 n2
  end.

Fixpoint eqv_list (vlst1 : V_list) (vlst2 : V_list) : bool :=
  match vlst1, vlst2 with
  | v1::r1, v2::r2 => if eqv v1 v2 then eqv_list r1 r2 else false
  | [], [] => true
  | _, _ => false
  end.
Definition v_in_e (v : Vertex) (e : Edge) : bool :=
  match e with E_ends e1 e2 =>
  match v, e1, e2 with index n, index n1, index n2 =>
  orb (beq_nat n n1)  (beq_nat n n2)
  end
  end.

(* return sublist after v, or [] *)
Fixpoint list_after_v (v : Vertex) (taxiway : V_list) {struct taxiway}: V_list :=
  match taxiway with  
  | a::rest => if eqv a v then rest else list_after_v v rest
  | _ => []
  end.

(* return [next_elem] after v, or [] *)
Definition next_neighbor (v : Vertex) (taxiway : V_list) : V_list :=
  match list_after_v v taxiway with
  | next_elem::rest => [next_elem]
  | _ => []
  end.

(* find a vertex in cur_taxi that is also in next_taxi, and chop the rest *)
Fixpoint chop_tail (cur_lst : V_list) (next_taxi : V_list) : option V_list :=
  match cur_lst with
  | [] => None
  | fst::rest => if existsb (eqv fst) next_taxi then Some [fst] else
      match chop_tail rest next_taxi with
      | None => None
      | Some res => Some (fst::res)
      end
  end.

(* for demonstration. Do not use in algo *)
Definition unwrap {T : Type} (thing : option (list T)) : list T := 
  match thing with 
  | Some thing' => thing' 
  | None => []
  end. 

(* example *)
Eval vm_compute in eqv_list (unwrap (chop_tail nC nB)) [C1; CB] == true.


(* TODO for now, if there are multiple intermediate vertexs, we arbitrary pick one *)
(* return a path segment of cur_taxi, from cur_vertex (exclusive) to a vertex on the next taxiway (inclusive) *) 
Definition get_seg (cur_vertex : Vertex) (cur_taxi : V_list) (next_taxi : V_list) : option V_list :=
  match (chop_tail  (list_after_v cur_vertex cur_taxi) next_taxi), 
        (chop_tail  (list_after_v cur_vertex (rev cur_taxi)) next_taxi) with 
    | None, None => None
    | Some lst1, Some lst2 => None
    | Some lst1, None => Some lst1
    | None, Some lst2 => Some lst2
  end.
(* test cases *)
Example eg_get_seg_1: get_seg CA nA [A3; A3] = Some [BA; A3]. 
Proof. reflexivity. Qed.
Example eg_get_seg_2: get_seg C1 nC nA = Some [CB; CA].
Proof. reflexivity. Qed.
Example eg_get_seg_3: get_seg C1 nC nB = Some [CB].
Proof. reflexivity. Qed.
Example eg_get_seg_4: get_seg CA nC nB = Some [CB].
Proof. reflexivity. Qed.

Fixpoint find_path (cur_vertex : Vertex) (cur_taxiway : V_list) (rest_taxiway_names : list V_list) : option V_list :=
    match rest_taxiway_names with
    | [] => Some []
    | next_taxiway::rest_taxiway =>
      match get_seg cur_vertex cur_taxiway next_taxiway with
        | None => None
        | Some seg => match rev seg with (* rev is to extract the last elem *)
          | [] => None (* Should be unreachable, since a valid seg contains at least a vertex on the next taxiway *)
          | last_vertex::rest => 
            match (find_path last_vertex next_taxiway rest_taxiway) with
            | None => None
            | Some result (* result of the recursive call *) => Some ((rev (last_vertex::rest)) ++ result)
            end
          end
      end
    end.
(* test cases *)
Eval vm_compute in  find_path C1 nC [nB; nA; [A3; A3]].
(* ATC CMD: (start_vertex, end_vertex, taxiway_names). taxiway_names is a subset of every taxiway in the graph *)
Definition find_path_wrapper (start_vertex : Vertex) (end_vertex : Vertex) (taxiway_names : list V_list) : option V_list :=
  match taxiway_names with
  | [] => None
  | fst_taxiway::rest_taxiways =>
    (* create a dummy taxiway in the end *)
    match find_path start_vertex fst_taxiway (rest_taxiways ++ [[end_vertex;end_vertex]]) with
    | None => None
    | Some res => Some (start_vertex::res)
    end   
  end.
(* test cases *)
Example eg_find_path_1: find_path_wrapper C1 A3 [nC;nB;nA] = Some [C1; CB; BA; A3].
Proof. reflexivity. Qed.
Example eg_find_path_2: find_path_wrapper A3 C1 (rev [nC;nB;nA]) = Some (rev [C1; CB; BA; A3]).
Proof. reflexivity. Qed.
Example eg_find_path_3: find_path_wrapper C1 A3 [nC;nA] = Some [C1; CB; CA; BA; A3].
Proof. reflexivity. Qed.
Example eg_find_path_4: find_path_wrapper C1 CB [nC] = Some [C1;CB].
Proof. reflexivity. Qed.
Example eg_find_path_5: find_path_wrapper C1 BA [nB] = None.
Proof. reflexivity. Qed.
Example eg_find_path_6: find_path_wrapper C1 A3 [nC;nB;nA;nC;nB;nA;nC;nB;nA] = Some [C1;CB;BA;CA;CB;BA;CA;CB;BA;A3].
Proof. reflexivity. Qed.
