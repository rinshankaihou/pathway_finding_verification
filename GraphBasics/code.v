
From mathcomp Require Import all_ssreflect.
From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.
Import ListNotations.
(*From Coq Require Import FSets.FMapInterface.*)
(* The definitions:
    Node
    Edge
    Node_list
    Edge_list *)



Check E_set (index 1) (index 2).

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



Definition Node := Vertex.

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


(* TODO for now, if there are multiple intermediate nodes, we arbitrary pick one *)
(* return a path segment of cur_taxi, from cur_node (exclusive) to a node on the next taxiway (inclusive) *) 
Definition get_seg (cur_node : Node) (cur_taxi : V_list) (next_taxi : V_list) : option V_list :=
  match (chop_tail  (list_after_v cur_node cur_taxi) next_taxi), 
        (chop_tail  (list_after_v cur_node (rev cur_taxi)) next_taxi) with 
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

Fixpoint find_path (cur_node : Node) (cur_taxiway : V_list) (rest_taxiway_names : list V_list) : option V_list :=
    match rest_taxiway_names with
    | [] => Some []
    | next_taxiway::rest_taxiway =>
      match get_seg cur_node cur_taxiway next_taxiway with
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
(* ATC CMD: (start_node, end_node, taxiway_names). taxiway_names is a subset of every taxiway in the graph *)
Definition find_path_wrapper (start_node : Vertex) (end_node : Vertex) (taxiway_names : list V_list) : option V_list :=
  match taxiway_names with
  | [] => None
  | fst_taxiway::rest_taxiways =>
    (* create a dummy taxiway in the end *)
    match find_path start_node fst_taxiway (rest_taxiways ++ [[end_node;end_node]]) with
    | None => None
    | Some res => Some (start_node::res)
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







Definition _Node_list : Type := list Node.
Definition Edge_list : Type := list Edge.
Inductive Node_list : Type :=
  | Some (n : Node_list)
  | None.

Notation "{ x }" := (Indexing x). (* where x is an edge*)
(* '~' defines an equivalence relation *)
(* Notation " x ~ y " :=  eq_nat (indexing x) (indexing y).*) (* where x,y are edges*)

Check G_vertex
Definition Adjacency_map : Type :=
  Vertex -> list (Vertex * string).


Definition add_edges(g : Graph) (vs : V_set) (am :  Adjacency_map) : Graph :=
  match vs with
  | [] => g
  | v::l => G_edge vs 

(* try to write out is_valid_indexing from adjacency_list *)
(* for now does not check the nodes appears in the value field is a subset of nodes in the key *)
Fixpoint is_valid_indexing_alter (AL : adjacency_list) : Prop :=
  exists ent1, ent2 : Vertex * (list Vertex * nat)


(* input to this algorithm is a GV_list and adjacency_list, where the former  
   is to ensure termination *)
(*is this function infinite?*)
(*abr. as AL *)
Definition adjacency_list : Type :=
  list Vertex * (list Vertex * nat).

 (*maps a node to adjacent nodes, along with the pathwaynames that connect them*)
(* '*' return the product type *) 

(*Definition gen_graph (AL : adjacency_list): Graph *)

(*nat is the index of taxiway. indexing models giving name to taxiway names*)
(* return the number of edges that has taxiway_name name attached to it *)
Fixpoint taxiway_degree (z : Node) (taxiway : nat) (edges : Edge_list) (indexing : Edge -> nat) : nat :=
  match edges with
  | nil => 0
  | e::l => if In z e /\ (eq_nat {e}  taxiway)(* if z is an end point of edge e*) then S (taxiway_degree z nat l indexing)
                else (taxiway_degree z nat l indexing)
  end.


(*input: all edge in the graph, indexing function that represents taxiway names*)
(* SPEC of the input. there are two distinct edges x, y in the graph*)
Definition is_valid_indexing (g : Graph) (indexing : Edge -> nat)  : Prop :=
  match g with 
  | Graph nodes edges => 
  forall taxiway, exists g -> In g Graph -> {g} = taxiway -> (* For any taxiway in the graph, there existss    *)
  exists x, exists y,                                        (* distinct nodes x, y in the graph s.t.,         *)
  x != y -> In x nodes -> In y nodes ->                      (* x, y are end points of taxiway, and            *)                              
    (taxiway_degree x taxiway edges indexing) = 1 /\     
    (taxiway_degree y taxiway edges indexing) = 1 /\                       
    forall z, In z nodes -> z!=x -> z!=y ->                  (* for other nodes z, the number of taxiways that,  
                                                                has name _taxiway_ and are attached to z,      *)
      (taxiway_degree z taxiway edges indexing) = 0 \/       (* is either 0                                    *)
      (taxiway_degree z taxiway edges indexing) = 2.         (* or 2.                                          *)
end.

(*find all neighbors of n on the taxiway taxi_way, there should be at most two nodes*)
Definition get_neighbors (n : Node) (taxi_way : nat) (g : graph) : Node_list:=
  Admitted.


(*return true if n is on taxiway*)
Definition is_on_taxiway (n:Node) (taxiway : nat) (g:graph) : bool :=
    Admitted.









