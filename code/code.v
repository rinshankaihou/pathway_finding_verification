From GraphBasics Require Export Graphs.
Require Import Coq.Lists.List.
From GraphBasics Require Export Vertices.


(* The definitions:
    Node
    Edge
    Node_list
    Edge_list *)

(* To do later. first touch fish *)

Print Vertex.
(* Inductive Vertex : Set :=  index : nat -> Vertex *)
Definition Node : Type := Vertex. (* alias *)
Print Edge.
Definition _Node_list : Type := list Node.
Definition Edge_list : Type := list Edge.
Inductive Node_list : Type :=
  | Some (n : Node_list)
  | None.
Definition Indexing : Type := Edge -> nat.
Notation "{ x }" := (Indexing x). (* where x is an edge*)
(* '~' defines an equivalence relation *)
(* Notation " x ~ y " :=  eq_nat (indexing x) (indexing y).*) (* where x,y are edges*)

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
  | e::l => if In z e /\ ({e} = nat)(* if z is an end point of edge e*) then S (taxiway_degree z nat l indexing)
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




