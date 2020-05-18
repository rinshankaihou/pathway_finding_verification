(*
  A print-help function for the example.
  We only support Ann Arbor case in Example.v
  First run extraction.v in Extraction.v to extract path_finding_example.ml, then run this file directly
*)



#use "path_finding_example.ml"

(* maps to string *)
 let ann_arbor_v2s_ext = function
  | O -> "input"
  | S O -> "AA3"
  | S (S O) -> "AB"
  | S (S (S O)) -> "AC"
  | S (S (S (S O))) -> "AA1"
  | S (S (S (S (S O)))) -> "Ch"
  | S (S (S (S (S (S O))))) -> "BC"
  | S (S (S (S (S (S (S O)))))) -> "A3r"
  | S (S (S (S (S (S (S (S O))))))) -> "A2r"
  | S (S (S (S (S (S (S (S (S O)))))))) -> "A1r"
  | _ -> "Error Vertex";;

let ann_arbor_t2s_ext = function
  | String ((Ascii (True, False, False, False, False, False, True, False)),
  EmptyString) -> "A"
  | String ((Ascii (False, True, False, False, False, False, True, False)),
  EmptyString) -> "B"
  | String ((Ascii (True, True, False, False, False, False, True, False)),
  EmptyString) -> "C"
  | String ((Ascii (True, False, False, False, False, False, True, False)),
  (String ((Ascii (True, False, False, False, True, True, False, False)),
  EmptyString))) -> "A1"
  | String ((Ascii (True, False, False, False, False, False, True, False)),
  (String ((Ascii (False, True, False, False, True, True, False, False)),
  EmptyString))) -> "A2"
  | String ((Ascii (True, False, False, False, False, False, True, False)),
  (String ((Ascii (True, True, False, False, True, True, False, False)),
  EmptyString))) -> "A3"
  | _ -> "Error Taxiway";;


(* a helper function *)
let rec string_list_append_ext = function
  | [] -> ""
  | h::t -> h ^ (string_list_append_ext t)

(* convert an edge to string *)
let edge_to_string_ext f g e = 
  string_list_append_ext ["(from "; f (snd (fst (e))); " to "; f (fst (fst e)); " on taxiway "; g (snd e); ")"]

(* a tool function *)
let rec map_ext f le = 
  match le with 
  | Nil -> []
  | Cons (h, t) -> (f h) :: (map_ext f t);;

(* map the path to ocaml list of string *)
let rec ann_arbor_e2s_ext le = map_ext (edge_to_string_ext ann_arbor_v2s_ext ann_arbor_t2s_ext) le;;

(* map the result to list of list string in ocaml *)
let example_result_string_ext = 
  match path_finding_example with
  | None -> [["No path found"]]
  | Some s -> map_ext ann_arbor_e2s_ext s
  

(* print function *)
let rec list_string_print_aux ls = 
  match ls with
  | [] -> print_string ""
  | [a] -> print_string a
  | h::t -> (print_string h; print_endline "; "; list_string_print_aux t);;

let list_string_print ls = 
  print_string "[";
  list_string_print_aux ls;
  print_endline "]";;


let rec print_path_edge le = 
  match le with
    | [] -> ()
    | [s] -> list_string_print s
    | h::t -> list_string_print h; print_path_edge t;; 

(* finally... print the result *)
let () = print_path_edge example_result_string_ext