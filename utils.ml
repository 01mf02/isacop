(******************************************************************************)
(* list routines *)

let float_sum = List.fold_left (+.) 0.

(* eliminate duplicates in a list *)
let nub l =
  let h = Hashtbl.create (List.length l * 2) in
  List.rev (List.fold_left (fun sf x -> if Hashtbl.mem h x then sf else (Hashtbl.add h x (); x :: sf)) [] l)

(* run function for every element and all other elements of the list *)
let rec iter_rest acc f = function
  [] -> ()
| h :: t -> f h (List.rev_append acc t); iter_rest (h :: acc) f t;;


(******************************************************************************)
(* hash table *)

let hashtbl_keys tbl = Hashtbl.fold (fun k _ ks -> k :: ks) tbl []

let hashtbl_find_default tbl k x = try Hashtbl.find tbl k with Not_found -> x

let hashtbl_map tbl k f =
  Hashtbl.replace tbl k (f (Hashtbl.find tbl k))

let hashtbl_map0 tbl k f x =
  Hashtbl.replace tbl k (f (try Hashtbl.find tbl k with Not_found -> x))

let hashtbl_map1 tbl k f x =
  Hashtbl.replace tbl k (try f x (Hashtbl.find tbl k) with Not_found -> x)

(* create hash table storing elements and number of occurrences in list *)
let hashtbl_from_list tbl = List.iter (fun x -> hashtbl_map1 tbl x (+) 1)


(******************************************************************************)
(* file routines *)

let with_in fp f = let c = open_in fp in let i = f c in close_in c; i

let with_out fp f = let c = open_out fp in f c; close_out c
