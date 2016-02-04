open Cnf
open Arglean
open Fof
open Utils




(* contrapositive <-> number mappings *)
let contr_no = Hashtbl.create 100 and no_contr = Hashtbl.create 100;;
let rec find_free_contr n = if Hashtbl.mem no_contr n then find_free_contr (n + 1) else n;;

let contr_number name =
  try Hashtbl.find contr_no name with Not_found ->
    let cno = find_free_contr (md5s name) in
    Hashtbl.add contr_no name cno; Hashtbl.add no_contr cno name; cno;;
let neg_atom_of_lit ((p, l) as a) = if p > 0 then Neg (Atom a) else Atom (-p, l);;
let atom_of_lit ((p, l) as a) = if p > 0 then Atom a else Neg (Atom (-p, l));;
let string_of_contr lit rest =
  string_of_form (rename_unbound (List.fold_right (fun a b ->
    Disj (neg_atom_of_lit a, b)) rest (atom_of_lit lit)));;






(* (lit-arguments, rest-clause, vars, contrapositive hash) *)
type contrapositive = (term list * lit list * int * int)

(* for every predicate, store list of possible contrapositives *)
let db : (int, contrapositive list) Hashtbl.t = Hashtbl.create 10017

let hash_lit = (-hash, [])

let iter_rest_nohash acc f =
  iter_rest acc (fun h rest -> f h (List.filter ((<>) hash_lit) rest))

let clause_max_var cl =
  1 + List.fold_left (fun sf (_, t) -> List.fold_left max_var sf t) (-1) cl

let clause_prefix_hash cl =
  if not !conj && List.for_all (fun (p, _) -> p < 0) cl &&
     not (List.mem hash_lit cl) then hash_lit :: cl else cl

let cl2predb predb cl =
  let max_var = clause_max_var cl in
  let cl = clause_prefix_hash cl in
  let contr_hash lit rest = contr_number (string_of_contr lit rest) in
  iter_rest_nohash [] (fun (p,tl) rest -> Hashtbl.add predb p
    (tl, rest, max_var, contr_hash (p, tl) rest)) (List.rev cl)


let cl2db predb p =
  Hashtbl.add db p (List.rev (Hashtbl.find_all predb p))

let axioms2db axs =
  let predb = Hashtbl.create 100 in
  List.iter (cl2predb predb) axs;
  Hashtbl.clear db;
  List.iter (cl2db predb) (hashtbl_keys predb)

let db_entries sub neglit =
  try Hashtbl.find db (fst neglit) with Not_found -> []
