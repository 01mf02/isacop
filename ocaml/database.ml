open Cnf
open Arglean
open Fof
open Utils


(* (lit-arguments, rest-clause, vars) *)
type contrapositive = (term list * lit list * int)

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
  iter_rest_nohash [] (fun (p,tl) rest -> Hashtbl.add predb p
    (tl, rest, max_var)) (List.rev cl)


let cl2db predb p =
  Hashtbl.add db p (List.rev (Hashtbl.find_all predb p))

let axioms2db axs =
  let predb = Hashtbl.create 100 in
  List.iter (cl2predb predb) axs;
  Hashtbl.clear db;
  List.iter (cl2db predb) (hashtbl_keys predb)

let db_entries sub neglit =
  try Hashtbl.find db (fst neglit) with Not_found -> []
