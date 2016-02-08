open Cnf
open Arglean
open Fof
open Utils


(* (lit-arguments, rest-clause, vars) *)
type contrapositive = (term list * lit list * int)

(* for every predicate, store list of possible contrapositives *)
let db : contrapositive list array = Array.make 10000 []

let int_of_nat n = if n mod 2 = 0 then n / 2 else - (n+1)/2
let nat_of_int i = if i >= 0 then 2*i else -(2*i + 1)


let hash_lit = (-hash, [])

let iter_rest_nohash acc f =
  iter_rest acc (fun h rest -> f h (List.filter ((<>) hash_lit) rest))

let clause_max_var cl =
  1 + List.fold_left (fun sf (_, t) -> List.fold_left max_var sf t) (-1) cl

let clause_prefix_hash cl =
  if not !conj && List.for_all (fun (p, _) -> p < 0) cl &&
     not (List.mem hash_lit cl) then hash_lit :: cl else cl

let contrapositive2db max_var (p,tl) rest =
  let n = nat_of_int p in
  Array.set db n ((tl, rest, max_var) :: Array.get db n)

let cl2db cl =
  let max_var = clause_max_var cl in
  let cl = clause_prefix_hash cl in
  iter_rest_nohash [] (contrapositive2db max_var) cl

let axioms2db = List.iter cl2db

let db_entries neglit = Array.get db (nat_of_int neglit)
