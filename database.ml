open Cnf
open Features
open Arglean
open Fof
open Utils

module FClassifier = Classifier.Classifier (FeatureOrdered)

(* (lit-arguments, rest-clause, vars, contrapositive hash) *)
type contrapositive = (term list * lit list * int * int)
(* contrapositive *)
type db_entry = contrapositive

(* for every predicate, store list of possible contrapositives *)
let db : (int, db_entry list * db_entry Dtree.dt) Hashtbl.t = Hashtbl.create 10017

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

let contrapositive_ml classifier feats (_, _, _, cn) =
  let goal_relevant (k,l) _ = Fm.mem (k,l) feats || Fm.mem (-k,l) feats in
  let (no, pf_no) = FClassifier.get_lbl_data classifier cn in
  (float_of_int no, Fm.filter goal_relevant pf_no)

let make_dtree cps =
  let insert_fun sf (((a, _, _, _), d) as e) = Dtree.insert e sf a in
  Dtree.update_jl (List.fold_left insert_fun Dtree.empty_dt cps)

let cl2db classifier predb feats p =
  let cps = List.rev (Hashtbl.find_all predb p) in
  let ml = List.map (fun c -> (c, contrapositive_ml classifier feats c)) cps in
  let dt = Dtree.empty_dt in
  Hashtbl.add db p (cps, dt)

let clauses_features = List.fold_left (List.fold_left featuresl) Fm.empty

let axioms2db classifier axs =
  let feats = clauses_features ([(hash, [])] :: axs) in
  let predb = Hashtbl.create 100 in
  List.iter (cl2predb predb) axs;
  Hashtbl.clear db;
  List.iter (cl2db classifier predb feats) (hashtbl_keys predb)

let db_entries sub neglit =
  try
    let dbe = Hashtbl.find db (fst neglit) in
    fst dbe
  with Not_found -> []
