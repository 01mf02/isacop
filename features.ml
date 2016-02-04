open Cnf;;
open Fof;;
open Fof_parse;;

let fea_undersubst = ref true;;  (* Check variables in the substitution when computing features *)
let fea_constpred  = ref true;;  (* Include consts and preds when computing features *)
let fea_subterm    = ref false;; (* Include subterms in computed features *)
(* A feature in the path that is not in the current literal is multiplied by
   the following decay factor for each step away from current lit *)
let weaken_feature = ref 0.8;;

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

let str_of_fea n = try Hashtbl.find no_cnst n with Not_found -> "~" ^ Hashtbl.find no_cnst (-n);;

type feature = (int * term list)
module FeatureOrdered = struct type t = (int * term list) let compare = compare end

module Fm = Map.Make(FeatureOrdered);;

(* set all variable indices to zero *)
let rec normalize = function
  | V n -> V 0
  | A (p, l) -> A (p, List.map normalize l);;

(* features of a proposition (or a function application) *)
let rec featuresp acc = function
  | (f, []) -> if !fea_constpred || !fea_subterm then Fm.add (f, []) () acc else acc
  | (f, l) ->
     let acc = List.fold_left featurest acc l in
     let acc = if !fea_constpred then Fm.add (f, []) () acc else acc in
     if !fea_subterm then Fm.add (f, List.map normalize l) () acc else acc
and featurest acc = function
  | V n -> if !fea_undersubst then (match subst.(n) with None -> acc | Some t -> featurest acc t) else acc
  | A (f, l) -> featuresp acc (f, l);;
let featuresl acc (p, l) = Fm.add (p, []) () (List.fold_left featurest acc l);;
let featurescl = List.fold_left featuresp Fm.empty;;

let de_form = function
  | Cnf.Neg (Cnf.Atom (n, l)) -> -n, l
  | Cnf.Atom (n, l) -> n, l
  | _ -> failwith "de_form";;

let path_features l =
  let weight = ref 1.0 in
  let fold_fun sf tm =
    let fea = featuresp Fm.empty (de_form tm) in
    let ret = Fm.fold (fun f _ sf ->
      Fm.add f (max !weight (try Fm.find f sf with Not_found -> 0.)) sf) fea sf in
    weight := !weight *. !weaken_feature;
    ret
  in
  if !weaken_feature > 0.0 then List.fold_left fold_fun Fm.empty l
  else try fold_fun Fm.empty (List.hd l) with _ -> Fm.empty;;
