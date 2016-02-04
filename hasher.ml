open Cnf
open Fof
open Fof_parse
open Features
open Classifier

let speclist = [
  ("-feanosubst", Arg.Clear fea_undersubst, "\t\tWhen computing features do not descend in substitution");
  ("-feanoconst", Arg.Clear fea_constpred, "\t\tDo not include constant features");
  ("-feasubterm", Arg.Set fea_subterm, "\t\tInclude subterm features");
  ("-feaweaken", Arg.Set_float Features.weaken_feature, "\t\tFactor to multiply next feature on path (0.0--1.0) default 0.8");
]

module FClassifier = Classifier (FeatureOrdered)

let training_ex (co, lit, pat, lem, nlit, npat, nlem) =
  let lit, pat, lem = if !fea_undersubst then lit, pat, lem else nlit, npat, nlem in
  let feats = path_features (lit :: pat) in
  let cn = md5s (string_of_form (rename_unbound co)) in
  (feats, cn)

let _ =
  Arg.parse speclist (fun _ -> ()) "Usage: ./hasher  [options]\nAvailable options are:";

  (* read new, unhashed data *)
  let l = Fof_lexer.data_file "data" in
  Printf.printf "Read data\n%!";

  let classifier = FClassifier.try_load "datai" in
  FClassifier.add_training_exs classifier (List.map training_ex l);
  FClassifier.write classifier "datai";
