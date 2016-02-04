let upd_fea = ref false;; (* Add features of the current literal to the cached features of the path *)
let do_nbayes = ref false;; (* Call nbayes to sort by relevance and set other weights *)
let use_dtree = ref false;; (* use discrimination tree for prefiltering of branches *)

(* LeanCoP params *)
let conj = ref true;;     (* conjecture-directed: if false negative clauses have # added *)
let cut1 = true;;     (* cut after lemma step *)
let cut2 = ref true;; (* cut after path step *)
let cut3 = ref true;; (* cut after lit step *)
let def = ref true;;      (* do definitional CNF. More predicates, less clauses *)

(* Weight of steps. 100 for all 3 is like leanCoP. *)
let optw = ref 1;;        (* weight of an optimal step *)
let singlew = ref 1;;     (* weight of an only-choice step *)
let nonoptw = ref 1;;     (* weight of a non-optimal step *)

(* NBayes params *)
let initwei = ref 2.0;;    (* initial weight of previous example number *)
let posweight = ref 2.0;;  (* weight for features shared with conjecture *)
let negweight = ref (-6.0);; (* weight for conjecture features never shared with contra *)
let invwei = ref (-0.05);;    (* weight for contra features not in conjecture *)

let depthsec = ref 0;;

(* datai file - training data *)
let datai = ref "datai";;

let speclist = [
  ("-learn", Arg.Unit (fun _ -> upd_fea := true; do_nbayes := true), "\t\tEnable learning");
  ("-feanosubst", Arg.Clear Features.fea_undersubst, "\t\tWhen computing features do not descend in substitution");
  ("-feanoconst", Arg.Clear Features.fea_constpred, "\t\tDo not include constant features");
  ("-feasubterm", Arg.Set Features.fea_subterm, "\t\tInclude subterm features");
  ("-feaweaken", Arg.Set_float Features.weaken_feature, "\t\tFactor to multiply next feature on path (0.0--1.0) default 0.8");
  ("-dtree", Arg.Set use_dtree, "\t\tEnable discrimination tree");
  ("-noconj", Arg.Clear conj, "\t\tDisable conjecture-directed search");
  ("-nocut2", Arg.Clear cut2, "\t\tDisable cut after path step");
  ("-nocut3", Arg.Clear cut3, "\t\tDisable cut after lit step");
  ("-nodef", Arg.Clear def, "\t\tDisable definitional CNF");
  ("-nb-initwei", Arg.Set_float initwei, "%f\tSet NB previous uses weight (default: 2.0)");
  ("-nb-poswei", Arg.Set_float posweight, "%f\t\tSet NB cooccurring feature weight (default: 2.0)");
  ("-nb-negwei", Arg.Set_float negweight, "%f\t\tSet NB conj-only feature weight (default: -6.0)");
  ("-nb-invwei", Arg.Set_float invwei, "%f\t\tSet NB contra-only feature weight (default: -0.05)");
  ("-step", Arg.Set_int nonoptw, "%i\t\tSet step granularity (default: 1)");
  ("-step-single", Arg.Set_int singlew, "%i\tSet single-step subtract (default: 1)");
  ("-step-opt", Arg.Set_int optw, "%i\t\tSet chosen-step subtract (default: 1)");
  ("-depthsec", Arg.Set_int depthsec, "%i\t\tMaximum time in seconds to spend at a depth (default: unlimited)");
  ("-datai", Arg.Set_string datai, "%s\t\tSet the training data file (default: datai)")
];;
