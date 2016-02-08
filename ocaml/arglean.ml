
(* LeanCoP params *)
let conj = ref true;; (* conjecture-directed: if false negative clauses have # added *)
let cut1 = true;;     (* cut after lemma step *)
let cut2 = ref true;; (* cut after path step *)
let cut3 = ref true;; (* cut after lit step *)
let def = ref true;;  (* do definitional CNF. More predicates, less clauses *)

let depthsec = ref 0;;

let speclist = [
  ("-noconj", Arg.Clear conj, "\t\tDisable conjecture-directed search");
  ("-nocut2", Arg.Clear cut2, "\t\tDisable cut after path step");
  ("-nocut3", Arg.Clear cut3, "\t\tDisable cut after lit step");
  ("-nodef", Arg.Clear def, "\t\tDisable definitional CNF");
  ("-depthsec", Arg.Set_int depthsec, "%i\t\tMaximum time in seconds to spend at a depth (default: unlimited)");
];;
