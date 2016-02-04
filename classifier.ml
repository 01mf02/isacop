open Utils

module Classifier (Feature : Map.OrderedType) = struct

module Fm = Map.Make(Feature)

type 'a t =
    (* number of training examples *)
  { mutable te_num : int
    (* number of times feature occurs in the training examples *)
  ; ftr_no : (Feature.t, float) Hashtbl.t
    (* number of times label occurs in the training examples (tfreq) *)
  ; lbl_no : ('a, int) Hashtbl.t
    (* how often did label occur together with feature (sfreq) *)
  ; lbl_ftr_no : ('a, float Fm.t) Hashtbl.t
    (* feature IDF *)
  ; mutable ftr_idf : float Fm.t
  }

let empty () : 'a t =
  { te_num = 1
  ; ftr_no = Hashtbl.create 1
  ; lbl_no = Hashtbl.create 1
  ; lbl_ftr_no = Hashtbl.create 1
  ; ftr_idf = Fm.empty
  }


(* ****************************************************************************)
(* Map helper functions *)

let list_of_map m = Fm.fold (fun k v vs -> (k, v) :: vs) m []

let map_map1 m k f x = Fm.add k (try f x (Fm.find k m) with Not_found -> x) m

let freq_map_of_list m l =
  List.fold_left (fun acc ftr -> map_map1 acc ftr (+.) 1.) m l

let maps_partition m1 m2 =
  Fm.fold (fun k1 v1 (l, i, r) ->
    try let v2 = Fm.find k1 m2 in (l, Fm.add k1 (v1, v2) i, Fm.remove k1 r)
    with Not_found -> (Fm.add k1 v1 l, i, r)) m1 (Fm.empty, Fm.empty, m2)


(* ****************************************************************************)
(* I/O *)

let load fp = with_in fp (fun c ->
  let te_num     = input_value c in
  let ftr_no     = input_value c in
  let lbl_no     = input_value c in
  let lbl_ftr_no = input_value c in
  let ftr_idf    = input_value c in
  Printf.printf "Read: %i training examples\n%!" te_num;
  Printf.printf "Read: %i features\n%!" (Hashtbl.length ftr_no);
  Printf.printf "Read: %i labels\n%!" (Hashtbl.length lbl_no);
  { te_num = te_num; ftr_no = ftr_no; lbl_no = lbl_no; lbl_ftr_no = lbl_ftr_no; ftr_idf = ftr_idf } )

let try_load fp = try load fp with 
  | Sys_error e -> empty () (* don't complain if file not found *)
  | _ -> failwith  ("Error reading " ^ fp ^ " file")

let write d fp = with_out fp (fun c ->
  output_value c d.te_num;
  output_value c d.ftr_no;
  output_value c d.lbl_no;
  output_value c d.lbl_ftr_no;
  output_value c d.ftr_idf;
  Printf.printf "Wrote %s with %i training examples\n%!" fp d.te_num)


(* ****************************************************************************)
(* obtain learned data *)

let get_idf d ftr = try Fm.find ftr d.ftr_idf with Not_found -> 0.

let get_lbl_data d lbl =
  try (Hashtbl.find d.lbl_no lbl, Hashtbl.find d.lbl_ftr_no lbl)
  with Not_found -> (0, Fm.empty)


(* ****************************************************************************)
(* update learned data *)

let update_ftr_no d ftrs = Fm.iter (fun k w -> hashtbl_map1 d.ftr_no k (+.) w) ftrs

let update_lbl_no d lbl = hashtbl_map1 d.lbl_no lbl (+) 1

let update_lbl_ftr_no d lbl ftrs =
  let fold_fun ftr w fm =
    map_map1 fm ftr (fun w1 w2 -> (w1 +. w2)) w in
  hashtbl_map0 d.lbl_ftr_no lbl (Fm.fold fold_fun ftrs) Fm.empty

let calc_idf d ftr =
  log (float_of_int d.te_num) -. log (hashtbl_find_default d.ftr_no ftr 0.)

let update_ftr_idf d =
  let ftrs = Utils.hashtbl_keys d.ftr_no in
  d.ftr_idf <- List.fold_left (fun m ftr -> Fm.add ftr (calc_idf d ftr) m) Fm.empty ftrs

let add_training_ex d (ftrs, lbl) =
  d.te_num <- d.te_num + 1;
  update_ftr_no d ftrs;
  update_lbl_no d lbl;
  update_lbl_ftr_no d lbl ftrs

let add_training_exs d l =
  List.iter (add_training_ex d) l;
  Printf.printf "pf, cn and cn_pf frequencies updated\n%!";
  update_ftr_idf d;
  Printf.printf "IDF information calculated\n%!"


(* ****************************************************************************)
(* Naive Bayes relevance *)

let relevance idf fl fi fr ftrs sfreq =
  let (l, i, r) = maps_partition ftrs sfreq in
  let sum f m = float_sum (List.map (fun (ftr, v) -> f (idf ftr) v) (list_of_map m)) in
  sum fl l +. sum fi i +. sum fr r


end

