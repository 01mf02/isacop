open Fof_parse;;
open Cnf;;
open Fof;;
open Features;;
open Arglean;;

let db = Hashtbl.create 10017;;
(* Each DB entry is a hashtable of discrimination trees, which keep:
     (lit-arguments, rest-clause, vars, contrapositive), (tfreq, sfreq)
        (term list * lit list    * int * int) * (float * (float * float) Im.t   *)


(* Some counters *)
let infer = ref 0;;
let depth = ref 0;;
let depthinfer = ref 0;;

let eq (sub, off) l1 l2 = eq_lit sub l1 l2;;

let unify (sub, off) l1 l2 = try Some (unify_lit sub l1 l2, off) with Unify -> None;;

let unify_rename (s, off) args1 (args2, rest, vars, _) =
  try Some(if vars = 0 then ((unify_list s args1 args2, off), rest) else
    let s, rest = unify_rename_subst off args1 args2 s rest in ((s, off + vars), rest))
  with Unify -> None;;

(* print_clause (fst sub) (lit1 :: rest); print_string "\t\t"; print_clause (fst sub) (List.rev path); print_char '\n'; *)

type proof = Lem of lit | Pat of lit | Res of (lit * lit list * lit list * int);;
exception Solved of (int list * proof) list

let te_num, pf_no, cn_no, cn_pf_no =
  if not !do_nbayes then 1, Hashtbl.create 1, Hashtbl.create 1, Hashtbl.create 1 else try
  let ic = open_in !datai in
  let te_num = ((input_value ic) : int) in
  let pf_no = ((input_value ic) : ((int * term list), float) Hashtbl.t) in
  let cn_no = ((input_value ic) : (int, int) Hashtbl.t) in
  let cn_pf_no = ((input_value ic) : (int, (float * float) Fm.t) Hashtbl.t) in
  close_in ic;
  te_num, pf_no, cn_no, cn_pf_no
with
| Sys_error _ -> 1, Hashtbl.create 1, Hashtbl.create 1, Hashtbl.create 1
| _ -> failwith  ("Error reading " ^ !datai ^ " file");;

let relevance fea (x, (tfreq, sfreq)) =
  let add_feat f (w, idf) (res, sfh) =
    try let (sf, _) = Fm.find f sfh in (res +. idf *. log (!posweight *. sf /. tfreq), Fm.remove f sfh)
    with Not_found -> (res +. idf *. !negweight, sfh) in
  let (res, sfh) = Fm.fold add_feat fea (!initwei *. log tfreq, sfreq) in
  let fold_sfh f (no, idf) sow = sow +. idf *. log (1. -. no /. (tfreq +. 1.)) in
  (x, res +. !invwei *. Fm.fold fold_sfh sfh 0.)
;;

let idf f = log (float_of_int te_num) -. log (try Hashtbl.find pf_no f with Not_found -> 0.);;
let relevancel pat = function
    [] -> []
  | [(x, _)] -> [(x, singlew)]
  | l ->
         let fea = path_features (List.map (fun (a,b) -> Cnf.Atom (a,b)) pat) in
         let fea = Fm.mapi (fun k v -> (idf k, v)) fea in
         let l2 = List.rev_map (relevance fea) l in
         let l3 = (List.stable_sort (fun (_, a) (_, b) -> compare b a) l2) in
         let l3h = List.hd l3 in
         let l3t = List.tl l3 in
(*         Format.printf "%% %s\n" (String.concat "," (List.map (fun (_, x) -> string_of_float x) l3));*)
(*         List.map (fun (xx, _) -> (xx, 100)) l3*)
(*         (l3h, 1) :: (List.map (fun x -> (x, 100)) l3t)*)
         (fst l3h, optw) :: (List.map (fun (x, _) -> (x, nonoptw)) l3t);;

let relevancel pat l = if !do_nbayes then relevancel pat l else List.map (fun (x, _) -> (x, nonoptw)) l;;

let print_nclause (subst, _) clause = print_clause clause;;
let print_clause (subst, _) clause = print_clause (List.map (inst_lit subst) clause);;

let update_features sf tm =
  let sf =
    if !weaken_feature = 0. then Fm.empty else
    if !weaken_feature = 1. then sf else
    Fm.map (fun (w, idf) -> w *. !weaken_feature, idf) sf in
  let fea = featuresp Fm.empty tm in
  Fm.fold (fun f _ sf ->
    try let (_, idf) = Fm.find f sf in Fm.add f (1., idf) sf
    with Not_found -> Fm.add f (1., idf f) sf) fea sf;;

let rec prove sub hist alt (todo, prf) = function
  | [] -> todo (sub, alt, prf)
  | (lit1 :: rest as cl) ->
     let (path, fea, lem, lim) = hist in
     (*  print_clause sub (lit1 :: rest); Format.print_string "\t\t"; print_clause sub (List.rev path); Format.print_char '\n';
     print_nclause sub (lit1 :: rest); Format.print_string "\t\t"; print_nclause sub (List.rev path); Format.print_char '\n';*)
     if (List.exists (fun x -> List.exists (eq sub x) path)) cl then alt () else
     if List.exists (eq sub lit1) lem then prove sub hist (if cut1 then alt else (fun () -> reduce sub lit1 rest hist alt (todo, prf) (negate lit1) path)) (todo, (fst sub, Lem lit1) :: prf) rest else
     reduce sub lit1 rest hist alt (todo, prf) (negate lit1) path

and reduce sub lit1 rest ((path,fea,lem,lim) as hist) alt (todo, prf) neglit = function
  | plit :: pt -> (match unify sub neglit plit with
    | Some sub2 -> prove sub2 hist (if !cut2 then alt else (fun () -> reduce sub lit1 rest hist alt (todo, prf) neglit pt)) (todo, (fst sub, Pat lit1) :: prf) rest
    | None -> reduce sub lit1 rest hist alt (todo, prf) neglit pt)
  | [] ->
     let nfea = (*if !upd_fea then update_features fea lit1 else*) fea in
      let hist = path, nfea, lem, lim in
      let dbs = try
        let dbe = Hashtbl.find db (fst neglit) in
        if !use_dtree then Dtree.trace_unifs (fst sub) (snd dbe) (snd neglit)
        else fst dbe with Not_found -> [] in
      extend sub lit1 rest hist alt (todo, prf) (relevancel (lit1 :: path) dbs)

and extend sub lit1 rest ((path, fea, lem, lim) as hist) alt (todo, prf) = function
  | (((_,_,vars,hsh) as eh), chwei) :: et -> (match if lim <= 0 && vars > 0 then None else unify_rename sub (snd lit1) eh with
    | Some (sub2, cla1) ->
      let ntodo (sub, nalt, prf) = prove sub (path, fea, lit1 :: lem, lim) (if !cut3 then alt else nalt) (todo, prf) rest in
      infer := !infer + 1; prove sub2 (lit1 :: path, fea, lem, lim - !chwei) (fun () -> extend sub lit1 rest hist alt (todo, prf) et) (ntodo, (fst sub, Res (lit1, path, lem, hsh)) :: prf) cla1
    | None -> extend sub lit1 rest hist alt (todo, prf) et)
  | [] -> alt ()

let prove lim = prove (empty_sub, 0) ([], Fm.empty, [], lim) (fun () -> ()) ((fun (_,_,prf) -> raise (Solved prf)), []) [(hash,[])];;

let rec iter_rest acc fnctn = function
  [] -> ()
| h :: t -> fnctn h (List.filter (fun x -> x <> (-hash, []))
             (List.rev_append acc t)); iter_rest (h :: acc) fnctn t;;

let axioms2db all_fea axs =
  let predb = Hashtbl.create 100 in
  let cl2predb cl =
    let max_var = 1 + List.fold_left (fun sf (_, t) -> List.fold_left max_var sf t) (-1) cl in
    let cl = if not !conj && List.for_all (fun (p, _) -> p < 0) cl &&
      not (List.mem (-hash, []) cl) then (-hash, []) :: cl else cl in
    let contr_hash lit rest = contr_number (string_of_contr lit rest) in
    iter_rest [] (fun (p,tl) rest -> Hashtbl.add predb p
      (tl, rest, max_var, contr_hash (p, tl) rest)) (List.rev cl) in
  List.iter cl2predb axs;
  Hashtbl.clear db;
  let keys = Hashtbl.fold (fun k _ sf -> Im.add k () sf) predb Im.empty in
  let cl2db k _ =
    let v = List.rev (Hashtbl.find_all predb k) in
    let gl_relevant (k,l) _ = Fm.mem (k,l) all_fea || Fm.mem (-k,l) all_fea in
    let data c = ((try float_of_int (Hashtbl.find cn_no c) with Not_found -> 0.),
      try Fm.filter gl_relevant (Hashtbl.find cn_pf_no c) with Not_found -> Fm.empty) in
    let vd = List.map (fun ((_, _, _, c) as e) -> (e, data c)) v in
    let dt = if !use_dtree then Dtree.update_jl (List.fold_left (fun sf (((a, _, _, _), d) as e) -> Dtree.insert e sf a) Dtree.empty_dt vd) else Dtree.empty_dt in
    Hashtbl.add db k (vd, dt);
  in
  Im.iter cl2db keys
;;

let order_setify l =
  let h = Hashtbl.create (List.length l * 2) in
  List.rev (List.fold_left (fun sf x -> if Hashtbl.mem h x then sf else (Hashtbl.add h x (); x :: sf)) [] l);;

let leancop file =
  let mat = file_mat true !def true file in
  (* Hidden in union2 in leancop *)
  let mat = List.filter (fun cl -> List.for_all (fun (p1,a1) -> List.for_all (fun (p2,a2) -> p1 <> -p2 || a1 <> a2) cl) cl) mat in
  let mat = List.map (fun l -> List.rev (order_setify (List.rev l))) mat in
  let all_fea = List.fold_left (List.fold_left featuresl) Fm.empty ([(hash, [])] :: mat) in
  (*List.iter (fun x -> Format.print_char '%'; print_clause ([], 0) x; Format.print_char '\n') mat; Format.printf "%%--\n%!";*)
  axioms2db all_fea mat;
  (*maxsec 10*) (fun () -> for i = 0 to 1000 do depth := i; depthinfer := !infer; prove (!nonoptw * i) done) ();
  (*cut3 := false;
  (*maxsec 10*) (fun () -> for i = 0 to 1000 do depth := i; prove i done) ();
  cut2 := false;
  (*maxsec 10*) (fun () -> for i = 0 to 1000 do depth := i; prove i done) ();*)
  failwith "over 1000"
;;

exception Alarm;;
exception CleanExit;;
let alarm _ = raise Alarm;;
let cleanexit _ = raise CleanExit;;
Sys.signal Sys.sigint (Sys.Signal_handle cleanexit);;
Sys.signal Sys.sigterm (Sys.Signal_handle cleanexit);;
Sys.signal Sys.sigalrm (Sys.Signal_handle alarm);;
let maxsec i f a = ignore (Unix.alarm i); try f a; ignore (Unix.alarm 0); () with Alarm -> ();;
at_exit (fun () ->
Format.printf "%% Inf: %i Depth: %i DInf: %i\n" !infer !depth (!infer - !depthinfer));;

let print_solved_features pl =
  ignore (Sys.signal Sys.sigint Sys.Signal_ignore);
  ignore (Sys.signal Sys.sigterm Sys.Signal_ignore);
  ignore (Sys.signal Sys.sigalrm Sys.Signal_ignore);
  let rec f2f acc = function
    (s, Res (lit, path, lem, contr)) :: t -> f2f ((inst_lit s lit, List.map (inst_lit s) path, List.map (inst_lit s) lem, lit, path, lem, contr) :: acc) t
  | _ :: t -> f2f acc t
  | [] -> acc
  in
  let l = f2f [] pl in
  List.iter (fun (lit, path, lem, nlit, npath, nlem, contr) ->
    Format.print_string (Hashtbl.find no_contr contr); Format.print_string ", (";
    pp_print_lit Format.std_formatter lit; Format.print_string "), (";
    pp_iter Format.std_formatter pp_print_lit "," path; Format.print_string "), (";
    pp_iter Format.std_formatter pp_print_lit "," lem; Format.print_string "), (";
    pp_print_lit Format.std_formatter nlit; Format.print_string "), (";
    pp_iter Format.std_formatter pp_print_lit "," npath; Format.print_string "), (";
    pp_iter Format.std_formatter pp_print_lit "," nlem; Format.print_string ").\n") l;;

if !tosolve <> "" then try leancop !tosolve
  with Solved prf -> Format.printf "\n%% SZS status Theorem\n%!"; print_solved_features prf
     | Failure "over 1000" -> Format.printf "\n%% SZS status CounterSatisfiable\n%!"
     | Failure x -> Format.printf "\n%% SZS status Error\n%%%s\n%!" x
     | CleanExit -> Format.printf "\n%% SZS status Unknown\n%!"
     | Parsing.Parse_error -> Format.printf "\n%% SZS status Error\n%%Parse_error\n%!";;
