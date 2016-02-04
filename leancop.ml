open Fof_parse
open Cnf
open Fof
open Arglean
open Database

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
exception Solved of (int list * proof) list;;


let print_nclause (subst, _) clause = print_clause clause;;
let print_clause (subst, _) clause = print_clause (List.map (inst_lit subst) clause);;







let rec prove sub ((path, lem, lim) as hist) alt (todo, prf) = function
  | [] -> todo (sub, alt, prf)
  | (lit1 :: rest as cl) ->
     if List.exists (fun x -> List.exists (eq sub x) path) cl then alt () else
     if List.exists (eq sub lit1) lem then prove sub hist
       (if cut1 then alt else (fun () -> reduce sub lit1 rest hist alt (todo, prf) (negate lit1) path)) (todo, (fst sub, Lem lit1) :: prf) rest
     else reduce sub lit1 rest hist alt (todo, prf) (negate lit1) path

and reduce sub lit1 rest ((path,lem,lim) as hist) alt (todo, prf) neglit = function
  | plit :: pt -> (match unify sub neglit plit with
    | Some sub2 -> prove sub2 hist (if !cut2 then alt else (fun () -> reduce sub lit1 rest hist alt (todo, prf) neglit pt)) (todo, (fst sub, Pat lit1) :: prf) rest
    | None -> reduce sub lit1 rest hist alt (todo, prf) neglit pt)
  | [] ->
      let hist = path, lem, lim in
      let dbs = Database.db_entries sub neglit in
      extend sub lit1 rest hist alt (todo, prf) dbs

and extend sub lit1 rest ((path, lem, lim) as hist) alt (todo, prf) = function
  | ((_,_,vars,hsh) as eh) :: et ->
    (match if lim <= 0 && vars > 0 then None else unify_rename sub (snd lit1) eh with
    | Some (sub2, cla1) ->
      let ntodo (sub, nalt, prf) = prove sub (path, lit1 :: lem, lim) (if !cut3 then alt else nalt) (todo, prf) rest in
      infer := !infer + 1; prove sub2 (lit1 :: path, lem, lim - 1) (fun () -> extend sub lit1 rest hist alt (todo, prf) et) (ntodo, (fst sub, Res (lit1, path, lem, hsh)) :: prf) cla1
    | None -> extend sub lit1 rest hist alt (todo, prf) et)
  | [] -> alt ()

let prove lim = prove
  (empty_sub, 0)
  ([], [], lim)
  (fun () -> ())
  ((fun (_,_,prf) -> raise (Solved prf)), [])
  [(hash,[])]


exception Alarm;;
exception CleanExit;;

let setup_signals () =
  ignore (Sys.signal Sys.sigint (Sys.Signal_handle (fun _ -> raise CleanExit)));
  ignore (Sys.signal Sys.sigterm (Sys.Signal_handle (fun _ -> raise CleanExit)));
  ignore (Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Alarm)))

(* run f a for maximally i seconds *)
let maxsec i f a =
  ignore (Unix.alarm i); try f a; ignore (Unix.alarm 0) with Alarm -> ()

(* true if the clause does not contain instances of Px and ~Px *)
let nontriv_clause cl =
  List.for_all (fun (p1,a1) -> List.for_all (fun (p2,a2) ->
    p1 <> -p2 || a1 <> a2) cl) cl

let simplify_matrix mat = List.map Utils.nub (List.filter nontriv_clause mat)

let leancop file =
  let mat = simplify_matrix (file_mat true !def true file) in
  Database.axioms2db mat;
  while !depth < 1000 do
    depthinfer := !infer;
    if !depthsec = 0 then prove (!depth)
    else maxsec !depthsec (fun () -> prove (!depth)) ();
    depth := !depth + 1
  done;
  (*cut3 := false;
  (*maxsec 10*) (fun () -> for i = 0 to 1000 do depth := i; prove i done) ();
  cut2 := false;
  (*maxsec 10*) (fun () -> for i = 0 to 1000 do depth := i; prove i done) ();*)
  failwith "over 1000"
;;


let print_res (lit, path, lem, nlit, npath, nlem, contr) =
  Format.print_string (Hashtbl.find no_contr contr); Format.print_string ", (";
  pp_print_lit Format.std_formatter lit; Format.print_string "), (";
  pp_iter Format.std_formatter pp_print_lit "," path; Format.print_string "), (";
  pp_iter Format.std_formatter pp_print_lit "," lem; Format.print_string "), (";
  pp_print_lit Format.std_formatter nlit; Format.print_string "), (";
  pp_iter Format.std_formatter pp_print_lit "," npath; Format.print_string "), (";
  pp_iter Format.std_formatter pp_print_lit "," nlem; Format.print_string ").\n"

let rec res_of_proof acc = function
  (s, Res (lit, path, lem, contr)) :: tl ->
   res_of_proof ((inst_lit s lit, List.map (inst_lit s) path, List.map (inst_lit s) lem,
     lit, path, lem, contr) :: acc) tl
| _ :: tl -> res_of_proof acc tl
| [] -> acc

let print_solved_features pl = List.iter print_res (res_of_proof [] pl)

let print_stats () =
  Format.printf "%% Inf: %i Depth: %i DInf: %i\n" !infer !depth (!infer - !depthinfer)

let print_status s = print_endline ("% SZS status " ^ s)
let print_error e = print_status "Error"; print_endline ("%" ^ e)

let print_result = function
  Solved prf -> print_status "Theorem"; print_solved_features prf
| Failure "over 1000" -> print_status "CounterSatisfiable"
| CleanExit -> print_status "Unknown"
| Failure x -> print_error x
| Parsing.Parse_error -> print_error "Parse_error"
| e -> raise e

let _ =
  at_exit print_stats;
  setup_signals ();

  let tosolve = ref "" in
  Arg.parse speclist (fun s -> tosolve := s)
    "Usage: ./leancop [options] <file.p>\nAvailable options are:";

  if !tosolve <> "" then try leancop !tosolve
  with e -> print_newline (); print_result e
