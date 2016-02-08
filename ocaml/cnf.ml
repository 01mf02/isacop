type term = V of int
          | A of int * term list;;
type lit = int * term list;;
type form = Atom of (int * term list)
          | Neg of form
          | Conj of form * form
          | Disj of form * form
          | Forall of int * form
          | Exists of int * form
          | Eqiv of form * form;;

exception Unify;;

let subst = Array.create 1000000 (None : term option);;
let sh = ref [];;
let rec restore_subst env =
  if not (!sh == env) then
    (subst.(List.hd !sh) <- None; sh := List.tl !sh; restore_subst env);;

(*let checked = Array.create 200000 false;;
let ch = ref [];;
let rec restore_checked = function
  | [] -> ch := []
  | h :: t -> checked.(h) <- false; restore_checked t;;*)

let rec istriv x = function
    V y -> (*if checked.(y) then false else*)
    y = x || (match subst.(y) with Some t -> (*if*) istriv x t (*then true else (checked.(y) <- true; ch := y :: !ch; false)*) | None -> false)
  | A (f, a) -> List.exists (istriv x) a && raise Unify;;
(*let istriv x = restore_checked !ch; istriv x;;*)

let rec unify tm1 tm2 = match tm1,tm2 with
    A(f,fargs),A(g,gargs) -> if f <> g then raise Unify
      else List.iter2 unify fargs gargs
  | tm, V(x) | V(x), tm -> (match subst.(x) with
      Some t -> unify tm t
    | None -> if istriv x tm then () else (subst.(x) <- Some tm; sh := x :: !sh));;


let unify_list env l1 l2 = restore_subst env; List.iter2 unify l1 l2; !sh;;

let unify_lit env ((h1 : int), l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unify_list env l1 l2;;

(*let offinc = 10000;;*)

let rec bump_small off tm = match tm with
    V v -> V(v + off)
  | A(f, a) -> A(f, List.map (bump_small off) a);;

(* Unification with renaming of the second argument *)
let rec unify_rename off t1 t2 = match t1,t2 with
    A(f,fargs),A(g,gargs) -> if f <> g then raise Unify else
        List.iter2 (unify_rename off) fargs gargs
  | _,V(x) -> let x = x + off in (match subst.(x) with
       Some t -> unify_rename 0 t1 t
     | None -> if not (istriv x t1) then (subst.(x) <- Some t1; sh := x :: !sh))
  | V(x),_ -> (match subst.(x) with
       Some t -> unify_rename off t t2
     | None ->
       let t2' = bump_small off t2 in
       if not (istriv x t2') then (subst.(x) <- Some t2'; sh := x :: !sh));;

let rec eq2 x = function
    V y -> y = x || (match subst.(y) with Some t -> eq2 x t | None -> false)
  | A (f, a) -> false;;

let rec eq tm1 tm2 =
(*  tm1 == tm2 ||*)
  match tm1,tm2 with
    A(f,fargs),A(g,gargs) -> f = g && List.for_all2 eq fargs gargs
  | _,V(x) -> (match subst.(x) with Some t -> eq tm1 t | None -> eq2 x tm1)
  | V(x),_ -> (match subst.(x) with Some t -> eq t tm2 | None -> eq2 x tm2);;

let eq_lit env (p1,args1) (p2,args2) =
  p1 = p2 && (restore_subst env; List.for_all2 eq args1 args2);;

(* In leanCoP: only for printing, in resolve is used by unify_rename2 *)
let rec inst_tm = function
    V(v) -> (match subst.(v) with Some t -> inst_tm t | None -> V(v))
  | A(f,args) -> A(f,List.map inst_tm args);;
let inst_lit env (p, l) = restore_subst env; (p, List.map inst_tm l);;

let rec bump_subst_vars off = function
    V x -> (*(match subst.(x + off) with
              | None -> *)V (x + off)(* | Some t -> t)*)
  | A (x, l) -> A (x, List.map (bump_subst_vars off) l);;

let unify_rename_subst off l1 l2 env list =
  restore_subst env;
  List.iter2 (unify_rename off) l1 l2;
  !sh, List.map (fun (p,l) -> p,List.map (bump_subst_vars off) l) list;;

let empty_sub = [];;

module Im = Map.Make(struct type t = int let compare = compare end);;

let md5s s = Int64.to_int ((Obj.magic (Digest.to_hex (Digest.string s))) : int64);;

let cnst_no, no_cnst = Hashtbl.create 100, Hashtbl.create 100;;

let rec find_free_const n = if Hashtbl.mem no_cnst n then find_free_const (n + 1) else n;;
let rec find_free_pred n =
  if Hashtbl.mem no_cnst n || Hashtbl.mem no_cnst (-n) then
    find_free_pred (if n + 1 < 0 then 1 else n + 1) else n;;

let const_number name =
  try Hashtbl.find cnst_no name with Not_found ->
    let cno = find_free_pred (abs (md5s name)) in
    Hashtbl.add cnst_no name cno; Hashtbl.add no_cnst cno name; cno;;

let pred_number name =
  try Hashtbl.find cnst_no name with Not_found ->
    let pno = find_free_pred (abs (md5s name)) in
    Hashtbl.add cnst_no name pno; Hashtbl.add no_cnst pno name; pno;;

let const name args = A (const_number name, args);;
let pred name args = Atom (pred_number name, args);;

let var_no, no_var, var_num = Hashtbl.create 100, Hashtbl.create 100, ref 0;;

let var (name : string) =
  try Hashtbl.find var_no name with Not_found ->
    incr var_num; Hashtbl.add var_no name !var_num; Hashtbl.add no_var !var_num name; !var_num;;

let eqn = pred_number "=";;

let list_forall vs t = List.fold_right (fun v sf -> Forall (var v, sf)) vs t;;
let list_exists vs t = List.fold_right (fun v sf -> Exists (var v, sf)) vs t;;
let list_conj = function [] -> invalid_arg "list_conj"
  | h :: t -> List.fold_left (fun sf e -> Conj (sf, e)) h t;;
let list_disj = function [] -> invalid_arg "list_disj"
  | h :: t -> List.fold_left (fun sf e -> Disj (sf, e)) h t;;
let is_uppercase s = s <> "" && s.[0] <> Char.lowercase s.[0];;
