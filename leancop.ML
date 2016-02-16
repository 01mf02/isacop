signature FTERM =
sig

type variable
type predicate
datatype term = V of variable | A of int * term list
type lit

val negateLit : lit -> lit
val termVars : term -> variable list
val mapVars : (variable -> variable) -> term -> term

end

structure FTerm : FTERM =
struct

type variable = int
type predicate = int
datatype term = V of variable | A of int * term list
type lit = predicate * term list

fun negateLit (i, l) = (~i, l)

fun termVars (V x) = [x]
  | termVars (A (_, args)) = List.concat (List.map termVars args)

fun mapVars f (V x) = V (f x)
  | mapVars f (A (g, args)) = A(g, map (mapVars f) args)

end


signature LIST =
sig

include LIST

val app_rest : 'a list -> ('a * 'a list -> 'b) -> 'a list -> unit

end

structure List : LIST =
struct

open List

(* run function for every element and all other elements of the list *)
fun app_rest _ _ [] = ()
  | app_rest acc f (h :: t) = (f (h, List.revAppend (acc, t)); app_rest (h :: acc) f t)

end


structure Substitution =
struct

open FTerm

type subst_array = term option Array.array
type subst_list = variable list
type environment = subst_list

val subst : subst_array = Array.array (1000000, NONE)
val sh : subst_list Unsynchronized.ref = Unsynchronized.ref []

fun mapSubst n s x = case Array.sub (subst, x) of NONE => n | SOME t => s t

fun addSubst x t = (Array.update (subst, x, SOME t); sh := x :: !sh)

fun restore_subst env =
  if (!sh) = env then ()
  else (Array.update (subst, List.hd (!sh), NONE); sh := List.tl (!sh); restore_subst env)

end


signature UNIFICATION =
sig

include FTERM

type environment

(*
val unifyList : environment -> term list -> term list -> environment
val unifyLit : environment -> lit -> lit -> environment
val unify_rename_subst : int -> term list -> term list -> environment -> lit list -> environment * lit list
val eqLit : environment -> lit -> lit -> bool
*)

val emptySub : environment

val eq : environment * 'a -> ''b * FTerm.term list -> ''b * FTerm.term list -> bool
val unify : environment * 'a -> ''b * FTerm.term list -> ''b * FTerm.term list -> (environment * 'a) option
val unify_rename : environment * FTerm.variable ->
              FTerm.term list ->
              FTerm.term list * ('a * FTerm.term list) list * FTerm.variable ->
              ((environment * FTerm.variable) * ('a * FTerm.term list) list) option

end

structure Unification : UNIFICATION =
struct

open FTerm

type subst_array = term option Array.array
type subst_list = variable list
type environment = subst_list

exception Unify

local
  (* isTriv x t if variable x is contained in the term t *)
  fun isTriv x (V y) = x = y orelse Substitution.mapSubst false (fn t => isTriv x t) x
    | isTriv x (A (_, a)) = if List.exists (isTriv x) a then true else raise Unify
in
  fun addSubst x t =
    if isTriv x t then () else Substitution.addSubst x t
end

fun unify (A(f, fa), A(g, ga)) = if f <> g then raise Unify else ListPair.appEq unify (fa, ga)
  | unify (V(x), tm) = Substitution.mapSubst (addSubst x tm) (fn t => unify (tm, t)) x
  | unify (tm, V(x)) = unify (V(x), tm)

fun unifyList env l1 l2 = (Substitution.restore_subst env; ListPair.appEq unify (l1, l2); !Substitution.sh)

fun unifyLit env (h1, l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unifyList env l1 l2

local
  fun bump_small off = mapVars (fn v => v + off)
in
  (* Unification with renaming of the second argument *)
  fun unify_rename off (t1, t2) = case (t1, t2) of
      (A(f,fa), A(g,ga)) => if f <> g then raise Unify else ListPair.appEq (unify_rename off) (fa, ga)
    | (_, V x) =>
        let val x = x + off
        in  Substitution.mapSubst (addSubst x t1) (fn t => unify_rename 0 (t1, t)) x
        end
    | (V x, _) => Substitution.mapSubst (addSubst x (bump_small off t2)) (fn t => unify_rename off (t, t2)) x

  fun unify_rename_subst off l1 l2 env list =
    (Substitution.restore_subst env;
    ListPair.appEq (unify_rename off) (l1, l2);
    (!Substitution.sh, List.map (fn (p,l) => (p,List.map (bump_small off) l)) list))
end

local
  fun varEqTerm x (V y) = x = y orelse Substitution.mapSubst false (varEqTerm x) y
    | varEqTerm _ (A _) = false

  fun eqTerm (tm1, tm2) = case (tm1,tm2) of
      (A(f,fargs),A(g,gargs)) => (f = g andalso ListPair.allEq eqTerm (fargs, gargs))
    | (V(x),_) => Substitution.mapSubst (varEqTerm x tm2) (fn t => eqTerm (tm1, t)) x
    | (_,V(_)) => eqTerm (tm2, tm1)
in
  fun eqLit env (p,pa) (q,qa) = p = q andalso (Substitution.restore_subst env; ListPair.allEq eqTerm (pa, qa))
end

val emptySub = []

fun wrap x = SOME x handle Unify => NONE

fun unify_rename1 (s, off) args1 (args2, rest, 0) = ((unifyList s args1 args2, off), rest)
  | unify_rename1 (s, off) args1 (args2, rest, vars) =
    let val (s, rest) = unify_rename_subst off args1 args2 s rest
    in  ((s, off + vars), rest)
    end


fun eq (sub, _) l1 l2 = eqLit sub l1 l2;;

fun unify (sub, off) l1 l2 = wrap (unifyLit sub l1 l2, off)

fun unify_rename sub args1 rest = wrap (unify_rename1 sub args1 rest)


end


signature MATRIX =
sig

type contrapositive
type matrix
val entries : matrix -> FTerm.predicate -> contrapositive list
val insert_clauses : matrix -> FTerm.lit list list -> unit
val hashek : FTerm.predicate

end

structure Matrix : MATRIX =
struct

val goal_directed = true

(* (lit-arguments, rest-clause, vars) *)
type contrapositive = (FTerm.term list * FTerm.lit list * int)

(* for every predicate, store list of possible contrapositives *)
type matrix = contrapositive list Array.array

(*fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2*)
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)


val hashek = 1
val hashek_lit = (~hashek, [])


fun litVars (_, ts) = List.concat (List.map FTerm.termVars ts)
fun clauseVars cl = List.concat (List.map litVars cl)

fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (clauseVars cl)

fun clause_prefix_hash cl =
  if not goal_directed andalso
     List.all (fn (p, _) => p < 0) cl andalso
     not (member (op =) cl hashek_lit)
  then hashek_lit :: cl else cl

local
  fun insert_contrapositive mat max_var ((p,tl), rest) =
    let val n = nat_of_int p
        val nohashek = List.filter (fn l => l <> hashek_lit) rest
    in  Array.update (mat, n, (tl, nohashek, max_var) :: Array.sub (mat, n))
    end

  fun insert_clause mat cl =
    let val max_var = clauseMaxVar cl
        val cl = clause_prefix_hash cl
    in  List.app_rest [] (insert_contrapositive mat max_var) cl
    end
in
  fun insert_clauses mat = List.app (insert_clause mat)
end

fun entries mat neglit = Array.sub (mat, nat_of_int neglit)
end


signature LEANCOP =
sig

datatype proof =
    Lem of FTerm.lit
  | Pat of FTerm.lit
  | Res of (FTerm.lit * FTerm.lit list * FTerm.lit list)

val set_matrix : FTerm.lit list list -> unit
val prove_some : int -> (int list * proof) list option

end

structure leanCoP : LEANCOP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

datatype proof =
    Lem of FTerm.lit
  | Pat of FTerm.lit
  | Res of (FTerm.lit * FTerm.lit list * FTerm.lit list)
exception Solved of (int list * proof) list

val db : Matrix.matrix = Array.array (10000, [])

val set_matrix = (Array.modify (K []) db; Matrix.insert_clauses db)


fun prove sub (hist as (path, lem, _)) alt (todo, prf) = fn
    [] => todo (sub, alt, prf)
  | (cl as lit1 :: rest) =>
     let val cont = (fn () => reduce sub lit1 rest hist alt (todo, prf) (FTerm.negateLit lit1) path)
         val nalt = if cut1 then alt else cont
     in  if List.exists (fn x => List.exists (Unification.eq sub x) path) cl
           then alt ()
         else if List.exists (Unification.eq sub lit1) lem
           then prove sub hist nalt (todo, (fst sub, Lem lit1) :: prf) rest
         else
           reduce sub lit1 rest hist alt (todo, prf) (FTerm.negateLit lit1) path
     end
and reduce sub lit1 rest hist alt (todo, prf) neglit = fn
    plit :: pt => (case Unification.unify sub neglit plit of
        SOME sub2 =>
          let val nprf = (fst sub, Pat lit1) :: prf
              fun cont () = reduce sub lit1 rest hist alt (todo, prf) neglit pt
              val nalt = if cut2 then alt else cont
          in prove sub2 hist nalt (todo, nprf) rest
          end
      | NONE => reduce sub lit1 rest hist alt (todo, prf) neglit pt)
  | [] =>
      let val dbs = Matrix.entries db (fst neglit)
      in  extend sub lit1 rest hist alt (todo, prf) dbs
      end
and extend sub lit1 rest (hist as (path, lem, lim)) alt (todo, prf) = fn
    ((eh as (_,_,vars)) :: et) =>
    (case (if lim <= 0 andalso vars > 0 then NONE else Unification.unify_rename sub (snd lit1) eh) of
      SOME (sub2, cla1) =>
      let val nhis1 = (path, lit1 :: lem, lim)
          fun ntodo (sub, nalt, prf) = prove sub nhis1 (if cut3 then alt else nalt) (todo, prf) rest
          val nhist = (lit1 :: path, lem, lim - 1)
          val nprf  = (fst sub, Res (lit1, path, lem)) :: prf
          fun nalt () = extend sub lit1 rest hist alt (todo, prf) et
      in  prove sub2 nhist nalt (ntodo, nprf) cla1
      end
    | NONE => extend sub lit1 rest hist alt (todo, prf) et)
  | [] => alt ()

fun prove_exception lim = prove
  (Unification.emptySub, 0)
  ([], [], lim)
  (fn () => ())
  ((fn (_,_,prf) => raise (Solved prf)), [])
  [(Matrix.hashek,[])]

fun prove_some lim = (prove_exception lim; NONE) handle (Solved prf) => SOME prf

end