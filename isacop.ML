

signature TERM =
sig

type variable
type predicate
datatype term = V of variable | A of int * term list
type lit
type environment

exception Unify

val predicate_ord : predicate * predicate -> order

val unifyList : environment -> term list -> term list -> environment
val unifyLit : environment -> lit -> lit -> environment
val unify_rename_subst : int -> term list -> term list -> environment -> lit list -> environment * lit list
val eqLit : environment -> lit -> lit -> bool
val negateLit : lit -> lit
val emptySub : environment
val termVars : term -> variable list

end


structure List =
struct

open List

fun iter2 f (x::xs) (y::ys) = (f x y; iter2 f xs ys)
  | iter2 _ [] [] = ()
  | iter2 _ _ _ = raise Fail "list lengths differ"

fun all2 f (x::xs) (y::ys) = f x y andalso all2 f xs ys
  | all2 _ [] [] = true
  | all2 _ _ _ = raise Fail "list lengths differ"

(* run function for every element and all other elements of the list *)
fun iter_rest _ _ [] = ()
  | iter_rest acc f (h :: t) = (f (h, List.revAppend (acc, t)); iter_rest (h :: acc) f t)

fun elem x (h::t) = x = h orelse elem x t
  | elem x [] = false

end


structure Term : TERM =
struct

type variable = int
type predicate = int
datatype term = V of variable | A of int * term list
type lit = predicate * term list
type environment = variable list

val predicate_ord = int_ord

val subst = Array.array (1000000, NONE : term option)
val sh : environment Unsynchronized.ref = Unsynchronized.ref []

exception Unify

fun mapSubst n s x = case Array.sub (subst, x) of NONE => n | SOME t => s t

local
  (* isTriv x t if variable x is contained in the term t *)
  fun isTriv x (V y) = x = y orelse mapSubst false (fn t => isTriv x t) x
    | isTriv x (A (_, a)) = if List.exists (isTriv x) a then true else raise Unify
in
  fun addSubst x t =
    if isTriv x t then ()
    else (Array.update (subst, x, SOME t); sh := x :: !sh)
end

fun restore_subst env =
  if (!sh) = env then ()
  else (Array.update (subst, List.hd (!sh), NONE); sh := List.tl (!sh); restore_subst env)





fun unify (A(f, fa)) (A(g, ga)) = if f <> g then raise Unify else List.iter2 unify fa ga
  | unify (V(x)) tm = mapSubst (addSubst x tm) (unify tm) x
  | unify tm (V(x)) = unify (V(x)) tm

fun unifyList env l1 l2 = (restore_subst env; List.iter2 unify l1 l2; !sh)

fun unifyLit env (h1, l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unifyList env l1 l2

local
  fun bump_small off (V v) = V(v + off)
    | bump_small off (A(f, a)) = A(f, List.map (bump_small off) a)
in
  (* Unification with renaming of the second argument *)
  fun unify_rename off t1 t2 = case (t1, t2) of
      (A(f,fa), A(g,ga)) => if f <> g then raise Unify else List.iter2 (unify_rename off) fa ga
    | (_, V x) =>
        let val x = x + off
        in  mapSubst (addSubst x t1) (unify_rename 0 t1) x
        end
    | (V x, _) => case Array.sub (subst, x) of
        SOME t => unify_rename off t t2
      | NONE => addSubst x (bump_small off t2)

  fun unify_rename_subst off l1 l2 env list =
    (restore_subst env;
    List.iter2 (unify_rename off) l1 l2;
    (!sh, List.map (fn (p,l) => (p,List.map (bump_small off) l)) list))
end

local
  fun varEqTerm x (V y) = x = y orelse mapSubst false (varEqTerm x) y
    | varEqTerm _ (A _) = false

  fun eqTerm tm1 tm2 = case (tm1,tm2) of
      (A(f,fargs),A(g,gargs)) => (f = g andalso List.all2 eqTerm fargs gargs)
    | (V(x),_) => mapSubst (varEqTerm x tm2) (eqTerm tm1) x
    | (_,V(_)) => eqTerm tm2 tm1
in
  fun eqLit env (p,pa) (q,qa) = p = q andalso (restore_subst env; List.all2 eqTerm pa qa)
end

val emptySub = []

fun negateLit (i, l) = (~i, l)

fun termVars (V x) = [x]
  | termVars (A (_, args)) = List.concat (List.map termVars args)

end

signature DATABASE =
sig

type contrapositive = (Term.term list * Term.lit list * int)
val db_entries : int -> contrapositive list
val hashek : Term.predicate

end

structure Database : DATABASE =
struct

(* (lit-arguments, rest-clause, vars) *)
type contrapositive = (Term.term list * Term.lit list * int)

(* structure PTable = Table(type key = Term.predicate val ord = Term.predicate_ord) *)

(* for every predicate, store list of possible contrapositives *)
val db : (contrapositive list) Array.array = Array.array (10000, [])

(*fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2*)
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)


(* TODO! *)
val hashek = 0
val hashek_lit = (~hashek, [])


fun litVars (_, ts) = List.concat (List.map Term.termVars ts)
fun clauseVars cl = List.concat (List.map litVars cl)

fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (clauseVars cl)

val goal_directed = true


fun clause_prefix_hash cl =
  if not goal_directed andalso
     List.all (fn (p, _) => p < 0) cl andalso
     not (List.elem hashek_lit cl)
  then hashek_lit :: cl else cl


local
  fun contrapositive2db max_var ((p,tl), rest) =
    let val n = nat_of_int p
        val nohashek = List.filter (fn l => l <> hashek_lit) rest
    in  Array.update (db, n, (tl, nohashek, max_var) :: Array.sub (db, n))
    end

  fun cl2db cl =
    let val max_var = clauseMaxVar cl
        val cl = clause_prefix_hash cl
    in  List.iter_rest [] (contrapositive2db max_var) cl
    end
in
  val axioms2db = List.app cl2db
end

fun db_entries neglit = Array.sub (db, nat_of_int neglit)
end

structure IsaCoP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

(* Some counters *)
val infer = Unsynchronized.ref 0
val depth = Unsynchronized.ref 0
val depthinfer = Unsynchronized.ref 0


fun eq (sub, _) l1 l2 = Term.eqLit sub l1 l2;;

fun unify (sub, off) l1 l2 = SOME (Term.unifyLit sub l1 l2, off) handle Term.Unify => NONE

fun unify_rename (s, off) args1 (args2, rest, vars) =
  let val xx = if vars = 0 then ((Term.unifyList s args1 args2, off), rest)
               else let val (s, rest) = Term.unify_rename_subst off args1 args2 s rest
                    in  ((s, off + vars), rest)
                    end
  in SOME xx
  end
  handle Term.Unify => NONE

datatype proof =
    Lem of Term.lit
  | Pat of Term.lit
  | Res of (Term.lit * Term.lit list * Term.lit list)
exception Solved of (int list * proof) list


fun prove sub (hist as (path, lem, lim)) alt (todo, prf) = fn
    [] => todo (sub, alt, prf)
  | (cl as lit1 :: rest) =>
     let val cont = (fn () => reduce sub lit1 rest hist alt (todo, prf) (Term.negateLit lit1) path)
         val nalt = if cut1 then alt else cont
     in  if List.exists (fn x => List.exists (eq sub x) path) cl
           then alt ()
         else if List.exists (eq sub lit1) lem
           then prove sub hist nalt (todo, (fst sub, Lem lit1) :: prf) rest
         else
           reduce sub lit1 rest hist alt (todo, prf) (Term.negateLit lit1) path
     end
and reduce sub lit1 rest hist alt (todo, prf) neglit = fn
    plit :: pt => (case unify sub neglit plit of
        SOME sub2 =>
          let val nprf = (fst sub, Pat lit1) :: prf
              fun cont () = reduce sub lit1 rest hist alt (todo, prf) neglit pt
              val nalt = if cut2 then alt else cont
          in prove sub2 hist nalt (todo, nprf) rest
          end
      | NONE => reduce sub lit1 rest hist alt (todo, prf) neglit pt)
  | [] =>
      let val dbs = Database.db_entries (fst neglit)
      in  extend sub lit1 rest hist alt (todo, prf) dbs
      end
and extend sub lit1 rest (hist as (path, lem, lim)) alt (todo, prf) = fn
    ((eh as (_,_,vars)) :: et) =>
    (case (if lim <= 0 andalso vars > 0 then NONE else unify_rename sub (snd lit1) eh) of
      SOME (sub2, cla1) =>
      let val nhis1 = (path, lit1 :: lem, lim)
          fun ntodo (sub, nalt, prf) = prove sub nhis1 (if cut3 then alt else nalt) (todo, prf) rest
          val nhist = (lit1 :: path, lem, lim - 1)
          val nprf  = (fst sub, Res (lit1, path, lem)) :: prf
          fun nalt () = extend sub lit1 rest hist alt (todo, prf) et
      in  infer := !infer + 1;
          prove sub2 nhist nalt (ntodo, nprf) cla1
      end
    | NONE => extend sub lit1 rest hist alt (todo, prf) et)
  | [] => alt ()

fun prove2 lim = prove
  (Term.emptySub, 0)
  ([], [], lim)
  (fn () => ())
  ((fn (_,_,prf) => raise (Solved prf)), [])
  [(Database.hashek,[])]

end


val _ =
  let val oc = TextIO.openOut "bla";
  in TextIO.closeOut oc
end