signature FTERM =
sig

type variable
type predicate
datatype term = V of variable | A of int * term list
type lit
type clause
type clauses

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
type clause = lit list
type clauses = clause list

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


signature MATRIX =
sig

type contrapositive
type matrix
val entries : matrix -> FTerm.predicate -> contrapositive list
val insert_clauses : matrix -> FTerm.clauses -> unit
val empty : int -> matrix
val hashek : FTerm.predicate

end

structure Matrix : MATRIX =
struct

val goal_directed = true

(* (lit-arguments, rest-clause, vars) *)
type contrapositive = (FTerm.term list * FTerm.clause * int)

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

fun empty size = Array.array (size, [])

end


signature SUBST =
sig

type substitution
val mapSubst : 'a -> (FTerm.term -> 'a) -> substitution -> FTerm.variable -> 'a
val addSubst : substitution -> FTerm.variable -> FTerm.term -> substitution
val emptySubst : substitution

end

structure Subst : SUBST =
struct

type substitution = (FTerm.variable * FTerm.term) list

fun getSubst subst x = case List.find (fn (x', _) => x = x') subst of
    NONE => NONE
  | SOME (_, t) => SOME t

fun mapSubst n s subst x = case getSubst subst x of NONE => n | SOME t => s t

fun addSubst subst x t = (x, t) :: subst

val emptySubst = []

end


signature UNIF =
sig

type subst_offset
val eq : subst_offset -> FTerm.lit -> FTerm.lit -> bool
val unify : subst_offset -> FTerm.lit -> FTerm.lit -> subst_offset option
val unify_contra : subst_offset -> FTerm.lit -> Matrix.contrapositive ->
  (subst_offset * FTerm.clause) option

end

structure Unif : UNIF =
struct

open FTerm

type subst_offset = Subst.substitution * int

exception Unify

fun isTriv sub x (V y) = x = y orelse Subst.mapSubst false (fn t => isTriv sub x t) sub x
  | isTriv sub x (A (_, a)) = if List.exists (isTriv sub x) a then true else raise Unify

fun addSubst sub x t = if isTriv sub x t then sub else Subst.addSubst sub x t

fun unifyTerm (A(f, fa), A(g, ga), sub) = if f <> g then raise Unify else unifyTerms sub (fa, ga)
  | unifyTerm (V(x), tm, sub) = Subst.mapSubst (addSubst sub x tm) (fn t => unifyTerm (tm, t, sub)) sub x
  | unifyTerm (tm, V(x), sub) = unifyTerm (V(x), tm, sub)
and unifyTerms sub = ListPair.foldlEq unifyTerm sub

fun unifyLit sub (h1, l1) (h2, l2) = if h1 <> h2 then raise Unify else unifyTerms sub (l1, l2)

fun offsetTermVars off = mapVars (fn v => v + off)
fun offsetLitVars off (p, l) = (p, List.map (offsetTermVars off) l)

(* Unification with renaming of the second argument *)
fun unify_rename off (t1, t2, sub) = case (t1, t2) of
    (A(f,fa), A(g,ga)) => if f <> g then raise Unify else unify_rename_list off sub (fa, ga)
  | (_, V x) =>
      let val x' = x + off
      in  Subst.mapSubst (addSubst sub x' t1) (fn t => unify_rename 0 (t1, t, sub)) sub x'
      end
  | (V x, _) => Subst.mapSubst (addSubst sub x (offsetTermVars off t2))
      (fn t => unify_rename off (t, t2, sub)) sub x
and unify_rename_list off = ListPair.foldlEq (unify_rename off)

fun unify_contrapos sub off (_, args1) (args2, rest, 0) =
      ((unifyTerms sub (args1, args2), off), rest)
  | unify_contrapos sub off (_, args1) (args2, rest, vars) =
    let val sub' = unify_rename_list off sub (args1, args2)
        val rest' = List.map (offsetLitVars off) rest
    in  ((sub', off + vars), rest')
    end

fun varEqTerm sub x (V y) = x = y orelse Subst.mapSubst false (varEqTerm sub x) sub y
  | varEqTerm _ _ (A _) = false

fun eqTerm sub (tm1, tm2) = case (tm1,tm2) of
    (A(f,fa),A(g,ga)) => (f = g andalso eqTermList sub (fa, ga))
  | (V(x),_) => Subst.mapSubst (varEqTerm sub x tm2) (fn t => eqTerm sub (tm1, t)) sub x
  | (_,V(_)) => eqTerm sub (tm2, tm1)
and eqTermList sub = ListPair.allEq (eqTerm sub)

fun eqLit sub (p, pa) (q, qa) = p = q andalso eqTermList sub (pa, qa)


fun eq (sub, _) l1 l2 = eqLit sub l1 l2

fun unify (sub, off) l1 l2 =
  SOME (unifyLit sub l1 l2, off) handle Unify => NONE

fun unify_contra (sub, off) lit contra =
  SOME (unify_contrapos sub off lit contra) handle Unify => NONE

end


signature LEANCOP =
sig

datatype proof =
    Lem of FTerm.lit
  | Pat of FTerm.lit
  | Res of (FTerm.lit * FTerm.clause * FTerm.clause)

val prove_some : Matrix.matrix -> int -> (Subst.substitution * proof) list option

end

structure leanCoP : LEANCOP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

datatype proof =
    Lem of FTerm.lit
  | Pat of FTerm.lit
  | Res of (FTerm.lit * FTerm.clause * FTerm.clause)
exception Solved of (Subst.substitution * proof) list

fun prove mat sub (hist as (path, lem, _)) alt (todo, prf) = fn
    [] => todo (sub, alt, prf)
  | (cl as lit1 :: rest) =>
     let val cont = (fn () => reduce mat sub lit1 rest hist alt (todo, prf) (FTerm.negateLit lit1) path)
         val nalt = if cut1 then alt else cont
     in  if List.exists (fn x => List.exists (Unif.eq sub x) path) cl
           then alt ()
         else if List.exists (Unif.eq sub lit1) lem
           then prove mat sub hist nalt (todo, (fst sub, Lem lit1) :: prf) rest
         else
           reduce mat sub lit1 rest hist alt (todo, prf) (FTerm.negateLit lit1) path
     end
and reduce mat sub lit1 rest hist alt (todo, prf) neglit = fn
    plit :: pt => (case Unif.unify sub neglit plit of
        SOME sub2 =>
          let val nprf = (fst sub, Pat lit1) :: prf
              fun cont () = reduce mat sub lit1 rest hist alt (todo, prf) neglit pt
              val nalt = if cut2 then alt else cont
          in prove mat sub2 hist nalt (todo, nprf) rest
          end
      | NONE => reduce mat sub lit1 rest hist alt (todo, prf) neglit pt)
  | [] =>
      let val dbs = Matrix.entries mat (fst neglit)
      in  extend mat sub lit1 rest hist alt (todo, prf) dbs
      end
and extend mat sub lit rest (hist as (path, lem, lim)) alt (todo, prf) = fn
    ((eh as (_,_,vars)) :: et) =>
    (case (if lim <= 0 andalso vars > 0 then NONE else Unif.unify_contra sub lit eh) of
      SOME (sub2, cla1) =>
      let val nhis1 = (path, lit :: lem, lim)
          fun ntodo (sub, nalt, prf) = prove mat sub nhis1 (if cut3 then alt else nalt) (todo, prf) rest
          val nhist = (lit :: path, lem, lim - 1)
          val nprf  = (fst sub, Res (lit, path, lem)) :: prf
          fun nalt () = extend mat sub lit rest hist alt (todo, prf) et
      in  prove mat sub2 nhist nalt (ntodo, nprf) cla1
      end
    | NONE => extend mat sub lit rest hist alt (todo, prf) et)
  | [] => alt ()

fun prove_exception mat lim = prove mat
  (Subst.emptySubst, 0)
  ([], [], lim)
  (fn () => ())
  ((fn (_,_,prf) => raise (Solved prf)), [])
  [(Matrix.hashek,[])]

fun prove_some mat lim = (prove_exception mat lim; NONE) handle (Solved prf) => SOME prf

end