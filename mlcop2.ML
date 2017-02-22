(*  Title:      mlCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Translation of leanCoP to Standard ML.
*)

signature FTERM =
sig

type ('c, 'v) term
type ('p, 'c, 'v) lit

val A : ('c * ('c, 'v) term list) -> ('c, 'v) term
val V : 'v -> ('c, 'v) term

val destApp : ('c, 'v) term -> ('c * ('c, 'v) term list)
val litVars : ('p, 'c, 'v) lit -> 'v list

end

structure FTerm : FTERM =
struct

type ('c, 'v) term = ('c, 'v) Tree.tree
type ('p, 'c, 'v) lit = 'p * ('c, 'v) term list

val A = Tree.Branch
val V = Tree.Leaf

fun destApp (Tree.Branch (f, args)) = (f, args)
  | destApp _ = raise Fail "destApp"

fun litVars (_, ts) = List.concat (List.map Tree.leafs ts)

end


signature LTERM =
sig

type constant
type variable
type term
type lit
type clause
type clauses

val toLit : bool * term -> lit
val negateLit : lit -> lit

val offsetTermVars : int -> term -> term
val offsetLitVars : int -> lit -> lit

val clauseVars : clause -> variable list

end


structure LTerm : LTERM =
struct

type constant = int
type variable = int
type predicate = int
type term = (constant, variable) FTerm.term
type lit = predicate * term list
type clause = lit list
type clauses = clause list

fun toLit (pol, Tree.Branch (P, args)) = (if pol then P else ~P, args)
  | toLit _ = raise Fail "toLit"

fun negateLit (i, l) = (~i, l)

fun offsetTermVars off = Tree.map_leafs (fn v => v + off)
fun offsetLitVars off (p, l) = (p, List.map (offsetTermVars off) l)

fun clauseVars cl = List.concat (List.map FTerm.litVars cl)

end


signature MATRIX =
sig

type 'a contrapositive
type 'a matrix

val empty : int -> 'a matrix
val insert_clause : 'a matrix -> LTerm.clause * 'a -> unit
val from_list : (LTerm.clause * 'a) list -> 'a matrix
val entries : 'a matrix -> LTerm.lit -> 'a contrapositive list

end

structure Matrix : MATRIX =
struct

(* (lit-arguments, rest-clause, vars, data) *)
type 'a contrapositive = (LTerm.term list * LTerm.clause * int * 'a)

(* for every predicate, store list of possible contrapositives *)
type 'a matrix = 'a contrapositive list Array.array


fun empty size = Array.array (size, [])

fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (LTerm.clauseVars cl)

fun insert_contrapositive mat max_var info ((p, tl), rest) =
  let val n = Utils.nat_of_int p
  in  Array.update (mat, n, (tl, rest, max_var, info) :: Array.sub (mat, n))
  end

fun insert_clause mat (cl, info) =
  let val max_var = clauseMaxVar cl
  in  Utils.app_rest [] (insert_contrapositive mat max_var info) cl
  end

fun from_list cls =
  let val preds = List.concat (map (map fst o fst) cls)
      val max_pred = preds |> map Utils.nat_of_int |> Utils.maximum
      val mat = empty (max_pred + 1)
  in List.app (insert_clause mat) cls; mat
  end

fun entries mat (p, _) = Array.sub (mat, Utils.nat_of_int p)

end


(* Partial functions *)
signature MORPHISM =
sig

type ('a, 'b) morphism
val apply : (''a, 'b) morphism -> ''a -> 'b option
val map : 'c -> ('b -> 'c) -> (''a, 'b) morphism -> ''a -> 'c
val add : ('a, 'b) morphism -> 'a -> 'b -> ('a, 'b) morphism
val empty : ('a, 'b) morphism

end

structure ListMorphism : MORPHISM =
struct

type ('a, 'b) morphism = ('a * 'b) list

fun apply morph x = Option.map snd (List.find (fn (x', _) => x = x') morph)

fun map n s morph x = Utils.maybe n s (apply morph x)

fun add morph x t = (x, t) :: morph

val empty = []

end


signature SUBST =
sig

include MORPHISM
type ('c, ''v) subst

val subst_until : ('c, ''v) subst -> (''v -> bool) -> ('c, ''v) FTerm.term -> ('c, ''v) FTerm.term

end

structure Subst : SUBST =
struct

open ListMorphism
type ('c, ''v) subst = (''v, ('c, ''v) FTerm.term) morphism

(* Substitute a term until f is true or the term cannot be substituted further *)
fun subst_until sub f (l as Tree.Leaf x) = if f x then l else ListMorphism.map l (subst_until sub f) sub x
  | subst_until _   _ (b as Tree.Branch _) = b

end


signature FUNIFY =
sig

exception Unify

include SUBST
include FTERM

val unifyTerm :
  (''c, ''v) term * (''c, ''v) term * (''c, ''v) subst -> (''c, ''v) subst

val unifyTerms :
  (''c, ''v) subst -> (''c, ''v) term list * (''c, ''v) term list -> (''c, ''v) subst

val unifyLit :
  (''c, ''v) subst -> ''p * (''c, ''v) term list -> ''p * (''c, ''v) term list -> (''c, ''v) subst

val eqTerm :
  (''c, ''v) subst -> (''c, ''v) term * (''c, ''v) term -> bool

val eqLit :
  (''c, ''v) subst -> ''p * (''c, ''v) term list -> ''p * (''c, ''v) term list -> bool

end


structure FUnify : FUNIFY =
struct

open Tree
open Subst
open FTerm

exception Unify

(* Return whether the term t is substituted to variable x.
   Raise exception if t is substituted to contain x as proper subterm (occurs check). *)
fun isTriv sub x t = case subst_until sub (fn y => x = y) t of
    Leaf y => x = y
  | Branch (_, a) => if List.exists (isTriv sub x) a then raise Unify else false

(* Add a substitution from x to t only if there does not exist an equivalent substitution yet. *)
fun addSubst sub x t = if isTriv sub x t then sub else Subst.add sub x t

(* Return new substitution if two terms can be unified, else raise exception. *)
fun unifyTerm (Tree.Branch (f, fa), Tree.Branch (g, ga), sub) =
      if f <> g then raise Unify else unifyTerms sub (fa, ga)
  | unifyTerm (Leaf x, tm, sub) =
      Subst.map (addSubst sub x tm) (fn t => unifyTerm (tm, t, sub)) sub x
  | unifyTerm (tm, Leaf x, sub) = unifyTerm (Leaf x, tm, sub)
and unifyTerms sub = ListPair.foldlEq unifyTerm sub

fun unifyLit sub (h1, l1) (h2, l2) = if h1 <> h2 then raise Unify else unifyTerms sub (l1, l2)

(* Return whether term can be substituted to a variable (no occurs check). *)
fun eqVar sub x t = case subst_until sub (fn y => x = y) t of Leaf y => x = y | Branch _ => false

fun eqTerm sub (t1, t2) = case (t1, t2) of
    (Branch(f, fa), Branch(g, ga)) => f = g andalso eqTermList sub (fa, ga)
  | (Leaf x, t2) => Subst.map (eqVar sub x t2) (fn t => eqTerm sub (t, t2)) sub x
  | (t1, Leaf _) => eqTerm sub (t2, t1)
and eqTermList sub = ListPair.allEq (eqTerm sub)

fun eqLit sub (p, pa) (q, qa) = p = q andalso eqTermList sub (pa, qa)

end


signature UNIF =
sig

type offset
type subst
val eq : subst * offset -> LTerm.lit -> LTerm.lit -> bool
val unify : subst * offset -> LTerm.lit -> LTerm.lit -> (subst * offset) option
val unify_contra : subst * offset -> LTerm.lit -> 'a Matrix.contrapositive ->
  ((subst * offset) * LTerm.clause) option
end

structure Unif : UNIF =
struct

open Tree

type offset = int
type subst = (LTerm.constant, LTerm.variable) Subst.subst

fun unify_contrapos sub off (_, args1) (args2, rest, vars, _) =
  if vars = 0 then ((FUnify.unifyTerms sub (args1, args2), off), rest)
  else
    let val offTV = List.map (LTerm.offsetTermVars off)
        val offLV = List.map (LTerm.offsetLitVars off)
    in  ((FUnify.unifyTerms sub (args1, offTV args2), vars + off), offLV rest)
    end

fun eq (sub, _) l1 l2 = FUnify.eqLit sub l1 l2

fun unify_contra (sub, off) lit contra =
  SOME (unify_contrapos sub off lit contra) handle FUnify.Unify => NONE

fun unify (sub, off) l1 l2 =
  SOME (FUnify.unifyLit sub l1 l2, off) handle FUnify.Unify => NONE

end


signature CPROOF =
sig

datatype ('l, 'r) proof_step =
    Lemma of 'l
  | Path of 'l
  | Resolution of 'l * 'r

type ('l, 'r) proof

val map_step : ('a -> 'b) -> ('a, 'c) proof_step -> ('b, 'c) proof_step
val literal : ('l, 'r) proof_step -> 'l

(*
val fold_proof : ('a -> 'b) ->
      ('c * 'd -> 'e * 'd) ->
        ('a, 'c) proof_step ->
          'd -> ('b, 'e) proof_step * 'd
val fold_resolution : ('r * 'b -> 's * 'b) -> ('l, 'r) proof_step -> 'b -> ('l, 's) proof_step * 'b
*)

val destResolution : ('l, 'r) proof_step -> ('l * 'r) option

val proof_variables : (('p, 'c, 'v) FTerm.lit, 'a) proof_step list -> 'v list

end

(* Connection proof *)
structure CProof : CPROOF =
struct

(* 'l stands for literal, and 'r for the data attached to a resolution step *)
datatype ('l, 'r) proof_step =
    Lemma of 'l
  | Path of 'l
  | Resolution of 'l * 'r
type ('l, 'r) proof = ('l, 'r) proof_step list

fun map_step f (Lemma l) = Lemma (f l)
  | map_step f (Path  l) = Path  (f l)
  | map_step f (Resolution (l, r)) = Resolution (f l, r)

fun literal (Lemma l) = l
  | literal (Path l) = l
  | literal (Resolution (l, _)) = l

(*
fun fold_resolution f (Resolution (l, r)) acc =
      let val (r', acc') = f (r, acc) in (Resolution (l, r'), acc') end
  | fold_resolution _ (Lemma l) acc = (Lemma l, acc)
  | fold_resolution _ (Path  l) acc = (Path l, acc)

fun fold_proof f g p acc = fold_resolution g (map_step f p) acc
*)

fun destResolution (Resolution r) = SOME r
  | destResolution _ = NONE


(* We cannot do eta-conversion here, otherwise we get an ML error:
   "Type variable is free in surrounding scope" *)
fun proof_variables p = List.concat (map (FTerm.litVars o literal) p)

end


signature MLCOP =
sig

type path
type lemmas

type 'a proof_step
type 'a proof

type history
type 'a alternative
type ('a, 'b) promise

type options
type ('a, 'b) state

val prove : options -> 'b Matrix.matrix -> ('a, 'b) state -> LTerm.clause -> 'a
val iterative_prove : options -> 'a Matrix.matrix -> LTerm.clause -> (Unif.subst * 'a proof) option

end

structure mlCoP : MLCOP =
struct

type path   = LTerm.lit list
type lemmas = LTerm.lit list
type history = path * lemmas * int

type options =
{ cut_prove : bool
, cut_reduce : bool
, cut_extend : bool
, max_path_len : int
}

fun set_max_path_len mpl {cut_prove = cp, cut_reduce = cr, cut_extend = ce, max_path_len = _} =
  {cut_prove = cp, cut_reduce = cr, cut_extend = ce, max_path_len = mpl}


type 'a proof_step = (LTerm.lit, Unif.offset * 'a Matrix.contrapositive) CProof.proof_step
type 'a proof = 'a proof_step list

(* continuation types *)
type 'a alternative = unit -> 'a
type ('a, 'b) promise = Unif.subst * Unif.offset -> 'a alternative -> 'b proof -> 'a

type ('a, 'b) state =
  (Unif.subst * Unif.offset) * history * 'a alternative * ('a, 'b) promise * 'b proof


fun prove opts mat (state as (sub, hist as (path, lem, _), alt, todo, prf)) cla =
  ((* writeln ("prove with cla = " ^ PolyML.makestring cla); *)
  case cla of
    [] => todo sub alt prf
  | (cl as lit :: rest) =>
     let val cont = (fn () => reduce opts mat state lit rest path)
         val nalt = if #cut_prove opts then alt else cont
         (* regularity check: all clause literals should not be on path *)
     in  if List.exists (fn x => List.exists (Unif.eq sub x) path) cl
           then alt ()
         (* if literal is among the lemmas, remove it and treat rest clause *)
         else if List.exists (Unif.eq sub lit) lem
           then prove opts mat (sub, hist, nalt, todo, CProof.Lemma lit :: prf) rest
         else
           reduce opts mat state lit rest path
     end)
and reduce opts mat (state as (sub, _, _, _, _)) lit rest path =
  let val neglit = LTerm.negateLit lit
  in
    (* writeln ("reduce with lit = " ^ PolyML.makestring lit ^ " and path = " ^ PolyML.makestring path); *)
    case Utils.findSome (Unif.unify sub (LTerm.negateLit lit)) path of
      (* negated literal is on the path *)
      SOME reduction => real_reduce opts mat state lit rest reduction
    | NONE => extend opts mat state lit rest (Matrix.entries mat neglit)
  end
and real_reduce opts mat (state as (_, hist, alt, todo, prf)) lit rest (_, nsub, path) =
  let (* possibly try to reduce with other literal on path later *)
    fun cont () = reduce opts mat state lit rest path
    val nalt = if #cut_reduce opts then alt else cont
  in prove opts mat (nsub, hist, nalt, todo, CProof.Path lit :: prf) rest
  end
and extend opts mat (state as (sub, (_, _, path_len), alt, _, _)) lit rest entries =
  let fun extensible (entry as (_, _, vars, _)) =
          if path_len >= #max_path_len opts andalso vars > 0 then NONE
          else Unif.unify_contra sub lit entry
  in
    (* writeln ("extend with entries = " ^ PolyML.makestring entries); *)
    case Utils.findSome extensible entries of
      (* we can unify literal with some matrix entry *)
      SOME extension => real_extend opts mat state lit rest extension
    | NONE => alt ()
  end
and real_extend opts mat state lit rest (entry, (nsub, cla1), et) =
  let val (sub, (path, lem, path_len), alt, todo, prf) = state
      val hist1 = (lit :: path, lem, path_len + 1)
      val hist2 = (path, lit :: lem, path_len)
      val step  = CProof.Resolution (lit, (snd sub, entry))
      fun todo1 sub alt2 prf =
        prove opts mat (sub, hist2, if #cut_extend opts then alt else alt2, todo, prf) rest
      fun alt1 () = extend opts mat state lit rest et
  in  prove opts mat (nsub, hist1, alt1, todo1, step :: prf) cla1
  end

val empty_state =
( (Subst.empty, 0) (* substitution & offset *)
, ([], [], 0) (* history *)
, fn () => NONE (* alternative *)
, fn sub => fn _ => fn prf => SOME (fst sub, prf) (* promise *)
, [] (* proof *)
)

(* Iterative deepening *)
fun iterative_prove opts mat clause =
  let fun depth_prove d = prove (set_max_path_len d opts) mat empty_state clause
  in Utils.iterate_until (fn d => d > #max_path_len opts) depth_prove 0
  end

end
