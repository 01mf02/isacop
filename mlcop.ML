(*  Title:      mlCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Translation of leanCoP to Standard ML.
*)



signature FTERM =
sig

type variable
type constant
datatype term = V of variable | A of constant * term list
type lit
type clause
type clauses

val destApp : term -> (int * term list)
val negateLit : lit -> lit
val mapVars : (variable -> term) -> term -> term
val termVars : term -> variable list
val litVars : lit -> variable list
val clauseVars : clause -> variable list

end

structure FTerm : FTERM =
struct

type variable = int
type constant = int
type predicate = int

datatype term = V of variable | A of constant * term list
type lit = predicate * term list
type clause = lit list
type clauses = clause list

fun destApp (A (f, args)) = (f, args)
  | destApp _ = raise Fail "destApp"

fun negateLit (i, l) = (~i, l)

fun mapVars f (V x) = f x
  | mapVars f (A (g, args)) = A(g, map (mapVars f) args)

fun termVars (V x) = [x]
  | termVars (A (_, args)) = List.concat (List.map termVars args)

fun litVars (_, ts) = List.concat (List.map termVars ts)

val clauseVars = List.concat o List.map litVars

end


signature MATRIX =
sig

type 'a contrapositive
type 'a matrix
val entries : 'a matrix -> FTerm.lit -> 'a contrapositive list
val insert_clauses : 'a matrix -> (FTerm.clause * 'a) list -> unit
val empty : int -> 'a matrix

end

structure Matrix : MATRIX =
struct

(* (lit-arguments, rest-clause, vars, data) *)
type 'a contrapositive = (FTerm.term list * FTerm.clause * int * 'a)

(* for every predicate, store list of possible contrapositives *)
type 'a matrix = 'a contrapositive list Array.array

(*fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2*)
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)


fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (FTerm.clauseVars cl)

(*Run function for every element and all other elements of the list.
  For example: app_rest [] f [1, 2, 3] =
    f (1, [2, 3]);
    f (2, [1, 3]);
    f (3, [1, 2])
*)
fun app_rest _ _ [] = ()
  | app_rest acc f (h :: t) = (f (h, List.revAppend (acc, t)); app_rest (h :: acc) f t)

local
  fun insert_contrapositive mat max_var info ((p,tl), rest) =
    let val n = nat_of_int p
    in  Array.update (mat, n, (tl, rest, max_var, info) :: Array.sub (mat, n))
    end

  fun insert_clause mat (cl, info) =
    let val max_var = clauseMaxVar cl
    in  app_rest [] (insert_contrapositive mat max_var info) cl
    end
in
  fun insert_clauses mat = List.app (insert_clause mat)
end

fun entries mat (p, _) = Array.sub (mat, nat_of_int p)

fun empty size = Array.array (size, [])

end


signature MORPHISM =
sig

type ('a, 'b) morphism
val map : 'c -> ('b -> 'c) -> (''a, 'b) morphism -> ''a -> 'c
val add : ('a, 'b) morphism -> 'a -> 'b -> ('a, 'b) morphism
val empty : ('a, 'b) morphism

end

structure ListMorphism : MORPHISM =
struct

type ('a, 'b) morphism = ('a * 'b) list

fun get morph x = case List.find (fn (x', _) => x = x') morph of
    NONE => NONE
  | SOME (_, t) => SOME t

fun map n s subst x = case get subst x of NONE => n | SOME t => s t

fun add subst x t = (x, t) :: subst

val empty = []

end


signature SUBST =
sig

include MORPHISM

type subst

val transitive : subst -> FTerm.term -> FTerm.term
val normalise : subst -> subst

end

structure Subst : SUBST =
struct

open ListMorphism

type subst = (FTerm.variable, FTerm.term) morphism

fun transitive sub =
  FTerm.mapVars (fn v => ListMorphism.map (FTerm.V v) (transitive sub) sub v)

fun normalise sub = List.map (fn (v, t) => (v, transitive sub t)) sub

end


signature UNIF =
sig

type offset
type subst_offset
val eq : subst_offset -> FTerm.lit -> FTerm.lit -> bool
val unify : subst_offset -> FTerm.lit -> FTerm.lit -> subst_offset option
val unify_contra : subst_offset -> FTerm.lit -> 'a Matrix.contrapositive ->
  (subst_offset * FTerm.clause) option

end

structure Unif : UNIF =
struct

open FTerm

type offset = int
type subst_offset = Subst.subst * offset

exception Unify

fun isTriv sub x (V y) = x = y orelse Subst.map false (fn t => isTriv sub x t) sub y
  | isTriv sub x (A (_, a)) = if List.exists (isTriv sub x) a then raise Unify else false

fun addSubst sub x t = if isTriv sub x t then sub else Subst.add sub x t

fun unifyTerm (A(f, fa), A(g, ga), sub) = if f <> g then raise Unify else unifyTerms sub (fa, ga)
  | unifyTerm (V(x), tm, sub) = Subst.map (addSubst sub x tm) (fn t => unifyTerm (tm, t, sub)) sub x
  | unifyTerm (tm, V(x), sub) = unifyTerm (V(x), tm, sub)
and unifyTerms sub = ListPair.foldlEq unifyTerm sub

fun unifyLit sub (h1, l1) (h2, l2) = if h1 <> h2 then raise Unify else unifyTerms sub (l1, l2)

fun offsetTermVars off = mapVars (fn v => V (v + off))
fun offsetLitVars off (p, l) = (p, List.map (offsetTermVars off) l)

(*Unify with renaming of the second argument.*)

fun unify_rename off (t1, t2, sub) = unifyTerm (t1, offsetTermVars off t2, sub)
(*fun unify_rename off (t1, t2, sub) = case (t1, t2) of
    (A(f,fa), A(g,ga)) => if f <> g then raise Unify else unify_rename_list off sub (fa, ga)
  | (t1, V x) =>
      let val x' = x + off
      in  Subst.map (addSubst sub x' t1) (fn t => unify_rename 0 (t1, t, sub)) sub x'
      end
  | (V x, t2) => Subst.map (addSubst sub x (offsetTermVars off t2))
      (fn t => unify_rename off (t, t2, sub)) sub x*)
and unify_rename_list off = ListPair.foldlEq (unify_rename off)


fun unify_contrapos sub off (_, args1) (args2, rest, vars, _) =
    if vars = 0 then ((unifyTerms sub (args1, args2), off), rest)
    else
      let val sub' = unify_rename_list off sub (args1, args2)
          val rest' = List.map (offsetLitVars off) rest
      in  ((sub', off + vars), rest')
      end

(*True if variable is equivalent to another variable under substitution.*)
fun eqVar sub x (V y) = x = y orelse Subst.map false (eqVar sub x) sub y
  | eqVar _   _ (A _) = false

fun eqTerm sub (t1, t2) = case (t1, t2) of
    (A(f, fa), A(g, ga)) => f = g andalso eqTermList sub (fa, ga)
  | (V x, t2) => Subst.map (eqVar sub x t2) (fn t => eqTerm sub (t, t2)) sub x
  | (t1, V _) => eqTerm sub (t2, t1)
and eqTermList sub = ListPair.allEq (eqTerm sub)

fun eqLit sub (p, pa) (q, qa) = p = q andalso eqTermList sub (pa, qa)


fun eq (sub, _) l1 l2 = eqLit sub l1 l2

fun unify (sub, off) l1 l2 =
  SOME (unifyLit sub l1 l2, off) handle Unify => NONE

fun unify_contra (sub, off) lit contra =
  SOME (unify_contrapos sub off lit contra) handle Unify => NONE

end


structure CProof =
struct

datatype ('l, 'r) proof_step =
    Lemma of 'l
  | Path of 'l
  | Resolution of 'l * 'r
type ('l, 'r) proof = ('l, 'r) proof_step list

fun fold_proof f _ (Lemma l) acc = (Lemma (f l), acc)
  | fold_proof f _ (Path  l) acc = (Path  (f l), acc)
  | fold_proof f g (Resolution (l, r)) acc =
    let val (r', acc') = g (r, acc) in (Resolution (f l, r'), acc') end

fun destResolution (Resolution r) = SOME r
  | destResolution _ = NONE

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

val prove : 'b Matrix.matrix -> Unif.subst_offset -> history -> 'a alternative -> ('a, 'b) promise -> 'b proof -> FTerm.clause -> 'a
val prove_default : 'a alternative -> ('a, 'b) promise -> 'b Matrix.matrix -> int -> 'a

end

structure mlCoP : MLCOP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

type path   = FTerm.lit list
type lemmas = FTerm.lit list
type history = path * lemmas * int


type 'a proof_step = (FTerm.lit, Unif.offset * 'a Matrix.contrapositive) CProof.proof_step
type 'a proof = 'a proof_step list

(* continuation types *)
type 'a alternative = unit -> 'a
type ('a, 'b) promise = Unif.subst_offset -> 'a alternative -> 'b proof -> 'a

(* Return first element that returns SOME plus the rest of the list, else NONE. *)
fun findSome f (x :: xs) = (case f x of SOME y => SOME (x, y, xs) | NONE => findSome f xs)
  | findSome _ [] = NONE

fun prove mat sub (hist as (path, lem, _)) alt todo prf cla =
  (writeln ("prove with cla = " ^ PolyML.makestring cla);
  case cla of
    [] => todo sub alt prf
  | (cl as lit :: rest) =>
     let val cont = (fn () => reduce mat sub lit rest hist alt todo prf path)
         val nalt = if cut1 then alt else cont
         (* regularity check: all clause literals should not be on path *)
     in  if List.exists (fn x => List.exists (Unif.eq sub x) path) cl
           then alt ()
         (* if literal is among the lemmas, remove it and treat rest clause *)
         else if List.exists (Unif.eq sub lit) lem
           then prove mat sub hist nalt todo (CProof.Lemma lit :: prf) rest
         else
           reduce mat sub lit rest hist alt todo prf path
     end)
and reduce mat sub lit rest hist alt todo prf path =
    let val neglit = FTerm.negateLit lit
    in
    writeln ("reduce with lit = " ^ PolyML.makestring lit ^ " and path = " ^ PolyML.makestring path);
    case findSome (Unif.unify sub neglit) path of
      (* negated literal is on the path *)
      SOME (_, nsub, pt) =>
        let (* possibly try to reduce with other literal on path later *)
            fun cont () = reduce mat sub lit rest hist alt todo prf pt
            val nalt = if cut2 then alt else cont
        in prove mat nsub hist nalt todo (CProof.Path lit :: prf) rest
        end
    | NONE => extend mat sub lit rest hist alt todo prf (Matrix.entries mat neglit)
    end
and extend mat sub lit rest (hist as (path, lem, lim)) alt todo prf entries =
    let fun extensible (entry as (_, _, vars, _)) =
            if lim <= 0 andalso vars > 0 then NONE
            else Unif.unify_contra sub lit entry
    in
    writeln ("extend with entries = " ^ PolyML.makestring entries);
    case findSome extensible entries of
      (* we can unify literal with some matrix entry *)
      SOME (entry, (nsub, cla1), et) =>
          let val hist1 = (lit :: path, lem, lim - 1)
              val hist2 = (path, lit :: lem, lim)
              val prf1  = CProof.Resolution (lit, (snd sub, entry)) :: prf
              fun todo1 sub alt2 prf = prove mat sub hist2 (if cut3 then alt else alt2) todo prf rest
              fun alt1 () = extend mat sub lit rest hist alt todo prf et
          in  prove mat nsub hist1 alt1 todo1 prf1 cla1
          end
    | NONE => alt ()
    end

val hashek = 1

fun prove_default alt todo mat lim =
  let val sub = (Subst.empty, 0)
      val hist = ([], [], lim)
      val prf = []
      val cla = [(hashek, [])]
  in prove mat sub hist alt todo prf cla
  end

end
