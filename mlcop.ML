(*  Title:      mlCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Translation of leanCoP to Standard ML.
*)

structure Tree =
struct

datatype ('b, 'l) tree = Branch of ('b * ('b, 'l) tree list) | Leaf of 'l

type 't monoid_tree = ('t list -> 't, 't) tree

fun deep (Branch (f, nodes)) = map deep nodes |> f
  | deep (Leaf l) = l

fun map_tree f (Leaf l) = f l
  | map_tree f (Branch (b, nodes)) = Branch (b, map (map_tree f) nodes)

fun leafs (Leaf l) = [l]
  | leafs (Branch (b, nodes)) = List.concat (map leafs nodes)

fun fold_map_tree f (Branch (b, nodes)) y =
      let val (nodes', y') = fold_map (fold_map_tree f) nodes y
      in (Branch (b, nodes'), y')
      end
  | fold_map_tree f (Leaf l) y = f l y

end



signature FTERM =
sig

type ('c, 'v) term

val A : ('c * ('c, 'v) term list) -> ('c, 'v) term
val V : 'v -> ('c, 'v) term

val destApp : ('c, 'v) term -> ('c * ('c, 'v) term list)
val mapVars : ('v -> ('c, 'v) term) -> ('c, 'v) term -> ('c, 'v) term
val termVars : ('c, 'v) term -> 'v list

end

structure FTerm : FTERM =
struct

type ('c, 'v) term = ('c, 'v) Tree.tree

val A = Tree.Branch
val V = Tree.Leaf

fun destApp (Tree.Branch (f, args)) = (f, args)
  | destApp _ = raise Fail "destApp"

val termVars = Tree.leafs

fun mapVars f tm = Tree.map_tree f tm

end

signature LTERM =
sig

type variable
type constant
type lit
type clause
type clauses

val negateLit : lit -> lit
val litVars : lit -> variable list
val clauseVars : clause -> variable list

end


structure LTerm =
struct

type variable = int
type constant = int
type predicate = int
type term = (constant, variable) FTerm.term
type lit = predicate * term list
type clause = lit list
type clauses = clause list

fun negateLit (i, l) = (~i, l)

fun litVars (_, ts) = List.concat (List.map FTerm.termVars ts)

fun clauseVars cl = List.concat (List.map litVars cl)

end


signature MATRIX =
sig

type 'a contrapositive
type 'a matrix
val entries : 'a matrix -> LTerm.lit -> 'a contrapositive list
val insert_clauses : 'a matrix -> (LTerm.clause * 'a) list -> unit
val empty : int -> 'a matrix

end

structure Matrix : MATRIX =
struct

(* (lit-arguments, rest-clause, vars, data) *)
type 'a contrapositive = (LTerm.term list * LTerm.clause * int * 'a)

(* for every predicate, store list of possible contrapositives *)
type 'a matrix = 'a contrapositive list Array.array

(*fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2*)
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)


fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (LTerm.clauseVars cl)

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

val transitive : subst -> LTerm.term -> LTerm.term
val normalise : subst -> subst

end

structure Subst : SUBST =
struct

open ListMorphism

type subst = (LTerm.variable, LTerm.term) morphism

fun transitive sub =
  FTerm.mapVars (fn v => ListMorphism.map (FTerm.V v) (transitive sub) sub v)

fun normalise sub = List.map (fn (v, t) => (v, transitive sub t)) sub

end


signature UNIF =
sig

type offset
type subst_offset
val eq : subst_offset -> LTerm.lit -> LTerm.lit -> bool
val unify : subst_offset -> LTerm.lit -> LTerm.lit -> subst_offset option
val unify_contra : subst_offset -> LTerm.lit -> 'a Matrix.contrapositive ->
  (subst_offset * LTerm.clause) option

end

structure Unif : UNIF =
struct

open Tree

type offset = int
type subst_offset = Subst.subst * offset

exception Unify


fun isTriv sub x (Leaf y) = x = y orelse Subst.map false (fn t => isTriv sub x t) sub y
  | isTriv sub x (Branch (_, a)) = if List.exists (isTriv sub x) a then raise Unify else false

fun addSubst sub x t = if isTriv sub x t then sub else Subst.add sub x t

fun unifyTerm (Tree.Branch(f, fa), Tree.Branch(g, ga), sub) = if f <> g then raise Unify else unifyTerms sub (fa, ga)
  | unifyTerm (Leaf x, tm, sub) = Subst.map (addSubst sub x tm) (fn t => unifyTerm (tm, t, sub)) sub x
  | unifyTerm (tm, Leaf x, sub) = unifyTerm (Leaf x, tm, sub)
and unifyTerms sub = ListPair.foldlEq unifyTerm sub

fun unifyLit sub (h1, l1) (h2, l2) = if h1 <> h2 then raise Unify else unifyTerms sub (l1, l2)

fun offsetTermVars off = FTerm.mapVars (fn v => FTerm.V (v + off))
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
fun eqVar sub x (Leaf y) = x = y orelse Subst.map false (eqVar sub x) sub y
  | eqVar _   _ (Branch _) = false

fun eqTerm sub (t1, t2) = case (t1, t2) of
    (Branch(f, fa), Branch(g, ga)) => f = g andalso eqTermList sub (fa, ga)
  | (Leaf x, t2) => Subst.map (eqVar sub x t2) (fn t => eqTerm sub (t, t2)) sub x
  | (t1, Leaf _) => eqTerm sub (t2, t1)
and eqTermList sub = ListPair.allEq (eqTerm sub)

fun eqLit sub (p, pa) (q, qa) = p = q andalso eqTermList sub (pa, qa)


fun eq (sub, _) l1 l2 = eqLit sub l1 l2

fun unify (sub, off) l1 l2 =
  SOME (unifyLit sub l1 l2, off) handle Unify => NONE

fun unify_contra (sub, off) lit contra =
  SOME (unify_contrapos sub off lit contra) handle Unify => NONE

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

val fold_proof : ('a -> 'b) ->
      ('c * 'd -> 'e * 'd) ->
        ('a, 'c) proof_step ->
          'd -> ('b, 'e) proof_step * 'd
val fold_resolution : ('r * 'b -> 's * 'b) -> ('l, 'r) proof_step -> 'b -> ('l, 's) proof_step * 'b
val destResolution : ('a, 'b) proof_step -> ('a * 'b) option

val proof_variables : (LTerm.lit, 'a) proof_step list -> LTerm.variable list

end

(* Connection proof *)
structure CProof : CPROOF =
struct

(* 'l stands for literal, and 'd for the data attached to a resolution step *)
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

fun fold_resolution f (Resolution (l, r)) acc =
      let val (r', acc') = f (r, acc) in (Resolution (l, r'), acc') end
  | fold_resolution _ (Lemma l) acc = (Lemma l, acc)
  | fold_resolution _ (Path  l) acc = (Path l, acc)

fun fold_proof f g p acc = fold_resolution g (map_step f p) acc

fun destResolution (Resolution r) = SOME r
  | destResolution _ = NONE

(* We cannot do eta-conversion here, otherwise we get an ML error:
   "Type variable is free in surrounding scope" *)
fun proof_variables p = List.concat (map (LTerm.litVars o literal) p)

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

val prove : 'b Matrix.matrix -> Unif.subst_offset -> history -> 'a alternative -> ('a, 'b) promise -> 'b proof -> LTerm.clause -> 'a
val prove_default : 'a alternative -> ('a, 'b) promise -> 'b Matrix.matrix -> int -> 'a

end

structure mlCoP : MLCOP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

type path   = LTerm.lit list
type lemmas = LTerm.lit list
type history = path * lemmas * int


type 'a proof_step = (LTerm.lit, Unif.offset * 'a Matrix.contrapositive) CProof.proof_step
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
    let val neglit = LTerm.negateLit lit
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
