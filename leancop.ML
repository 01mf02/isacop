signature FTERM =
sig

type variable
type predicate
datatype term = V of variable | A of int * term list
type lit
type clause
type clauses

val negateLit : lit -> lit
val mapVars : (variable -> variable) -> term -> term
val termVars : term -> variable list
val litVars : lit -> variable list
val clauseVars : clause -> variable list

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

fun mapVars f (V x) = V (f x)
  | mapVars f (A (g, args)) = A(g, map (mapVars f) args)

fun termVars (V x) = [x]
  | termVars (A (_, args)) = List.concat (List.map termVars args)

fun litVars (_, ts) = List.concat (List.map termVars ts)

fun clauseVars cl = List.concat (List.map litVars cl)

end


signature MATRIX =
sig

type 'a contrapositive
type 'a matrix
val entries : 'a matrix -> FTerm.lit -> 'a contrapositive list
val insert_clauses : 'a matrix -> (FTerm.clause * 'a) list -> unit
val empty : int -> 'a matrix
val hashek : FTerm.predicate

end

structure Matrix : MATRIX =
struct

val goal_directed = true

(* (lit-arguments, rest-clause, vars) *)
type 'a contrapositive = (FTerm.term list * FTerm.clause * int * 'a)

(* for every predicate, store list of possible contrapositives *)
type 'a matrix = 'a contrapositive list Array.array

(*fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2*)
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)


val hashek = 1
val hashek_lit = (~hashek, [])

fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (FTerm.clauseVars cl)

fun clause_prefix_hash cl =
  if not goal_directed andalso
     List.all (fn (p, _) => p < 0) cl andalso
     not (Option.isSome (List.find (fn lit => lit = hashek_lit) cl))
  then hashek_lit :: cl else cl

(* run function for every element and all other elements of the list *)
fun app_rest _ _ [] = ()
  | app_rest acc f (h :: t) = (f (h, List.revAppend (acc, t)); app_rest (h :: acc) f t)

local
  fun insert_contrapositive mat max_var info ((p,tl), rest) =
    let val n = nat_of_int p
        val nohashek = List.filter (fn l => l <> hashek_lit) rest
    in  Array.update (mat, n, (tl, nohashek, max_var, info) :: Array.sub (mat, n))
    end

  fun insert_clause mat (cl, info) =
    let val max_var = clauseMaxVar cl
        val cl = clause_prefix_hash cl
    in  app_rest [] (insert_contrapositive mat max_var info) cl
    end
in
  fun insert_clauses mat = List.app (insert_clause mat)
end

fun entries mat (p, _) = Array.sub (mat, nat_of_int p)

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
val unify_contra : subst_offset -> FTerm.lit -> 'a Matrix.contrapositive ->
  (subst_offset * FTerm.clause) option

end

structure Unif : UNIF =
struct

open FTerm

type subst_offset = Subst.substitution * int

exception Unify

fun isTriv sub x (V y) = x = y orelse Subst.mapSubst false (fn t => isTriv sub x t) sub y
  | isTriv sub x (A (_, a)) = if List.exists (isTriv sub x) a then raise Unify else false

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
  | (t1, V x) =>
      let val x' = x + off
      in  Subst.mapSubst (addSubst sub x' t1) (fn t => unify_rename 0 (t1, t, sub)) sub x'
      end
  | (V x, t2) => Subst.mapSubst (addSubst sub x (offsetTermVars off t2))
      (fn t => unify_rename off (t, t2, sub)) sub x
and unify_rename_list off = ListPair.foldlEq (unify_rename off)

fun unify_contrapos sub off (_, args1) (args2, rest, vars, _) =
    if vars = 0 then ((unifyTerms sub (args1, args2), off), rest)
    else
      let val sub' = unify_rename_list off sub (args1, args2)
          val rest' = List.map (offsetLitVars off) rest
      in  ((sub', off + vars), rest')
      end

(* True if variable is equivalent to another variable under substitution. *)
fun eqVar sub x (V y) = x = y orelse Subst.mapSubst false (eqVar sub x) sub y
  | eqVar _   _ (A _) = false

fun eqTerm sub (t1, t2) = case (t1, t2) of
    (A(f, fa), A(g, ga)) => f = g andalso eqTermList sub (fa, ga)
  | (V x, t2) => Subst.mapSubst (eqVar sub x t2) (fn t => eqTerm sub (t, t2)) sub x
  | (t1, V _) => eqTerm sub (t2, t1)
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

type path
type lemmas

datatype 'a proof_step =
    Lemma of FTerm.lit
  | Path of FTerm.lit
  | Resolution of (FTerm.lit * path * lemmas * 'a)
type 'a proof = (Subst.substitution * 'a proof_step) list

type history
type 'a alternative
type ('a, 'b) promise

val prove : 'b Matrix.matrix -> Unif.subst_offset -> history -> 'a alternative -> ('a, 'b) promise -> 'b proof -> FTerm.clause -> 'a
val prove_default : 'a alternative -> ('a, 'b) promise -> 'b Matrix.matrix -> int -> 'a

end

structure leanCoP : LEANCOP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

type path   = FTerm.lit list
type lemmas = FTerm.lit list
type history = path * lemmas * int


datatype 'a proof_step =
    Lemma of FTerm.lit
  | Path of FTerm.lit
  | Resolution of (FTerm.lit * path * lemmas * 'a)
type 'a proof = (Subst.substitution * 'a proof_step) list

(* continuation types *)
type 'a alternative = unit -> 'a
type ('a, 'b) promise = Unif.subst_offset -> 'a alternative -> 'b proof -> 'a

fun add_step (sub, _) step prf = (sub, step) :: prf

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
           then prove mat sub hist nalt todo (add_step sub (Lemma lit) prf) rest
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
        let val nprf = add_step sub (Path lit) prf
            (* possibly try to reduce with other literal on path later *)
            fun cont () = reduce mat sub lit rest hist alt todo prf pt
            val nalt = if cut2 then alt else cont
        in prove mat nsub hist nalt todo nprf rest
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
      SOME ((_, _, _, info), (nsub, cla1), et) =>
          let val hist1 = (lit :: path, lem, lim - 1)
              val hist2 = (path, lit :: lem, lim)
              fun todo1 sub alt2 prf = prove mat sub hist2 (if cut3 then alt else alt2) todo prf rest
              (* TODO: record nsub instead of sub in proof? *)
              val prf1  = add_step nsub (Resolution (lit, path, lem, info)) prf
              fun alt1 () = extend mat sub lit rest hist alt todo prf et
          in  prove mat nsub hist1 alt1 todo1 prf1 cla1
          end
    | NONE => alt ()
    end

fun prove_default alt todo mat lim =
  let val sub = (Subst.emptySubst, 0)
      val hist = ([], [], lim)
      val prf = []
      val cla = [(Matrix.hashek, [])]
  in prove mat sub hist alt todo prf cla
  end

end
