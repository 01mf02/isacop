

signature FTERM =
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


structure FTerm : FTERM =
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





fun unify (A(f, fa), A(g, ga)) = if f <> g then raise Unify else ListPair.appEq unify (fa, ga)
  | unify (V(x), tm) = mapSubst (addSubst x tm) (fn t => unify (tm, t)) x
  | unify (tm, V(x)) = unify (V(x), tm)

fun unifyList env l1 l2 = (restore_subst env; ListPair.appEq unify (l1, l2); !sh)

fun unifyLit env (h1, l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unifyList env l1 l2

local
  fun bump_small off (V v) = V(v + off)
    | bump_small off (A(f, a)) = A(f, List.map (bump_small off) a)
in
  (* Unification with renaming of the second argument *)
  fun unify_rename off (t1, t2) = case (t1, t2) of
      (A(f,fa), A(g,ga)) => if f <> g then raise Unify else ListPair.appEq (unify_rename off) (fa, ga)
    | (_, V x) =>
        let val x = x + off
        in  mapSubst (addSubst x t1) (fn t => unify_rename 0 (t1, t)) x
        end
    | (V x, _) => mapSubst (addSubst x (bump_small off t2)) (fn t => unify_rename off (t, t2)) x

  fun unify_rename_subst off l1 l2 env list =
    (restore_subst env;
    ListPair.appEq (unify_rename off) (l1, l2);
    (!sh, List.map (fn (p,l) => (p,List.map (bump_small off) l)) list))
end

local
  fun varEqTerm x (V y) = x = y orelse mapSubst false (varEqTerm x) y
    | varEqTerm _ (A _) = false

  fun eqTerm (tm1, tm2) = case (tm1,tm2) of
      (A(f,fargs),A(g,gargs)) => (f = g andalso ListPair.allEq eqTerm (fargs, gargs))
    | (V(x),_) => mapSubst (varEqTerm x tm2) (fn t => eqTerm (tm1, t)) x
    | (_,V(_)) => eqTerm (tm2, tm1)
in
  fun eqLit env (p,pa) (q,qa) = p = q andalso (restore_subst env; ListPair.allEq eqTerm (pa, qa))
end

val emptySub = []

fun negateLit (i, l) = (~i, l)

fun termVars (V x) = [x]
  | termVars (A (_, args)) = List.concat (List.map termVars args)

end

signature DATABASE =
sig

type contrapositive = (FTerm.term list * FTerm.lit list * int)
val entries : int -> contrapositive list
val hashek : FTerm.predicate

end

structure Database : DATABASE =
struct

(* (lit-arguments, rest-clause, vars) *)
type contrapositive = (FTerm.term list * FTerm.lit list * int)

(* structure PTable = Table(type key = Term.predicate val ord = Term.predicate_ord) *)

(* for every predicate, store list of possible contrapositives *)
val db : (contrapositive list) Array.array = Array.array (10000, [])

(*fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2*)
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)


(* TODO! *)
val hashek = 0
val hashek_lit = (~hashek, [])


fun litVars (_, ts) = List.concat (List.map FTerm.termVars ts)
fun clauseVars cl = List.concat (List.map litVars cl)

fun clauseMaxVar cl = 1 + List.foldl Int.max (~1) (clauseVars cl)

val goal_directed = true


fun clause_prefix_hash cl =
  if not goal_directed andalso
     List.all (fn (p, _) => p < 0) cl andalso
     not (member (op =) cl hashek_lit)
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
    in  List.app_rest [] (contrapositive2db max_var) cl
    end
in
  val axioms2db = List.app cl2db
end

fun entries neglit = Array.sub (db, nat_of_int neglit)
end


signature INTBIMAP =
sig

type left
type right
type bimap

val    empty : int -> bimap
val   insert : (bimap * left) -> (bimap * right)
val  forward : (bimap * left) -> right option
val backward : (bimap * right) -> left option

end

functor IntBimap (Key : KEY) : INTBIMAP =
struct

structure Tab = Table (Key)

type left = Key.key
type right = int

type bimap = {
  forth : int Tab.table
, back : Key.key option Array.array
, maxIndex : int
}

fun empty size = {forth = Tab.empty, back = Array.array (size, NONE), maxIndex = 0}

fun forward ({forth, ...}, x) = Tab.lookup forth x

fun backward ({back, ...} : bimap, i) = Array.sub (back, i)

local
  fun insertNew ({back = b, maxIndex = m, forth = f}, x) =
    (Array.update (b, m, SOME x); ({forth = Tab.update (x,m) f, back = b, maxIndex = m + 1}, m))
in
  fun insert (bm, x) = case forward (bm, x) of SOME i => (bm, i) | NONE => insertNew (bm, x)
end

end


structure Symmap = IntBimap (type key = string val ord = string_ord)


signature ISACOP =
sig

structure Classical: CLASSICAL

end

structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);


val cut1 = true
val cut2 = true
val cut3 = true

(* Some counters *)
val infer = Unsynchronized.ref 0
val depth = Unsynchronized.ref 0
val depthinfer = Unsynchronized.ref 0


fun eq (sub, _) l1 l2 = FTerm.eqLit sub l1 l2;;

fun unify (sub, off) l1 l2 = SOME (FTerm.unifyLit sub l1 l2, off) handle FTerm.Unify => NONE

fun unify_rename (s, off) args1 (args2, rest, vars) =
  let val xx = if vars = 0 then ((FTerm.unifyList s args1 args2, off), rest)
               else let val (s, rest) = FTerm.unify_rename_subst off args1 args2 s rest
                    in  ((s, off + vars), rest)
                    end
  in SOME xx
  end
  handle FTerm.Unify => NONE

datatype proof =
    Lem of FTerm.lit
  | Pat of FTerm.lit
  | Res of (FTerm.lit * FTerm.lit list * FTerm.lit list)
exception Solved of (int list * proof) list


fun prove sub (hist as (path, lem, _)) alt (todo, prf) = fn
    [] => todo (sub, alt, prf)
  | (cl as lit1 :: rest) =>
     let val cont = (fn () => reduce sub lit1 rest hist alt (todo, prf) (FTerm.negateLit lit1) path)
         val nalt = if cut1 then alt else cont
     in  if List.exists (fn x => List.exists (eq sub x) path) cl
           then alt ()
         else if List.exists (eq sub lit1) lem
           then prove sub hist nalt (todo, (fst sub, Lem lit1) :: prf) rest
         else
           reduce sub lit1 rest hist alt (todo, prf) (FTerm.negateLit lit1) path
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
      let val dbs = Database.entries (fst neglit)
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
  (FTerm.emptySub, 0)
  ([], [], lim)
  (fn () => ())
  ((fn (_,_,prf) => raise (Solved prf)), [])
  [(Database.hashek,[])]


val trace = Attrib.setup_config_bool @{binding isacop_trace} (K true);

fun cond_tracing true msg = tracing (msg ())
  | cond_tracing false _ = ();

fun TRACE ctxt rl tac i st =
  (cond_tracing (Config.get ctxt trace) (fn () => Display.string_of_thm ctxt rl); tac i st);

(* Negate goal and move it to first position. *)
(* P1 ==> ... Pn ==> G
   ------------------------------
   P1 ==> ... Pn ==> False ==> ~G
   ------------------------------
   ~G ==> P1 ==> ... Pn ==> False
*)
fun negOfGoal_tac ctxt =
  resolve_tac ctxt @{thms ccontr} THEN' rotate_tac ~1

fun simp_tac_only ctxt ths =
  put_simpset FOL_basic_ss ctxt addsimps ths
  |> TRY oo asm_full_simp_tac

fun destConstFree (Const (c, T)) = (c, T)
  | destConstFree (Free (f, T)) = (f, T)
  | destConstFree x = raise TERM ("destConstFree", [x])

(* Also known as Curry's C combinator. *)
fun flip f x y = f y x

(* TODO! Introduce Skolem functions! *)
fun conv_term tab (Bound b) = (tab, FTerm.V b)
  | conv_term tab t =
  let val (P, args) = strip_comb t
      val Ps = fst (destConstFree P)
      val (tab', P') = Symmap.insert (tab, Ps)
      val (tab'', args') = conv_args tab' args
  in (tab'', FTerm.A (P', args'))
  end
and conv_args tab =
  List.foldl (fn (t, (tab, args)) => conv_term tab t ||> flip cons args) (tab, []) ##> List.rev


fun conv_prop tab (@{const "Not"} $ t) = conv_prop tab t ||> FTerm.negateLit
  | conv_prop tab t =
  let val (tab', FTerm.A (P, args)) = conv_term tab t
  in (tab', (P, args))
  end

fun stripq all ex (Const (@{const_name "All"}, _) $ Abs (x, T, t)) = stripq ((x,T)::all) ex t
  | stripq all ex (Const (@{const_name "Ex"}, _) $ Abs (x, T, t)) = stripq all ((x, T, all)::ex) t
  | stripq all ex t = (all, ex, t)

fun fold_clauses f acc (@{const conj} $ t $ u) = fold_clauses f (f (t, acc)) u
  | fold_clauses f acc t = f (t, acc)

fun fold_clause f acc (@{const disj} $ t $ u) = fold_clause f (f (t, acc)) u
  | fold_clause f acc t = f (t, acc)

fun strip_trueprop (Const (@{const_name "Trueprop"}, _) $ t) = t
  | strip_trueprop t = t

(*fun foldl1 f (x::xs) = List.foldl f x xs

val term_of_clauses =
  List.foldl (fn (cl, acc) => FOLogic.mk_conj (
  foldl1 (fn (t , acc) => FOLogic.mk_disj (t, acc)) cl, acc))*)

fun pretty_term (FTerm.V v) = Pretty.str ("v" ^ Int.toString v)
  | pretty_term (FTerm.A (f, [])) = Pretty.str (Int.toString f)
  | pretty_term (FTerm.A (f, args)) = Pretty.block
      [ Pretty.str (Int.toString f)
      , Pretty.enclose "(" ")" (Pretty.commas (map pretty_term args))
      ]

fun pretty_lit (P, args) = pretty_term (FTerm.A (P, args))
val pretty_clause = Pretty.separate " \<or>" o map pretty_lit
val pretty_clauses = Pretty.block o Pretty.separate " \<and>" o map (Pretty.enclose "(" ")" o pretty_clause)

fun conv_clause tab =
  fold_clause (fn (t, (tab, cl)) => conv_prop tab t ||> flip cons cl) (tab, []) ##> List.rev
fun conv_clauses tab =
  fold_clauses (fn (cl, (tab, cls)) => conv_clause tab cl ||> flip cons cls) (tab, []) ##> List.rev
fun conv_asms tab =
  List.foldl (fn (cls, (tab, asms)) => conv_clauses tab cls ||> flip cons asms) (tab, []) ##> List.rev

fun isacop_focus ({context = ctxt, prems: thm list, asms: cterm list, concl: cterm, ...}) =
  let val _ = map (Syntax.pretty_term ctxt o strip_trueprop o Thm.term_of) asms |> Pretty.writeln_chunks
      val tasms = map (strip_trueprop o Thm.term_of) asms
      val tasm2 = map (#3 o stripq [] []) tasms
      val (symm, _) = Symmap.insert (Symmap.empty 10000, "#")
      val (tab, cls) = conv_asms symm tasm2
      val _ = map pretty_clauses cls |> Pretty.writeln_chunks
  in all_tac
  end

fun raw_isacop ctxt =
  (* K (print_tac ctxt "Initial proof state") THEN' *)
  negOfGoal_tac ctxt THEN'
  (* K (print_tac ctxt "After negation") THEN' *)
  simp_tac_only ctxt @{thms meta_simps IFOL_simps cla_simps} THEN'
  (* K (print_tac ctxt "After simplification") THEN' *)
  simp_tac_only ctxt @{thms prenex_ex prenex_all} THEN'
  (* K (print_tac ctxt "After prenexing") THEN' *)
  simp_tac_only ctxt @{thms precnf_simps} THEN'
  simp_tac_only ctxt @{thms cnf_simps} THEN'
  simp_tac_only ctxt @{thms conj_simps disj_simps} THEN'
  K (print_tac ctxt "After clausification") THEN'
  Subgoal.FOCUS isacop_focus ctxt THEN'
  K all_tac

fun isacop_tac (ctxt:Proof.context) lim =
  let
    val start = Timing.start ();
    val lim = Config.get ctxt depth_limit;
  in
    Object_Logic.atomize_prems_tac ctxt THEN' raw_isacop ctxt
  end;

val _ =
  Theory.setup
    (Method.setup @{binding isacop}
      (Scan.lift (Scan.option Parse.nat) >>
        (fn NONE => SIMPLE_METHOD' o blast_tac
          | SOME lim => (fn ctxt =>
              (writeln ("IsaCoP with lim = " ^ Int.toString lim);
              SIMPLE_METHOD' (isacop_tac ctxt lim)))))
      "lean connection calculus prover");
end

exception Undefined
fun undefined () = raise Undefined
