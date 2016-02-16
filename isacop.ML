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

fun empty size = {forth = Tab.empty, back = Array.array (size, NONE), maxIndex = 1}

fun forward ({forth, ...}, x) = Tab.lookup forth x

fun backward ({back, ...} : bimap, i) = Array.sub (back, i)

local
  fun insertNew ({back = b, maxIndex = m, forth = f}, x) =
    (Array.update (b, m, SOME x); ({forth = Tab.update (x,m) f, back = b, maxIndex = m + 1}, m))
in
  fun insert (bm, x) = case forward (bm, x) of SOME i => (bm, i) | NONE => insertNew (bm, x)
end

end

structure IsaCoP =
struct

structure Symmap = IntBimap (type key = string val ord = string_ord)

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);
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
      val (symm, _) = Symmap.insert (Symmap.empty 10000, @{const_name hashek})
      val (tab, cls) = conv_asms symm tasm2 ||> List.concat
      val _ = pretty_clauses cls |> Pretty.writeln
      val _ = leanCoP.set_matrix cls
      val prf = leanCoP.prove_some 10
  in all_tac
  end

fun raw_isacop ctxt =
  (* introduce hashek into goal *)
  resolve_tac ctxt @{thms hashekE} THEN'
  K (print_tac ctxt "Initial proof state") THEN'
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
