(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction
*)

datatype binop = And | Or
datatype ('a, 'e) quantifier = All of 'a | Ex of 'e
datatype ('a, 'e) treeop = Bin of binop | Quant of ('a, 'e) quantifier

fun get_All (All a) = SOME a | get_All _ = NONE
fun get_Ex  (Ex  e) = SOME e | get_Ex  _ = NONE

fun get_Quant (Bin _) = NONE | get_Quant (Quant q) = SOME q

fun syntax_tree quants t = case t of
    Const (@{const_name "IFOL.All"}, _) $ Abs (x, T, t') =>
      Tree.Branch (Quant (All x), [syntax_tree ((x, T) :: quants) t'])
  | Const (@{const_name "IFOL.Ex"}, _) $ Abs (x, T, t') =>
      Tree.Branch (Quant (Ex x), [syntax_tree ((x, T) :: quants) t'])
  | @{const "IFOL.conj"} $ t1 $ t2 =>
      Tree.Branch (Bin And, map (syntax_tree quants) [t1, t2])
  | @{const "IFOL.disj"} $ t1 $ t2 =>
      Tree.Branch (Bin Or, map (syntax_tree quants) [t1, t2])
  | t => Tree.Leaf (quants, t)

val free_to_const = map_aterms (fn t => case t of Free x => Const x | _ => t)

fun transform_leaf leaf = leaf |>> map Free ||> free_to_const |> subst_bounds |> Tree.Leaf

structure SymIntBimap = IntBimap (type key = string val ord = fast_string_ord)
fun sym_int m x = SymIntBimap.forward (m, x) |> Option.valOf
fun int_sym m x = SymIntBimap.backward (m, x) |> Option.valOf

val tree_path_quants =
  Tree.path_tree [] #> Tree.branches #> List.mapPartial (Utils.option_map_snd get_Quant)

fun skolem (above, x) = (x, List.mapPartial (Option.composePartial (get_All, get_Quant)) above)

val allquantified_variables = List.mapPartial (snd #> get_All)
val skolems = List.mapPartial (Utils.option_map_snd get_Ex #> Option.map skolem)

fun literal_of_term (@{const "IFOL.Not"} $ t) = (false, t)
  | literal_of_term t = (true, t)

val literal_tree = Tree.map_leafs (literal_of_term #> Tree.Leaf)

fun tree_consts tree = fold Term.add_const_names (Tree.leafs tree |> map snd)

val var_bimap = SymIntBimap.fromList

(* Make sure that hashek is assigned the integer "1", because it is defined
   that way in mlCoP. *)
fun const_bimap skolems consts =
  SymIntBimap.fromList (@{const_name "hashek"} :: map fst skolems @ consts)

fun to_lterm (bimaps as (cm, vm)) t = case strip_comb t of
    (Free (x, _), []) => FTerm.V (sym_int vm x)
  | (Const (x, _), args) => FTerm.A (sym_int cm x, map (to_lterm bimaps) args)
  | _ => raise Fail "to_lterm"

fun strip_quants (Tree.Branch (Quant _, [t])) = strip_quants t
  | strip_quants (Tree.Branch (b, nodes)) = Tree.Branch (b, map strip_quants nodes)
  | strip_quants t = t

val to_preclauses = Tree.debinarize (Bin And) #> map (Tree.debinarize (Bin Or) #> map Tree.leaf_of)

fun to_clauses bimaps = (map o map) (apsnd (to_lterm bimaps) #> LTerm.toLit)

structure Tptp =
struct

val prepend = curry (op ^)
fun enclose start stop s = start ^ s ^ stop
val parens = enclose "(" ")"
val normalise = String.translate (fn c => if c = #"." then "_" else String.str c)
fun print_lterm (cm, vm) =
  Tree.to_string (prepend "c" o normalise o int_sym cm, prepend "X" o int_sym vm)
fun print_pred (cm, _) p = if p > 0 then int_sym cm p else "~" ^ int_sym cm (~p)
val atom_of_lit = apfst Int.abs
fun lit_prefix (p, _) = if p > 0 then "" else "~ "

fun print_lit bimaps lit = lit_prefix lit ^ (lit |> atom_of_lit |> Tree.Branch |> print_lterm bimaps)
fun print_clause bimaps = parens o String.concatWith " | " o List.map (print_lit bimaps)
fun print_clauses bimaps = String.concatWith "\n" o List.map (print_clause bimaps)
fun print_cnf bimaps =
  map_index (fn (i, cl) => ["ax" ^ Int.toString i, "axiom", print_clause bimaps cl])
val hashek_cnf = ["hashek", "negated_conjecture", "(c" ^ normalise @{const_name hashek} ^ ")"]
fun cnf bimaps cls = hashek_cnf :: print_cnf bimaps cls
val cnf_line = enclose "cnf" "." o parens o String.concatWith ", "

end


fun mk_skolem_term (f, args) =
  list_comb (Const (f, dummyT), map (fn arg => Free (arg, dummyT)) args)

(* Replace existential free variables by appropriate Skolem terms *)
fun subst_skolems sklm t = case t of
    (Free (x, _)) => Utils.maybe t mk_skolem_term (List.find (fn (x', _) => x = x') sklm)
  | _ => t

fun skolemise_terms sklm = Tree.map_leafs (map_aterms (subst_skolems sklm) #> Tree.Leaf)

fun distinguish_vars t = IsaUtils.rename_abs_distinct t 0 |> fst

fun clauses_of_term t =
  let val st = t |> distinguish_vars |> syntax_tree [] |> Tree.map_leafs transform_leaf
      val quants = tree_path_quants st
      val vars = allquantified_variables quants
      val sklm = skolems quants
      val lt = st |> skolemise_terms sklm |> literal_tree
      val consts = tree_consts lt []
      val bimaps = (const_bimap sklm consts, var_bimap vars)
      val clauses = lt |> strip_quants |> to_preclauses |> to_clauses bimaps
      val _ = List.app writeln (Tptp.cnf bimaps clauses |> List.map Tptp.cnf_line)
  in (clauses, (bimaps, lt))
  end

structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);

val clauses_of_thm = Thm.concl_of #> FOLogic.dest_Trueprop #> clauses_of_term
val matrix_of_clauses = map_index swap #> Matrix.from_list

fun reconstruct_tac _ = (@{print} "Success."; K no_tac)

fun raw_isacop_tac lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})
    val prem = IsaUtils.make_conj_rule prems
    val (matrix, (bimaps, tree)) = clauses_of_thm prem |>> matrix_of_clauses
    val opts = {cut_prove = true, cut_reduce = true, cut_extend = false, max_path_len = lim}
    val tac = Utils.maybe (K no_tac) reconstruct_tac (mlCoP.iterative_prove opts matrix)
  in HEADGOAL tac
  end)

val hashek_and = @{lemma "P \<and> hashek \<Longrightarrow> P" by (simp add: hashek_def)}

fun pre_isacop_tac ctxt =
  resolve_tac ctxt [hashek_and] THEN'
  K (print_tac ctxt "Initial proof state") THEN'
  IsaUtils.neg_goal_tac ctxt THEN'
  IsaUtils.pnf_cnf_tac ctxt THEN'
  K (print_tac ctxt "After clausification")

fun isacop_method (lim, ths) ctxt facts =
  let val lim' = Option.getOpt (lim, Config.get ctxt depth_limit)
  in HEADGOAL (pre_isacop_tac ctxt THEN' raw_isacop_tac lim' ctxt)
  end

val _ =
  Theory.setup
    (Method.setup @{binding isacop}
      (Scan.lift (Scan.option Parse.nat) -- Attrib.thms >> (METHOD oo isacop_method))
      "lean connection calculus prover")

end
