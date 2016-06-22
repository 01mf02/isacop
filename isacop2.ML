(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction
*)


signature EXPANSION_TREE =
sig

type bimaps
type term_tree
type lit_tree
val literal_tree : (string * typ) list -> term -> lit_tree
val clauses_of_term : term ->  LTerm.lit list list * (bimaps * lit_tree)

end

structure Expansion_Tree : EXPANSION_TREE =
struct

datatype binop = And | Or
datatype ('a, 'e) quantifier = All of 'a | Ex of 'e
datatype ('a, 'e) treeop = Bin of binop | Quant of ('a, 'e) quantifier

type bimaps = SymIntBimap.bimap * SymIntBimap.bimap
type term_tree = ((string, string) treeop, term) Tree.tree
type lit_tree = ((string, string) treeop, bool * term) Tree.tree

fun get_All (All a) = SOME a | get_All _ = NONE
fun get_Ex  (Ex  e) = SOME e | get_Ex  _ = NONE

fun get_Quant (Bin _) = NONE | get_Quant (Quant q) = SOME q

val free_to_const = map_aterms (fn t => case t of Free x => Const x | _ => t)

fun to_fterm t = case strip_comb t of
    (Free (x, _), []) => FTerm.V x
  | (Const (x, _), args) => FTerm.A (x, map to_fterm args)
  | _ => raise Fail "to_fterm"

fun literal_of_term (@{const "IFOL.Not"} $ t) = (false, t)
  | literal_of_term t = (true, t)


(* Convert a term in negation normal form to a syntax tree, where
   bound variables are replaced by constants with the variable name, and
   free variables are replaced by constants. *)
fun literal_tree quants t = case t of
    Const (@{const_name "IFOL.All"}, _) $ Abs (x, T, t') =>
      Tree.Branch (Quant (All x), [literal_tree ((x, T) :: quants) t'])
  | Const (@{const_name "IFOL.Ex"}, _) $ Abs (x, T, t') =>
      Tree.Branch (Quant (Ex x), [literal_tree ((x, T) :: quants) t'])
  | @{const "IFOL.conj"} $ t1 $ t2 =>
      Tree.Branch (Bin And, map (literal_tree quants) [t1, t2])
  | @{const "IFOL.disj"} $ t1 $ t2 =>
      Tree.Branch (Bin Or, map (literal_tree quants) [t1, t2])
  | t => (map Free quants, free_to_const t) |> subst_bounds |> literal_of_term |> Tree.Leaf


fun get_quant (All a) = a | get_quant (Ex e) = e
fun set_quant (All _) a' = All a' | set_quant (Ex _) e' = Ex e'

fun naturalise_variables (acc as (qi, i)) tree = case tree of
    Tree.Branch (Quant q, nodes) =>
      Tree.Branch (Quant (set_quant q i),
        map (naturalise_variables ((get_quant q, i) :: qi, i+1)) nodes)
  | Tree.Branch (Bin b, nodes) => Tree.Branch (Bin b, map (naturalise_variables acc) nodes)
  | Tree.Leaf (pol, t) => (pol, Tree.subst_all_leafs qi t) |> Tree.Leaf

fun skolemise above tree i = case tree of
     Tree.Branch (Quant (Ex e), nodes) =>
      let val skolem = FTerm.A (i, map FTerm.V above)
          val subst = Tree.map_leafs (apsnd (Tree.subst_some_leafs [(e, skolem)]) #> Tree.Leaf)
          val (nodes', i') = fold_map (skolemise above) (List.map subst nodes) (i+1)
      in  (Tree.Branch (Quant (Ex i), nodes'), i')
      end
  | Tree.Branch (Quant (All a), nodes) =>
      let val (nodes', i') = fold_map (skolemise (a :: above)) nodes i
      in (Tree.Branch (Quant (All a), nodes'), i')
      end
  | Tree.Branch (Bin b, nodes) =>
      let val (nodes', i') = fold_map (skolemise above) nodes i
      in  (Tree.Branch (Bin b, nodes'), i')
      end
  | Tree.Leaf l => (Tree.Leaf l, i)

fun skolem_tree cm tree =
  let val naturalised = tree
    |> Tree.map_leafs (apsnd (to_fterm #> Tree.map_branches (sym_int cm)) #> Tree.Leaf)
    |> naturalise_variables ([], 0)
  in skolemise [] naturalised 0
  end

val tree_path_quants =
  Tree.path_tree [] #> Tree.branches #> List.mapPartial (Utils.option_map_snd get_Quant)

fun skolem (above, x) = (x, List.mapPartial (Option.composePartial (get_All, get_Quant)) above)

val allquantified_variables = List.mapPartial (snd #> get_All)
val skolems = List.mapPartial (Utils.option_map_snd get_Ex #> Option.map skolem)

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


fun mk_skolem_term (f, args) =
  list_comb (Const (f, dummyT), map (fn arg => Free (arg, dummyT)) args)

(* Replace existential free variables by appropriate Skolem terms *)
fun subst_skolems sklm t = case t of
    (Free (x, _)) => Utils.maybe t mk_skolem_term (List.find (fn (x', _) => x = x') sklm)
  | _ => t

fun skolemise_terms sklm = Tree.map_leafs (apsnd (map_aterms (subst_skolems sklm)) #> Tree.Leaf)

fun distinguish_vars t = IsaUtils.rename_abs_distinct t 0 |> fst

fun clauses_of_term t =
  let val st = t |> distinguish_vars |> literal_tree []
      val quants = tree_path_quants st
      val vars = allquantified_variables quants
      val sklm = skolems quants
      val lt = st |> skolemise_terms sklm
      val consts = tree_consts lt []
      val bimaps = (const_bimap sklm consts, var_bimap vars)
      val clauses = lt |> strip_quants |> to_preclauses |> to_clauses bimaps
      val _ = List.app writeln (Tptp.cnf bimaps clauses |> List.map Tptp.cnf_line)
  in (clauses, (bimaps, lt))
  end

end


structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);

val clauses_of_thm = Thm.concl_of #> FOLogic.dest_Trueprop #> Expansion_Tree.clauses_of_term
val matrix_of_clauses = map_index swap #> Matrix.from_list

fun reconstruct_tac _ = (@{print} "Success."; K no_tac)

fun raw_isacop_tac lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})
    val prem = IsaUtils.make_conj_rule prems
    val (matrix, (bimaps, tree)) = clauses_of_thm prem |>> matrix_of_clauses
    val opts = {cut_prove = true, cut_reduce = true, cut_extend = false, max_path_len = lim}
    val hashek = 1
    val start_clause = [(hashek, [])]
    val proof = mlCoP.iterative_prove opts matrix start_clause
    val tac = Utils.maybe (K no_tac) reconstruct_tac proof
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
