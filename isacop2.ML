(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction
*)


signature EXPANSION_TREE =
sig

type syntax_tree
type skolem_tree
val syntax_tree : (string * typ) list -> term -> syntax_tree
val skolem_of_term : term -> skolem_tree * SymIntBimap.bimap
val clauses_of_skolem : skolem_tree -> LTerm.lit list list

end

structure Expansion_Tree : EXPANSION_TREE =
struct

datatype binop = And | Or
datatype ('a, 'e) quantifier = All of 'a | Ex of 'e
datatype ('a, 'e) treeop = Bin of binop | Quant of ('a, 'e) quantifier

type syntax_tree = ((string, string) treeop, term) Tree.tree
type skolem_tree = ((int, int) treeop, bool * LTerm.term) Tree.tree

val free_to_const = map_aterms (fn t => case t of Free x => Const x | _ => t)

(* Convert a term in negation normal form to a syntax tree, where
   bound variables are replaced by constants with the variable name, and
   free variables are replaced by constants. *)
fun syntax_tree quants t = case t of
    Const (@{const_name "IFOL.All"}, _) $ Abs (x, T, t') =>
      Tree.Branch (Quant (All x), [syntax_tree ((x, T) :: quants) t'])
  | Const (@{const_name "IFOL.Ex"}, _) $ Abs (x, T, t') =>
      Tree.Branch (Quant (Ex x), [syntax_tree ((x, T) :: quants) t'])
  | @{const "IFOL.conj"} $ t1 $ t2 =>
      Tree.Branch (Bin And, map (syntax_tree quants) [t1, t2])
  | @{const "IFOL.disj"} $ t1 $ t2 =>
      Tree.Branch (Bin Or, map (syntax_tree quants) [t1, t2])
  | t => (map Free quants, free_to_const t) |> subst_bounds |> Tree.Leaf


fun literal_of_term (@{const "IFOL.Not"} $ t) = (false, t)
  | literal_of_term t = (true, t)

fun to_fterm t = case strip_comb t of
    (Free (x, _), []) => FTerm.V x
  | (Const (x, _), args) => FTerm.A (x, map to_fterm args)
  | _ => raise Fail "to_fterm"

val literal_tree = Tree.map_leafs (literal_of_term #> apsnd to_fterm)

val literal_tree_consts =
  Tree.leafs #> map (Tree.branches o snd) #> List.concat #> distinct (op =)


fun get_quant (All a) = a | get_quant (Ex e) = e
fun set_quant (All _) a' = All a' | set_quant (Ex _) e' = Ex e'

fun naturalise_consts cm = Tree.map_leafs (apsnd (Tree.map_branches (sym_int cm)))

fun naturalise_variables (acc as (qi, i)) tree = case tree of
    Tree.Branch (Quant q, nodes) =>
      Tree.Branch (Quant (set_quant q i),
        map (naturalise_variables ((get_quant q, i) :: qi, i+1)) nodes)
  | Tree.Branch (Bin b, nodes) => Tree.Branch (Bin b, map (naturalise_variables acc) nodes)
  | Tree.Leaf (pol, t) => (pol, Tree.subst_all_leafs qi t) |> Tree.Leaf

fun skolemise above tree i = case tree of
     Tree.Branch (Quant (Ex e), nodes) =>
      let val skolem = FTerm.A (i, map FTerm.V above)
          val subst = Tree.map_leafs (apsnd (Tree.subst_some_leafs [(e, skolem)]))
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

fun skolem_tree cm = Utils.flip (skolemise []) (SymIntBimap.size cm + 1)

fun strip_quants (Tree.Branch (Quant _, [t])) = strip_quants t
  | strip_quants (Tree.Branch (b, nodes)) = Tree.Branch (b, map strip_quants nodes)
  | strip_quants t = t

val to_clauses =
  Tree.debinarize (Bin And) #> map (Tree.debinarize (Bin Or) #> map (Tree.leaf_of #> LTerm.toLit))

val clauses_of_skolem = strip_quants #> to_clauses

fun skolem_of_term t =
  let val literal = t |> syntax_tree [] |> literal_tree
      val cm = literal |> literal_tree_consts |> SymIntBimap.fromList
      val natural = literal |> naturalise_consts cm |> naturalise_variables ([], 0)
  in (skolem_tree cm natural |> fst, cm)
  end

end


structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);

val clauses_of_thm = Thm.concl_of #> FOLogic.dest_Trueprop
  #> Expansion_Tree.skolem_of_term #>> Expansion_Tree.clauses_of_skolem
val matrix_of_clauses = map_index swap #> Matrix.from_list

fun reconstruct_tac _ = (@{print} "Success."; K no_tac)

val hashek_true = @{lemma "hashek" by (simp add: hashek_def)}

fun raw_isacop_tac lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})
    val prem = IsaUtils.make_conj_rule prems
    val (matrix, cm) = clauses_of_thm prem |>> matrix_of_clauses
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
