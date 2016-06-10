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

val tree_path_quants =
  Tree.path_tree [] #> Tree.branches #> List.mapPartial (Utils.option_map_snd get_Quant)

fun skolem (above, x) = (x, List.mapPartial (Option.composePartial (get_All, get_Quant)) above)

val variables = List.mapPartial (snd #> get_All)
val skolems = List.mapPartial (Utils.option_map_snd get_Ex #> Option.map skolem)

fun literal_of_term (@{const "IFOL.Not"} $ t) = (false, t)
  | literal_of_term t = (true, t)

val literal_tree = Tree.map_leafs (literal_of_term #> Tree.Leaf)

fun tree_consts tree = fold Term.add_const_names (Tree.leafs tree |> map snd)

val var_bimap = SymIntBimap.fromList

fun const_bimap skolems consts = SymIntBimap.fromList ("hashek" :: map fst skolems @ consts)

fun to_lterm (bimaps as (cm, vm)) t = case strip_comb t of
    (Free (x, _), []) => FTerm.V (sym_int vm x)
  | (Const (x, _), args) => FTerm.A (sym_int cm x, map (to_lterm bimaps) args)
  | _ => raise Fail "to_lterm"

fun strip_quants (Tree.Branch (Quant _, [t])) = strip_quants t
  | strip_quants (Tree.Branch (b, nodes)) = Tree.Branch (b, map strip_quants nodes)
  | strip_quants t = t

val to_preclauses = Tree.debinarize (Bin And) #> map (Tree.debinarize (Bin Or) #> map Tree.leaf_of)

fun to_clauses bimaps = (map o map) (apsnd (to_lterm bimaps) #> LTerm.toLit)

fun clauses_of_term t =
  let val st = t |> syntax_tree [] |> Tree.map_leafs transform_leaf
      val quants = tree_path_quants st
      val vars = variables quants
      val sklm = skolems quants
      val lt = literal_tree st
      val consts = tree_consts lt []
      val bimaps = (const_bimap sklm consts, var_bimap vars)
      val clauses = lt |> strip_quants |> to_preclauses |> to_clauses bimaps
  in (clauses, (bimaps, lt))
  end

structure IsaCop =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);

val clauses_of_thm = Thm.concl_of #> FOLogic.dest_Trueprop #> clauses_of_term
val matrix_of_clauses = map (rpair ()) #> Matrix.from_list

fun raw_isacop lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})
    val prem = IsaUtils.make_conj_rule prems
    val (matrix, (bimaps, tree)) = clauses_of_thm prem |>> matrix_of_clauses
    val tac = case mlCoP.maybe_prove matrix lim of
        SOME p => (@{print} "Success."; K no_tac)
      | NONE => (@{print} "No connection proof found."; K no_tac)
  in HEADGOAL tac
  end)

fun isacop_method (lim, ths) ctxt facts =
  let val lim' = Option.getOpt (lim, Config.get ctxt depth_limit)
  in HEADGOAL (raw_isacop lim' ctxt)
  end

val _ =
  Theory.setup
    (Method.setup @{binding isacop}
      (Scan.lift (Scan.option Parse.nat) -- Attrib.thms >> (METHOD oo isacop_method))
      "lean connection calculus prover")

end
