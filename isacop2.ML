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

fun tree_consts tree = fold Term.add_const_names (Tree.leafs tree)

structure SymIntBimap = IntBimap (type key = string val ord = fast_string_ord)

val tree_path_quants =
  Tree.path_tree [] #> Tree.branches #> List.mapPartial (Utils.option_map_snd get_Quant)

fun skolem (above, x) = (x, List.mapPartial (Option.composePartial (get_All, get_Quant)) above)

val variables = List.mapPartial (snd #> get_All)
val skolems = List.mapPartial (Utils.option_map_snd get_Ex #> Option.map skolem)

fun literal_of_term (@{const "IFOL.Not"} $ t) = (false, t)
  | literal_of_term t = (true, t)

val literal_tree = Tree.map_leafs (literal_of_term #> Tree.Leaf)



(*
 * Bimap creation:
 * Concatenate Skolem functions with existing tree constants to create SymIntBimap for constants
   (omit negation!)
 * Create SymIntBimap for variables

 * Convert term to FOF:
 * First, handle negation
 * Application \<rightarrow> Look up in constant bimap and transform arguments.
 * Constant \<rightarrow> Look up in constant bimap
 * Free variable \<rightarrow> Look up in variable bimap

 * Tree to Matrix:
 * Convert leaf terms to FOF via bimaps
 * Throw away quantifiers
 * Merge successive \<and> and \<or>.
 *)