(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction
*)


signature EXPANSION_TREE =
sig

datatype binop = And | Or
datatype ('a, 'e) quantifier = All of 'a | Ex of 'e
datatype ('a, 'e) treeop = Bin of binop | Quant of ('a, 'e) quantifier
type syntax_tree
type skolem_tree
val syntax_tree : (string * typ) list -> term -> syntax_tree
val skolems_of_terms : term list -> skolem_tree list * SymIntBimap.bimap
val clauses_of_skolem : skolem_tree -> LTerm.lit list list

end

(* TODO: this structure does not contain anything about expansion trees,
   change it to something more appropriate like "syntax tree" *)
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

fun skolem_of_literal literal =
  (*make sure that the integer index of all constants is > 0,
    because only then can we distinguish positive from negative literals*)
  let val cm = SymIntBimap.fromList ("" :: literal_tree_consts literal)
      val natural = literal |> naturalise_consts cm |> naturalise_variables ([], 0)
  in (skolem_tree cm natural |> fst, cm)
  end

fun dest_And (Tree.Branch (Bin And, nodes)) = nodes
  | dest_And _ = raise Fail "dest_And"

val skolems_of_terms =
   map (syntax_tree [] #> literal_tree) #> curry Tree.Branch (Bin And)
   #> skolem_of_literal #>> dest_And

end

signature DESKOLEMISATION =
sig

type ('a, 'f) etree



type thm_id = int
type cls_id = int

val deskolemise :
  thm list -> Expansion_Tree.skolem_tree list ->
  (Unif.subst * (thm_id * cls_id) mlCoP.proof) -> int

(* TODO: Tame this monster. :) *)
val expand_leaf :
  Unif.subst -> (LTerm.variable * term) list * (LTerm.term * term) list ->
  thm * ('e, 'f) etree -> ('e, thm * ('e, 'f) etree) etree

end

structure Deskolemisation : DESKOLEMISATION =
struct

type ('e, 'f) etree =
  (Unif.offset, (LTerm.variable, 'e) Expansion_Tree.treeop, 'f) Edge_Tree.edge_tree

type thm_id = int
type cls_id = int

val xx = List.mapPartial CProof.destResolution #> map snd

val clause_copies = List.mapPartial CProof.destResolution #> map (snd ##> #4)

(* TODO: forgets about clause id -- is this really wanted? *)
val merge_copies =
  map (fn (offset, (th_i, _)) => [(th_i, [offset])]) #> Utils.unionsWith (op =) (op @)

open Expansion_Tree

(* every edge for a variable v consists of a list of offsets such that
   for every two offsets o1 and o2 in the list, v+o1 is equivalent to v+o2 *)

(* make t obsolete and instead reconstruct t by deleting all nodes from expansion tree *)
fun merge_trees eq t offset et = case (et, t) of
    (Edge_Tree.Branch (Quant (All x), nodes), Tree.Branch (Quant (All y), [snode])) =>
      let val _ = @{assert} (x = y)
          val i = find_index (eq x offset o hd o fst) nodes
          val nodes' =
            if i < 0 then ([offset], Edge_Tree.from_tree [offset] snode) :: nodes
            else nth_map i (fn (offsets, enode) =>
              (offset :: offsets, merge_trees eq snode offset enode)) nodes
      in Edge_Tree.Branch (Quant (All x), nodes')
      end
  | (Edge_Tree.Branch (Quant (Ex x), [(e, enode)]), (Tree.Branch (Quant (Ex y), [snode]))) =>
      let val _ = @{assert} (x = y)
      in Edge_Tree.Branch (Quant (Ex x), [(e, merge_trees eq snode offset enode)])
      end
  (* this merge operation is only valid for prenex normal form
     TODO: adapt this case when giving up prenex normal form *)
  | (_, _) => et


fun offsets_tree eq tree offsets = case offsets of
    off1::offs => fold (merge_trees eq tree) offs (Edge_Tree.from_tree [off1] tree)
  | [] => raise Fail "offsets_tree"


fun tau subst (freshs, witnesses) x = undefined ()

fun expand_leaf sub (freshs, witnesses) (th, tree) =
  (case tree of
    Edge_Tree.Branch (Quant (All x), [(off, node)]) =>
      (case Subst.subst_until sub (K false) (FTerm.V (x + off)) of
        Tree.Leaf y => undefined () (* look up variable in freshs or invent new fresh variable *)
      | _ =>
        (case tau sub (freshs, witnesses) (x + off) of
          NONE => undefined () (* do not expand leaf, we miss a witness *)
        | SOME y => undefined () (* instantiate theorem with y *)
        )
      )
  | Edge_Tree.Branch (Quant (All x), nodes) =>
      Edge_Tree.Branch (Quant (All x), map (fn (off, node) => (off,
        Edge_Tree.Leaf (th, Edge_Tree.Branch (Quant (All x), [(off, node)])))) nodes)
  | Edge_Tree.Branch (Quant (Ex x), [(off, node)]) =>
      let val th' = th (* instantiate existential and obtain witness *)
      in  Edge_Tree.Branch (Quant (Ex x), [(off,
            Edge_Tree.Leaf (th', node))])
      end
  )

fun expansion_tree ths (i, tree) = (i, Edge_Tree.Leaf (tree, List.nth (ths, i)))

fun deskolemise ths skolems (subst, proof) =
  let val copies = proof |> clause_copies |> merge_copies
      fun eq x off1 off2 = FUnify.eqTerm subst (FTerm.V (x + off1), FTerm.V (x + off2))
      val copies_trees = map (fn (i, offsets) => (i, offsets_tree eq (List.nth (skolems, i)) offsets)) copies
      val expansion_trees = map (expansion_tree ths) copies_trees
      val expansion_tree = (* Edge_Tree.Branch (Bin And, map (fn tr => ([], tr)) expansion_trees) *) 0
  in 1
  end

end


structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20)

val label_clausess =
  map_index (fn (th_i, th) => map_index (fn (cl_i, cl) => (cl, (th_i, cl_i))) th)
val matrix_of_clausess = label_clausess #> List.concat #> Matrix.from_list

fun reconstruct_tac ths (skolems, cm) (subst, proof) =
  let val _ = Deskolemisation.deskolemise ths skolems (subst, proof)
  in @{print} "Success."; K no_tac
  end

val hashek_true = @{lemma "hashek" by (simp add: hashek_def)}

fun raw_isacop_tac lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})

    val ts = prems |> map (Thm.concl_of #> FOLogic.dest_Trueprop)
    val (skolems, cm) = Expansion_Tree.skolems_of_terms ts
    val clausess = skolems |> map Expansion_Tree.clauses_of_skolem

    val _ = clausess |> List.concat |> Tptp.cnf cm |> List.app (Tptp.show_cnf_line #> writeln)
    val opts = {cut_prove = true, cut_reduce = true, cut_extend = false, max_path_len = lim}
    val start_clause = [(sym_int cm @{const_name hashek}, [])]
    val proof = mlCoP.iterative_prove opts (matrix_of_clausess clausess) start_clause
    val tac = Utils.maybe (K no_tac) (reconstruct_tac prems (skolems, cm)) proof
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
