(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction

TODO:

- Implement path rule.
- Fix non-found lemma (in lemma_ex).
*)


(** General helpers **)

fun hd_tl (hd :: tl) = (hd, tl)
  | hd_tl _ = raise Fail "hd_tl"

fun pair_list (x, y) = [x, y]


fun flip f x y = f y x

fun valOf' str opt = case opt of SOME s => s | _ => raise Fail str

fun do_while f (continue, acc) = if continue then do_while f (f acc) else acc

fun elim_equals eq l =
  let fun f x (prev, i) = case AList.lookup eq prev x of
      SOME j => (j, (prev, i))
    | NONE => (i, ((x, i) :: prev, i + 1))
  in fold_map f l ([], 0)
  end;

val _ = @{assert}
 (elim_equals (op =) ["a", "b", "a", "c"] =
  ([0, 1, 0, 2], ([("c", 2), ("b", 1), ("a", 0)], 3)))


(** Isabelle-related helpers **)

fun simp_only_tac ctxt ths =
  put_simpset FOL_basic_ss ctxt addsimps ths
  |> TRY oo asm_full_simp_tac

fun inst_spec ct th =
  th RS (Thm.instantiate' [SOME (Thm.ctyp_of_cterm ct)] [NONE, SOME ct] @{thm spec})

fun obtain_exists th =
  Obtain.result (fn ctxt => eresolve_tac ctxt @{thms exE} 1) [th] #>>
  (fn (x, th') => (the_single x, the_single th'))

fun atomize_thm ctxt thm =
  let
    val thm' = forall_intr_vars thm
    val thm'' = thm' |> Thm.cprop_of |> Object_Logic.atomize ctxt
    val same = Thm.concl_of #> Logic.dest_equals #> op =
  (* to prevent loop, rewrite only if atomizing changed something *)
  in if same thm'' then thm' else Simplifier.rewrite_rule ctxt [thm''] thm'
  end

fun map_bndvars f = map_aterms (fn t => case t of Bound i => f i | _ => t)

fun th_cterm_of th = Thm.global_cterm_of (Thm.theory_of_thm th)

fun rename_distinct t i =
  case t of
    Abs (x, T, t1) =>
      let val (t1', i') = rename_distinct t1 (i+1)
      in (Abs (x ^ Int.toString i, T, t1'), i')
      end
  | t1 $ t2 =>
      let val (t1', (t2', i')) = i |> rename_distinct t1 ||> rename_distinct t2
      in (t1' $ t2', i')
      end
  | _ => (t, i)

(*TODO: use this in preprocessing*)
fun rename_distinct_th th i =
  let val (t', i') = rename_distinct (Thm.prop_of th) i
  in (Thm.rename_boundvars (Thm.prop_of th) t' th, i')
  end

val rename_distinct_th_test =
  let val th = Thm.assume @{cprop "\<forall>x. \<forall>y. P(x)"}
      val result = rename_distinct_th th 0 |>> Thm.prop_of
  in @{assert} (result = (@{prop "\<forall>x0. \<forall>y1. P(x0)"}, 2))
  end

fun remove_trivial_prem th =
  let
    val prem = case Thm.prems_of th of x::_ => x | _ => raise Fail "no premises"
    val (l, r) = Logic.dest_implies prem
    val _ = @{assert} (l = r)
    val triv = Thm.trivial (th_cterm_of th l)
  in Thm.implies_elim th triv
  end

(* Versions of FOL.conj_mono & FOL.disj_mono with Pure implications *)
val conj_mono = @{lemma "(P \<Longrightarrow> P') \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> P \<and> Q \<Longrightarrow> P' \<and> Q'" by auto}
val disj_mono = @{lemma "(P \<Longrightarrow> P') \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> P \<or> Q \<Longrightarrow> P' \<or> Q'" by auto}

fun conj_mono_rule conj ths = (conj_mono OF ths @ [conj]) |> funpow 2 remove_trivial_prem
fun disj_mono_rule conj ths = (disj_mono OF ths @ [conj]) |> funpow 2 remove_trivial_prem

val conj_mono_rule_test =
  let val res = conj_mono_rule
    (Thm.assume @{cprop "a \<and> b"})
    [Thm.assume @{cprop "a \<Longrightarrow> c"},
     Thm.assume @{cprop "b \<Longrightarrow> d"}]
  in @{assert} (Thm.prop_of res = @{prop "c \<and> d"})
  end

fun make_conj_rule [] = @{thm TrueI}
  | make_conj_rule (th :: []) = th
  | make_conj_rule (th :: ths) = @{thm conjI} OF [th, make_conj_rule ths]

val make_conj_rule_test =
  let val ths = map Thm.assume [@{cprop P}, @{cprop Q}]
  in @{assert} (Thm.prop_of (make_conj_rule ths) = @{prop "P \<and> Q"})
  end

fun dest_conj_rule th =
  case Thm.prop_of th |> FOLogic.dest_Trueprop of @{const conj} $ _ $ _  =>
    (@{thm conjunct1} OF [th]) :: dest_conj_rule (@{thm conjunct2} OF [th])
  | _ => [th]

val dest_conj_rule_test =
  let val th = Thm.assume @{cprop "a \<and> b \<and> c"}
      val result = dest_conj_rule th |> map (FOLogic.dest_Trueprop o Thm.prop_of)
  in @{assert} (result = [@{term "a::o"}, @{term "b::o"}, @{term "c::o"}])
  end

fun prove_with_tac t tac = Goal.prove @{context} [] [] t (K (tac @{context} 1))


val hashek_and = @{lemma "P \<and> hashek \<Longrightarrow> P" by (simp add: hashek_def)}


(* Negate goal and move it to first position. *)
(* P1 ==> ... Pn ==> G
   ------------------------------
   P1 ==> ... Pn ==> False ==> ~G
   ------------------------------
   ~G ==> P1 ==> ... Pn ==> False
*)
fun neg_goal_tac ctxt =
  resolve_tac ctxt @{thms ccontr} THEN' rotate_tac ~1

fun clausify_tac ctxt =
  simp_only_tac ctxt @{thms meta_simps IFOL_simps cla_simps} THEN'
  simp_only_tac ctxt @{thms prenex_ex prenex_all} THEN'
  simp_only_tac ctxt @{thms precnf_simps} THEN'
  simp_only_tac ctxt @{thms cnf_simps} THEN'
  simp_only_tac ctxt @{thms conj_simps disj_simps}


structure Termmap = IntBimap (type key = term val ord = Term_Ord.fast_term_ord)


structure Tree =
struct

datatype ('b, 'l) tree = Branch of ('b * ('b, 'l) tree list) | Leaf of 'l

type 't monoid_tree = ('t list -> 't, 't) tree

fun deep (Branch (f, nodes)) = map deep nodes |> f
  | deep (Leaf l) = l

type ('b, 'l, 'e) edge_tree = ('b * 'e, 'l * 'e) tree

(*TODO: write fold_map_edge_tree*)

fun map_tree f (Leaf l) = f l
  | map_tree f (Branch (b, nodes)) = Branch (b, map (map_tree f) nodes)

fun fold_map_tree f (Branch (b, nodes)) y =
      let val (nodes', y') = fold_map (fold_map_tree f) nodes y
      in (Branch (b, nodes'), y')
      end
  | fold_map_tree f (Leaf l) y = f l y

end



signature QUANTIFIER =
sig

datatype ('a, 'e) quantifier = All of 'a | Ex of 'e
type iquantifier

val strip_quants : iquantifier list -> term -> iquantifier list * term
val zip_quants : ('a, 'b) quantifier list -> ''c list * ''d list -> (''c, ''d) quantifier list

end

structure Quantifier : QUANTIFIER =
struct

datatype ('a, 'e) quantifier = All of 'a | Ex of 'e

(* (name, type) *)
type sty = string * typ
type iquantifier = (sty, sty) quantifier

fun quant_of @{const_name "All"} = SOME All
  | quant_of @{const_name "Ex" } = SOME Ex
  | quant_of _ = NONE

fun strip_quants quants (Const (quant, _) $ Abs (x, T, t)) =
      (case quant_of quant of
        SOME q => strip_quants ((q (x, T)) :: quants) t
      | NONE => (List.rev quants, t))
  | strip_quants quants t = (List.rev quants, t)

fun map_quant (fa, _) (All a) = fa a
  | map_quant (_, fe) (Ex  e) = fe e

fun zip_quants quants (all, ex) =
  let
    fun fa (hd::tl, ex) = (All hd, (tl, ex))
      | fa _ = raise Fail "too few all quantifiers"
    fun fe (all, hd :: tl) = (Ex hd, (all, tl))
      | fe _ = raise Fail "too few exists quantifiers"
    val (quants', rest) = fold_map (map_quant (K fa, K fe)) quants (all, ex)
    val _ = @{assert} (rest = ([], []))
  in quants'
  end

end


datatype binop = And | Or
datatype ('a, 'e) treeop = Bin of binop | Quant of ('a, 'e) Quantifier.quantifier

fun syntax_tree_of_tm tm = case tm of
    @{const "IFOL.conj"} $ t1 $ t2 => Tree.Branch (Bin And, map syntax_tree_of_tm [t1, t2])
  | @{const "IFOL.disj"} $ t1 $ t2 => Tree.Branch (Bin Or , map syntax_tree_of_tm [t1, t2])
  | Const (@{const_name "All"}, _) $ Abs (_, _, t) =>
      Tree.Branch (Quant (Quantifier.All ()), [syntax_tree_of_tm t])
  | Const (@{const_name "Ex"}, _) $ Abs (_, _, t) =>
      Tree.Branch (Quant (Quantifier.Ex  ()), [syntax_tree_of_tm t])
  | t => Tree.Leaf t 


structure Edge_Tree =
struct

datatype ('b, 'e, 'l) edge_tree =
    Branch of ('b * ('e * ('b, 'e, 'l) edge_tree) list)
  | Leaf of 'l



end




structure Expansion_Tree =
struct

fun normal_leaf th = Tree.Leaf (th, NONE)

(*TODO: find better name.*)
fun xxx f tms =
  let val ass = map Thm.assume tms
  in Tree.Branch (map2 Thm.implies_intr tms #> f, map normal_leaf ass)
  end

(*TODO: stub*)
fun get_univ ws inst = inst

fun step sub (th, inst) (acc as (ctxt, ws)) =
  case Thm.concl_of th of
    @{const "IFOL.conj"} $ t1 $ t2 => (xxx (conj_mono_rule th) (map (th_cterm_of th) [t1, t2]), acc)
  | @{const "IFOL.disj"} $ t1 $ t2 => (xxx (disj_mono_rule th) (map (th_cterm_of th) [t1, t2]), acc)
  | Const (@{const_name "All"}, _) $ Abs (x, T, t) =>
      (case inst of
        NONE => (Tree.Branch (make_conj_rule, map (curry Tree.Leaf th) (sub x)), acc)
      | SOME inst =>
          (case get_univ ws inst of
            NONE => (normal_leaf th, acc)
          | SOME x' => (normal_leaf (inst_spec x' th), acc)
          )
      )
  | Const (@{const_name "Ex"}, _) $ Abs (x, T, t) =>
      let val ((witness, th'), ctxt') = obtain_exists th ctxt
      (*Problem: at this point, we need as context the information which universal quantifiers
        are above the current leaf, to uniquely identify the witness*)
      in (normal_leaf th', (ctxt', (x, witness) :: ws))
      end
  | _ => (normal_leaf th, acc)

val deep = Tree.map_tree fst #> Tree.deep

end


signature SKOLEMISATION =
sig

type skolemised

val skolem_function : string -> term
val skolemise_ths : thm list -> skolemised list

end

structure Skolemisation : SKOLEMISATION =
struct

type skolemised =
{ quantifiers : Quantifier.iquantifier list
, skolems : string list
, skolemised : term
}

fun skolem_function name = Const (name, dummyT)

fun skolemise_term all ex ((quant, quanti) :: quants) t ctxt =
  (case quant of
    Quantifier.All _ => skolemise_term (quanti :: all) ex quants t ctxt
  | Quantifier.Ex (x, _) =>
      let val (name, ctxt') = Name.variant (Name.skolem x) ctxt
          val skolem = list_comb (skolem_function name, List.map Bound (rev all))
          val t' = map_bndvars (fn i => if i = quanti then skolem else Bound i) t
      in skolemise_term all (name :: ex) quants t' ctxt'
      end)
  | skolemise_term _ ex [] t ctxt = ((rev ex, t), ctxt)

fun skolemise_th th ctxt =
  let
    val t = th |> Thm.concl_of |> FOLogic.dest_Trueprop
    val (quants, bare) = Quantifier.strip_quants [] t
    val quants' = quants ~~ ((List.length quants - 1) downto 0)
    val ((ex, sk), ctxt') = skolemise_term [] [] quants' bare ctxt
  in ({ quantifiers = quants, skolems = ex, skolemised = sk }, ctxt')
  end

fun skolemise_ths ths = fold_map skolemise_th ths Name.context |> fst

end


structure FOLogic =
struct

open FOLogic
fun dest_disj (Const (@{const_name disj}, _) $ t $ t') = t :: dest_disj t'
  | dest_disj t = [t];

end


structure Isa_to_CoP =
struct

fun conv_term (Bound b) tab = (FTerm.V b, tab)
  | conv_term t tab =
  let val (P, args) = strip_comb t
      val (tab', P') = Termmap.insert (tab, P)
      val (args', tab'') = fold_map conv_term args tab'
  in (FTerm.A (P', args'), tab'')
  end

fun conv_prop (@{const "Not"} $ t) tab = conv_prop t tab |>> FTerm.negateLit
  | conv_prop t tab = conv_term t tab |>> FTerm.destApp

val conv_clause = fold_map conv_prop
val conv_clauses = fold_map conv_clause
val conv_asms = fold_map conv_clauses

val clausify = map FOLogic.dest_disj o FOLogic.dest_conj

fun convert_terms tab = map clausify #> flip conv_asms tab

end


structure FTerm =
struct

open FTerm

fun pretty_term (FTerm.V v) = Pretty.str ("v" ^ Int.toString v)
  | pretty_term (FTerm.A (f, [])) = Pretty.str (Int.toString f)
  | pretty_term (FTerm.A (f, args)) = Pretty.block
      [ Pretty.str (Int.toString f)
      , Pretty.enclose "(" ")" (Pretty.commas (map pretty_term args))
      ]

fun pretty_lit (P, args) = pretty_term (FTerm.A (P, args))
val pretty_clause = Pretty.separate " \<or>" o map pretty_lit
val pretty_clauses = Pretty.block o Pretty.separate " \<and>" o
  map (Pretty.enclose "(" ")" o pretty_clause)

end

structure CProof =
struct

open CProof
open Pretty

fun pretty_step (fl, _)  (Path  t) = block [str "Path: " , fl t]
  | pretty_step (fl, _)  (Lemma t) = block [str "Lemma: ", fl t]
  | pretty_step (fl, fr) (Resolution (t, th)) = block [str "Resolution: ", fl t, str ", ", fr th]

fun pretty_proof f = map (pretty_step f) #> chunks

end

structure IProof =
struct

type clause_no = int
type fproof = (clause_no * (thm * Skolemisation.skolemised)) mlCoP.proof
type iproof = (term, thm) CProof.proof

fun pretty_iproof ctxt = CProof.pretty_proof (Syntax.pretty_term ctxt, Thm.pretty_thm ctxt)

end


signature INSTANTIATION =
sig

type conv_fun

val instantiate_proof :
  Proof.context -> Termmap.bimap * Skolemisation.skolemised list ->
  Subst.subst * IProof.fproof -> Proof.context * conv_fun * thm list

end

structure Instantiation : INSTANTIATION =
struct

type conv_fun = FTerm.constant * FTerm.term list -> term

fun unskolemise tab x =
  Termmap.forward (tab, Skolemisation.skolem_function x) |> valOf' "unskolemise"

fun conv_sym tab sym = Termmap.backward (tab, sym) |> valOf' ("conv_sym: " ^ Int.toString sym)


fun self_subst off vars = map (fn v => (v, FTerm.V v)) (off upto off + vars - 1)

val subst_ord = prod_ord int_ord (K EQUAL)

fun get_subs off vars =
  filter (fn (v, _) => off <= v andalso v < off + vars)
  (*if substitution does not contain binding for variable, create one to itself*)
  #> union (is_equal o subst_ord) (self_subst off vars)
  #> sort subst_ord #> rev


exception Unsubst

(*TODO: Perhaps we need to do more here? (Making type most general?)
        See Isar Implementation manual from 2016, p. 119 *)
(* This version does not work inside a proof, because variant_fixes creates Skolem terms
   à la "x1__", which subsequently cannot be read as terms. *)
fun invent_universals ctxt vars =
  let
    val names = map (fn v => "x" ^ Int.toString v) vars
    val (vars, ctxt') = Variable.variant_fixes names ctxt |> tap @{print warning}
  in (Syntax.read_terms ctxt' vars, ctxt')
  end

(* 
(* TODO: This function could create clashing variables? *)
fun invent_universals ctxt vars =
  (map (fn v => "x" ^ Int.toString v) vars |> Syntax.read_terms ctxt, ctxt)
*)

fun convert_term maps t (acc as (_, tmmap)) =
      case AList.lookup (op =) tmmap t of
        SOME t' => (t', acc)
      | NONE => convert_fresh_term maps t acc
and convert_fresh_term _ (FTerm.V v) (ctxt, tmmap) =
      let val (t', ctxt') = invent_universals ctxt [v] |>> the_single
      in (t', (ctxt', (FTerm.V v, t') :: tmmap))
      end
  | convert_fresh_term (maps as (symmap, skolems)) (FTerm.A (f, fa)) acc =
      let val f' = conv_sym symmap f
          val _ = case fst (strip_comb f') of
              (*uh-oh, we encountered a Skolem symbol for which we have not
                instantiated a witness yet, so we delay converting this term by
                throwing an exception, hopefully getting the witness later*)
              Const (fh, _) => if member (op =) skolems fh then raise Unsubst else ()
            | _ => ();
          val (args', acc') = fold_map (convert_term maps) fa acc
      in  (list_comb (f', args'), acc')
      end

fun treat_qu maps (todo as (prev, Quantifier.All sub :: quants, (i, th))) (acc as (tmmap, ctxt, _)) =
     (let val (ho, (ctxt', tmmap')) = convert_term maps sub (ctxt, tmmap)
          val th' = inst_spec (Thm.cterm_of ctxt ho) th
      in treat_qu maps (sub::prev, quants, (i, th')) (tmmap', ctxt', true)
      end
      handle Unsubst => (todo, acc))
  | treat_qu maps (prev, Quantifier.Ex sk :: quants, (i, th)) (tmmap, ctxt, _) =
      let val ((x, th'), ctxt') = obtain_exists th ctxt
          val skt = FTerm.A (sk, rev prev)
          val tmmap' = (skt, snd x |> Thm.term_of) :: tmmap
      in treat_qu maps (prev, quants, (i, th')) (tmmap', ctxt', true)
      end
  | treat_qu _ todo acc = (todo, acc)

fun transform_res symtab sub res =
  let val (_, (off, (_, _, vars, thinfo))) = res
      val (i, (thm, ({quantifiers, skolems, ...}))) = thinfo
      (*TODO: Variables seem to be wrongly calculated sometimes?*)
      val _ = @{print} (off, vars, thm)
      val subs = get_subs off vars sub |> map snd
      val skolems' = map (unskolemise symtab) skolems
  in ((i, thm), Quantifier.zip_quants quantifiers (subs, skolems'))
  end

fun instantiate_theorems tabs (ctxt, tmmap, ths) =
  let val (ths', (tmmap', ctxt', changed)) = fold_map (treat_qu tabs) ths (tmmap, ctxt, false)
  in (changed, (ctxt', tmmap', ths'))
  end

fun lit_sign (P, Pa) =
  let val (sign, P') = if P < 0 then (fn x => FOLogic.not $ x, ~P) else (I, P)
  in (FTerm.A (P', Pa), sign)
  end

(* TODO: This ignores the change of the accumulator from unsub2! *)
fun conv_lit (sub, maps, acc) =
  lit_sign #>> Subst.transitive sub #>> flip (convert_term maps) acc #>> fst #> (op |>)

fun instantiate_proof ctxt (symtab, sktab) (sub, prf) =
  let
    val sub' = Subst.normalise sub
    val skolems = List.map #skolems sktab |> List.concat

    val res = map_filter CProof.destResolution prf |> map (transform_res symtab sub')
    val thform = List.map (fn (ith, quants) => ([], quants, ith)) res

    (*remove duplicate theorems, but save information where they were so
      we can put them back into their place later
      otherwise, existentials may be instantiated several times!*)
    fun i_th_eq (i1, th1) (i2, th2) = i1 = i2 andalso Thm.concl_of th1 = Thm.concl_of th2
    fun thform_eq ((_, q1, ith1), (_, q2, ith2)) = q1 = q2 andalso i_th_eq ith1 ith2
    val (is, (thuniq, _)) = elim_equals thform_eq thform
    val thuniq' = List.rev (map fst thuniq)

    val _ = @{print} "Before instantiation ..."
    val (ctxt', tmmap, instantiated) =
      do_while (instantiate_theorems (symtab, skolems)) (true, (ctxt, [], thuniq'))
    val inst = map (fn (_, quants, th) =>
      case quants of [] => th | _ => raise Fail "quantifiers left to instantiate") instantiated
    val _ = @{print} "After instantiation ..."

    val conv_fun = conv_lit (sub', (symtab, skolems), (ctxt', tmmap))
    fun nth_conj (i, th) = nth (dest_conj_rule th) i
  in (ctxt', conv_fun, map (curry List.nth inst #> nth_conj) is)
  end

end


structure Reconstruction =
struct

fun remove_neg (@{const Not} $ t) = (true, t)
  | remove_neg t = (false, t)

fun flip_polarity t =
  let val (is_neg, unneg) = remove_neg t in
  if is_neg then unneg else @{const Not} $ t
  end

(* prove theorems of the shape "a \<or> b \<or> c \<longrightarrow> b \<or> c \<or> a \<or> c" *)
fun disj_imp_tac ctxt i =
  resolve_tac ctxt @{thms impI} i THEN
  REPEAT (SOMEGOAL (eresolve_tac ctxt @{thms disjE})) THEN
  ALLGOALS (asm_simp_tac ctxt)

val _ = prove_with_tac @{prop "a \<or> b \<or> c \<longrightarrow> b \<or> c \<or> a \<or> c"} disj_imp_tac
val _ = prove_with_tac @{prop "a \<longrightarrow> a"} disj_imp_tac


(* create p1 \<or> p2 \<or> ... \<or> pn \<or> c, \<not>p1, \<not>p2, ..., \<not>pn |- c *)
fun contrapos_rule ctxt clause concl =
  let
    val disj = List.foldr FOLogic.mk_disj concl clause |> FOLogic.mk_Trueprop
    val negs = map (FOLogic.mk_Trueprop o flip_polarity) clause
    val goal = List.foldr Logic.mk_implies (FOLogic.mk_Trueprop concl) (disj :: negs)
    val res = Goal.prove ctxt [] [] goal (K (simp_only_tac ctxt @{thms disj_simps not_simps} 1))
  in (disj, res)
  end

val contrapos_rule_test =
  let
    val (disj, concl) = ([@{term "a::o"}, @{term "\<not>b::o"}], @{term "c::o"})
    val (_, th) = contrapos_rule @{context} disj concl
  in @{assert} ((Thm.prop_of th) aconv @{term "a \<or> \<not> b \<or> c \<Longrightarrow> \<not> a \<Longrightarrow> b \<Longrightarrow> c"})
  end

(*Given "A |- ~a ==>  a", prove "A |-  a" or
        "A |-  a ==> ~a", prove "A |- ~a"*)
fun finish_rule ctxt imp =
  let
    val left = imp |> Thm.prems_of |> the_single
    val (left_is_neg, left_unneg) = left |> FOLogic.dest_Trueprop |> remove_neg
    val left_ct = Thm.cterm_of ctxt left
    val left_th = Thm.assume left_ct
    val right_th = imp OF [left_th]
    val anything = @{thm notE} OF (if left_is_neg then [left_th, right_th] else [right_th, left_th])
    val left_impl_anything = Thm.implies_intr left_ct anything
    val left_impl_false = Thm.instantiate' [] [SOME @{cterm False}] left_impl_anything
    val neg_th = if left_is_neg then @{thm ccontr} else @{thm notI}
    val unneg_ct = Thm.cterm_of ctxt left_unneg
    val neg_th' = Thm.instantiate' [] [SOME unneg_ct] neg_th
  in Thm.implies_elim neg_th' left_impl_false
  end

val finish_rule_test =
  let val fr = Thm.assume #> finish_rule @{context} #> Thm.concl_of
  in @{assert} (fr @{cprop "\<not>a \<Longrightarrow> a"} = @{prop a});
     @{assert} (fr @{cprop "a \<Longrightarrow> \<not>a"} = @{prop "\<not>a"})
  end

(* Prove disjunction from the conclusion of the theorem. *)
fun disj_rule ctxt disj th =
  let
    val imp = FOLogic.mk_imp (FOLogic.dest_Trueprop (Thm.concl_of th), FOLogic.dest_Trueprop disj)
    val imp_th = Goal.prove ctxt [] [] (FOLogic.mk_Trueprop imp) (K (disj_imp_tac ctxt 1))
  in @{thm mp} OF [imp_th, th]
  end

val disj_rule_test =
  let fun dr gl = Thm.assume #> disj_rule @{context} gl
      val (gl, ass) = (@{prop "a \<or> b"}, @{cprop "b \<or> a"})
  in @{assert} ((Thm.prop_of (dr gl ass)) aconv gl)
  end

(* Given a term t and a theorem "x1 \<or> ... \<or> \<not>t \<or> ... \<or> xn", yield
   ([x1, ..., xn], "\<not>x1 \<Longrightarrow> ... \<Longrightarrow> \<not>xn \<Longrightarrow> \<not>t"
 *)
fun resolve_rule ctxt t th =
  let
    val neg = flip_polarity t
    val clause = th |> Thm.concl_of |> FOLogic.dest_Trueprop |> FOLogic.dest_disj
    val clause' = remove1 (op =) neg clause
    val _ = @{assert} (List.length clause' = List.length clause - 1)
    val (disj, contra) = contrapos_rule ctxt clause' neg
  in (clause', contra OF [disj_rule ctxt disj th])
  end

val resolve_rule_test =
  let fun rt t = Thm.assume #> resolve_rule @{context} t ##> Thm.prop_of
  in
    @{assert} (rt @{term "b::o"} @{cprop "a \<or> \<not>b \<or> \<not>c"} =
      ([@{term "a::o"}, @{term "\<not>c"}], @{term "\<not> a \<Longrightarrow> c \<Longrightarrow> \<not> b"}));
    @{assert} (rt @{term "\<not>b::o"} @{cprop "b \<or> a \<or> c"} =
       ([@{term "a::o"}, @{term "c::o"}], @{term "\<not> a \<Longrightarrow> \<not> c \<Longrightarrow> b"}))
  end


fun cprop_of ctxt = FOLogic.mk_Trueprop #> Thm.cterm_of ctxt

fun recon ctxt _ (CProof.Path t :: tl) =
      (t |> flip_polarity |> cprop_of ctxt |> Thm.assume, tl)
  | recon _ lemmas (CProof.Lemma t :: tl) =
      (case List.find (fn x => Thm.concl_of x = t) lemmas of
        SOME x => (x, tl)
      | NONE => raise Fail "lemma not found")
  | recon ctxt lemmas (CProof.Resolution (t, th) :: tl) =
      let
        val (clause, contra) = resolve_rule ctxt t th

        fun foldf _ (found, lms, prf) =
          let val (nthm, nprf) = recon ctxt lms prf
          in (nthm :: found, nthm :: lms, nprf)
          end

        val (ths, _, tl') = fold foldf clause ([], lemmas, tl)
        val tprf = contra OF (List.rev ths)
      in (Thm.implies_intr (cprop_of ctxt t) tprf |> finish_rule ctxt, tl')
      end
  | recon _ _ _ = raise Fail "recon"

fun reconstruct ctxt = List.rev #> recon ctxt [] #> fst

end

structure Equivalence =
struct

(*
fun invent_tfrees t =
  let
    val tvars = Term.add_tvars t []
    val subst = map (fn ((s, i), S) => ((s, i), TFree (s (* ^ string_of_int i *), S))) tvars
  in subst_TVars subst t
  end
*)

(* Depending on type T, show:
   * x1 \<equiv> y1 \<Longrightarrow> ... \<Longrightarrow> xn \<equiv> yn \<Longrightarrow> P x1 \<dots> xn \<Longrightarrow> P y1 \<dots> yn.
   * x1 \<equiv> y1 \<Longrightarrow> ... \<Longrightarrow> xn \<equiv> yn \<Longrightarrow> f x1 \<dots> xn \<equiv> f y1 \<dots> yn.
 *)
fun congr ctxt (name, T) =
  let
    (* assign term sort to every type, otherwise we cannot use eq_reflection below! *)
    val T = map_type_tfree (fn (n, S) => TFree (n, @{sort term})) T
    val (Ts, T') = strip_type T

    val is = map Int.toString (1 upto length Ts)
    val (left, right) = apply2 (fn side => map (fn b => side ^ b) is) ("x", "y")
    val ts = apply2 (map Free o (fn names => names ~~ Ts)) (left, right)
    val c  = apply2 (fn t => list_comb (Const (name, T), t)) ts
    val eqs = ListPair.mapEq (FOLogic.mk_Trueprop o FOLogic.mk_eq) ts
    val goal =
      if T' = FOLogic.oT
      then Logic.mk_implies o apply2 FOLogic.mk_Trueprop
      else FOLogic.mk_Trueprop o FOLogic.mk_eq
  in
    Goal.prove ctxt (left @ right) eqs (goal c) (fn {context = ctxt, prems = prs} =>
      (* convert to meta-logic equality for rewriting *)
      let val meqs = map (fn th => th RS @{thm eq_reflection}) prs
      in HEADGOAL (rewrite_goal_tac ctxt meqs THEN' simp_tac ctxt)
      end)
  end

(* Tests for congruence axioms are hard in FOL, because there exist hardly any
   meaningful predicates or functions that have a concrete type other than 'a or o. *)
val _ =
  let fun cong sym th = (Thm.prop_of (congr @{context} sym)) aconv (Thm.prop_of th)
  in @{assert} (cong (dest_Const @{term "True"}) @{lemma "True \<Longrightarrow> True" by simp})
  end

fun cong_consts ts =
  fold Term.add_consts ts []
  |> filter_out (fst #> member (op =) [@{const_name IFOL.eq}])
  |> filter_out (snd #> binder_types #> exists (fn T => T = @{typ o} orelse T = @{typ prop}))

fun cong_axioms ctxt = (* map invent_tfrees #> *) cong_consts #> map (congr ctxt)

end


structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);

(* Unfortunately, we cannot move this to mlCoP, otherwise we have to give it a type,
   and when giving it the automatically inferred type, we get an error:
   "Type variable is free in surrounding scope". Why? *)
val prove_option =
  let fun todo sub _ prf = SOME (fst sub, prf)
      fun alt () = NONE
  in  mlCoP.prove_default alt todo
  end

fun iproof_of_cproof ctxt tabs (sub, fprf) =
  let
    val (ctxt', conv_fun, ths) = Instantiation.instantiate_proof ctxt tabs (sub, fprf)
    val convert_step = CProof.fold_proof conv_fun (hd_tl o snd)
    val (iprf, _) = fold_map convert_step fprf ths
  in (ctxt', iprf)
  end

fun reconstruct ctxt tabs fprf =
  let
    val (ctxt', iprf) = iproof_of_cproof ctxt tabs fprf
    val _ = IProof.pretty_iproof ctxt' iprf |> Pretty.writeln

    val th = Reconstruction.reconstruct ctxt' iprf
    val hashek_not = @{lemma "\<not>hashek \<Longrightarrow> False" by (simp add: hashek_def)}
  in hashek_not OF (Proof_Context.export ctxt' ctxt [th])
  end

fun clause_matrix cls = Matrix.empty 10000 |> tap (flip Matrix.insert_clauses cls)
val init_termmap = Termmap.insert (Termmap.empty 10000, @{const hashek}) |> fst

fun mat_of_ths ths =
  let
    val sktab = Skolemisation.skolemise_ths ths
    val (clss, symtab) = sktab |> map #skolemised |> Isa_to_CoP.convert_terms init_termmap

    (* With every clause, save the theorem (premise) it came from, plus
       the index of the theorem conjunct that contains the clause.  *)
    fun flatten (cls, th) = map_index (fn (i, cl) => (cl, (i, th))) cls
    val cls = ListPair.mapEq flatten (clss, ths ~~ sktab) |> List.concat
    val _ = cls |> List.map #1 |> FTerm.pretty_clauses |> Pretty.writeln
  in (clause_matrix cls, (symtab, sktab))
  end


fun raw_isacop lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})
    val (mat, tabs) = mat_of_ths prems
    val tac = case prove_option mat lim of
        SOME p => resolve_tac ctxt [reconstruct ctxt tabs p]
      | NONE => (@{print} "No connection proof found."; K no_tac)
  in HEADGOAL tac
  end)

fun isacop_method (lim, ths) ctxt facts =
  let
    val lim' = case lim of NONE => Config.get ctxt depth_limit | SOME l => l
    val eqs = Equivalence.cong_axioms ctxt (map Thm.prop_of facts)
    val trans' = @{lemma "x = y \<Longrightarrow> x = z \<Longrightarrow> y = z" by simp}
    val ths' = @{thm refl} :: trans' :: facts @ ths @ eqs
    val atomized = map (atomize_thm ctxt) ths'
  in
    HEADGOAL
    (
      Method.insert_tac ctxt atomized THEN'
      (* introduce hashek into goal *)
      resolve_tac ctxt [hashek_and] THEN'
      K (print_tac ctxt "Initial proof state") THEN'
      neg_goal_tac ctxt THEN'
      clausify_tac ctxt THEN'
      K (print_tac ctxt "After clausification") THEN'
      raw_isacop lim' ctxt
    )
  end

val _ =
  Theory.setup
    (Method.setup @{binding isacop}
      (Scan.lift (Scan.option Parse.nat) -- Attrib.thms >> (METHOD oo isacop_method))
      "lean connection calculus prover")

end
