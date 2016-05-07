(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction

TODO:

- Fix case when multiple conjuncts are in clause (in conj_clause_ex).
- Implement path rule.
- Fix non-found lemma (in lemma_ex).
*)

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

fun prove_with_tac t tac = Goal.prove @{context} [] [] t (K (tac @{context} 1))


fun hd_tl (hd :: tl) = (hd, tl)
  | hd_tl _ = raise Fail "hd_tl"

fun flip f x y = f y x

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



signature SKOLEMISATION =
sig

type mapping
type table
type quant_type

val skolem_function : string -> term
val fold_quants : ('a -> 'c) * ('b -> 'c) -> quant_type list -> 'a list * 'b list -> 'c list
val skolemise_assms : thm list -> table

end

structure Skolemisation : SKOLEMISATION =
struct

datatype quant_type = All | Ex

(* all/ex, (name, type) *)
type quant_info = quant_type * (string * typ)

type skolemised = {
  quantifiers : quant_info list
, skolems : string list
, skolemised : term
}

type mapping = thm * skolemised
type table = mapping list


fun quant_of @{const_name "All"} = SOME All
  | quant_of @{const_name "Ex" } = SOME Ex
  | quant_of _ = NONE

fun strip_quants quants (Const (quant, _) $ Abs (x, T, t)) =
      (case quant_of quant of
        SOME q => strip_quants ((q, (x, T)) :: quants) t
      | NONE => (List.rev quants, t))
  | strip_quants quants t = (List.rev quants, t)

fun map_bndvars f = map_aterms (fn t => case t of Bound i => f i | _ => t)

fun skolem_function name = Const (name, dummyT)

fun skolemise_term all ex (((quant, (x, _)), quanti) :: quants) t ctxt =
  (case quant of
    All => skolemise_term (quanti :: all) ex quants t ctxt
  | Ex =>
      let val (name, ctxt') = Name.variant (Name.skolem x) ctxt
          val skolem = list_comb (skolem_function name, List.map Bound (rev all))
          val t' = map_bndvars (fn i => if i = quanti then skolem else Bound i) t
      in skolemise_term all (name :: ex) quants t' ctxt'
      end)
  | skolemise_term _ ex [] t ctxt = ((rev ex, t), ctxt)

fun skolemise_assm assm ctxt =
  let
    val t = assm |> Thm.concl_of |> FOLogic.dest_Trueprop
    val (quants, bare) = strip_quants [] t
    val quants' = quants ~~ ((List.length quants - 1) downto 0)
    val ((ex, sk), ctxt') = skolemise_term [] [] quants' bare ctxt
  in ((assm, { quantifiers = quants, skolems = ex, skolemised = sk }), ctxt')
  end

fun skolemise_assms assms = fold_map skolemise_assm assms Name.context |> fst


fun map_quant (fa, _) All (hd :: tl, ex) = (fa hd, (tl,  ex))
  | map_quant (_, fe) Ex (all, hd :: tl) = (fe hd, (all, tl))
  | map_quant _ _ _ = raise Fail "map_quant"

fun fold_quants fs = fst oo fold_map (map_quant fs)

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

fun convert tab = map clausify #> flip conv_asms tab

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

signature IPROOF =
sig

type proof

end

structure IProof =
struct

type fproof = (int * Skolemisation.mapping) mlCoP.proof
type iproof = (term, thm) CProof.proof

fun pretty_step ctxt (CProof.Path t) =
      Pretty.block [Pretty.str "Path: " , Syntax.pretty_term ctxt t]
  | pretty_step ctxt (CProof.Lemma t) =
      Pretty.block [Pretty.str "Lemma: ", Syntax.pretty_term ctxt t]
  | pretty_step ctxt (CProof.Resolution (t, th)) = Pretty.block
      [Pretty.str "Resolution: ", Syntax.pretty_term ctxt t,
       Pretty.str ", ", Thm.pretty_thm ctxt th]

end


signature COP_TO_ISA =
sig

val convert_proof :
  Proof.context -> Termmap.bimap * Skolemisation.table ->
  Subst.subst * IProof.fproof -> Proof.context * IProof.iproof

end

structure CoP_to_Isa : COP_TO_ISA =
struct

fun unskolemise tab x =
  case (Termmap.forward (tab, Skolemisation.skolem_function x)) of
      SOME s => s
    | NONE => raise Fail "unskolemise"

fun conv_sym tab sym =
  case Termmap.backward (tab, sym) of
      SOME t => t
    | NONE => raise Fail ("conv_sym: " ^ Int.toString sym)


fun self_mapping off vars = map (fn v => (v, FTerm.V v)) (off upto off + vars - 1)

fun get_subs off vars =
  filter (fn (v, _) => off <= v andalso v < off + vars)
  (*if substitution does not contain binding for variable, create one to itself*)
  #> union (fn ((u, _), (v, _)) => u = v) (self_mapping off vars)

val order_subs = sort (prod_ord int_ord (K EQUAL)) #> rev


exception Unsubst

datatype quant_info =
    (* forall quantifier is mapped to a FO term via substitution *)
    All of FTerm.term
    (* existential quantifier has a certain FO identifier *)
  | Ex of int

(*TODO: Perhaps we need to do more here? (Making type most general?)
        See Isar Implementation manual from 2016, p. 119 *)
fun invent_universals ctxt v =
  let val (vars, ctxt') = Variable.variant_fixes (map Int.toString v) ctxt
  in (Syntax.read_terms ctxt' vars, ctxt')
  end

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
            Const (fh, _) => if member (op =) skolems fh then raise Unsubst else ()
          | _ => ();
        val (args', acc') = fold_map (convert_term maps) fa acc
    in  (list_comb (f', args'), acc')
    end

fun treat_qu maps (todo as (prev, All sub :: quants, th)) (acc as (tmmap, ctxt, _)) =
     (let val (ho, (ctxt', tmmap')) = convert_term maps sub (ctxt, tmmap)
          val th' = inst_spec (Thm.cterm_of ctxt ho) th
      in treat_qu maps (sub::prev, quants, th') (tmmap', ctxt', true)
      end
      handle Unsubst => (todo, acc))
  | treat_qu maps (prev, Ex sk :: quants, th) (tmmap, ctxt, _) =
      let val ((x, th'), ctxt') = obtain_exists th ctxt
          val skt = FTerm.A (sk, rev prev)
          val tmmap' = (skt, snd x |> Thm.term_of) :: tmmap
      in treat_qu maps (prev, quants, th') (tmmap', ctxt', true)
      end
  | treat_qu _ todo acc = (todo, acc)



fun transform_res symtab sub res =
  let val (_, (off, (_, _, vars, thinfo))) = res
      val (i, (thm, ({quantifiers, skolems, ...}))) = thinfo
      val skolems' = map (unskolemise symtab) skolems
      val subs = get_subs off vars sub |> order_subs
      val quant_info = Skolemisation.fold_quants (All, Ex) (map fst quantifiers) (map snd subs, skolems')
  in ((i, thm), quant_info)
  end

fun instantiate_theorems tabs (ctxt, tmmap, ths) =
  let val (ths', (tmmap', ctxt', changed)) = fold_map (treat_qu tabs) ths (tmmap, ctxt, false)
  in (changed, (ctxt', tmmap', ths'))
  end

val verify_result =
  List.map (fn (_, quants, th) =>
    case quants of [] => th | _ => raise Fail "quantifiers left to instantiate")

fun lit_sign (P, Pa) =
  let val (sign, P') = if P < 0 then (fn x => FOLogic.not $ x, ~P) else (I, P)
  in (FTerm.A (P', Pa), sign)
  end

(* TODO: This ignores the change of the accumulator from unsub2! *)
fun conv_lit (sub, maps, acc) =
  lit_sign #>> Subst.transitive sub #>> flip (convert_term maps) acc #>> fst #> (op |>)

fun boo res =
  let
    val thform = List.map (fn ((_, th), quants) => ([], quants, th)) res

    (*remove duplicate theorems, but save information where they were so
      we can put them back into their place later
      otherwise, existentials may be instantiated several times!*)
    fun thform_eq ((_, q1, th1), (_, q2, th2)) = q1 = q2 andalso Thm.concl_of th1 = Thm.concl_of th2
    val (is, (thuniq, _)) = elim_equals thform_eq thform
    val thuniq' = List.rev (map fst thuniq)
  in (is, thuniq')
  end

fun convert_proof ctxt (symtab, sktab) (sub, prf) =
  let
    val sub' = Subst.normalise sub
    val res = map_filter CProof.destResolution prf |> map (transform_res symtab sub')
    val (is, thuniq') = boo res

    val skolems = List.map (#skolems o #2) sktab |> List.concat

    val _ = @{print} "Before instantiation ..."
    val (ctxt', tmmap, final) =
      do_while (instantiate_theorems (symtab, skolems)) (true, (ctxt, [], thuniq'))
    val _ = @{print} "After instantiation ..."
    val final' = List.map (fn i => List.nth (final, i)) is
    val verified = verify_result final'
    fun real_recon data = CProof.fold_proof (conv_lit data) (hd_tl o snd)
    val (prf', _) = fold_map (real_recon (sub', (symtab, skolems), (ctxt', tmmap))) prf verified
    val _ = Pretty.writeln_chunks (map (IProof.pretty_step ctxt') prf')
  in
    (ctxt', prf')
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

val _ =
  let
    val (disj, concl) = ([@{term "a::o"}, @{term "\<not>b::o"}], @{term "c::o"})
    val (_, th) = contrapos_rule @{context} disj concl |> tap @{print}
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

(* Test finish_rule. *)
val _ =
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

val _ =
  let fun dr gl = Thm.assume #> disj_rule @{context} gl
      val (gl, ass) = (@{prop "a \<or> b"}, @{cprop "b \<or> a"})
  in @{assert} ((Thm.prop_of (dr gl ass)) aconv gl)
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
        val neg = flip_polarity t
        val clause = th |> Thm.concl_of |> FOLogic.dest_Trueprop |> FOLogic.dest_disj
        val clause' = remove1 (op =) neg clause
        val _ = @{assert} (List.length clause' = List.length clause - 1)

        val (disj, contra) = contrapos_rule ctxt clause' neg
        val disj_prf = disj_rule ctxt disj th

        fun foldf _ (found, lms, prf) =
          let val (nthm, nprf) = recon ctxt lms prf
          in (nthm :: found, nthm :: lms, nprf)
          end

        val (ths, _, nprf) = fold foldf clause' ([], lemmas, tl)
        val tprf = contra OF (disj_prf :: List.rev ths)
      in (Thm.implies_intr (cprop_of ctxt t) tprf |> finish_rule ctxt, nprf)
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


val fol_blacklist = [@{const_name IFOL.Trueprop}, @{const_name IFOL.eq}]
val pure_blacklist = [@{const_name Pure.imp}]
val const_blacklist = fol_blacklist @ pure_blacklist

fun cong_consts ts =
  fold Term.add_consts ts []
  |> filter_out (member (op =) const_blacklist o fst)

fun cong_axioms ctxt = (* map invent_tfrees #> *) cong_consts #> map (congr ctxt)

end

structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);

exception Solved

val prove_option =
  let fun todo sub _ prf = SOME (fst sub, prf)
      fun alt () = NONE
  in  mlCoP.prove_default alt todo
  end

(* With every clause, save the theorem (premise) it came from, plus
   the index of the theorem conjunct that contains the clause.  *)
fun recon_info (cls, prem) = map_index (fn (i, cl) => (cl, (i, prem))) cls



fun reconstruct ctxt tabs p =
  let
    val (ctxt', prf) = CoP_to_Isa.convert_proof ctxt tabs p
    val th = Reconstruction.reconstruct ctxt' prf
    val hashek_not = @{lemma "\<not>hashek \<Longrightarrow> False" by (simp add: hashek_def)}
  in hashek_not OF (Proof_Context.export ctxt' ctxt [th])
  end

fun clause_matrix cls = Matrix.empty 10000 |> tap (flip Matrix.insert_clauses cls)

fun to_ml prems =
  let
    val sktab = Skolemisation.skolemise_assms prems
    val symm = Termmap.insert (Termmap.empty 10000, @{const hashek}) |> fst
    val (clss, symtab) = sktab |> map (#skolemised o #2) |> Isa_to_CoP.convert symm

    val cls = ListPair.mapEq recon_info (clss, sktab) |> List.concat
    val _ = cls |> List.map #1 |> FTerm.pretty_clauses |> Pretty.writeln
  in (clause_matrix cls, (symtab, sktab))
  end


fun raw_isacop lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let
    val _ = @{assert} ((Thm.term_of concl) aconv @{prop False})
    val (mat, tabs) = to_ml prems
    val tac = case prove_option mat lim of
        SOME p => resolve_tac ctxt [reconstruct ctxt tabs p]
      | NONE => (@{print} "No connection proof found."; K no_tac)
  in HEADGOAL tac
  end)

fun isacop_method (lim, ths) ctxt facts =
  let
    val lim' = case lim of NONE => Config.get ctxt depth_limit | SOME l => l
    val eqs = Equivalence.cong_axioms ctxt (map Thm.prop_of facts)
    val ths' = @{thm refl} :: @{thm trans} :: facts @ ths @ eqs
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
