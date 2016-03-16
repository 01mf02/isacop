(*  Title:      isaCoP.ML
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Tableau prover with proof reconstruction

TODO:

- Fix case when multiple conjuncts are in clause (in conj_clause_ex).
- Implement path rule.
- Fix non-found lemma (in lemma_ex).
*)


structure Prenex =
struct

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

fun clausify_tac ctxt =
  simp_tac_only ctxt @{thms meta_simps IFOL_simps cla_simps} THEN'
  (* K (print_tac ctxt "After simplification") THEN' *)
  simp_tac_only ctxt @{thms prenex_ex prenex_all} THEN'
  (* K (print_tac ctxt "After prenexing") THEN' *)
  simp_tac_only ctxt @{thms precnf_simps} THEN'
  simp_tac_only ctxt @{thms cnf_simps} THEN'
  simp_tac_only ctxt @{thms conj_simps disj_simps}

fun prepare_tac ctxt =
  (* introduce hashek into goal *)
  resolve_tac ctxt @{thms hashekE} THEN'
  K (print_tac ctxt "Initial proof state") THEN'
  negOfGoal_tac ctxt THEN'
  (* K (print_tac ctxt "After negation") THEN' *)
  clausify_tac ctxt THEN'
  K (print_tac ctxt "After clausification")

end


structure Skolemisation =
struct

datatype quant_type = All | Ex

(* all/ex, (name, type) *)
type quant_info = quant_type * (string * typ)
(* theorem, (quantifiers, Skolem names, term without quantifiers *)
type mapping = thm * (quant_info list * string list * term)
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

fun strip_trueprop (Const (@{const_name "Trueprop"}, _) $ t) = t
  | strip_trueprop t = t

fun skolemise_assm assm ctxt =
  let
    val t = assm |> Thm.concl_of |> strip_trueprop
    val (quants, bare) = strip_quants [] t
    val quants' = quants ~~ ((List.length quants - 1) downto 0)
    val ((ex, sk), ctxt') = skolemise_term [] [] quants' bare ctxt
  in ((assm, (quants, ex, sk)), ctxt')
  end

fun skolemise_assms assms = fold_map skolemise_assm assms Name.context

end


structure Symmap = IntBimap (type key = string val ord = string_ord)
structure Termmap = IntBimap (type key = term val ord = Term_Ord.fast_term_ord)



structure HOL_to_FOL =
struct

fun destConstFree (Const (c, T)) = (c, T)
  | destConstFree (Free (f, T)) = (f, T)
  | destConstFree x = raise TERM ("destConstFree", [x])

fun conv_term (Bound b) tab = (FTerm.V b, tab)
  | conv_term t tab =
  let val (P, args) = strip_comb t (* |>> fst o destConstFree*)
      val (tab', P') = Termmap.insert (tab, P)
      val (args', tab'') = fold_map conv_term args tab'
  in (FTerm.A (P', args'), tab'')
  end

fun conv_prop (@{const "Not"} $ t) tab = conv_prop t tab |>> FTerm.negateLit
  | conv_prop t tab = conv_term t tab |>> FTerm.destApp

val conv_clause = fold_map conv_prop
val conv_clauses = fold_map conv_clause
val conv_asms = fold_map conv_clauses


val dest_conj = FOLogic.dest_conj
fun dest_disj (Const (@{const_name disj}, _) $ t $ t') = t :: dest_disj t'
  | dest_disj t = [t];

val clausify = map dest_disj o dest_conj

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
val pretty_clauses = Pretty.block o Pretty.separate " \<and>" o map (Pretty.enclose "(" ")" o pretty_clause)

end

signature FOL_TO_HOL =
sig

datatype proof =
    Lemma of term
  | Path of term
  | Resolution of term * thm

val reconstruct : Proof.context -> Termmap.bimap -> Skolemisation.table ->
  Subst.subst * (int * Skolemisation.mapping) mlCoP.proof ->
  Proof.context * (FTerm.term * term) list * thm list * proof list

end

structure FOL_to_HOL : FOL_TO_HOL =
struct

datatype proof =
    Lemma of term
  | Path of term
  | Resolution of term * thm

fun conv_sym tab sym = case Termmap.backward (tab, sym) of
      SOME t => t
    | NONE => raise Fail ("conv_sym: " ^ Int.toString sym)

fun destResolution (mlCoP.Resolution r) = SOME r
  | destResolution _ = NONE


fun get_subs off vars =
     filter (fn (v, _) => off <= v andalso v < off + vars)
     (*if substitution does not contain binding for variable, create one to itself*)
  #> union (fn ((u, _), (v, _)) => u = v) (map (fn v => (v, FTerm.V v)) (off upto off + vars - 1))
  #> sort (prod_ord int_ord (K EQUAL))
  #> rev

fun inst_spec ct th =
  th RS (Thm.instantiate' [SOME (Thm.ctyp_of_cterm ct)] [NONE, SOME ct] @{thm spec})

fun obtain_ex th ctxt =
  let val ((x, th'), ctxt') = Obtain.result (fn _ => eresolve_tac ctxt @{thms exE} 1) [th] ctxt
  in ((the_single x, the_single th'), ctxt')
  end

exception Unsubst

datatype quant_info =
    (* forall quantifier is mapped to a FO term via substitution *)
    All of FTerm.term
    (* existential quantifier has a certain FO identifier *)
  | Ex of int

fun make_quant_info Skolemisation.All (sub :: subs, skolems) = (All sub, (subs, skolems))
  | make_quant_info Skolemisation.Ex (subs, skolem :: skolems) = (Ex skolem, (subs, skolems))
  | make_quant_info _ _ = raise Fail "make_quant_info"

fun invent_universal2 v ctxt =
  let (*TODO: Perhaps we need to do more here? (Making type most general?)
        See Isar Implementation manual from 2016, p. 119 *)
      val (var, ctxt') = Variable.variant_fixes [Int.toString v] ctxt
      val t' = Syntax.read_term ctxt' (the_single var)
  in (t', ctxt')
  end

fun unsub2 (maps as (symmap, skolems)) t (acc as (tmmap, ctxt)) =
  case AList.lookup (op =) tmmap t of
    SOME ho => (ho, acc)
  | NONE =>
      (case t of
        FTerm.V v =>
          let val (t', ctxt') = invent_universal2 v ctxt
          in (t', ((FTerm.V v, t') :: tmmap, ctxt'))
          end
      | FTerm.A (f, fa) =>
          let val f' = conv_sym symmap f
              val _ = case fst (strip_comb f') of
                  Const (fh, _) => if member (op =) skolems fh then raise Unsubst else ()
                | _ => ();
              val (args', acc') = fold_map (unsub2 maps) fa acc
          in  (list_comb (f', args'), acc')
          end
      )

fun treat_qu maps (todo as (prev, All sub :: quants, th)) (acc as (tmmap, ctxt, _)) =
     (let val (ho, (tmmap', ctxt')) = unsub2 maps sub (tmmap, ctxt)
      in treat_qu maps (sub::prev, quants, inst_spec (Thm.cterm_of ctxt ho) th) (tmmap', ctxt', true)
      end
      handle Unsubst => (todo, acc))
  | treat_qu maps (prev, Ex sk :: quants, th) (tmmap, ctxt, _) =
      let val ((x, th'), ctxt') = obtain_ex th ctxt
          val skt = FTerm.A (sk, rev prev)
          val tmmap' = (skt, snd x |> Thm.term_of) :: tmmap
      in treat_qu maps (prev, quants, th') (tmmap', ctxt', true)
      end
  | treat_qu _ todo acc = (todo, acc)

fun transform_res symtab sub res =
  let val (_, (off, (_, _, vars, thinfo))) = res
      val (i, (thm, (quants, skolems, _)) : Skolemisation.mapping) = thinfo
      val skolems' = map (fn x => Option.valOf (Termmap.forward (symtab, Skolemisation.skolem_function x))) skolems
      val subs = get_subs off vars sub
      val quant_info = fold_map make_quant_info (map fst quants) (map snd subs, skolems')
  in ((i, thm), fst quant_info)
  end

fun do_while f (continue, acc) = if continue then do_while f (f acc) else acc

fun instantiate_theorems tabs (ctxt, tmmap, ths) =
  let val (ths', (tmmap', ctxt', changed)) = fold_map (treat_qu tabs) ths (tmmap, ctxt, false)
  in (changed, (ctxt', tmmap', ths'))
  end

val verify_result =
  List.map (fn (_, quants, th) =>
    case quants of [] => th | _ => raise Fail "quantifiers left to instantiate")

fun conv_lit (sub, maps, acc) (P, Pa) =
  let val (sign, P') = if P < 0 then (fn x => FOLogic.not $ x, ~P) else (I, P)
      val t = (FTerm.A (P', Pa))
      val t' = Subst.transitive sub t
  in unsub2 maps t' acc |> fst |> sign
  end

fun real_recon data (mlCoP.Lemma t) ths = (Lemma (conv_lit data t), ths)
  | real_recon data (mlCoP.Path t) ths = (Path (conv_lit data t), ths)
  | real_recon data (mlCoP.Resolution (t, _)) (th::ths) = (Resolution (conv_lit data t, th), ths)
  | real_recon _ _ _ = raise Fail "real_recon"

fun pretty_step ctxt (Path t) = Pretty.block [Pretty.str "Path: ", Syntax.pretty_term ctxt t]
  | pretty_step ctxt (Lemma t) = Pretty.block [Pretty.str "Lemma: ", Syntax.pretty_term ctxt t]
  | pretty_step ctxt (Resolution (t, th)) = Pretty.block
      [Pretty.str "Resolution: ", Syntax.pretty_term ctxt t,
       Pretty.str ", ", Thm.pretty_thm ctxt th]

fun elim_equals eq l =
  let fun f x (prev, i) = case AList.lookup eq prev x of
      SOME j => (j, (prev, i))
    | NONE => (i, ((x, i) :: prev, i + 1))
  in fold_map f l ([], 0)
  end;

val _ = @{assert}
 (elim_equals (op =) ["a", "b", "a", "c"] =
  ([0, 1, 0, 2], ([("c", 2), ("b", 1), ("a", 0)], 3)))

fun intro_equals l = List.map (fn i => List.nth (l, i))

fun reconstruct ctxt symtab (sktab : Skolemisation.table) (sub, prf) =
  let
    val _ = @{print} "Welcome to reconstruct!"
    val sub' = Subst.normalise sub
    val res = map_filter destResolution prf |> map (transform_res symtab sub')
    val skolems = List.map (fn (_, (_, syms, _)) => syms) sktab |> List.concat
    val thform = List.map (fn ((_, th), quants) => ([], quants, th)) res

    (*remove duplicate theorems, but save information where they were so
      we can put them back into their place later
      otherwise, existentials may be instantiated several times!*)
    fun thform_eq ((_, q1, th1), (_, q2, th2)) = q1 = q2 andalso Thm.concl_of th1 = Thm.concl_of th2
    val (is, (thuniq, _)) = elim_equals (thform_eq) thform
    val thuniq' = List.rev (map fst thuniq)

    val _ = @{print} "Before instantiation ..."
    val (ctxt', tmmap, final) =
      do_while (instantiate_theorems (symtab, skolems)) (true, (ctxt, [], thuniq'))
    val _ = @{print} "After instantiation ..."
    val final' = intro_equals final is
    val verified = verify_result final'
    val (prf', _) = fold_map (real_recon (sub', (symtab, skolems), (tmmap, ctxt'))) prf verified
    val _ = Pretty.writeln_chunks (map (pretty_step ctxt') prf')
  in
    (ctxt', tmmap, verified, prf')
  end

end

structure Reconstruction =
struct

(*
let rec recon sub lemmas = function
    Pat g :: tl -> (ASSUME (Meson.hol_of_literal (ss sub g)), tl)
  | Lem g :: tl -> find (fun x -> concl x = Meson.hol_of_literal (ss sub g)) lemmas, tl
  | Res (g, (n, th)) :: tl ->
    let foldf (found, lms, prf) _ =
      let (nthm, nprf) = recon sub lms prf in (nthm :: found, nthm :: lms, nprf) in

    let (ths, nlms, nprf) = List.fold_left foldf ([],lemmas,tl) (List.tl (disjuncts (concl th))) in

    (* from |- t1 \<or> t2 \<or> ... \<or> tn \<or> ..., tm , create |- \<not>t1 \<and> \<not>t2 \<and> ... \<and> \<not>tm \<longrightarrow> tn *)
    let cth : thm = Meson.make_hol_contrapos(n,th) in
    (* get rid of implication, obtaining tn *)
    let hth : thm = if ths = [] then cth else MATCH_MP cth (end_itlist CONJ (rev ths)) in

    (* PART_MATCH : (term -> term) -> thm -> term -> thm *)
    (* instantiate hth theorem to match the clashing literal *)
    let ith = PART_MATCH I hth (Meson.hol_of_literal (ss sub g)) in

    (* DISCH ... transforms  A, ~ith |- ith  to  A |- ~ith --> ith *)
    (* finish_RULE then transforms this to A |- ith *)
    Meson.finish_RULE (DISCH (hol_negate(concl ith)) ith), nprf
  | [] -> assert false
*)



fun is_neg (@{const Not} $ t) = (true, t)
  | is_neg t = (false, t)

fun flip_polarity t =
  let val (is, sans) = is_neg t in
  if is then sans else @{const Not} $ t
  end


(* prove theorems of the shape "a \<or> b \<or> c \<longrightarrow> b \<or> c \<or> a \<or> c" *)
fun reorder_disj ctxt =
  resolve_tac ctxt @{thms impI} 1 THEN
  TRY (assume_tac ctxt 1) THEN  (* in case of sth. like a \<longrightarrow> a *)
  REPEAT
   (eresolve_tac ctxt @{thms disjE} 1 THEN
    REPEAT (CHANGED (Prenex.simp_tac_only ctxt @{thms disj_simps not_simps} 1)))

(* create \<not>p1, \<not>p2, ..., \<not>pn, p1 \<or> p2 \<or> ... \<or> pn \<or> c |- c *)
(* attention: premises are reversed! *)
fun make_contrapos ctxt prems concl =
  let
    val _ = @{print} "contrapos start"
    val prems' = prems
    val _ = @{print} "prems destroyed"
    val concl' = concl
    val _ = @{print} "concl destroyed"
    val disj = List.foldl FOLogic.mk_disj concl' prems' |> FOLogic.mk_Trueprop
    val _ = @{print} "disj created"
    val negs = map (FOLogic.mk_Trueprop o flip_polarity) prems
    val goal = List.foldl Logic.mk_implies (FOLogic.mk_Trueprop concl) (disj :: negs)
    val res = Goal.prove ctxt [] [] goal (fn _ => Prenex.simp_tac_only ctxt @{thms disj_simps not_simps} 1)
  in (disj, res)
  end


(*Given "A |- ~a ==>  a", prove "A |-  a" or
        "A |-  a ==> ~a", prove "A |- ~a"*)
fun finish_rule ctxt impl =
  let
    val left = impl |> Thm.prems_of |> the_single
    val (left_is_neg, left_unneg) = left |> FOLogic.dest_Trueprop |> is_neg
    val left_ct = Thm.cterm_of ctxt left
    val left_th = Thm.assume left_ct
    val right_th = impl OF [left_th]
    val anything = @{thm notE} OF (if left_is_neg then [left_th, right_th] else [right_th, left_th])
    val left_impl_anything = Thm.implies_intr left_ct anything
    val left_impl_false = Thm.instantiate' [] [SOME @{cterm False}] left_impl_anything
    (* val _ = @{print} left *)
    (* val _ = @{print} (FOLogic.dest_Trueprop left) *)
    val neg_th = if left_is_neg then @{thm ccontr} else @{thm notI}
    val unneg_ct = Thm.cterm_of ctxt left_unneg
    val neg_th' = Thm.instantiate' [] [SOME unneg_ct] neg_th
  in Thm.implies_elim neg_th' left_impl_false
  end



fun recon ctxt _ (FOL_to_HOL.Path t :: tl) =
      let val t' = t |> flip_polarity |> FOLogic.mk_Trueprop
          val ct = Thm.cterm_of ctxt t'
      in (Thm.assume ct, tl, ctxt)
      end
  | recon ctxt lemmas (FOL_to_HOL.Lemma t :: tl) =
      (case List.find (fn x => Thm.concl_of x = t) lemmas of
        SOME x => (x, tl, ctxt)
      | NONE => raise Fail "lemma not found")
  | recon ctxt lemmas (FOL_to_HOL.Resolution (t, th) :: tl) =
      let
        val negt = flip_polarity t
        val disjuncts = th |> Thm.concl_of |> FOLogic.dest_Trueprop |> HOL_to_FOL.dest_disj
        val rest = remove1 (op =) negt disjuncts
        (*val _ = (@{print} (disjuncts, negt))*)
        val _ = @{assert} (List.length rest = List.length disjuncts - 1)
        val _ = @{print} "Before contrapos"
        val (disj, contra) = make_contrapos ctxt rest negt
        val _ = @{print} "After contrapos"

        val disj_imp = FOLogic.mk_imp (FOLogic.dest_Trueprop (Thm.concl_of th), FOLogic.dest_Trueprop disj)
        val _ = @{print} disj_imp
        val disj_imp_prf = Goal.prove ctxt [] [] (FOLogic.mk_Trueprop disj_imp) (fn _ => reorder_disj ctxt)
        val _ = @{print} disj_imp_prf
        val disj_prf = @{thm mp} OF [disj_imp_prf, th]
        val _ = @{print warning} disj_prf

        fun foldf _ (found, lms, prf, ctxt) =
          let val (nthm, nprf, nctxt) = recon ctxt lms prf
          in (nthm :: found, nthm :: lms, nprf, nctxt)
          end
        val (ths, _, nprf, nctxt) = fold foldf rest ([], lemmas, tl, ctxt)
        (*val _ = @{print} (contra, disj_prf, List.rev (th :: ths))*)
        (*val _ = @{print warning} contra'*)
        val tprf = contra OF (ths @ [disj_prf])
        val _ = @{print} tprf

        (* val to_discharge = Thm.cterm_of nctxt (FOLogic.mk_Trueprop t) *)
        (* val (transform_th, _) = Assumption.assume_export false [to_discharge]; *)

        val xx = Thm.implies_intr (Thm.cterm_of nctxt (FOLogic.mk_Trueprop t)) tprf
        (* val xx = transform_th tprf *)
        val _ = @{print} "implication introduced"
        val _ = @{print warning} xx
        val _ = (Thm.hyps_of xx) |> map (Syntax.pretty_term nctxt) |> Pretty.writeln_chunks
        val _ = @{print warning} "end"
        val _ = @{print} ("Original problem:")
        val _ = Syntax.pretty_term ctxt t |> Pretty.writeln
        val _ = @{print} (th)
        (* val absurd_th = if wasfalse then absurd_impl_pos else absurd_impl_neg *)
        (* val _ = (@{print} "Proving:"; @{print} t; @{print} "with"; @{print} (absurd_th, xx)) *)
        (*val absurd_inst = absurd_th OF [xx]
        val _ = @{print} absurd_inst*)
        (* val final = Goal.prove nctxt [] [] (FOLogic.mk_Trueprop negt) *)
         (* (fn _ => resolve_tac nctxt [absurd_th] 1 THEN resolve_tac nctxt [xx] 1 THEN assume_tac nctxt 1) *)
        val final = finish_rule nctxt xx
        val _ = @{print} "goal proved!"
      in (final, nprf, nctxt)
      end
  | recon _ _ _ = raise Fail "recon"

end


structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);
val trace = Attrib.setup_config_bool @{binding isacop_trace} (K true);

fun cond_tracing true msg = tracing (msg ())
  | cond_tracing false _ = ();

fun TRACE ctxt rl tac i st =
  (cond_tracing (Config.get ctxt trace) (fn () => Thm.string_of_thm ctxt rl); tac i st);


exception Solved

val prove_some =
  let fun todo sub _ prf = SOME (fst sub, prf)
      fun alt () = NONE
  in  mlCoP.prove_default alt todo
  end

(* With every clause, save the theorem (premise) it came from, plus
   the index of the theorem conjunct that contains the clause.  *)
fun recon_info (cls, prem) = map_index (fn (i, cl) => (cl, (i, prem))) cls


fun asdf asms =
  let (*val _ = map (Syntax.pretty_term ctxt o strip_trueprop o Thm.term_of) asms |> Pretty.writeln_chunks*)
    val (skolemised, _) = Skolemisation.skolemise_assms asms
    val clausified = map HOL_to_FOL.clausify (map (#3 o #2) skolemised)
    val (symm, _) = Termmap.insert (Termmap.empty 10000, @{const hashek})
    val (clss, symtab) = HOL_to_FOL.conv_asms clausified symm
  in (clss, symtab, skolemised)
  end

val hashek_finish = @{lemma "~hashek ==> False" by (simp add: hashek_def)}

fun raw_isacop lim = Subgoal.FOCUS (fn {context = ctxt, prems: thm list, concl: cterm, ...} =>
  let (*val _ = map (Syntax.pretty_term ctxt o Thm.term_of) asms |> Pretty.writeln_chunks*)
      val _ = @{print} concl
      val (clss, symtab, sktab) = asdf prems
      val cls = ListPair.mapEq recon_info (clss, sktab) |> List.concat
      val _ = cls |> List.map #1 |> FTerm.pretty_clauses |> Pretty.writeln
      val mat = Matrix.empty 10000
      val _ = Matrix.insert_clauses mat cls
      (* val _ = PolyML.makestring mat |> writeln; *)
      val tac = case prove_some mat lim of
          SOME p =>
            let
              val _ = @{print} p
              val (ctxt', _, ths, prf) = FOL_to_HOL.reconstruct ctxt symtab sktab p
              val _ = map (Thm.pretty_thm ctxt) ths |> Pretty.writeln_chunks;
              val (finalth, _, ctxt'') = Reconstruction.recon ctxt' [] (List.rev prf)
              val finalth' = singleton (Proof_Context.export ctxt'' ctxt) finalth
              val _ = @{print} "reconstruction successful!"
              val _ = @{print} finalth'
              val fals = hashek_finish OF [finalth']
              val _ = @{print} fals
            in resolve_tac ctxt [fals]
            end
        | NONE => (writeln "Sorry, no proof found."; K no_tac)
  in tac 1
  end)

fun isacop_tac lim (ctxt:Proof.context) =
  let
    val lim' = case lim of NONE => Config.get ctxt depth_limit | SOME l => l;
  in
    Object_Logic.atomize_prems_tac ctxt THEN'
    Prenex.prepare_tac ctxt THEN'
    raw_isacop lim' ctxt
  end;

val _ =
  Theory.setup
    (Method.setup @{binding isacop}
      (Scan.lift (Scan.option Parse.nat) >>
        (fn lim => (fn ctxt => SIMPLE_METHOD' (isacop_tac lim ctxt))))
      "lean connection calculus prover");
end
