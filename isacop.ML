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

fun skolemise_term all ex (((quant, (x, _)), quanti) :: quants) t ctxt =
  (case quant of
    All => skolemise_term (quanti :: all) ex quants t ctxt
  | Ex =>
      let val (name, ctxt') = Name.variant (Name.skolem x) ctxt
          val skolem = list_comb (Const (name, dummyT), List.map Bound (rev all))
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

val reconstruct : Proof.context -> Termmap.bimap -> Skolemisation.table ->
  Subst.subst * (int * Skolemisation.mapping) leanCoP.proof -> thm list

end

structure FOL_to_HOL : FOL_TO_HOL =
struct

fun conv_sym tab sym = case Termmap.backward (tab, sym) of
      SOME t => t
    | NONE => raise Fail ("conv_sym: " ^ Int.toString sym)

fun conv_term _ (FTerm.V v) = Bound v
  | conv_term tab (FTerm.A (f, args)) =
    list_comb (conv_sym tab f, map (conv_term tab) args)

fun destResolution (leanCoP.Resolution r) = SOME r
  | destResolution _ = NONE

fun get_subs off vars =
     filter (fn (v, _) => off <= v andalso v < off + vars)
  #> sort (prod_ord int_ord (K EQUAL))
  #> rev

fun inst_spec ct th =
  th RS (instantiate' [SOME (Thm.ctyp_of_cterm ct)] [NONE, SOME ct] @{thm spec})

fun obtain_ex th ctxt =
  let val ((x, th'), ctxt') = Obtain.result (fn _ => etac @{thm exE} 1) [th] ctxt
  in ((the_single x, the_single th'), ctxt')
  end

(*Go through substitution.
  If a term is mapped to an application A (f, fa)
    If f is a Skolem symbol
      If A (f, fa) is in tmmap, return tmmap entry
      Else fail
    Else recurse into fa and replace stuff there
  Else (term is mapped to a variable v)
    If v is in substitution
      Handle substitute for v
    Else
      Fix a new variable for v and return it
*)

exception Unsubst

fun dest_skolem f symmap =
  let val t = Termmap.backward (symmap, f)
  in
    case t of
      SOME (Const (x, _)) => SOME x
    | SOME (Const (x, _) $ _) => SOME x
    | _ => NONE
  end

fun invent_universal v (tmmap, ctxt) =
  let (*TODO: Perhaps we need to do more here? (Making type most general?)
        See Isar Implementation manual, p. 119 *)
      val (var, ctxt') = Variable.variant_fixes [Int.toString v] ctxt
      val t' = Syntax.read_term ctxt' (the_single var)
      val tmmap' = (FTerm.V v, t') :: tmmap
  in (t', (tmmap', ctxt'))
  end

fun unsubst (maps as (symmap, skmap)) (t as FTerm.A (f, args)) (acc as (tmmap, _)) =
      let val ft = dest_skolem f symmap
      in
        (*f is a Skolem symbol*)
        if Option.isSome ft andalso List.exists (fn (_, (_, syms, _)) => member (op =) syms (Option.valOf ft)) skmap then
          (case AList.lookup (op =) tmmap t  of
            SOME ho => (ho, acc)
          | NONE => raise Unsubst)
        else
          let val f' = case Termmap.backward (symmap, f) of SOME ho => ho | NONE => raise Fail "unsubst"
              val (args', acc') = fold_map (unsubst maps) args acc
          in  (list_comb (f', args'), acc')
          end
      end
  | unsubst _ (t as FTerm.V v) (acc as (tmmap, _)) =
      case AList.lookup (op =) tmmap t of
        SOME tm => (tm, acc)
      | NONE => invent_universal v acc

(* TODO: merge this with get_sub *)
fun fill_sub off vars sub (tmmap, ctxt) =
  let
    fun f i acc =
      case AList.lookup (op =) sub i of
        SOME t => (t, acc)
      | NONE => invent_universal i acc
  in
    fold_map f (off upto off + vars - 1) (tmmap, ctxt)
  end


(*Fold over quantifiers of a formula.
  If existential, instantiate via snippet.
  If universal, get from substitution
*)

(* TODO: give this function also the tmmap, and save new variable x together with original FTerm *)
(* for this, pass also FTerms that were used as Skolem terms *)
fun treat_quant Skolemisation.All (th, sub::substs, ctxt) =
      (inst_spec (Thm.cterm_of ctxt sub) th, substs, ctxt)
  | treat_quant Skolemisation.All (_, [], _) = raise Fail "not enough All instances"
  | treat_quant Skolemisation.Ex  (th, substs, ctxt) =
      let val ((x, th'), ctxt') = obtain_ex th ctxt
      in (th', substs, ctxt')
      end

(*We need two mappings:
  - one from (int * thm) to thm (thmap), and
  - one from FTerm.term to Isabelle terms (tmmap), containing Skolem terms *)
fun treat_res (symtab, sktab, sub) (res as (lit, (off, (_, _, vars, (i, skm as (thm, (quants, _, _))))))) ((ctxt, thmap, tmmap), todo) =
  let
    val th_subs = get_subs off vars sub
    val maps = (symtab, sktab)
    val (th_subs', (tmmap', ctxt')) = fold_map (fn (v, t) => fn acc => let val (t', acc') = unsubst maps t acc in ((v, t'), acc') end) th_subs (tmmap, ctxt)
    val (th_subs'', (tmmap'', ctxt'')) = fill_sub off vars th_subs' (tmmap', ctxt')
  in
    (* TODO: fail if Skolem variables in substitution that are not in mapping *)
    if length th_subs = vars then
      let val (inst', [], ctxt''') = fold treat_quant (map #1 quants) (thm, th_subs'', ctxt'')
      in ((ctxt''', ((i, skm), inst') :: thmap, tmmap), todo)
      end
    else
      ((ctxt, thmap, tmmap), res :: todo)
  end

fun iterate f acc [] = acc
  | iterate f acc todo =
      let val (acc', todo') = fold f todo (acc, [])
      in
        if List.length todo = List.length todo' then raise (Fail "iterate")
        else iterate f acc' todo'
      end


fun reconstruct ctxt symtab sktab (sub, prf) =
  let
    val res = map_filter destResolution prf
    val (ctxt', thmap, tmmap) = iterate (treat_res (symtab, sktab, sub)) (ctxt, [], []) res
  in (map snd thmap)
  end

(*
- If all term references to foreign Skolem functions are in mapping,
  instantiate theorem with corresponding terms and
  add Skolem function reference to mapping (FO_term, HO_term)
- Else postpone theorem
- Iterate this procedure over all theorems in extension steps
- If procedure terminates with non-empty list, fail
- Map every extension step theorem now to its instantiated version
  and select the conjunct with the correct assumption number
*)

end


structure IsaCoP =
struct

val depth_limit = Attrib.setup_config_int @{binding isacop_depth_limit} (K 20);
val trace = Attrib.setup_config_bool @{binding isacop_trace} (K true);

fun cond_tracing true msg = tracing (msg ())
  | cond_tracing false _ = ();

fun TRACE ctxt rl tac i st =
  (cond_tracing (Config.get ctxt trace) (fn () => Display.string_of_thm ctxt rl); tac i st);


exception Solved

val prove_some =
  let fun todo sub _ prf = SOME (fst sub, prf)
      fun alt () = NONE
  in  leanCoP.prove_default alt todo
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


fun isacop_focus ({context = ctxt, prems: thm list, concl: cterm, ...}) =
  let (*val _ = map (Syntax.pretty_term ctxt o Thm.term_of) asms |> Pretty.writeln_chunks*)
      val (clss, symtab, sktab) = asdf prems
      val cls = ListPair.mapEq recon_info (clss, sktab) |> List.concat
      val _ = cls |> List.map #1 |> FTerm.pretty_clauses |> Pretty.writeln
      val mat = Matrix.empty 10000
      val _ = Matrix.insert_clauses mat cls
      (* val _ = PolyML.makestring mat |> writeln; *)
      val _ = case prove_some mat 10 of
          SOME p => (@{print} p; FOL_to_HOL.reconstruct ctxt symtab sktab p |> map (Display.pretty_thm ctxt) |> Pretty.writeln_chunks; raise Solved)
        | NONE => writeln "Sorry, no proof found."
  in all_tac
  end


fun raw_isacop ctxt =
  Subgoal.FOCUS isacop_focus ctxt THEN'
  K all_tac

fun isacop_tac (ctxt:Proof.context) lim =
  let
    val start = Timing.start ();
    val lim = Config.get ctxt depth_limit;
  in
    Object_Logic.atomize_prems_tac ctxt THEN' Prenex.prepare_tac ctxt THEN' raw_isacop ctxt
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
