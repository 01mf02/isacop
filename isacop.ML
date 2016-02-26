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

fun strip_quants quants (Const (quant, _) $ Abs (x, T, t)) =
      if quant = @{const_name "All"} orelse quant = @{const_name "Ex"} then
        strip_quants ((quant, (x, T)) :: quants) t
      else (List.rev quants, t)
  | strip_quants quants t = (List.rev quants, t)

fun map_bndvars f = map_aterms (fn t => case t of Bound i => f i | _ => t)

fun skolemise_term all (((quant, (x, _)), quanti) :: quants, t) ctxt =
  if quant = @{const_name "All"} then skolemise_term (quanti :: all) (quants, t) ctxt
  else
    let val (name, ctxt') = Name.variant (Name.skolem x) ctxt
        val skolem = List.foldl (op $) (Const (name, dummyT)) (List.map Bound all)
        val t' = map_bndvars (fn i => if i = quanti then skolem else Bound i) t
    in skolemise_term all (quants, t') ctxt'
    end
  | skolemise_term _ ([], t) ctxt = (t, ctxt)

fun skolemise_assm assm ctxt =
  let
    val (quants, bare) = strip_quants [] assm
    val indexed = quants ~~ ((List.length quants - 1) downto 0)
  in skolemise_term [] (indexed, bare) ctxt
  end

fun skolemise_assms assms = fold_map skolemise_assm assms Name.context

end


structure Symmap = IntBimap (type key = string val ord = string_ord)



structure HOL_to_FOL =
struct

fun destConstFree (Const (c, T)) = (c, T)
  | destConstFree (Free (f, T)) = (f, T)
  | destConstFree x = raise TERM ("destConstFree", [x])

fun conv_term (Bound b) tab = (FTerm.V b, tab)
  | conv_term t tab =
  let val (P, args) = strip_comb t |>> fst o destConstFree
      val (tab', P') = Symmap.insert (tab, P)
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


structure FOL_to_HOL =
struct

(*
- Get (FO_variable, FO_term) list for theorem
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
  let fun todo sub _ prf = SOME (sub, prf)
      fun alt () = NONE
  in  leanCoP.prove_default alt todo
  end

(* With every clause, save the theorem (premise) it came from, plus
   the index of the theorem conjunct that contains the clause.  *)
fun recon_info (cls, prem) = map_index (fn (i, cl) => (cl, (i, prem))) cls

fun strip_trueprop (Const (@{const_name "Trueprop"}, _) $ t) = t
  | strip_trueprop t = t

fun asdf asms =
  let (*val _ = map (Syntax.pretty_term ctxt o strip_trueprop o Thm.term_of) asms |> Pretty.writeln_chunks*)
    val clausify =
         map (strip_trueprop o Thm.term_of)
      #> Skolemisation.skolemise_assms
      #> fst
      #> map HOL_to_FOL.clausify
    val (symm, _) = Symmap.insert (Symmap.empty 10000, @{const_name hashek})
    val (clss, tab) = HOL_to_FOL.conv_asms (clausify asms) symm
  in (clss, tab)
  end


fun isacop_focus ({context = ctxt, prems: thm list, asms: cterm list, concl: cterm, ...}) =
  let (*val _ = map (Syntax.pretty_term ctxt o Thm.term_of) asms |> Pretty.writeln_chunks*)
      val (clss, _) = asdf asms
      val cls = ListPair.mapEq recon_info (clss, prems) |> List.concat
      val _ = cls |> List.map #1 |> FTerm.pretty_clauses |> Pretty.writeln
      val mat = Matrix.empty 10000
      val _ = Matrix.insert_clauses mat cls
      (* val _ = PolyML.makestring mat |> writeln; *)
      val _ = case prove_some mat 10 of
          SOME p => (@{print} p; raise Solved)
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
