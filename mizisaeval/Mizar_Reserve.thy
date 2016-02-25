theory Mizar_Reserve
imports Mizar
keywords "reserve" :: thy_decl
     and "mtheorem" :: thy_goal
begin

ML {*
structure Miz_Reserve_Data = Theory_Data
(
  type T = term Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge _ = Symtab.empty;
);
fun reserve_cmd (vs, tm) lthy =
  let
    val lthy' = Local_Theory.background_theory
      (Sign.add_syntax Syntax.mode_default
        [("Mizar.attr_mode", @{typ "a => m => m"}, Infixr ("", 50))]) lthy
    val tm = (Syntax.read_term lthy' tm)
    val _ = if fastype_of tm <> @{typ "m"} then
      raise Fail "not a correctly typed constraint" else ();
    fun reserve thy =
      fold (fn v => fn thy => Miz_Reserve_Data.map (Symtab.update (v, tm)) thy)
        vs thy;
  in Local_Theory.background_theory reserve lthy end;

val () =
  Outer_Syntax.local_theory @{command_keyword reserve}
    "reserve variable names with types"
    ((Parse.list1 Parse.text -- (Parse.$$$ "for" |-- Parse.term)) >> reserve_cmd);
*}

ML {*
fun setup_proof ((name, attr), str) lthy =
  let
    val prop = Syntax.read_prop lthy str
    val attr = map (Attrib.check_src lthy) attr;
    val fs = Term.add_frees prop []
    val _ = if filter_out (fn (_, ty) => ty = @{typ s}) fs <> [] then
      warning "Warning: Free variables! Is it a scheme?" else ()
    val setfs = filter (fn (_, ty) => ty = @{typ s}) fs
    fun do_var (v as (n, _)) (lthy, assms) =
      (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of lthy)) n of
        NONE => raise Fail ("Non-reserved free set variable: " ^ n ^ " in goal!")
      | SOME D =>
          let val (_, lthy) = Variable.add_fixes [n] lthy;
          val cp = Thm.cterm_of lthy (FOLogic.mk_Trueprop ((@{term is_mode} $ (Free v)) $ D))
          val (assm, lthy) = yield_singleton (Assumption.add_assms Assumption.presume_export) cp lthy
          in (lthy, assm :: assms) end)
    val (lthy2, assms) = fold do_var setfs (lthy, [])
    val (_, lthy3) = Proof_Context.note_thmss "" [((Binding.name Auto_Bind.assmsN, []), [(assms, [])])] lthy2
    fun after_qed thms lthy' =
      let
      val a = [((name, attr), [(flat thms, [])])];
(*      val _ = tracing (PolyML.makestring a)*)
      val a = Attrib.partial_evaluation lthy' a;
(*      val _ = tracing (PolyML.makestring a)*)
      in
      Local_Theory.notes a lthy' |> snd end;
  in
    Proof.theorem NONE after_qed [[(prop, [])]] lthy3
  end;

Outer_Syntax.local_theory_to_proof @{command_keyword "mtheorem"} "Mizar theorem"
  ((Parse_Spec.opt_thm_name ":" -- Parse.prop) >> setup_proof)
*}

parse_translation {* [(@{syntax_const "_BallML2"},
  let fun tr ctxt [((Const (@{syntax_const "_vs"}, _)) $ (v as (_ $ (vv as Free (n, _)) $ _)) $ vs), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BallML2a: Variable " ^ n ^ " not reserved and 'being' not given!")
          | SOME D => Syntax.const @{const_syntax Ball} $ D $ (Syntax_Trans.abs_tr [v, tr ctxt [vs, P]]))
        | tr ctxt [(v as (_ $ (vv as Free (n, _)) $ _)), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BallML2b: Variable " ^ n ^ " not reserved and 'being' not given!")
          | SOME D => Syntax.const @{const_syntax Ball} $ D $ (Syntax_Trans.abs_tr [v, P]))
  in tr end)] *}

parse_translation {* [(@{syntax_const "_BexML2"},
  let fun tr ctxt [((Const (@{syntax_const "_vs"}, _)) $ (v as (_ $ (vv as Free (n, _)) $ _)) $ vs), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BexML2a: Variable " ^ n ^ " not reserved and 'being' not given!")
          | SOME D => Syntax.const @{const_syntax Bex} $ D $ (Syntax_Trans.abs_tr [v, tr ctxt [vs, P]]))
        | tr ctxt [(v as (_ $ (vv as Free (n, _)) $ _)), P] =
          (case Symtab.lookup (Miz_Reserve_Data.get (Proof_Context.theory_of ctxt)) n of
            NONE => raise Fail ("BexML2b: Variable " ^ n ^ " not reserved and 'being' not given!")
          | SOME D => Syntax.const @{const_syntax Bex} $ D $ (Syntax_Trans.abs_tr [v, P]))
  in tr end)] *}

(*consts Function :: mode
reserve x for Function
mtheorem bla[rule_format]: "P \<longrightarrow> x = (x :: st)"
thm assms
by auto
print_theorems
thm bla*)
(*declare [[syntax_ambiguity_warning=false]]*)

end
