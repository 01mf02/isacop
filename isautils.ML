structure IsaUtils =
struct

(* adapted from FOL_basic_ss in simpdata.ML *)
fun mini_simpset ctxt =
  empty_simpset ctxt
(*setSSolver (mk_solver "FOL safe" safe_solver)
  setSolver (mk_solver "FOL unsafe" unsafe_solver)*)
(*|> Simplifier.set_subgoaler asm_simp_tac*)
  |> Simplifier.set_mksimps (mksimps mksimps_pairs)
  |> Simplifier.set_mkcong mk_meta_cong
  |> simpset_of

fun simp_only_tac ctxt ths =
  put_simpset (mini_simpset ctxt) ctxt addsimps ths
  |> TRY oo asm_full_simp_tac

fun make_conj_rule [] = @{thm TrueI}
  | make_conj_rule (th :: []) = th
  | make_conj_rule (th :: ths) = @{thm conjI} OF [th, make_conj_rule ths]

val make_conj_rule_test =
  let val ths = map Thm.assume [@{cprop P}, @{cprop Q}]
  in @{assert} (Thm.prop_of (make_conj_rule ths) = @{prop "P \<and> Q"})
  end

(* Negate goal and move it to first position. *)
(* P1 ==> ... Pn ==> G
   ------------------------------
   P1 ==> ... Pn ==> False ==> ~G
   ------------------------------
   ~G ==> P1 ==> ... Pn ==> False
*)
fun neg_goal_tac ctxt =
  resolve_tac ctxt @{thms ccontr} THEN' rotate_tac ~1

fun pnf_cnf_tac ctxt =
  simp_only_tac ctxt @{thms meta_simps IFOL_simps cla_simps} THEN'
  simp_only_tac ctxt @{thms prenex_ex prenex_all} THEN'
  simp_only_tac ctxt @{thms precnf_simps} THEN'
  simp_only_tac ctxt @{thms cnf_simps} THEN'
  simp_only_tac ctxt @{thms conj_simps disj_simps}

end