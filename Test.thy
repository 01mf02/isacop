theory Test imports "~~/src/FOL/FOL"
begin

definition "Pre(x) \<equiv> True"


lemma "\<lbrakk>x1 = x2; Pre(x1)\<rbrakk> \<Longrightarrow> Pre(x2)"
proof -
  
ML_prf {*
val ctxt0 = @{context}
val (fixes, ctxt1) = Variable.add_fixes ["x1", "x2"] ctxt0
val ([tyin], tyout) = strip_type (type_of @{term Pre})
val ([x1, x2]) = map (fn n => Free (n, tyin)) fixes
val eq = Logic.mk_equals (x1, x2)
val ass = Assumption.assume ctxt1 (Thm.cterm_of ctxt1 eq)
*}
  assume E: "x1 = x2"
  {
    assume P: "Pre(x1)"
    have "Pre(x2)" using P unfolding E .
  }
  note i = this
  show "Pre(x1) \<Longrightarrow> Pre(x2)" using i .
qed

end