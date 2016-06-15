(*  Title:      IsaCoP.thy
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Theory to load IsaCoP into FOL.

As this is work in progress, see isaCoP.ML for current limitations.
*)


theory IsaCoP2 imports "~~/src/FOL/FOL" "Preprocessing"
begin


section \<open>Haskek\<close>

(* In memoriam Jaroslav Hašek. *)
definition "hashek == True"


section \<open>Prover and tactic\<close>

declare [[ML_print_depth = 20]]

ML_file "utils.ML"
ML_file "tree.ML"
ML_file "mlcop2.ML"
ML_file "intbimap.ML"
ML_file "isautils.ML"
ML_file "isacop2.ML"

declare [[ML_exception_trace = true]]

(* Miller's example: Drinker's Paradox *)
lemma "\<exists>x. \<forall>y. P(x) \<longrightarrow> P(y)"
apply isacop
sorry

lemma "(\<exists>x. \<not>P(x)) \<or> (\<forall>x. P(x))"
apply isacop
sorry

(* Chad's problem: A lemma that blast cannot solve, but Metis can instantly. *)
lemma "
      \<forall>x y. \<exists>z. Q(x, y, z)
  \<Longrightarrow> \<forall>x y z. P(x) \<longrightarrow> P(y) \<longrightarrow> Q(x, y, z) \<longrightarrow> P(z)
  \<Longrightarrow> \<forall>x y z w. Q(x, y, z) \<longrightarrow> Q(x, y, w) \<longrightarrow> P(z) \<longrightarrow> P(w)
  \<Longrightarrow> \<forall>y z w. Q(a, y, z) \<longrightarrow> Q(a, z, w) \<longrightarrow> Q(b, y, w)
  \<Longrightarrow> P(a)
  \<Longrightarrow> Q(b, a, b)
  \<Longrightarrow> P(b)"
apply (isacop 1000)
sorry
