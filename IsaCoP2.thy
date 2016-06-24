(*  Title:      IsaCoP.thy
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Theory to load IsaCoP into FOL.

As this is work in progress, see isaCoP.ML for current limitations.
*)


theory IsaCoP2 imports "~~/src/FOL/FOL" "Preprocessing"
begin


section \<open>Haskek\<close>

(* In memoriam Jaroslav Hašek, creator of "Švejk". *)
definition "hashek == True"


section \<open>Prover and tactic\<close>

declare [[ML_print_depth = 20]]
declare [[ML_exception_trace = true]]

ML_file "utils.ML"
ML_file "tree.ML"
ML_file "mlcop2.ML"
ML_file "intbimap.ML"
ML_file "isautils.ML"
ML_file "tptp.ML"
ML_file "isacop2.ML"


(* Miller's example: Drinker's Paradox *)
lemma "\<exists>x. \<forall>y. P(x) \<longrightarrow> P(y)"
apply isacop
sorry

lemma "(\<exists>x. \<not>P(x)) \<or> (\<forall>x. P(x))"
apply isacop
sorry

lemma "\<forall>x. (P(x) \<or> ~hashek) \<Longrightarrow> \<forall>x. ~(P(x)) \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop_tac 10 @{context} 1 *})
sorry

(* Example from reviewer 3 -- gets unfortunately simplified too much before *)
lemma "\<forall>x y. P(x,y) \<Longrightarrow> \<not>(\<forall>z. \<exists>w. \<not>P(z,w))"
apply isacop
sorry

(* Example from reviewer 3 again, but this time without simplification *)
lemma "(\<forall>x y. P(x,y) \<or> \<not>hashek) \<Longrightarrow> \<forall>z. \<exists>w. \<not>P(z,w) \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop_tac 10 @{context} 1 *})
sorry

lemma "b \<or> (\<forall>x. (P(x) \<and> b)) \<Longrightarrow> b"
apply (tactic {* IsaCoP.pre_isacop_tac @{context} 1 *})
apply (tactic {* IsaCoP.raw_isacop_tac 10 @{context} 1 *})
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
apply (isacop 100)
sorry
