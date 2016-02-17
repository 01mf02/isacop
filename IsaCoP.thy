theory IsaCoP imports "~~/src/FOL/FOL"
begin


section {* Haskek *}

definition "hashek == True"

lemma hashekE:
  assumes "P \<and> hashek"
  shows "P"
using assms unfolding hashek_def by simp


section {* Clausification *}

lemma imp_clause: "(a \<longrightarrow> b) \<longleftrightarrow> \<not>a \<or> b"
by blast

lemma iff_clause: "(a \<longleftrightarrow> b) \<longleftrightarrow> ((a \<longrightarrow> b) \<and> (b \<longrightarrow> a))"
by blast

lemmas precnf_simps = imp_clause iff_clause


lemma disj_conj: "a \<or> (b \<and> c) \<longleftrightarrow> (a \<or> b) \<and> (a \<or> c)"
by blast

lemma conj_disj: "(b \<and> c) \<or> a \<longleftrightarrow> (a \<or> b) \<and> (a \<or> c)"
by blast

lemmas cnf_simps = disj_conj conj_disj


lemma conj_ex: "a \<and> (\<exists>x. P(x)) \<longleftrightarrow> (\<exists>x. P(x) \<and> a)"
by auto

lemma ex_conj: "(\<exists>x. P(x)) \<and> a \<longleftrightarrow> (\<exists>x. P(x) \<and> a)"
by simp

lemma disj_ex: "a \<or> (\<exists>x. P(x)) \<longleftrightarrow> (\<exists>x. P(x) \<or> a)"
by auto

lemma ex_disj: "(\<exists>x. P(x)) \<or> a \<longleftrightarrow> (\<exists>x. P(x) \<or> a)"
by simp


lemma conj_all: "a \<and> (\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. P(x) \<and> a)"
by auto

lemma all_conj: "(\<forall>x. P(x)) \<and> a \<longleftrightarrow> (\<forall>x. P(x) \<and> a)"
by simp

lemma disj_all: "a \<or> (\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. P(x) \<or> a)"
by auto

lemma all_disj: "(\<forall>x. P(x)) \<or> a \<longleftrightarrow> (\<forall>x. P(x) \<or> a)"
by simp

lemmas prenex_ex  = conj_ex   ex_conj disj_ex   ex_disj
lemmas prenex_all = conj_all all_conj disj_all all_disj


section {* Prover and tactic *}

ML_file "leancop.ML"
ML_file "intbimap.ML"
ML_file "isacop.ML"


section {* Tests *}

ML_val {*
open FTerm;
Unif.unify_contra ([], 0) (0, [V 0]) ([V 1], [], 1);

val clauses = [[(~1, []), (~2, [A (3, [])])], [(2, [V 0])]];

@{assert} (Unif.unify ([], 0) (0, [V 0]) (0, [A (0, [])]) = SOME ([(0, A (0, []))], 0));
@{assert} (Unif.unify ([(0, A (2, []))], 0) (0, [V 0]) (0, [A (1, [])]) = NONE);

@{assert} (Unif.unify_contra ([], 0) (0, []) ([], [], 0) = SOME (([], 0), []));

(*val mat = Matrix.empty 6;
Matrix.insert_clauses mat clauses;

writeln "Starting leanCoP ...";
leanCoP.prove_exception mat 10;*)
*}


declare [[ML_print_depth = 50]]
ML {* @{term "\<forall>x. \<exists>y. f(x, y) \<and> Q(r)"} *}

lemma "\<not>b(x) \<or> \<not>hashek \<Longrightarrow> \<forall>y. (b(y)) \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop @{context} 1 *} )

lemma "\<forall>x y. P(x,y) \<Longrightarrow> \<exists>a. \<forall>b. P(a, b)"
apply (isacop 1)

lemma "\<And>a. \<forall>x. \<exists>y. P(x,y) \<Longrightarrow> \<forall>x. P(f(x),a) \<Longrightarrow> Q(r)"
apply (isacop 1)

lemma
  "\<And>s. \<forall>x. ((P(x) \<longleftrightarrow> a \<and> b) \<or> ((\<forall>z. R(z,s)) \<or> (\<exists>y. \<forall>w. \<exists>v. Q(y, w, v)) \<and> r)) \<or> z \<Longrightarrow> a \<or> (b \<and> c) \<Longrightarrow> True \<Longrightarrow> False"
apply (isacop 1)
sorry


lemma "\<And>y. y \<Longrightarrow> Q \<Longrightarrow> R \<Longrightarrow> \<forall>x. P(x)"
by (isacop 1)

end
