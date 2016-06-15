theory Preprocessing imports "~~/src/FOL/FOL"
begin


section \<open>Clausification\<close>

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

end