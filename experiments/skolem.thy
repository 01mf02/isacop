theory skolem imports "~~/src/FOL/FOL"
begin

lemma
  assumes c:"\<forall>x::nat. P(x)"
  assumes b:"\<forall>y::nat. \<exists>u::nat. Q(y,u)"
shows "\<exists>u. P(u) \<and> Q(0,u)"
proof -
  have d: "\<exists>y. Q(0,y)" using b by blast (* P(0, ey(0)) *)
  obtain u where f: "Q(0,u)" using d by blast
  have e: "P(u)" using c by blast
  have "P(u) \<and> Q(0,u)" using e f by blast
  thus "\<exists>u. P(u) \<and> Q(0,u)" by blast
qed

lemma
  assumes c:"\<forall>x::nat. \<not>P(x)"
  assumes a:"\<forall>y::nat. \<exists>u::nat. R(y,u)"
  assumes b:"\<forall>z::nat. \<exists>w::nat. Q(z,w)"
shows "\<exists>u w. \<not>P(w) \<and> Q(u, w) \<and> R(0,u)"
proof -
  have d: "\<exists>u. R(0,u)" using a by blast (* R(0, ey(0)) *)
  then obtain u where f: "R(0,u)" by blast
  have "\<exists>w. Q(u, w)" using b by blast
  then have "\<exists>w. Q(u, w) \<and> R(0,u)" using f by blast
  then obtain w where g: "Q(u, w) \<and> R(0,u)" by blast
  have "\<not>P(w)" using c by blast
  then have "\<not>P(w) \<and> Q(u, w) \<and> R(0,u)" using g by blast
  thus "\<exists>u w. \<not>P(w) \<and> Q(u, w) \<and> R(0,u)" by blast
qed

lemma
  assumes c:"\<forall>x::nat. P(x)"
  assumes a:"\<forall>y::nat. \<exists>u::nat. R(y,u)"
  assumes b:"\<forall>z::nat. \<exists>w::nat. Q(z,w)"
shows "\<exists>u w. P(w) \<and> Q(u, w) \<and> R(0,u)"
proof -
  have d: "\<exists>u. R(0,u)" using a by blast (* R(0, ey(0)) *)
  then obtain u where f: "R(0,u)" by blast
  have "\<exists>w. Q(u, w)" using b by blast
  then have "\<exists>w. Q(u, w) \<and> R(0,u)" using f by blast
  then obtain w where g: "Q(u, w) \<and> R(0,u)" by blast
  have "P(w)" using c by blast
  then have "P(w) \<and> Q(u, w) \<and> R(0,u)" using g by blast
  thus "\<exists>u w. P(w) \<and> Q(u, w) \<and> R(0,u)" by blast
qed


lemma
  assumes "\<forall>x z. P(f(x), z)"
  shows "\<exists>y. \<forall>w. P(y, w)"
proof (rule ccontr)
  fix x
  assume "\<not> (\<exists>y. \<forall>w. P(y, w))"
  then have NC: "\<forall>y. \<exists>w. \<not> P(y, w)" by auto

  have NCy: "\<exists>w. \<not>P(f(x), w)" using NC by auto
  show False
  proof (rule exE[OF NCy])
    fix w
    assume NCyw: "\<not> P(f(x), w)"
    then show False using spec[OF spec[OF assms(1)]] by contradiction
  qed
qed

definition "hashek == True"

lemma hashek_prop:
  assumes "a \<and> hashek"
  assumes "b \<and> hashek"
  shows "a \<and> b"
using assms unfolding hashek_def by simp

ML {*

val x = 2;

*}

print_simpset

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


lemma "((\<forall>x. P(x,y,z)) \<and> Q) \<longleftrightarrow> (\<forall>x. (P(x,y,z) \<and> Q))"
using [[simp_trace]] apply simp
done

thm FOL.IFOL_simps
thm FOL.int_all_simps
thm FOL.cla_simps

thm refl [THEN P_iff_T]
thm conj_simps
thm disj_simps
thm not_simps
thm imp_simps
thm iff_simps
thm quant_simps


lemma "\<forall>x. ((P(x) \<longleftrightarrow> a \<and> b) \<or> ((\<forall>z. R(z,s)) \<or> (\<exists>y. \<forall>w. \<exists>v. Q(y, w, v)) \<and> r)) \<or> z \<Longrightarrow> a \<or> (b \<and> c) \<Longrightarrow> True \<Longrightarrow> False"
apply (simp only: meta_simps IFOL_simps cla_simps)
apply (simp only: prenex_ex prenex_all)
apply (simp only: precnf_simps)
apply (simp only: cnf_simps)
apply (simp only: conj_simps disj_simps)
oops

ML_file "../isacop.ML"

lemma "True \<Longrightarrow> False"
apply (tactic {* TRY (asm_full_simp_tac @{context} 1) *})
oops


lemma
  "\<forall>x. ((P(x) \<longleftrightarrow> a \<and> b) \<or> ((\<forall>z. R(z,s)) \<or> (\<exists>y. \<forall>w. \<exists>v. Q(y, w, v)) \<and> r)) \<or> z \<Longrightarrow> a \<or> (b \<and> c) \<Longrightarrow> True \<Longrightarrow> False"
  "a \<or> \<not>a"
by (isacop 1)

lemma "Q \<Longrightarrow> R \<Longrightarrow> \<forall>x. P(x) \<or> \<not>P(x)"
by (isacop 1)