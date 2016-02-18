theory skolem imports "~~/src/FOL/FOL"
begin

lemma
  assumes c:"\<forall>x. P(x)"
  assumes b:"\<forall>y. \<exists>u. Q(y,u)"
shows "\<exists>u. P(u) \<and> Q(a,u)"
proof -
  have d: "\<exists>y. Q(a,y)" using b by blast (* P(0, ey(0)) *)
  obtain u where f: "Q(a,u)" using d by blast
  have e: "P(u)" using c by blast
  have "P(u) \<and> Q(a,u)" using e f by blast
  thus "\<exists>u. P(u) \<and> Q(a,u)" by blast
qed

lemma
  assumes c:"\<forall>x. \<not>P(x)"
  assumes a:"\<forall>y. \<exists>u. R(y,u)"
  assumes b:"\<forall>z. \<exists>w. Q(z,w)"
shows "\<exists>u w. \<not>P(w) \<and> Q(u, w) \<and> R(a,u)"
proof -
  have d: "\<exists>u. R(a,u)" using a by blast (* R(0, ey(0)) *)
  then obtain u where f: "R(a,u)" by blast
  have "\<exists>w. Q(u, w)" using b by blast
  then have "\<exists>w. Q(u, w) \<and> R(a,u)" using f by blast
  then obtain w where g: "Q(u, w) \<and> R(a,u)" by blast
  have "\<not>P(w)" using c by blast
  then have "\<not>P(w) \<and> Q(u, w) \<and> R(a,u)" using g by blast
  thus "\<exists>u w. \<not>P(w) \<and> Q(u, w) \<and> R(a,u)" by blast
qed

lemma
  assumes c:"\<forall>x. P(x)"
  assumes a:"\<forall>y. \<exists>u. R(y,u)"
  assumes b:"\<forall>z. \<exists>w. Q(z,w)"
shows "\<exists>u w. P(w) \<and> Q(u, w) \<and> R(a,u)"
proof -
  have d: "\<exists>u. R(a,u)" using a by blast (* R(0, ey(0)) *)
  then obtain u where f: "R(a,u)" by blast
  have "\<exists>w. Q(u, w)" using b by blast
  then have "\<exists>w. Q(u, w) \<and> R(a,u)" using f by blast
  then obtain w where g: "Q(u, w) \<and> R(a,u)" by blast
  have "P(w)" using c by blast
  then have "P(w) \<and> Q(u, w) \<and> R(a,u)" using g by blast
  thus "\<exists>u w. P(w) \<and> Q(u, w) \<and> R(a,u)" by blast
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
