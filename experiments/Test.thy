theory Test imports FOL "~~/src/FOL/ex/Nat"
begin

find_theorems name: exE

lemma
  assumes A1: "\<forall>x. \<exists>y. P(x, y)"
  shows PC: "\<exists>a b. P(0, a) \<and> P(Suc(0), b)"
proof (rule ccontr)
  assume "\<not> (\<exists>a b. P(0, a) \<and> P(Suc(0), b))"
  then have NC: "\<forall>a b. \<not>P(0, a) \<or> \<not>P(Suc(0), b)" by simp

  have A10: "\<exists>y. P(0,      y)" by (rule allE[OF A1])
  have A1S: "\<exists>y. P(Suc(0), y)" by (rule allE[OF A1])

  show False
  proof (rule exE[OF A10], rule exE[OF A1S])
    fix a b
    assume A10a: "P(0, a)"
    assume A1Sb: "P(Suc(0), b)"
    have NCab: "\<not> P(0, a) \<or> \<not> P(Suc(0), b)" using NC by auto
    show False
    proof (rule disjE[OF NCab])
      assume "\<not> P(0, a)"
      then show False using A10a by contradiction
    next
      assume "\<not> P(Suc(0), b)"
      then show False using A1Sb by contradiction
    qed
  qed
qed

end