theory Mizar_Defs
imports Mizar_Reserve
begin

(* W tym pliku wprowadzimy: *)
(*
mdefinition ("{_}")
  "let y be object"
func "{y}" \<rightarrow> set means
  "for x holds x in it iff x = y"
existence .
uniqueness .
*)

lemma means_property:
assumes df: "f = the1(\<lambda>x. Q implies x is D & P(x))"
 and q: "Q"
 and ex: "ex x being D st P (x)"
 and un: "\<And>x y. x is D \<Longrightarrow> y is D \<Longrightarrow> 
     P (x) \<Longrightarrow> P (y) \<Longrightarrow> x = y"
 shows "f is D & P(f) & (x is D & P(x) implies x = f)"
text_raw {*}%EndSnippet*}
unfolding df
proof
  have e: "Ex (\<lambda>x. Q implies x is D & P(x))" using ex q by auto
  have u: "\<And>x y. (Q implies x is D & P(x)) & (Q implies y is D & P(y)) implies x = y" using un q by auto
  show x: "the1(\<lambda>x. Q implies x is D & P(x)) is D & P(the1(\<lambda>x. Q implies x is D & P(x)))" using the1_property[OF e u] q by auto
  thus "x is D & P(x) implies x = the1(\<lambda>x. Q implies x is D & P(x))" using un by auto
qed

lemma equals_property:
assumes df: "f = the1(\<lambda>x. Q implies x be D & x=g)"
 and q: "Q"
 and coherence: "g be D"
 shows "f is D & f = g"
text_raw {*}%EndSnippet*}
proof -
  have ex: "ex x being D st x=g" using coherence by auto
  show "f is D & (f = g)" using means_property[OF df q ex] by auto
qed

lemma equals_property_nolet:
assumes df: "f = the1(\<lambda>x.(x be D & x=g))"
 and coherence: "g is D"
 shows "f is D & (f = g)"
using equals_property[of f True D g] assms by auto

lemma mode_property:
assumes df: "M \<equiv> define_mode(\<lambda>x. Q implies x be D & P(x))"
 and q: "Q"
 and ex: "ex x being D st P (x)"
 shows "(x is M iff (x is D & P(x))) & Ex (\<lambda>x. x is M)" using q ex defmode_property[OF df] by auto

lemma mode_property_nolet:
assumes df: "M \<equiv> define_mode(\<lambda>x. x be D & P(x))"
 and ex1: "ex x being D st P (x)"
 shows "(x is M iff (x is D & P(x))) & Ex (\<lambda>x. x is M)" using mode_property[of M True D P] assms by auto

abbreviation (input) means_prefix
   ("let _ func _ \<rightarrow> _ means _" [0,0,0] 10)
where "let lt func def \<rightarrow> dom means cond \<equiv>
  def = the1 (\<lambda>it. lt implies (it be dom & cond(it)))"

abbreviation (input) equals_prefix
   ("let _ func _ \<rightarrow> _ equals _" [0,0,0] 10)
where "let lt func def \<rightarrow> dom equals exp \<equiv>
   def = the1 (\<lambda>it. lt implies (it be dom & it = exp))"
text_raw {*}%EndSnippet*}

abbreviation (input) equals_prefix_nolet
   ("func _ \<rightarrow> _ equals _" [10,10] 10)
where "func a \<rightarrow> b equals c \<equiv>
   a = the1 (\<lambda>it. it be b & it = c)"

(* Here we could use the following syntax translation instead of an abbreviation to introduce a
   named lambda.*)
abbreviation (input) attr_prefix ("let _ attr _ means _" [10,10,10] 10)
where "let lt attr def means exp \<equiv> (def \<equiv> define_attr(\<lambda>it. lt(it) & exp(it)))"
(*syntax attr_prefix :: "o \<Rightarrow> a \<Rightarrow> s \<Rightarrow> o \<Rightarrow> o" ("let _ attr _ is _ means _" [10,10,10,10] 10)
translations "attr_prefix(lt,X,def,exp)" => "CONST Pure.eq(def, CONST define_attr(\<lambda>X. lt & exp))"*)

abbreviation (input) attr_prefix_nolet ("attr _ means _" [10,10] 10)
where "attr def means exp \<equiv> (def \<equiv> CONST define_attr(exp))"

abbreviation (input) mode_prefix ("let _ mode _ \<rightarrow> _ means _" [10,10,10,10] 10)
where "let lt mode M \<rightarrow> b means c \<equiv> (M \<equiv> define_mode(\<lambda>it. lt implies (it be b & c(it))))"

abbreviation (input) mode_prefix_nolet ("mode _ \<rightarrow> _ means _" [10,10,10] 10)
where "mode M \<rightarrow> b means c \<equiv> (M \<equiv> define_mode(\<lambda>it.(it be b & c(it))))"

abbreviation (input) cluster_prefix_fun ("let _ cluster _ \<rightarrow> _" [10,10,10] 10)
where "let lt cluster fun \<rightarrow> attrs \<equiv> (lt implies is_attr (fun,attrs))"

abbreviation (input) cluster_prefix_ex ("let _ cluster _ for _" [10,10,10] 10)
where "let lt cluster attrs for type \<equiv> (lt implies (ex X being type st is_attr(X, attrs)))"

abbreviation (input) cluster_prefix_attrs2 ("let _ cluster _ \<rightarrow> _ for _" [10,10,10,10] 10)
where "let lt cluster attrs1 \<rightarrow> attrs2 for type \<equiv> (lt implies (for X being type st is_attr(X, attrs1) holds is_attr(X, attrs2)))"

abbreviation (input) cluster_prefix_attrs ("let _ cluster \<rightarrow> _ for _" [10,10,10] 10)
where "let lt cluster \<rightarrow> attrs2 for type \<equiv> (lt implies (for X being type holds is_attr(X, attrs2)))"

abbreviation (input) cluster_prefix_fun_nolet ("cluster _ \<rightarrow> _" [10,10] 10)
where "cluster fun \<rightarrow> attrs \<equiv> is_attr(fun, attrs)"

abbreviation (input) cluster_prefix_ex_nolet ("cluster _ for _" [10,10] 10)
where "cluster attrs for type \<equiv> (ex X being type st is_attr(X, attrs))"

end
