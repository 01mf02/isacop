theory IsaCoP imports "~~/src/FOL/FOL"
begin


section \<open>Haskek\<close>

definition "hashek == True"

lemma hashekE:
  assumes "P \<and> hashek"
  shows "P"
using assms unfolding hashek_def by simp


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


section \<open>Prover and tactic\<close>

ML_file "leancop.ML"
ML_file "intbimap.ML"
ML_file "isacop.ML"


section \<open>Tests\<close>

ML_val {*
open FTerm;
Unif.unify_contra ([], 0) (0, [V 0]) ([V 1], [], 1, NONE);

val clauses = [[(~1, []), (~2, [A (3, [])])], [(2, [V 0])]];

@{assert} (Unif.unify ([], 0) (0, [V 0]) (0, [A (0, [])]) = SOME ([(0, A (0, []))], 0));
@{assert} (Unif.unify ([(0, A (2, []))], 0) (0, [V 0]) (0, [A (1, [])]) = NONE);

@{assert} (Unif.unify_contra ([], 0) (0, []) ([], [], 0, NONE) = SOME (([], 0), []));

(*val mat = Matrix.empty 6;
Matrix.insert_clauses mat clauses;

writeln "Starting leanCoP ...";
leanCoP.prove_exception mat 10;*)
*}


declare [[ML_print_depth = 50]]
ML {* @{term "\<forall>x. \<exists>y. f(x, y) \<and> Q(r)"} *}


lemma extension: "P \<or> Q \<Longrightarrow> \<not>P \<or> R \<Longrightarrow> (P \<Longrightarrow> R \<Longrightarrow> C) \<Longrightarrow> (Q \<Longrightarrow> C) \<Longrightarrow> C"
by blast


section \<open>Example of the Lemma rule\<close>

lemma "\<not>hashek \<or> p \<or> q \<Longrightarrow> \<not>p \<or> r \<Longrightarrow> \<not>r \<Longrightarrow> \<not>q \<or> p \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop @{context} 1 *} )
oops

(*
[ ([], Lemma (p, []))
, ([], Resolution ((q, []), [(#, [])], [(p, [])]))
, ([], Resolution ((r, []), [(p, []), (#, [])], []))
, ([], Resolution ((p, []), [(#, [])], []))
, ([], Resolution ((1, []), [], []))
]
*)

lemma
  assumes "\<not>hashek \<or> p \<or> q"
  assumes "\<not>p \<or> r"
  assumes "\<not>r"
  assumes "\<not>q \<or> p"
  shows "False"
proof -
  have 1: "p \<or> q" using hashek_def assms(1) by simp
  have 2: "p \<Longrightarrow> False" proof -
    assume p
    then have r using assms(2) by simp
    then show ?thesis using assms(3) by contradiction
  qed
  have 3: "q \<Longrightarrow> False" proof -
    assume q
    then have p using assms(4) by simp
    then show ?thesis using 2 by simp
  qed

  show ?thesis apply (rule disjE[OF 1 2 3]) .
qed

section \<open>Example of the Path rule\<close>

lemma "\<not>hashek \<or> p \<Longrightarrow> \<not>p \<or> q \<Longrightarrow> \<not>q \<or> \<not>p \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop @{context} 1 *} )
oops

(*
[ ([], Path (~2, []))
, ([], Resolution ((~3, []), [(2, []), (1, [])], []))
, ([], Resolution ((2, []), [(1, [])], []))
, ([], Resolution ((1, []), [], []))
]
*)

lemma
  assumes "\<not>hashek \<or> p"
  assumes "\<not>p \<or> q"
  assumes "\<not>q \<or> \<not>p"
  shows "False"
proof -
  have 1: "p" using assms(1) using hashek_def by simp
  have 2: "\<not>q" using 1 assms(3) by simp
  have 3: "\<not>p" using 2 assms(2) by simp
  (* to reconstruct the path rule, we have to reference a fact that was
     previously proven on the branch *)
  (* as soon as we have no literal in a clause anymore,
     we show the thesis *)
  show ?thesis using 1 3 by contradiction
qed

section \<open>Substitution involving only universal quantifiers\<close>

lemma "\<not>P(a) \<or> \<not>Q(b) \<or> \<not>hashek \<Longrightarrow> \<forall>x. P(x) \<Longrightarrow> \<forall>x. Q(x) \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop @{context} 1 *} )
oops

(*
[ ([(0, A (3, []))], Resolution ((~4, [A (5, [])]), [(1, [])], [(~2, [A (3, [])])]))
, ([], Resolution ((~2, [A (3, [])]), [(1, [])], []))
, ([], Resolution ((1, []), [], []))
]
*)

lemma
  assumes "\<not>P(a) \<or> \<not>Q(b) \<or> \<not>hashek"
  assumes "\<forall>x. P(x)"
  assumes "\<forall>x. Q(x)"
  shows "False"
proof -
  have 1: "\<not>P(a) \<or> \<not>Q(b)" using assms(1) hashek_def by simp
  have 2: "P(a)" using assms(2) by (rule allE)
  have 3: "\<not>Q(b)" using assms(1) 2 hashek_def by simp
  have 4: "Q(b)" using assms(3) by (rule allE)
  have 5: "False" using 3 4 by contradiction
  show ?thesis using 5 .
qed


section \<open>More experiments\<close>

(*Sometimes, we have to fix a variable if it is not substituted with a constant.*)
lemma
  assumes "\<forall>x. P(x)"
  assumes "\<forall>x. \<not>P(x)"
  shows "False"
proof -
  fix a
  have 1: "P(a)" using assms(1) by simp
  have 2: "\<not>P(a)" using assms(2) by simp
  show ?thesis using 1 2 by auto
qed

(*To instantiate existantial quantifiers, we fix all of the variables, then assume the
  statement without the existential quantifier.*)
lemma
  assumes "\<forall>x. P(x)"
  assumes "\<exists>x. \<not>P(x)"
  assumes "\<exists>x. Q(x)"
  shows "False"
proof -
  {
    fix x y
    assume "Q(y)"
    assume "\<not>P(x)"
    then have False using assms(1) by auto
  }
  note block = this

  show ?thesis using exE[OF assms(2) exE[OF assms(3) block]] .
qed

(*When we have alternating quantifiers, we always open a proof block
  when we encounter an existential, otherwise we just fix the universal.*)
lemma
  assumes "\<forall>x. \<exists>y. \<forall>z. P(x, y, z)"
  shows "\<exists>a b c. P(a, b, c)"
proof -
  fix a
  have all1: "\<exists>y. \<forall>z. P(a, y, z)" using spec[OF assms(1)] .
  {
    fix b
    assume ex1: "\<forall>z. P(a, b, z)"
    fix c
    have all2: "P(a, b, c)" using spec[OF ex1] .
    then have "\<exists>a b c. P(a, b, c)" by auto
  }
  note block = this
  show ?thesis using exE[OF all1 block] .
qed

(*A real life-saver!*)
(*Taken from: https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2010-February/msg00132.html*)
ML {*
  val ctxt1 = @{context};
  val cert = Thm.cterm_of ctxt1;

  val (_, ctxt2) = ctxt1 |> Variable.add_fixes ["P", "f"];
  val [A, C] = Syntax.read_props ctxt2 ["EX x. P (f (x))", "EX y. P(y)"];
  val ([a], ctxt3) = ctxt2
    |> Variable.declare_term A
    |> Variable.declare_term C
    |> Assumption.add_assumes [cert A];

  val ((xs, [b]), ctxt4) = ctxt3
    |> Obtain.result (fn _ => etac @{thm exE} 1) [a];

  val res = Goal.prove ctxt4 [] [] C (fn _ => rtac @{thm exI} 1 THEN rtac b 1);
  val final_res = singleton (Proof_Context.export ctxt4 ctxt1) res;
*}


(* You can read off the index of the conjunct that is used from an assumption. *)
lemma " \<not>b \<or> \<not>hashek \<Longrightarrow> a \<and> b \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop @{context} 1 *} )
oops

lemma "\<not>b(x) \<or> \<not>hashek \<Longrightarrow> \<forall>y. (b(y)) \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop @{context} 1 *} )
oops

(* TODO: clausification does not work! *)
lemma "\<forall>x y. P(x,y) \<Longrightarrow> \<exists>a. \<forall>b. P(a, b)"
apply (isacop 1)
oops

lemma "\<And>a. \<forall>x. \<exists>y. P(x,y) \<Longrightarrow> \<forall>x. P(f(x),a) \<Longrightarrow> Q(r)"
apply (isacop 1)
oops

lemma
  "\<And>s. \<forall>x. ((P(x) \<longleftrightarrow> a \<and> b) \<or> ((\<forall>z. R(z,s)) \<or> (\<exists>y. \<forall>w. \<exists>v. Q(y, w, v)) \<and> r)) \<or> z \<Longrightarrow> a \<or> (b \<and> c) \<Longrightarrow> True \<Longrightarrow> False"
apply (isacop 1)
oops


lemma "\<And>y. y \<Longrightarrow> Q \<Longrightarrow> R \<Longrightarrow> \<forall>x. P(x)"
apply (isacop 1)
oops

end
