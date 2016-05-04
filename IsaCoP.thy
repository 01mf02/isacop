(*  Title:      IsaCoP.thy
    Author:     Michael Färber, Universität Innsbruck
    Copyright   2016 Michael Färber

Theory to load IsaCoP into FOL.

As this is work in progress, see isaCoP.ML for current limitations.
*)


theory IsaCoP imports "~~/src/FOL/FOL"
begin


section \<open>Haskek\<close>

(* In memoriam Jaroslav Hašek. *)
definition "hashek == True"


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


section \<open>Work in progress\<close>

definition "Quak(x,y) == True"
definition "Quip(x) == True"
definition "fork(x) == x"

lemma quak: "Quak(x, y) \<Longrightarrow> Quak(y, x)" unfolding Quak_def by simp
lemma quip: "Quip(x)" unfolding Quip_def by simp


section \<open>Prover and tactic\<close>

ML_file "mlcop.ML"
ML_file "intbimap.ML"
ML_file "isacop.ML"


section \<open>leanCoP tests\<close>

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


section \<open>Working examples\<close>

(* Cezary's example: Here, it is necessary to instantiate one clause partially,
   before the other clause can be instantiated, to finally fully instantiate
   the first clause.*)
lemma "(\<forall>x. \<exists>y. \<not>P(x, y) \<or> \<not>hashek) \<Longrightarrow> \<exists>x. \<forall>y. P(x, y) \<Longrightarrow> False"
by (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )

lemma "\<not>b(x) \<or> \<not>hashek \<Longrightarrow> \<forall>y. (b(y)) \<Longrightarrow> False"
by (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )

lemma "\<forall>x y. P(x,y) \<Longrightarrow> \<exists>a. \<forall>b. P(a, b)"
using quip by (isacop 1)

(* Syllogism of Felapton *)
lemma felapton_ex: "\<exists>c. Centaur(c) \<Longrightarrow> \<forall>c. Centaur(c) \<longrightarrow> \<not>Vote(c) \<Longrightarrow> \<forall>c. Centaur(c) \<longrightarrow> Intelligent(c) \<Longrightarrow>
  \<exists>b. Intelligent(b) \<and> \<not>Vote(b)"
by (isacop)

(* Damo's Example: Depth 5 is required here! *)
lemma damo_ex: "a \<or> b \<Longrightarrow> a \<longrightarrow> c(Damo) \<Longrightarrow> b \<longrightarrow> c(Much) \<Longrightarrow> \<exists>person. c(person)"
by (isacop 5)

(* Redundant quantors are correctly instantiated. *)
lemma "\<exists>y. \<forall>x. P(x, f(x), g(x)) \<Longrightarrow> \<forall>x. \<exists>y z. P(x, y, z)"
by isacop


subsection \<open>Substitution involving only universal quantifiers\<close>

lemma "\<not>P(a) \<or> \<not>Q(b) \<or> \<not>hashek \<Longrightarrow> \<forall>x. P(x) \<Longrightarrow> \<forall>x. Q(x) \<Longrightarrow> False"
by (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )

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


subsection \<open>Example of the Path rule\<close>

lemma "\<not>hashek \<or> p \<Longrightarrow> \<not>p \<or> q \<Longrightarrow> \<not>q \<or> \<not>p \<Longrightarrow> False"
by (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )

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



section \<open>Things that do not work yet\<close>

(* Strange "Inner syntax error - Failed to parse term" *)
lemma "\<forall>x y. P(x, y) \<or> \<not>hashek  \<Longrightarrow> \<forall>x y. \<not>P(y, x) \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )
oops

(* Same error as above. *)
lemma
  "\<forall>x. \<exists>y. \<forall>z. P(x, y, z) \<or> R(x) \<or> Q(z) \<or> \<not>hashek \<Longrightarrow>
  \<not>R(a) \<Longrightarrow> \<not>Q(b) \<Longrightarrow> \<not>Q(c) \<Longrightarrow>
  \<forall>w. \<not>P(a, w, b) \<or> \<not>P(a, w, c) \<Longrightarrow>
  False"
apply (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )
oops

(* You can read off the index of the conjunct that is used from an assumption. *)
lemma conj_clause_ex: " \<not>b \<or> \<not>hashek \<Longrightarrow> a \<and> b \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )
oops

(* As above. *)
lemma "\<exists>x. P(x) \<and> Q(x) \<Longrightarrow> \<exists>x. Q(x) \<and> P(x)"
apply isacop
oops


(* Proof with all kinds of rules *)
lemma "p \<or> q \<or> \<not>hashek \<Longrightarrow> \<not>q \<or> p \<Longrightarrow> \<not>p \<or> r \<Longrightarrow> \<not>r \<or> \<not>p \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )
oops



subsection \<open>Example of the Lemma rule\<close>

lemma lemma_ex: "\<not>hashek \<or> p \<or> q \<Longrightarrow> \<not>p \<or> r \<Longrightarrow> \<not>r \<Longrightarrow> \<not>q \<or> p \<Longrightarrow> False"
apply (tactic {* IsaCoP.raw_isacop 10 @{context} 1 *} )
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



section \<open>Unsolvable goals\<close>

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

(* Example from "Applications of unskolemization", Ritu Chadha, 1991. *)
(* leanCoP does not find a proof. *)
(* Quickcheck reports that it is not valid. *)
lemma
  assumes
   "\<forall>x y z w.
      ((Q(y) \<or> L(b, y)) \<and> \<not>Q(g(a)) \<and> L(g(a), a) \<and> R(x, g(a)) \<or> \<not>P(x, g(a))) \<and>
      (\<not>R(w, z) \<or> \<not>D(w, z))"
  shows "\<exists>u. \<forall>v. (L(b, u) \<and> L(u, a) \<and> (\<not>P(v, u) \<or> \<not>D(v, u) \<or> M(a)))"
using assms apply (isacop 100)
oops



section \<open>ML-related stuff\<close>

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

  val ((xs, b), ctxt4) = ctxt3
    |> Obtain.result (fn _ => eresolve_tac ctxt3 @{thms exE} 1) [a];

  val res = Goal.prove ctxt4 [] [] C (fn _ => resolve_tac ctxt4 @{thms exI} 1 THEN resolve_tac ctxt4 b 1);
  val final_res = singleton (Proof_Context.export ctxt4 ctxt1) res;
*}

declare [[ML_print_depth = 50]]
ML {* @{term "\<forall>x. \<exists>y. f(x, y) \<and> Q(r)"} *}


lemma "a \<or> b \<or> c \<longrightarrow> c \<or> b \<or> a \<or> c"
by (tactic {* Reconstruction.reorder_disj @{context} *})

lemma "b(x) \<longrightarrow> b(x)"
by (tactic {* Reconstruction.reorder_disj @{context} *})



section \<open>Exemplary reconstruction proofs\<close>

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

lemma
  assumes "\<exists>x. P(x)"
  assumes "\<forall>x. \<not>P(x)"
  shows "False"
proof -
  {
    fix w
    assume A: "P(w)"
    have "~P(w)" using assms(2) by simp
    then have False using A by simp
  }
  note block = this
  show ?thesis using exE[OF assms(1) block] .
qed

(* Cezary's example no. 2: Backwards reasoning test with existential quantifiers. *)
lemma
  assumes "\<forall>x. \<exists>y. \<forall>z. P(x, y, z) \<or> R(x) \<or> Q(z)"
  assumes "\<not>R(a)"
  assumes "\<not>Q(b)"
  assumes "\<not>Q(c)"
  assumes "\<forall>w. \<not>P(a, w, b) \<or> \<not>P(a, w, c)"
  shows "False"
proof -
  {
    assume Y: "\<exists>y. \<forall>z. P(a, y, z) \<or> R(a) \<or> Q(z)"
    {
      fix w0
      assume Z: "\<forall>z. P(a, w0, z) \<or> R(a) \<or> Q(z)"
      {
        assume B: "P(a, w0, b) \<or> R(a) \<or> Q(b)"
        {
          assume C: "P(a, w0, c) \<or> R(a) \<or> Q(c)"
          {
            assume W: "\<not>P(a, w0, b) \<or> \<not>P(a, w0, c)"
            (* ground reasoning *)
            have False using B C assms(2-4) W by auto
          }
          then have False using assms(5) by auto
        }
        then have False using Z by auto
      }
      then have False using Z by auto
    }
    then have False using Y by auto
  }
  then show ?thesis using assms(1) by auto
qed

end
