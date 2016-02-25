theory Tarski
imports Mizar_Defs Mizar_By
begin

(* HIDDEN *)

axiomatization
  object :: m and
  set :: m
where
  (* object is the root of type hierarchy *)
  object_root[miz]: "x is object" and
  object_exists[miz]: "ex x being object st True" and
  hidden_mode[rule_format,miz]: "x is set implies x is object"

abbreviation not_equal (infixl "<>" 50) where
  "x <> y \<equiv> not (x = y)"

abbreviation mizneq (infixl "\<noteq>" 50) where
  "a \<noteq> b \<equiv> not a = b"

(*TARSKI_0*)

reserve x,y,z,u,a for object
reserve M,N,X,Y,Z for set

consts
  prefix_in :: "s \<Rightarrow> s \<Rightarrow> o" (infixl "in" 50)

--"Set axiom"
axiomatization where tarski_0_1[miz]:
  "for x being object holds x is set"

--"Extensionality axiom"
axiomatization where tarski_0_2[miz]:
  "X is set \<Longrightarrow> Y is set \<Longrightarrow>
    (for x being object holds x in X iff x in Y) implies X = Y"

--"Axiom of pair"
axiomatization where tarski_0_3[miz]:
  "ex z being set st
     for a being object holds
       a in z iff a = x or a = y"

--"Axiom of union"
axiomatization where tarski_0_4[miz]:
  "X is set \<Longrightarrow>
     ex Z st for x holds x in Z iff (ex Y st x in Y & Y in X)"

--"Axiom of regularity"
axiomatization where tarski_0_5[miz]:
  "X is set \<Longrightarrow> x in X implies (ex Y st Y in X & not (ex z st z in X & z in Y))"

--"Fraenkel's scheme"
axiomatization where tarski_0_sch_1[miz]:
  "A is set \<Longrightarrow>
     for x,y,z st P(x, y) & P(x, z) holds y = z \<Longrightarrow>
       ex X st for x holds
         x in X iff (ex y st y in A & P(y, x))"

(*TARSKI*)
theorem set_exists[miz]: "ex x being set st True"
using mizs by auto

theorem all_set: "x is set"
using mizs by auto

lemmas tarski_th_2 = tarski_0_2

definition tarski_def_1 ("{_}") where
   "let y be object
   func {y} \<rightarrow> set means \<lambda>it.
   for x holds x in it iff x = y"

schematic_goal tarski_def_1:
  assumes "y is object" shows "?X"
apply (rule means_property[OF tarski_def_1_def assms])
using mizs assms apply auto
sorry

lemmas tarski_def_1a[miz] = tarski_def_1[THEN conjunct1,THEN conjunct1,simplified]
lemmas tarski_def_1b[miz] = tarski_def_1[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas tarski_def_1c[miz] = tarski_def_1[THEN conjunct2,rule_format,unfolded atomize_conjL[symmetric],simplified, rule_format]

definition setpair ("{ _ , _ }") where
"let y be object & z be object
  func {y, z} \<rightarrow> set means \<lambda>it. (for x being object holds x in it iff (x = y or x = z))"

schematic_goal tarski_def_2:
  assumes "y is object & z is object" shows "?X"
apply (rule means_property[OF setpair_def assms])
using mizs assms apply auto
sorry

lemmas tarski_def_2b[miz] = tarski_def_2[THEN conjunct1,THEN conjunct2,simplified,rule_format]
lemmas tarski_def_2a[miz] = tarski_def_2[THEN conjunct1,THEN conjunct1,simplified,rule_format]

theorem tarski_def_2_commutativity[miz]:
  "for x,y being object holds {x,y} = {y,x}"
using mizs assms apply auto sorry

definition tarski_def_3_prefix:: "s \<Rightarrow> s \<Rightarrow> o" (infixl "c=" 50)
where tarski_def_3_pre: "X is set \<Longrightarrow> Y is set \<Longrightarrow> X c= Y iff (for x holds x in X implies x in Y)"

lemmas tarski_def_3[miz] = tarski_def_3_pre[OF all_set all_set]

syntax "Tarski.tarski_def_3_prefix" :: "s \<Rightarrow> s \<Rightarrow> o" (infixl "\<subseteq>" 50)

definition tarski_def_4 ("union _" [90] 90) where
   "let X be set
   func union X \<rightarrow> set means \<lambda>it.
   for x holds
   x in it iff (ex Y st x in Y & Y in X)"

schematic_goal tarski_def_4:
  assumes "X is set" shows "?X"
apply (rule means_property[OF tarski_def_4_def assms])
using mizs assms apply auto
sorry

lemmas tarski_def_4a[miz] = tarski_def_4[THEN conjunct1,THEN conjunct1,OF all_set]
lemmas tarski_def_4b[miz] = tarski_def_4[THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]
lemmas tarski_th_3 = tarski_0_5

theorem prefix_in_asymmetry:
  "for x,X being set holds not (x in X & X in x)"
using mizs apply auto
sorry

lemmas[miz] = bspec[OF bspec[OF prefix_in_asymmetry all_set] all_set,rule_format]

definition tarski_def_5 ("[_ , _]") where 
   "let x be object & y be object
   func [x,y] \<rightarrow> object equals
   {{x, y}, {x}}"

schematic_goal tarski_def_5:
  assumes "x is object & y is object" shows "?X"
apply (rule equals_property[OF tarski_def_5_def assms])
using assms mizs by auto

definition
  are_equipotent_prefix :: "s \<Rightarrow> s \<Rightarrow> o" ("_,_ areequipotent" [100,100])
where
  tarski_def_6: "X is set \<Longrightarrow> Y is set \<Longrightarrow>
    X, Y areequipotent iff
    (ex Z st
     (for x st x in X ex y st y in Y & [x,y] in Z) &
     (for y st y in Y ex x st x in X & [x,y] in Z) &
     (for x,y,z,u st [x,y] in Z & [z,u] in Z holds x = z iff y = u))"

(*TARSKI_A*)

axiomatization where
tarski_a_th_1[miz]:
  "for N holds ex M st N in M &
     (for X,Y holds X in M & Y c= X implies Y in M) &
     (for X st X in M ex Z st Z in M & (for Y st Y c= X holds Y in Z)) &
     (for X holds X c= M implies X,M areequipotent or X in M)"

(*XBOOLE_0*) 

theorem xboole_0_sch_1:
  "A is set \<Longrightarrow>
    ex X being set st for x being object holds
      x in X iff x in A & P(x)"
using mizs apply auto
sorry

definition empty :: a ("empty")
where xboole_0_def_1a[THEN defattr_property,miz]:
  "empty \<equiv> define_attr(\<lambda>X. X is set & not (ex x st x in X))"
definition nonempty :: a ("non empty")
where xboole_0_def_1b[THEN defattr_property,miz]:
  "nonempty \<equiv> define_attr(\<lambda>X. X is set & (ex x st x in X))"

theorem xboole_0_cl_1[miz]:
   "cluster empty for set"
using mizs apply auto
sorry

definition xboole_0_def_2_prefix ("{}") where
  "func {} \<rightarrow> set equals the empty set"

schematic_goal xboole_0_def_2: shows "?X"
apply (rule equals_property_nolet[OF xboole_0_def_2_prefix_def])
using mizs by auto

lemmas xboole_0_def_2a[miz] = xboole_0_def_2[THEN conjunct1]
lemmas xboole_0_def_2b[miz] = xboole_0_def_2[THEN conjunct2]

definition prefix_cup (infixl "\<union>" 65) where
"let X be set & Y be set
  func X \<union> Y \<rightarrow> set means \<lambda>it. for x holds x in it iff x in X or x in Y"

schematic_goal xboole_0_def_3:
  assumes "X is set & Y is set" shows "?X"
apply (rule means_property[OF prefix_cup_def assms])
using mizs assms apply auto
sorry

(* Again, we assume that if a user writes "X \<union> Y" they want it to be a set *)
lemmas xboole_0_def_3a[miz] = xboole_0_def_3[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set,OF all_set]
lemmas xboole_0_def_3b[miz] = xboole_0_def_3[THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]

mtheorem cup_commutativity: "X \<union> Y = Y \<union> X" using assms mizs apply auto sorry
lemmas [miz] = cup_commutativity[OF all_set,OF all_set]

mtheorem cup_idempotence: "X \<union> X = X" using assms mizs apply auto sorry
lemmas [miz] = cup_idempotence[OF all_set]

definition prefix_cap (infixl "\<inter>" 70) where
"let X be set & Y be set
  func X \<inter> Y \<rightarrow> set means \<lambda>it. (for x holds (x in it iff (x in X & x in Y)))"

schematic_goal xboole_0_def_4:
  assumes "X is set & Y is set" shows "?X"
apply (rule means_property[OF prefix_cap_def assms])
using assms mizs apply auto sorry

lemmas xboole_0_def_4a[miz] = xboole_0_def_4[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set,OF all_set]
lemmas xboole_0_def_4b[miz] = xboole_0_def_4[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]

mtheorem cap_commutativity: "X \<inter> Y = Y \<inter> X" using assms mizs apply auto sorry
lemmas [miz] = cap_commutativity[OF all_set,OF all_set]

mtheorem cap_idempotence: "X \<inter> X = X" using assms mizs apply auto sorry
lemmas [miz] = cap_idempotence[OF all_set]

definition prefix_min (infixl "\\" 70) where
"let X be set & Y be set
  func X \\ Y \<rightarrow> set means \<lambda>it.
    for x being object holds (x in it iff (x in X & not x in Y))"

schematic_goal xboole_0_def_5:
  assumes "X is set & Y is set" shows "?X"
apply (rule means_property[OF prefix_min_def assms])
using mizs assms apply auto sorry

lemmas xboole_0_def_5a[miz] = xboole_0_def_5[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct1,OF all_set,OF all_set]
lemmas xboole_0_def_5b[miz] = xboole_0_def_5[unfolded atomize_conjL[symmetric],THEN conjunct1,THEN conjunct2,simplified all_set,simplified,rule_format]

definition xboole_0_def_6_prefix (infixl "\\+\\" 65)
where
"let X is set & Y is set
 func X \\+\\ Y \<rightarrow> set equals (X \\ Y) \<union> (Y \\ X)"

schematic_goal xboole_0_def_6:
   assumes "X is set & Y is set"
   shows "?X"
apply (rule equals_property[OF xboole_0_def_6_prefix_def assms])
  using assms mizs apply auto
done

lemmas xboole_0_def_6b[miz] = xboole_0_def_6[simplified all_set, simplified]

mtheorem sccap_commutativity: "X \\+\\ Y = Y \\+\\ X" using assms mizs
apply auto done
lemmas [miz] = sccap_commutativity[OF all_set,OF all_set]

definition prefix_misses (infixl "misses" 60) where
  xboole_0_def_7: "X is set & Y is set \<Longrightarrow> (X misses Y) iff X \<inter> Y = {}"
lemmas [miz] = xboole_0_def_7[simplified all_set, simplified]

mtheorem misses_symmetry: "X misses Y iff Y misses X"
using assms mizs by auto

definition xboole_0_def_8 (infixl "c<" 40)
where xboole_0_def_8: "X is set \<Longrightarrow> Y is set \<Longrightarrow> (X c< Y) iff X c= Y & X<>Y"

syntax "Tarski.xboole_0_def_8" :: "s \<Rightarrow> s \<Rightarrow> o" (infixl "\<subset>" 40)

lemmas [miz] = xboole_0_def_8[simplified all_set,simplified]
mtheorem xboole_0_def_8_irreflexivity:
  "not (X c< X)" using assms mizs by auto

mtheorem xboole_0_def_8_asymmetry[miz]:
  "X c< Y implies not (Y c< X)"
using assms mizs apply auto sorry

definition
  prefix_xboole_0_def_9 ("_ , _ are c= comparable"[50,50] 40)
where
  xboole_0_def_9: "X is set & Y is set \<Longrightarrow> 
       X,Y are c= comparable iff (X c= Y or Y c= X)"
lemmas [miz] = xboole_0_def_9[simplified all_set,simplified]

mtheorem xboole_0_def_9_symmetry:
  "X,Y are c= comparable implies Y,X are c= comparable" using assms mizs
apply auto
done

mtheorem xboole_0_def_10: "X = Y iff (X c= Y & Y c= X)"
using assms mizs
apply auto
sorry

abbreviation meets_prefix ("_ meets _" 60)
  where "X meets Y \<equiv> not (X misses Y)"

mtheorem xboole_0_th_1:
"x in X \\+\\ Y iff not (x in X iff x in Y)"
using assms mizs apply auto
done

mtheorem xboole_th2: 
  "(for x holds (not x in X) iff (x in Y iff x in Z)) implies X = Y \\+\\ Z"
using assms mizs apply auto
sorry

theorem xboole_0_cl_2[miz]:
  "cluster {} \<rightarrow> empty"
using mizs apply auto
sorry

lemma [miz]: "\<not>x in {}"
using mizs apply auto
done

theorem xboole_0_cl_3[rule_format,miz]: 
   "let x be object 
    cluster {x} \<rightarrow> non empty"
using mizs apply auto
done

theorem xboole_0_cl_4[rule_format,miz]: 
  "let x be object & y be object 
   cluster {x,y} \<rightarrow> non empty"
using mizs apply auto
done

theorem xboole_0_cl_5[miz]: "cluster non empty for set"
using mizs apply auto
sorry

theorem xboole_0_cl_6[miz]:
  "let D be non empty set & X be set
   cluster D \<union> X \<rightarrow> non empty"
using mizs apply auto
done

mtheorem xboole_0_lm_1: "X is empty implies X={}"
using assms mizs apply auto
sorry

mtheorem xboole_0_th_3: "(X meets Y) iff (ex x being object st x in X & x in Y)"
using assms mizs apply auto
sorry

mtheorem xboole_0_th_4: "(X meets Y) iff (ex x st x in X\<inter> Y)"
using assms mizs apply auto
sorry

theorem xboole_0_th_5:
  "for X,Y being set, x being object st
    X misses Y & x in X \<union> Y holds ((x in X & not x in Y) or (x in Y & not x in X))"
using assms mizs apply auto
sorry

theorem xboole_0_sch_2:
  assumes "X1 is set" "X2 is set"
    "for x being object holds x in X1 iff P(x)"
    "for x being object holds x in X2 iff P(x)"
  shows "X1 = X2"
  using assms mizs apply auto sorry

lemmas xboole_0_sch_3 = xboole_0_sch_2

theorem xboole_0_th_6:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y & not x in X"
  using assms mizs apply auto sorry

theorem xboole_0_th_7:
  "for X being set st X <> {} holds ex x being object st x in X"
  using assms mizs apply auto sorry

theorem xboole_0_th_8:
  "for X,Y being set st X c< Y holds
     ex x being object st x in Y & X c= Y\\{x}"
  using assms mizs apply auto sorry

abbreviation include_antyonym ("_ c\\= _" 40)
  where "X c\\= Y == not (X c= Y)"

abbreviation in_antonym ("_ nin _" 40)
  where "X nin Y == not (X in Y)"

(* XBOOLE_1 *)

section ""
reserve x,A,B,X,X9,Y,Y9,Z,V for set

--"$N Modus Barbara"
mtheorem 1: "X \<subseteq> Y \<and> Y \<subseteq> Z \<longrightarrow> X \<subseteq> Z" using assms mizs by auto
mtheorem 2: "{} \<subseteq> X" using assms mizs by auto
mtheorem 3: "X \<subseteq> {} \<longrightarrow> X = {}" using assms mizs by auto
mtheorem 4: "X \<union> Y \<union> Z = X \<union> (Y \<union> Z)" using assms mizs by auto
mtheorem 5: "X \<union> Y \<union> Z = X \<union> Z \<union> (Y \<union> Z)" using assms mizs by auto
mtheorem 6: "X \<union> (X \<union> Y) = X \<union> Y" using assms mizs by auto
mtheorem 7: "X \<subseteq> X \<union> Y" using assms mizs by auto
mtheorem 8: "X \<subseteq> Z \<and> Y \<subseteq> Z \<longrightarrow> X \<union> Y \<subseteq> Z" using assms mizs by auto
mtheorem 9: "X \<subseteq> Y \<longrightarrow> X \<union> Z \<subseteq> Y \<union> Z" using assms mizs by auto
mtheorem 10: "X \<subseteq> Y \<longrightarrow> X \<subseteq> Z \<union> Y" using assms mizs by auto
mtheorem 11: "X \<union> Y \<subseteq> Z \<longrightarrow> X \<subseteq> Z" using assms mizs by auto
mtheorem 12: "X \<subseteq> Y \<longrightarrow> X \<union> Y = Y" using assms mizs by auto
mtheorem 13: "X \<subseteq> Y \<and> Z \<subseteq> V \<longrightarrow> X \<union> Z \<subseteq> Y \<union> V" using assms mizs by auto
mtheorem 14: "Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V:set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V) \<longrightarrow> X = Y \<union> Z" using assms mizs
  sorry
mtheorem 15: "X \<union> Y = {} \<longrightarrow> X = {}" using assms mizs by auto
mtheorem 16: "X \<inter> Y \<inter> Z = X \<inter> (Y \<inter> Z)" using assms mizs by auto
mtheorem 17: "X \<inter> Y \<subseteq> X" using assms mizs by auto
mtheorem 18: "X \<subseteq> Y \<inter> Z \<longrightarrow> X \<subseteq> Y" using assms mizs by auto
mtheorem 19: "Z \<subseteq> X \<and> Z \<subseteq> Y \<longrightarrow> Z \<subseteq> X \<inter> Y" using assms mizs by auto
mtheorem 20: "X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V:set. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X) \<longrightarrow> X = Y \<inter> Z" using assms mizs by auto
mtheorem 21: "X \<inter> (X \<union> Y) = X" using assms mizs by auto
mtheorem 22: "X \<union> X \<inter> Y = X" using assms mizs by auto
mtheorem 23: "X \<inter> (Y \<union> Z) = X \<inter> Y \<union> X \<inter> Z" using assms mizs by auto
mtheorem 24: "X \<union> Y \<inter> Z = (X \<union> Y) \<inter> (X \<union> Z)" using assms mizs by auto
mtheorem 25: "X \<inter> Y \<union> Y \<inter> Z \<union> Z \<inter> X = (X \<union> Y) \<inter> (Y \<union> Z) \<inter> (Z \<union> X)" using assms mizs by auto
mtheorem 26: "X \<subseteq> Y \<longrightarrow> X \<inter> Z \<subseteq> Y \<inter> Z" using assms mizs by auto
mtheorem 27: "X \<subseteq> Y \<and> Z \<subseteq> V \<longrightarrow> X \<inter> Z \<subseteq> Y \<inter> V" using assms mizs by auto
mtheorem 28: "X \<subseteq> Y \<longrightarrow> X \<inter> Y = X" using assms mizs by auto
mtheorem 29: "X \<inter> Y \<subseteq> X \<union> Z" using assms mizs by auto
mtheorem 30: "X \<subseteq> Z \<longrightarrow> X \<union> Y \<inter> Z = (X \<union> Y) \<inter> Z" using assms mizs by auto
mtheorem 31: "X \<inter> Y \<union> X \<inter> Z \<subseteq> Y \<union> Z" using assms mizs by auto
mtheorem Lm1: "X \\ Y = {} \<longleftrightarrow> X \<subseteq> Y" using mizs by auto
mtheorem 32: "X \\ Y = Y \\ X \<longrightarrow> X = Y" using assms mizs by auto
mtheorem 33: "X \<subseteq> Y \<longrightarrow> X \\ Z \<subseteq> Y \\ Z" using assms mizs by auto
mtheorem 34: "X \<subseteq> Y \<longrightarrow> Z \\ Y \<subseteq> Z \\ X" using assms mizs by auto
mtheorem Lm2: "X \\ (Y \<inter> Z) = X \\ Y \<union> X \\ Z" using assms mizs by auto
mtheorem 35: "X \<subseteq> Y \<and> Z \<subseteq> V \<longrightarrow> X \\ V \<subseteq> Y \\ Z" using assms mizs by auto
mtheorem 36: "X \\ Y \<subseteq> X" using assms mizs by auto
mtheorem 37: "X \\ Y = {} \<longleftrightarrow> X \<subseteq> Y" using mizs by auto
mtheorem 38: "X \<subseteq> Y \\ X \<longrightarrow> X = {}" using assms mizs by auto
mtheorem 39: "X \<union> Y \\ X = X \<union> Y" using assms mizs by auto
mtheorem 40: "(X \<union> Y) \\ Y = X \\ Y" using assms mizs by auto
mtheorem 41: "X \\ Y \\ Z = X \\ (Y \<union> Z)" using assms mizs by auto
mtheorem 42: "(X \<union> Y) \\ Z = X \\ Z \<union> Y \\ Z" using assms mizs by auto
mtheorem 43: "X \<subseteq> Y \<union> Z \<longrightarrow> X \\ Y \<subseteq> Z" using assms mizs by auto
mtheorem 44: "X \\ Y \<subseteq> Z \<longrightarrow> X \<subseteq> Y \<union> Z" using assms mizs by auto
mtheorem 45: "X \<subseteq> Y \<longrightarrow> Y = X \<union> Y \\ X" using assms mizs by auto
mtheorem 46: "X \\ (X \<union> Y) = {}" using assms mizs by auto
mtheorem 47: "X \\ (X \<inter> Y) = X \\ Y" using assms mizs by auto
mtheorem 48: "X \\ (X \\ Y) = X \<inter> Y" using assms mizs by auto
mtheorem 49: "X \<inter> (Y \\ Z) = X \<inter> Y \\ Z" using assms mizs by auto
mtheorem 50: "X \<inter> (Y \\ Z) = X \<inter> Y \\ (X \<inter> Z)" using assms mizs by auto
mtheorem 51: "X \<inter> Y \<union> X \\ Y = X" using assms mizs by auto
mtheorem 52: "X \\ (Y \\ Z) = X \\ Y \<union> X \<inter> Z" using assms mizs by auto
mtheorem 53: "X \\ (Y \<union> Z) = X \\ Y \<inter> (X \\ Z)" using assms mizs by auto
mtheorem 54: "X \\ (Y \<inter> Z) = X \\ Y \<union> X \\ Z" using assms mizs by auto
mtheorem 55: "(X \<union> Y) \\ (X \<inter> Y) = X \\ Y \<union> Y \\ X" using assms mizs by auto
mtheorem Lm3: "X \<subseteq> Y \<and> Y \<subset> Z \<longrightarrow> X \<subset> Z" using assms mizs by auto
mtheorem 56: "X \<subset> Y \<and> Y \<subset> Z \<longrightarrow> X \<subset> Z" using assms mizs by auto
mtheorem 57: "not (X \<subset> Y \<and> Y \<subset> X)" using assms mizs by auto
mtheorem 58: "X \<subset> Y \<and> Y \<subseteq> Z \<longrightarrow> X \<subset> Z" using assms mizs by auto
mtheorem 59: "X \<subseteq> Y \<and> Y \<subset> Z \<longrightarrow> X \<subset> Z" using assms mizs by auto
mtheorem 60: "X \<subseteq> Y \<longrightarrow> not (Y \<subset> X)" using assms mizs by auto
mtheorem 61: "X \<noteq> {} \<longrightarrow> {} \<subset> X" using assms mizs by auto
mtheorem 62: "not (X \<subset> {})" using assms mizs by auto
--"$N Modus Celarent"
--"$N Modus Darii"
mtheorem 63: "X \<subseteq> Y \<and> Y misses Z \<longrightarrow> X misses Z" using assms mizs by auto
mtheorem 64: "A \<subseteq> X \<and> B \<subseteq> Y \<and> X misses Y \<longrightarrow> A misses B" using assms mizs by auto
mtheorem 65: "X misses {}" using assms mizs by auto
mtheorem 66: "(X meets X) \<longleftrightarrow> X \<noteq> {}" using assms mizs by auto
mtheorem 67: "X \<subseteq> Y \<and> X \<subseteq> Z \<and> Y misses Z \<longrightarrow> X = {}" using assms mizs by auto
--"$N Modus Darapti"
mtheorem 68: "\<forall>A:non empty set. A \<subseteq> Y \<and> A \<subseteq> Z \<longrightarrow> (Y meets Z)" using assms mizs by auto
mtheorem 69: "\<forall>A:non empty set. A \<subseteq> Y \<longrightarrow> (A meets Y)" using assms mizs by auto
mtheorem 70: "(X meets Y \<union> Z) \<longleftrightarrow> (X meets Y) \<or> (X meets Z)" using assms mizs by auto
mtheorem 71: "X \<union> Y = Z \<union> Y \<and> X misses Y \<and> Z misses Y \<longrightarrow> X = Z" using assms using assms mizs by auto
mtheorem 72: "X9 \<union> Y9 = X \<union> Y \<and> X misses X9 \<and> Y misses Y9 \<longrightarrow> X = Y9" using assms using assms mizs by auto
mtheorem 73: "X \<subseteq> Y \<union> Z \<and> X misses Z \<longrightarrow> X \<subseteq> Y" using assms mizs by auto
mtheorem 74: "X meets Y \<inter> Z \<longrightarrow> X meets Y" using assms mizs by auto
mtheorem 75: "X meets Y \<longrightarrow> X \<inter> Y meets Y" using assms mizs by auto
mtheorem 76: "Y misses Z \<longrightarrow> X \<inter> Y misses X \<inter> Z" using assms mizs by auto
mtheorem 77: "X meets Y \<and> X \<subseteq> Z \<longrightarrow> X meets Y \<inter> Z" using assms mizs by auto
mtheorem 78: "X misses Y \<longrightarrow> X \<inter> (Y \<union> Z) = X \<inter> Z" using assms mizs by auto
mtheorem 79: "X \\ Y misses Y" using assms mizs by auto
mtheorem 80: "X misses Y \<longrightarrow> X misses Y \\ Z" using assms mizs by auto
mtheorem 81: "X misses Y \\ Z \<longrightarrow> Y misses X \\ Z" using assms mizs by auto
mtheorem 82: "X \\ Y misses Y \\ X" using assms mizs by auto
mtheorem 83: "X misses Y \<longleftrightarrow> X \\ Y = X" using assms using assms mizs by auto
mtheorem 84: "(X meets Y) \<and> X misses Z \<longrightarrow> (X meets Y \\ Z)" using assms mizs by auto
mtheorem 85: "X \<subseteq> Y \<longrightarrow> X misses Z \\ Y" using assms mizs by auto
mtheorem 86: "X \<subseteq> Y \<and> X misses Z \<longrightarrow> X \<subseteq> Y \\ Z" using assms mizs by auto
mtheorem 87: "Y misses Z \<longrightarrow> X \\ Y \<union> Z = (X \<union> Z) \\ Y" using assms mizs by auto
mtheorem 88: "X misses Y \<longrightarrow> (X \<union> Y) \\ Y = X" using assms mizs by auto
mtheorem 89: "X \<inter> Y misses X \\ Y" using assms mizs by auto
mtheorem 90: "X \\ (X \<inter> Y) misses Y" using assms mizs by auto
mtheorem 91: "X \\+\\ Y \\+\\ Z = X \\+\\ (Y \\+\\ Z)" using assms mizs by auto
mtheorem 92: "X \\+\\ X = {}" using assms mizs by auto
mtheorem 93: "X \<union> Y = X \\+\\ Y \<union> X \<inter> Y" using assms mizs by auto
mtheorem Lm4: "X \<inter> Y misses X \\+\\ Y" using assms mizs by auto
mtheorem Lm5: "X \\+\\ Y = (X \<union> Y) \\ (X \<inter> Y)" using assms mizs by auto
mtheorem 94: "X \<union> Y = X \\+\\ Y \\+\\ X \<inter> Y" using assms mizs by auto
mtheorem 95: "X \<inter> Y = X \\+\\ Y \\+\\ (X \<union> Y)" using assms mizs by auto
mtheorem 96: "X \\ Y \<subseteq> X \\+\\ Y" using assms mizs by auto
mtheorem 97: "X \\ Y \<subseteq> Z \<and> Y \\ X \<subseteq> Z \<longrightarrow> X \\+\\ Y \<subseteq> Z" using assms mizs by auto
mtheorem 98: "X \<union> Y = X \\+\\ Y \\ X" using assms mizs by auto
mtheorem 99: "(X \\+\\ Y) \\ Z = X \\ (Y \<union> Z) \<union> Y \\ (X \<union> Z)" using assms mizs by auto
mtheorem 100: "X \\ Y = X \\+\\ X \<inter> Y" using assms mizs by auto
mtheorem 101: "X \\+\\ Y = (X \<union> Y) \\ (X \<inter> Y)" using assms mizs by auto
mtheorem 102: "X \\ (Y \\+\\ Z) = X \\ (Y \<union> Z) \<union> X \<inter> Y \<inter> Z" using assms mizs by auto
mtheorem 103: "X \<inter> Y misses X \\+\\ Y" using assms mizs by auto
mtheorem 104: "X \<subset> Y \<or> X = Y \<or> Y \<subset> X \<longleftrightarrow> X , Y are c= comparable" using assms mizs by auto
section ""
mtheorem 105: "\<forall>Y,X:set. X \<subset> Y \<longrightarrow> Y \\ X \<noteq> {}" using assms mizs by auto
mtheorem 106: "X \<subseteq> A \\ B \<longrightarrow> X \<subseteq> A \<and> X misses B" using assms mizs by auto
mtheorem 107: "X \<subseteq> A \\+\\ B \<longleftrightarrow> X \<subseteq> A \<union> B \<and> X misses A \<inter> B" using assms mizs by auto
mtheorem 108: "X \<subseteq> A \<longrightarrow> X \<inter> Y \<subseteq> A" using assms mizs by auto
mtheorem 109: "X \<subseteq> A \<longrightarrow> X \\ Y \<subseteq> A" using assms mizs by auto
mtheorem 110: "X \<subseteq> A \<and> Y \<subseteq> A \<longrightarrow> X \\+\\ Y \<subseteq> A" using assms mizs by auto
mtheorem 111: "X \<inter> Z \\ (Y \<inter> Z) = X \\ Y \<inter> Z" using assms mizs by auto
mtheorem 112: "X \<inter> Z \\+\\ Y \<inter> Z = (X \\+\\ Y) \<inter> Z" using assms mizs by auto
mtheorem 113: "X \<union> Y \<union> Z \<union> V = X \<union> (Y \<union> Z \<union> V)" using assms mizs by auto
mtheorem 114: "\<forall>D,C,B,A:set. A misses D \<and> B misses D \<and> C misses D \<longrightarrow> A \<union> B \<union> C misses D" using assms mizs by auto
mtheorem 115: "not (A \<subset> {})" using assms mizs by auto
mtheorem 116: "X \<inter> (Y \<inter> Z) = X \<inter> Y \<inter> (X \<inter> Z)" using assms mizs by auto
mtheorem 117: "\<forall>C,G,P:set. C \<subseteq> G \<longrightarrow> P \\ C = P \\ G \<union> P \<inter> (G \\ C)" using assms mizs by auto
 
