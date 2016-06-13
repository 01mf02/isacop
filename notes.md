13.6.2016
=========

A counterexample for Skolem functions with congruence axioms
------------------------------------------------------------

$\forall x. \exists y. P x y \land \lnot  Px y \land x = c$

Skolemised: $\forall x. P x (f x) \land \lnot P x (f x) \land x = c$

* $P a (f a)$
* $\lnot P a (f a)$
* $a = c$

* $P b (f b)$
* $\lnot P b (f b)$
* $b = c$

$P a (f a)$ is resolved with $\lnot P b (f b)$ by rewriting $a$ with $b$.
That only works, however, if congruence axioms for Skolem functions
are produced.

A counterexample for inner Skolemisation
----------------------------------------

1. $\lnot P(a, c)$
2. $\forall w. P(w, c)$
3. $\forall x y. P(x, y) \land \exists z. \lnot P(z, y)$

Inner-Skolemize $F_3$, yielding: $P(x, y) \land \lnot P(f(y), y)$

Instantiate $F_3$ two times:

1. $P(a, c) \land \lnot P(f(c), c)$
2. $P(f(c), c) \land \lnot P(f(c), c)$

We can resolve these two and get: $P(a, c) \land \lnot P(f(c), c)$.
Resolving this with original $F_1$ and $F_2$ gives $\bot$.

However, the first resolve step did only work because the $f(c)$ witnesses
were the same in the inner Skolemisation; in the natural deduction scenario,
these would actually be different witnesses!
So one has to do something about them if one uses inner Skolemisation.


8.6.2016
========

$\sigma$ is a confluent TRS, so equality modulo $\sigma$ is decidable

Construct *one* deep formula for all copies of a clause, then
extract relevant parts for each clause copy


30.5.2016
=========

* Every clause has disjoint variables (via offset).
* Every Skolem function will contain only variables that have occurred
  in "higher" $\forall$s.
* We want to create a single ground instance for all copies of a clause.
* To avoid duplicate existential retrieval, we need to find paths that are
  equal modulo $\sigma$.
* Idea: Construct expansion tree for each clause copy separately,
  then merge them.
* For this, store the offset of the clause copy at every $\forall$ of its
  expansion tree, then when merging two expansion trees, store list of
  offsets among every $\forall$ quantifier.
* Question: How to detect case where e.g. $P(x) \land \lnot P(x)$,
  where $x$ does not have to be instantiated, but still contributes
  to the result?
  Read again Pfenning? TODO: Answer Miller mail!
* Inner Skolemisation: Example where it makes a difference:
      - $\forall x y. P(x, y) \land (\exists z. P(y, z))$
      - Skolemised: $P(x, y) \land P(y, f(y))$
  In proofs, this would create different witnesses for $f(y)$ even if
  the values of $y$ would be the same, because the Isabelle witnesses
  for $f(y)$ depend also on $x$.
  However, it might be possible nonetheless to reconstruct such proofs,
  because the refutation of a formula containing such an existential witness
  can only work if the refuting formula contains an all-quantified variable
  at the place of the witness. (Does this claim really hold?)
* Store witness to be the (Skolem function ID, variables),
  where a variable is an offset and a variable ID
  



26.4.2016
=========

`HEADGOAL` is called *twice* when there exists at least one goal:
Once on a state with no subgoals, and once on a state with the actual
first subgoal. I suspect this is such that there always exists a head.

For example:

~~~ sml
fun dummy_method opt ctxt facts = HEADGOAL (K (print_tac ctxt "Hoy") THEN' K all_tac)

val _ =
  Theory.setup
    (Method.setup @{binding dummy}
      (Scan.lift (Scan.option Parse.nat) >> (METHOD oo dummy_method))
      "Dummy")
~~~

~~~ isabelle
lemma "True" apply (dummy)
~~~

Output:

~~~
proof (prove)
goal (1 subgoal):
 1. True 
Hoy
No subgoals! 
Hoy
 1. True
~~~
