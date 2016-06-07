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