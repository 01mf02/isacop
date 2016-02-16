use "leancop.ML";
open FTerm;

(* !x. P(x) ==> P(a) /\ # *)
(* ~# \/ ~P(a) ==> !x. P(x) ==> False *)
val clauses = [[(~1, []), (~2, [A (3, [])])], [(2, [V 0])]];

val mat = Matrix.empty 6;
Matrix.insert_clauses mat clauses;

print "Starting leanCoP ...\n";
leanCoP.prove_exception mat 10;
