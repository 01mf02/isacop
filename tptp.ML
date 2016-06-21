structure Tptp =
struct

val prepend = curry (op ^)
fun enclose start stop s = start ^ s ^ stop
val parens = enclose "(" ")"
val normalise = String.translate (fn c => if c = #"." then "_" else String.str c)
fun print_lterm (cm, vm) =
  Tree.to_string (prepend "c" o normalise o int_sym cm, prepend "X" o int_sym vm)
fun print_pred (cm, _) p = if p > 0 then int_sym cm p else "~" ^ int_sym cm (~p)
val atom_of_lit = apfst Int.abs
fun lit_prefix (p, _) = if p > 0 then "" else "~ "

fun print_lit bimaps lit = lit_prefix lit ^ (lit |> atom_of_lit |> Tree.Branch |> print_lterm bimaps)
fun print_clause bimaps = parens o String.concatWith " | " o List.map (print_lit bimaps)
fun print_clauses bimaps = String.concatWith "\n" o List.map (print_clause bimaps)
fun print_cnf bimaps =
  map_index (fn (i, cl) => ["ax" ^ Int.toString i, "axiom", print_clause bimaps cl])
val hashek_cnf = ["hashek", "negated_conjecture", "(c" ^ normalise @{const_name hashek} ^ ")"]
fun cnf bimaps cls = hashek_cnf :: print_cnf bimaps cls
val cnf_line = enclose "cnf" "." o parens o String.concatWith ", "

end
