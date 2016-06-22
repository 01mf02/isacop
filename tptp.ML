signature TPTP =
sig

val cnf : SymIntBimap.bimap -> LTerm.lit list list -> string list list
val show_cnf_line : string list -> string

end


structure Tptp : TPTP =
struct

val prepend = curry (op ^)
fun enclose start stop s = start ^ s ^ stop
val parens = enclose "(" ")"
val normalise = String.translate (fn c => if c = #"." then "_" else String.str c)
fun show_constant cm x =
  SymIntBimap.backward (cm, x) |> Utils.maybe ("s" ^ Int.toString x) (prepend "c" o normalise)
fun show_lterm cm = Tree.to_string (show_constant cm, prepend "X" o Int.toString)
val atom_of_lit = apfst Int.abs
fun lit_prefix (p, _) = if p > 0 then "" else "~ "

fun show_lit cm lit = lit_prefix lit ^ (lit |> atom_of_lit |> Tree.Branch |> show_lterm cm)
fun show_clause cm = parens o String.concatWith " | " o List.map (show_lit cm)
fun cnf_fields cm =
  map_index (fn (i, cl) => [Int.toString i, "axiom", show_clause cm cl])
val hashek_cnf = ["hashek", "negated_conjecture", "(c" ^ normalise @{const_name hashek} ^ ")"]
fun cnf cm cls = hashek_cnf :: cnf_fields cm cls
val show_cnf_line = enclose "cnf" "." o parens o String.concatWith ", "

end
