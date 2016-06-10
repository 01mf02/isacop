structure IsaUtils =
struct

fun make_conj_rule [] = @{thm TrueI}
  | make_conj_rule (th :: []) = th
  | make_conj_rule (th :: ths) = @{thm conjI} OF [th, make_conj_rule ths]

val make_conj_rule_test =
  let val ths = map Thm.assume [@{cprop P}, @{cprop Q}]
  in @{assert} (Thm.prop_of (make_conj_rule ths) = @{prop "P \<and> Q"})
  end

end