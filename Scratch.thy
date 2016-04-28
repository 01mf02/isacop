theory Scratch imports "~~/src/FOL/FOL"
begin

find_theorems "_ = _ \<Longrightarrow>_ \<equiv> _"

declare [[show_types, show_sorts]]

ML {*
val g = Goal.prove @{context} ["x", "y"] [@{prop "(x::'a) = y"}] @{prop "f(x::'a) = f(y)"}
  (fn {context = ctxt, prems = prs} =>
    (writeln (@{make_string} prs); print_tac ctxt "hi" THEN
     let val meqs = map (fn th => th RS @{thm eq_reflection}) prs
     in writeln (@{make_string} meqs);  rewrite_goal_tac ctxt meqs 1 THEN print_tac ctxt "hi" THEN
     simp_tac ctxt 1 end))
*}

ML {*
val g = Goal.prove @{context} ["x", "y"] [@{prop "(x::'a) = y"}] @{prop "P(x::'a) \<Longrightarrow> P(y)"}
  (fn {context = ctxt, prems = prs} =>
    (writeln (@{make_string} prs); print_tac ctxt "hi" THEN
     let val meqs = map (fn th => th RS @{thm eq_reflection}) prs
     in writeln (@{make_string} meqs);  rewrite_goal_tac ctxt meqs 1 THEN print_tac ctxt "hi" THEN
     simp_tac ctxt 1 end))
*}

ML {*
val ty = TVar (("'a", 0), @{sort term})
val tx = Free ("x", ty)
val ty = Free ("y", ty)
val eq = FOLogic.mk_eq (tx, ty) |> FOLogic.mk_Trueprop
val t = Term.close_schematic_term tx
*}

end