structure Database =
struct

type variable = int
datatype term = V of variable | A of int * term list
type lit = int * term list

val subst = Array.array (1000000, NONE : term option)
val sh : variable list Unsynchronized.ref = Unsynchronized.ref []

exception Unify

(* isTriv x t if variable x is contained in the term t *)
fun isTriv x (V y) = x = y orelse (case Array.sub (subst, x) of NONE => false | SOME t => isTriv x t)
  | isTriv x (A (_, a)) = if List.exists (isTriv x) a then true else raise Unify

fun iter2 f (x::xs) (y::ys) = let val _ = f x y in iter2 f xs ys end
  | iter2 _ _ _ = ()

fun addSubst x t = (Array.update (subst, x, SOME t); sh := x :: !sh)

fun unify (A(f, fa)) (A(g, ga)) = if f <> g then raise Unify else iter2 unify fa ga
  | unify (V(x)) tm = (case Array.sub (subst, x) of
      SOME t => unify tm t
    | NONE => if isTriv x tm then () else Array.update (subst, x, SOME tm))
  | unify tm (V(x)) = unify (V(x)) tm

fun restore_subst env =
  if (!sh) = env then ()
  else (Array.update (subst, List.hd (!sh), NONE); sh := List.tl (!sh); restore_subst env)

fun unify_list env l1 l2 = (restore_subst env; iter2 unify l1 l2; !sh)

fun unify_lit env ((h1 : int), l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unify_list env l1 l2

fun bump_small off (V v) = V(v + off)
  | bump_small off (A(f, a)) = A(f, List.map (bump_small off) a)

(* Unification with renaming of the second argument *)
fun unify_rename off t1 t2 = case (t1, t2) of
    (A(f,fa), A(g,ga)) => if f <> g then raise Unify else iter2 (unify_rename off) fa ga
  | (_, V x) =>
      let val x = x + off in
      case Array.sub (subst, x) of
        SOME t => unify_rename 0 t1 t
      | NONE => if isTriv x t1 then () else addSubst x t1
      end
  | (V x, _) => case Array.sub (subst, x) of
      SOME t => unify_rename off t t2
    | NONE => let val t2' = bump_small off t2 in if isTriv x t2' then () else addSubst x t2 end

fun eq2 x (V y) = y = x orelse (case Array.sub (subst, y) of SOME t => eq2 x t | NONE => false)
  | eq2 _ (A _) = false


end

val _ =
  let val oc = TextIO.openOut "bla";
  in TextIO.closeOut oc
end