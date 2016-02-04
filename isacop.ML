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

fun addSubst x t = let val _ = Array.update (subst, x, SOME t) in sh := x :: !sh end

fun unify (A(f, fa)) (A(g, ga)) = if f <> g then raise Unify else iter2 unify fa ga
  | unify (V(x)) tm = (case Array.sub (subst, x) of
      SOME t => unify tm t
    | NONE => if isTriv x tm then () else Array.update (subst, x, SOME tm))
  | unify tm (V(x)) = unify (V(x)) tm
end

val _ =
  let val oc = TextIO.openOut "bla";
  in TextIO.closeOut oc
end