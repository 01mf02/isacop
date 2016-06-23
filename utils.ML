structure Utils =
struct

(* Bijection between integers and natural numbers *)
fun int_of_nat n = if n mod 2 = 0 then n div 2 else ~(n+1) div 2
fun nat_of_int i = if i >= 0 then 2*i else ~(2*i + 1)

fun int_nat_inverse i = int_of_nat (nat_of_int i) = i
val int_nat_test = @{assert} (int_nat_inverse 5 andalso int_nat_inverse (~3))

(* Return first element that returns SOME plus the rest of the list, else NONE. *)
fun findSome f (x :: xs) = (case f x of SOME y => SOME (x, y, xs) | NONE => findSome f xs)
  | findSome _ [] = NONE

fun flip f x y = f y x

fun lookup x = Option.map snd o List.find (fn (y, _) => x = y)

(*Run function for every element and all other elements of the list.
  For example: app_rest [] f [1, 2, 3] =
    f (1, [2, 3]);
    f (2, [1, 3]);
    f (3, [1, 2])
*)
fun app_rest _ _ [] = ()
  | app_rest acc f (h :: t) = (f (h, List.revAppend (acc, t)); app_rest (h :: acc) f t)

fun maybe n s x = case x of
    NONE => n
  | SOME x' => s x'

fun option_map_snd f (x, y) = Option.map (pair x) (f y)

val maximum = List.foldr Int.max 0

fun iterate_until b f x =
  if b x then NONE
  else case f x of SOME y => SOME y
                 | NONE => iterate_until b f (x+1)

fun mapEq eq (k, v) f = map (fn (k', v') => if eq (k, k') then (k, f (v, v')) else (k', v'))

fun unionWith eq f = fold (fn (k, v) => fn acc =>
  if member eq (map fst acc) k then mapEq eq (k, v) f acc else (k, v) :: acc)

fun unionsWith eq f xs = fold (unionWith eq f) xs []

end
