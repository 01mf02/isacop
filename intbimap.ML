signature BIMAP =
sig

type left
type right
type bimap

val    empty : int -> bimap
val fromList : left list -> bimap

val   insert : (bimap * left) -> (bimap * right)
val  forward : (bimap * left) -> right option
val backward : (bimap * right) -> left option

val domain : bimap -> left list
val size : bimap -> int

end

functor IntBimap (Key : KEY) : BIMAP =
struct

structure Tab = Table (Key)

type left = Key.key
type right = int

type bimap = {
  forth : int Tab.table
, back : Key.key option Array.array
, maxIndex : int
}

fun empty size = {forth = Tab.empty, back = Array.array (size, NONE), maxIndex = 0}

fun forward ({forth, ...}, x) = Tab.lookup forth x

fun backward ({back, maxIndex, ...}, i) = if i < maxIndex then Array.sub (back, i) else NONE

local
  fun insertNew ({back = b, maxIndex = m, forth = f}, x) =
    (Array.update (b, m, SOME x); ({forth = Tab.update (x,m) f, back = b, maxIndex = m + 1}, m))
in
  fun insert (bm, x) = case forward (bm, x) of SOME i => (bm, i) | NONE => insertNew (bm, x)
end

fun fromList l = List.foldl (swap #> insert #> fst) (empty (length l)) l

fun domain {forth, ...} = Tab.keys forth

fun size ({maxIndex, ...}) = maxIndex

end


structure SymIntBimap = IntBimap (type key = string val ord = fast_string_ord)
fun sym_int m x = SymIntBimap.forward (m, x) |> Option.valOf
fun int_sym m x = SymIntBimap.backward (m, x) |> Option.valOf

structure SymIntBimap_Test =
struct

val elements = ["A", "B", "C"]
val ibm = SymIntBimap.fromList elements
val _ = @{assert} (SymIntBimap.size ibm = 3)
val _ = @{assert} (SymIntBimap.domain ibm = elements)
val _ = @{assert} (SymIntBimap.forward (ibm, "C") = SOME 2)
val _ = @{assert} (SymIntBimap.forward (ibm, "D") = NONE)
val _ = @{assert} (SymIntBimap.backward (ibm, 2) = SOME "C")
val _ = @{assert} (SymIntBimap.backward (ibm, 3) = NONE)

end