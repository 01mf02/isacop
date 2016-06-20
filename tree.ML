structure Tree =
struct

datatype ('b, 'l) tree = Branch of ('b * ('b, 'l) tree list) | Leaf of 'l

fun map_leafs f (Leaf l) = f l
  | map_leafs f (Branch (b, nodes)) = Branch (b, map (map_leafs f) nodes)

fun leafs (Leaf l) = [l]
  | leafs (Branch (_, nodes)) = List.concat (map leafs nodes)

fun leaf_of (Leaf l) = l
  | leaf_of _ = raise Fail "leaf_of"

fun branches (Leaf _) = []
  | branches (Branch (b, nodes)) = b :: List.concat (map branches nodes)

fun path_tree path (Leaf l) = Leaf (path, l)
  | path_tree path (Branch (b, nodes)) = Branch ((path, b), map (path_tree (b :: path)) nodes)

fun debinarize b br = case br of
    (Branch (b', [n1, n2])) => if b = b' then n1 :: debinarize b n2 else [br]
  | _ => [br]

fun fold_tree (_, fl) (Leaf l) = fl l
  | fold_tree (fb, fl) (Branch (b, nodes)) = fb (b, map (fold_tree (fb, fl)) nodes)

fun to_string (sb, sl) = fold_tree (fn (b, nodes) => case nodes of
    [] => sb b
  | _  => sb b ^ "(" ^ String.concatWith ", " nodes ^ ")", sl)

end

structure Monoid_Tree =
struct

open Tree

type 't monoid_tree = ('t list -> 't, 't) tree

fun deep (Branch (f, nodes)) = f (map deep nodes)
  | deep (Leaf l) = l

end