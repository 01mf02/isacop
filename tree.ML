structure Tree =
struct

datatype ('b, 'l) tree = Branch of ('b * ('b, 'l) tree list) | Leaf of 'l

fun map_tree f (Leaf l) = f l
  | map_tree f (Branch (b, nodes)) = Branch (b, map (map_tree f) nodes)

fun leafs (Leaf l) = [l]
  | leafs (Branch (_, nodes)) = List.concat (map leafs nodes)

fun branches (Leaf l) = []
  | branches (Branch (b, nodes)) = b :: List.concat (map branches nodes)

fun fold_map_tree f (Branch (b, nodes)) y =
      let val (nodes', y') = fold_map (fold_map_tree f) nodes y
      in (Branch (b, nodes'), y')
      end
  | fold_map_tree f (Leaf l) y = f l y

end

structure Monoid_Tree =
struct

open Tree

type 't monoid_tree = ('t list -> 't, 't) tree

fun deep (Branch (f, nodes)) = f (map deep nodes)
  | deep (Leaf l) = l

end