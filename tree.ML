structure Tree =
struct

datatype ('b, 'l) tree = Branch of ('b * ('b, 'l) tree list) | Leaf of 'l

fun map_tree (_, fl) (Leaf l) = fl l
  | map_tree (fb, fl) (Branch (b, nodes)) = fb (b, map (map_tree (fb, fl)) nodes)

fun map_replace_leafs f = map_tree (Branch, f)
fun map_leafs f = map_replace_leafs (f #> Leaf)
fun map_branches f = map_tree (fn (b, nodes) => Branch (f b, nodes), Leaf)
fun leafs t = map_tree (fn (_, nodes) => List.concat nodes, fn l => [l]) t
fun branches t = map_tree (fn (b, nodes) => b :: List.concat nodes, fn _ => []) t

fun leaf_of (Leaf l) = l
  | leaf_of _ = raise Fail "leaf_of"

fun path_tree path (Leaf l) = Leaf (path, l)
  | path_tree path (Branch (b, nodes)) = Branch ((path, b), map (path_tree (b :: path)) nodes)

fun debinarize b br = case br of
    (Branch (b', [n1, n2])) => if b = b' then n1 :: debinarize b n2 else [br]
  | _ => [br]

fun subst_some_leafs subst =
  map_replace_leafs (fn x => Utils.maybe (Leaf x) I (Utils.lookup x subst))

fun subst_all_leafs subst =
  map_leafs (fn x => Option.valOf (Utils.lookup x subst))

fun to_string (sb, sl) = map_tree (fn (b, nodes) => case nodes of
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

structure Edge_Tree =
struct

open Tree

type ('e, 'b, 'l) edge_tree = ('e * 'b, 'e * 'l) tree

fun make_edges e (Leaf l) = (Leaf (e, l))
  | make_edges e (Branch (b, nodes)) = Branch ((e, b), map (make_edges e) nodes)

fun map_edge f (Leaf (e, l)) = Leaf (f e, l)
  | map_edge f (Branch ((e, b), nodes)) = Branch ((f e, b), nodes)

(* TODO: Not used right now. *)
fun map_branches_edges _ (Leaf l) = Leaf l
  | map_branches_edges f (Branch ((l, b), nodes)) =
      Branch ((l, b), map (map_branches_edges f o map_edge (f b)) nodes)

fun edge (Leaf (e, _)) = e
  | edge (Branch ((e, _), _)) = e

fun set_edge (e, Leaf (_, l)) = Leaf (e, l)
  | set_edge (e, Branch ((_, b), nodes)) = Branch ((e, b), nodes)

fun edges_nodes nodes = map (fn n => (edge n, n)) nodes

structure Edge_Tree2 =
struct

datatype ('e, 'b, 'l) edge_tree = ELeaf of 'l | EBranch of 'b * (('e * ('e, 'b, 'l) edge_tree) list)

fun from_tree _ (Tree.Leaf l) = ELeaf l
  | from_tree e (Tree.Branch (b, nodes)) = EBranch (b, map (fn n => (e, from_tree e n)) nodes)



end

end
