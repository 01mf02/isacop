structure Term =
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

fun iter2 f (x::xs) (y::ys) = (f x y; iter2 f xs ys)
  | iter2 _ _ _ = ()

fun all2 f (x::xs) (y::ys) = f x y andalso all2 f xs ys
  | all2 _ _ _ = true

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

fun varEqTerm x (V y) = y = x orelse (case Array.sub (subst, y) of SOME t => varEqTerm x t | NONE => false)
  | varEqTerm _ (A _) = false

val eq2 = varEqTerm

fun eq tm1 tm2 = case (tm1,tm2) of
    (A(f,fargs),A(g,gargs)) => (f = g andalso all2 eq fargs gargs)
  | (_,V(x)) => (case Array.sub (subst, x) of SOME t => eq tm1 t | NONE => eq2 x tm1)
  | (V(x),_) => (case Array.sub (subst, x) of SOME t => eq t tm2 | NONE => eq2 x tm2);;

fun eq_lit env (p,pa) (q,qa) = p = q andalso (restore_subst env; all2 eq pa qa)

val bump_subst_vars = bump_small

fun unify_rename_subst off l1 l2 env list =
  (restore_subst env;
  iter2 (unify_rename off) l1 l2;
  (!sh, List.map (fn (p,l) => (p,List.map (bump_subst_vars off) l)) list))

val empty_sub = []

fun negate (i, l) = (~i, l)

end


structure Database =
struct

fun db_entries x y = []

end



structure IsaCoP =
struct

val cut1 = true
val cut2 = true
val cut3 = true

(* Some counters *)
val infer = Unsynchronized.ref 0
val depth = Unsynchronized.ref 0
val depthinfer = Unsynchronized.ref 0


fun eq (sub, _) l1 l2 = Term.eq_lit sub l1 l2;;

fun unify (sub, off) l1 l2 = SOME (Term.unify_lit sub l1 l2, off) handle Term.Unify => NONE

fun unify_rename (s, off) args1 (args2, rest, vars, _) =
  let val xx = if vars = 0 then ((Term.unify_list s args1 args2, off), rest)
               else let val (s, rest) = Term.unify_rename_subst off args1 args2 s rest
                    in  ((s, off + vars), rest)
                    end
  in SOME xx
  end
  handle Term.Unify => NONE

datatype proof =
    Lem of Term.lit
  | Pat of Term.lit
  | Res of (Term.lit * Term.lit list * Term.lit list * int)
exception Solved of (int list * proof) list


fun prove sub (hist as (path, lem, lim)) alt (todo, prf) = fn
    [] => todo (sub, alt, prf)
  | (cl as lit1 :: rest) =>
     let val cont = (fn () => reduce sub lit1 rest hist alt (todo, prf) (Term.negate lit1) path)
         val nalt = if cut1 then alt else cont
     in  if List.exists (fn x => List.exists (eq sub x) path) cl
           then alt ()
         else if List.exists (eq sub lit1) lem
           then prove sub hist nalt (todo, (fst sub, Lem lit1) :: prf) rest
         else
           reduce sub lit1 rest hist alt (todo, prf) (Term.negate lit1) path
     end
and reduce sub lit1 rest (hist as (path,lem,lim)) alt (todo, prf) neglit = fn
    plit :: pt =>
      let val cont = (fn () => reduce sub lit1 rest hist alt (todo, prf) neglit pt)
          val nalt = if cut2 then alt else cont
      in  case unify sub neglit plit of
            SOME sub2 => prove sub2 hist nalt (todo, (fst sub, Pat lit1) :: prf) rest
          | NONE => reduce sub lit1 rest hist alt (todo, prf) neglit pt
      end
  | [] =>
      let val hist = (path, lem, lim)
          val dbs = Database.db_entries sub neglit
      in  extend sub lit1 rest hist alt (todo, prf) dbs
      end
and extend sub lit1 rest (hist as (path, lem, lim)) alt (todo, prf) = fn
    ((eh as (_,_,vars,hsh)) :: et) =>
    (case (if lim <= 0 andalso vars > 0 then NONE else unify_rename sub (snd lit1) eh) of
      SOME (sub2, cla1) =>
      let val ntodo = fn (sub, nalt, prf) => prove sub (path, lit1 :: lem, lim) (if cut3 then alt else nalt) (todo, prf) rest
          val nhist = (lit1 :: path, lem, lim - 1)
          val nprf  = (fst sub, Res (lit1, path, lem, hsh)) :: prf
          val nalt  = (fn () => extend sub lit1 rest hist alt (todo, prf) et)
      in  infer := !infer + 1;
          prove sub2 nhist nalt (ntodo, nprf) cla1
      end
    | NONE => extend sub lit1 rest hist alt (todo, prf) et)
  | [] => alt ()

(* TODO! *)
val hash = 0

fun prove2 lim = prove
  (Term.empty_sub, 0)
  ([], [], lim)
  (fn () => ())
  ((fn (_,_,prf) => raise (Solved prf)), [])
  [(hash,[])]


end

val _ =
  let val oc = TextIO.openOut "bla";
  in TextIO.closeOut oc
end