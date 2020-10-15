(**
 * The function definitions in this file are taken from or made to match
 * Section 8 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

(**
 * Original definition:
 *
 *   is_root h = (case h of leaf → true | (l, x, r) → r == leaf)
 *)
is_root ∷ Tree α → Bool
is_root h = match h with
  | leaf      → true
  | (l, x, r) → match r with
    | leaf          → true
    | (lr, xr, rr) → false

(**
 * Original definition:
 *
 *   pheap leaf = true
 *   pheap (l, x, r) = (pheap l /\ pheap r /\ (\forall y \in set_tree l. x <= y))
 *)
pheap ∷ Ord α ⇒ Tree α → Bool
pheap h = match h with
  | leaf → true
  | (l, x, r) → (Bool.and (Bool.and (pheap l) (pheap r)) (all_leq l x))

all_leq t x = match t with
  | leaf → true
  | (l, y, r) → if y > x
    then false
    else (Bool.and (all_leq l x) (all_leq r x))

(**
 * Original definition:
 *
 *   link leaf = leaf
 *   link (lx, x, leaf) = (lx, x, leaf)
 *   link (lx, x, (ly, y, ry)) = (if x < y then ((ly, y, lx), x, ry) else ((lx, x, ly), y, ry))
 *)
link ∷ Ord α ⇒ Tree α → Tree α
link h = match h with
  | leaf        → leaf
  | (lx, x, rx) → match rx with
    | leaf        → (lx, x, leaf)
    | (ly, y, ry) → if x < y
      then ((ly, y, lx), x, ry)
      else ((lx, x, ly), y, ry)

(**
 * Original definition:
 *
 *   insert x h = merge (leaf, x, leaf) h
 *)
insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert x h = (merge (Tree.singleton x) h)

(**
 * Original definition:
 *
 *   merge leaf h = h
 *   merge h leaf = h
 *   merge (lx, x, leaf) (ly, y, leaf) = link (lx, x, (ly, y, leaf))
 *
 * But note that we cannot restrict ourselves to the arguments having
 * a right-subtree equal to leaf.
 *
 * Proof of a logarithmic upper bound for merge, in analogy to Lemma 8.4:
 *
 * As potential function we take:
 *
 *   Phi leaf       := 0
 *   Phi (l, _, r) := Phi l + Phi r + log' |l| + log' |r|
 *
 * where
 *
 *   |leaf| := 1    and    |(l, _, r)| := |l| + |r|
 *
 * Let h1 := (lx, x, leaf) and h2 := (ly, y, leaf)
 *
 * We want to show
 *
 *   Phi (merge h1 h2) - (Phi h1 + Phi h2) =
 *   Phi (merge h1 h2) -  Phi h1 - Phi h2  <=
 *   log' (|h1| + |h2|)
 *
 * First, observe following equality
 *
 *     Phi (merge h1 h2)
 *   = Phi (link (lx, x, h2))                                       (def. merge)
 *   = Phi ((ly, y, lx), x, leaf)                                    (w.l.o.g. by def. link)
 *   = Phi (ly, y, lx) + Phi leaf + log' |(ly, y, lx)| + log' |leaf|  (def. Phi)
 *   = Phi (ly, y, lx) + 0       + log' |(ly, y, lx)| + 0           (def. Phi, |_|)
 *   = Phi (ly, y, lx) + log' (|ly| + |lx|)                         (def. |_|)
 *   = Phi ly + Phi lx + log' |lx| + log' |ly| + log' (|ly| + |lx|) (def. Phi)
 *
 * Then, it follows that
 *
 *      Phi (merge h1 h2) - Phi h1 - Phi h2
 *    = Phi ly + Phi lx + log' |lx| + log' |ly| + log' (|ly + |lx|) (def. Phi)
 *    - Phi lx - Phi leaf - log' |lx| - log' |leaf|
 *    - Phi ly - Phi leaf - log' |ly| - log' |leaf|
 *    = ~                                                           (def. Phi, |_|)
 *    - Phi lx - 0       - log' |lx| - 0
 *    - Phi ly - 0       - log' |ly| - 0
 *    = log' (|ly| + |lx|)
 *   <= log' (|lx| + |ly| + 2)                    (monotone log')
 *    = log' (|lx| + |leaf| + |ly| + |leaf|)
 *    = log' (|h1| + |h2|)
 *
 * For the more general case:
 *
 * Let h1 := (lx, x, rx) and h2 := (ly, y, ry)
 *
 * We want to show
 *
 *   Phi (merge h1 h2) - (Phi h1 + Phi h2) =
 *   Phi (merge h1 h2) -  Phi h1 - Phi h2  <=
 *   log' (|h1| + |h2|)
 *
 * First, observe following equality
 *
 *     Phi (merge h1 h2)
 *   = Phi (link (lx, x, (ly, y, leaf)))    (def. merge)
 *   Case x < y:
 *     = Phi ((ly, y, lx), x, leaf)                                    (def. link)
 *     = Phi (ly, y, lx) + Phi leaf + log' |(ly, y, lx)| + log' |leaf|  (def. Phi)
 *     = Phi (ly, y, lx) + 0       + log' (|ly| + |lx|) + 0           (def. Phi, |_|)
 *     = Phi ly + Phi lx + log' |lx| + log' |ly| + log' (|ly| + |lx|) (def. Phi)
 *   Case x >= y:
 *     = Phi ((lx, x, ly), y, leaf)                                    (def. link)
 *     = Phi (lx, x, ly) + Phi leaf + log' |(lx, x, ly)| + log' |leaf|  (def. Phi)
 *     = Phi (lx, x, ly) + 0       + log' (|lx| + |ly|) + 0           (def. Phi, |_|)
 *     = Phi lx + Phi ly + log' |ly| + log' |lx| + log' (|lx| + |ly|) (def. Phi)
 *   = Phi lx + Phi ly + log' |lx| + log' |ly| + log' (|lx| + |ly|) (comm. +)
 *
 * Then, it follows that
 *
 *      Phi (merge h1 h2) - Phi h1 - Phi h2
 *    = Phi lx + Phi ly + log' |lx| + log' |ly| + log' (|lx + |ly|) (def. Phi)
 *    - Phi lx - Phi rx - log' |lx| - log' |rx|
 *    - Phi ly - Phi ry - log' |ly| - log' |ry|
 *    = log' (|ly| + |lx|) - Phi rx - log' |rx| - Phi ry - log' |ry|
 *   <= log' (|ly| + |lx|)                       (log' |_| >= 0, Phi _ >= 0, def. -)
 *   <= log' (|lx| + |rx| + 1 + |ly| + |ry| + 1) (monotone log'))
 *    = log' (|h1| + |h2|)
 *)
merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge h1 h2 = match h1 with
  | leaf        → h2
  | (lx, x, rx) → match h2 with
    | leaf        → (lx, x, rx)
    | (ly, y, ry) → (link (lx, x, (ly, y, leaf)))

del_min ∷ Ord α ⇒ Tree α → Tree α
del_min h = match h with
  | leaf      → leaf
  | (l, x, r) → (pass2 (pass1 l))

pass1 ∷ Ord α ⇒ Tree α → Tree α
pass1 h = match h with
  | leaf        → leaf
  | (lx, x, rx) → match rx with
    | leaf        → (lx, x, leaf)
    | (ly, y, ry) → (link (lx, x, (ly, y, pass1 ry)))

pass2 ∷ Ord α ⇒ Tree α → Tree α
pass2 h = match h with
  | leaf      → leaf
  | (l, x, r) → (link (l, x, pass2 r))

merge_pairs ∷ Ord α ⇒ Tree α → Tree α
merge_pairs h = match h with
  | leaf        → leaf
  | (lx, x, rx) → match rx with
    | leaf        → (lx, x, leaf)
    | (ly, y, ry) → (link (link (lx, x, (ly, y, merge_pairs ry))))

merge_pairs_nolink ∷ Ord α ⇒ Tree α → Tree α
merge_pairs_nolink h = match h with
  | leaf -> leaf
  | (la, a, ra) -> match ra with
    | leaf -> (la, a, leaf)
    | (lb, b, rb) -> match merge_pairs_nolink rb with
      | leaf -> if a < b
        then ((lb, b, la), a, leaf)
        else ((la, a, lb), b, leaf)
      | (lc, c, rc) -> if a < b
        then if a < c
          then ((lc, c, (lb, b, la)), a, rc)
          else (((lb, b, la), a, lc), c, rc)
        else if b < c
          then ((lc, c, (la, a, lb)), b, rc)
          else (((la, a, lb), b, lc), c, rc)

merge_pairs_via_pass ∷ Ord α ⇒ Tree α → Tree α
merge_pairs_via_pass h = pass2 (pass1 h)