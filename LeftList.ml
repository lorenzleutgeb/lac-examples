cons ∷ α ⨯ Tree α → Tree α
cons x t = (t, x, leaf)

cons_cons ∷ α ⨯ α ⨯ Tree α → Tree α
cons_cons x y t = ((t, x, leaf), y, leaf)

tl ∷ Tree α → Tree α
tl t = match t with
  | leaf      → leaf
  | (l, x, r) → l

(**
 * The number of recursive calls is equivalent to
 * the "leftmost depth" of t1. We interpret t1 as
 * a list, where all elements are the left child
 * nodes, starting from t1.
 * The size of t2 is irrelevant when determining
 * the number of recursive calls to append!
 * We therefore expect cost to be expressed only
 * in some terms dependent on t1.
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate:
 *   append t1 t2 | 1 * rk(t1)
 *
 * Attempt to prove:
 * Case: t1 == (l, x, r)
 *   rk(t1)                                >= rk((append l t2, x, r)) + 1
 *   rk((l, x, r))                         >= ...
 *   rk(l) + log'(|l|) + log'(|r|) + rk(r) >= ...
 *   rk(l) + log'(|l|) + log'(|r|) + rk(r) >= rk((append l t2, x, r)) + 1
 *   ...                                   >= rk(append l t2) + log'(|append l t2|) + log'(|r|) + rk(r) + 1
 *   rk(l) + log'(|l|)                     >= rk(append l t2) + log'(|append l t2|) + 1
 * ! At this point we are stuck, since we do not know how to cancel `append l t2`.
 * Case: t1 == leaf
 *   rk(t1)  >= 0
 *   rk(leaf) >= 0
 *   0       >= 0
 *)
append ∷ Tree α ⨯ Tree α → Tree α
append t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (cons x (append l t2))

(**
 * This function is equivalent to
 *
 *     f t = leaf
 *
 * on trees, but costs the "leftmost depth"
 * of t.
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate:
 *   descend t | 1 * rk(t)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   rk(t)   >= 0
 *   rk(leaf) >= 0
 *   0       >= 0
 * Case: t == (l, x, r)
 *   rk(t)                                 >= rk(l) + 1
 *   rk((l, x, r))                         >= rk(l) + 1
 *   rk(l) + log'(|l|) + log'(|r|) + rk(r) >= rk(l) + 1
 *           log'(|l|) + log'(|r|) + rk(r) >=         1
 * ! Error, since for l == leaf and r == leaf we have that 0 >= 1.
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate:
 *   descend x t | 1 * p_{(1, 2)}
 *   ...              | 1 * log'(1 * |t| + 2)
 *   ...              |     log'(    |t| + 2)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   log'(|t| + 2) >= 0
 *   log'(|t| + 2) >= log'(2) = 1 >= 0
 * Case: t == (l, x, r)
 *   log'(|t|         + 2) >= log'(|l| + 2) + 1
 *   log'(|(l, x, r)| + 2) >= log'(|l| + 2) + 1
 *   log'(|l| + |r|   + 2) >= log'(|l| + 2) + 1
 * ! Error, since for l == leaf and r == leaf we have that 1 >= 2.
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate with new potential `ht` (short for "height"):
 *   ht(leaf)      := 1
 *   ht((l, _, r) := max({ht(l), ht(r)}) + 1
 *
 *   descend x t | ht(t)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   ht(t) >= 0
 *   by definition of ht.
 * Case: t == (l, x, r)
 *   ht(t)                   >= ht(l) + 1
 *   ht((l, y, r))           >= ht(l) + 1
 *   max({ht(l), ht(r)}) + 1 >= ht(l) + 1
 *   max({ht(l), ht(r)})     >= ht(l)
 *   Case: ht(l) >= ht(r)
 *     ht(l) >= ht(l)
 *   Case: ht(l) < ht(r)
 *     ht(r) >= ht(l)
 *)
descend ∷ Tree α → Tree β
descend t = match t with
  | leaf      → leaf
  | (l, x, r) → (descend l)

(**
 * This function is equivalent to
 *
 *     f t1 t2 = leaf
 *
 * on trees, but costs the "leftmost depth"
 * of t1.
 *)
descend_on_first ∷ Tree α ⨯ Tree α → Tree β
descend_on_first t1 t2 = match t1 with
  | leaf      → leaf
  | (l, x, r) → (descend_on_first l t2)

(**
 * This function is equivalent to
 *
 *     f t1 t2 = leaf
 *
 * on trees, but costs the "leftmost depth"
 * of t2.
 *)
descend_on_second ∷ Tree α ⨯ Tree α → Tree β
descend_on_second t1 t2 = match t2 with
  | leaf      → leaf
  | (l, x, r) → (descend_on_second t1 l)

inorder ∷ Tree α ⨯ Tree α → Tree α
inorder t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (inorder l (cons x (inorder r t2)))

is ∷ Tree α → Bool
is t = match t with
  | leaf        → true
  | (lx, x, rx) → match rx with
    | leaf        → is lx
    | (ly, y, ry) → false

(**
 * This function is equivalent to
 *
 *     id x = x
 *
 * on trees, but costs the "leftmost depth"
 * of t.
 *)
iter ∷ Tree α → Tree α
iter t = match t with
  | leaf      → leaf
  | (l, x, r) → (cons x (iter l))

postorder ∷ Tree α ⨯ Tree α → Tree α
postorder t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (postorder l (postorder r (cons x t2)))

preorder ∷ Tree α ⨯ Tree α → Tree α
preorder t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (cons x (preorder l (preorder r t2)))

(**
 * The number of recursive calls is equivalent to
 * the "leftmost depth" of t1. We interpret t1 as
 * a list, where all elements are the left child
 * nodes, starting from t1.
 * We discard r.
 * The size of t2 is irrelevant when determining
 * the number of recursive calls to append_reverse!
 * We therefore expect cost to be expressed only
 * in some terms dependent on t1.
 * We think that our type system cannot solve this.
 *)
rev_append ∷ Tree α ⨯ Tree α → Tree α
rev_append t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (rev_append l (cons x t2))
