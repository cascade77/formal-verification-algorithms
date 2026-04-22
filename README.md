# Formal Verification of Algorithms

Formal verification of algorithms and data structures using Rocq and Lean4.
This is a learning project following Software Foundations and Sedgewick's
Algorithms, applying formal proof techniques to verify real algorithms
from scratch.

---

## Structure
```
formal-verification-algorithms/
├── sorting/      # Sorted list properties verified in Lean4
├── bst/          # Binary Search Trees and Red-Black Trees verified in Rocq
│   ├── BST.v
│   ├── RBT.v
│   └── notes/    
├── block_decomposition/  # MPI block decomposition verified in Rocq
│   ├── block_decomp.v
│   └── notes/
├── mergesort/
│   ├── MergeSort.v           # Merge, Split, Mergesort verified in Rocq
│   └── notes/
└── README.md
```
---

## sorting/

Formal verification of sorted list properties in Lean4. Defines `Sorted`
as both a boolean function and a `Prop`, then proves structural properties
about sorted lists.

**Theorem 1.** `empty_sorted`. The empty list is sorted.

**Theorem 2.** `single_sorted`. Any single element list is sorted.

**Theorem 3.** `two_sorted`. A two element list `[a, b]` is sorted if and only if `a ≤ b`.

**Theorem 4.** `sorted_tail`. If a list is sorted, its tail is also sorted.

**Theorem 5.** `sorted_cons`. A list `a :: b :: l` is sorted if and only if `a ≤ b` and `b :: l` is sorted.

**Theorem 6.** `sorted_head_le`. If `a :: b :: l` is sorted, then `a ≤ b`.

**Theorem 7.** `sorted_length_eq`. The custom `listLength` function agrees with the built-in `List.length` for all lists.

---

## bst/

Formal verification of Binary Search Trees in Rocq, building toward
Red-Black Trees. The BST ordering invariant is defined inductively and
insertion is proved correct. Based on the 2-3 tree and Red-Black BST
treatment from [Sedgewick & Wayne, Section 3.3](https://algs4.cs.princeton.edu/33balanced/).

### BST.v
**Lemma 1.** `all_keys_insert`. If all keys in a tree satisfy predicate P,
and the inserted key also satisfies P, then all keys in the resulting tree
still satisfy P.

**Theorem 2.** `insert_bst`. If a tree satisfies the BST invariant, then
inserting any key produces a tree that also satisfies the BST invariant.

### RBT.v
Defines the three structural invariants: no consecutive red links, perfect black balance, and BST ordering. Implements the three fix operations and insertion.

**Definitions.** `color`, `rbtree`, `is_red`, `no_red_red`, `black_balanced`, `black_height`, `bst_rbt`.

**Fix operations.** `rotate_left`, `rotate_right`, `flip_colors`, `fix_up`.

**Insertion.** `rbt_insert_aux` inserts like a BST and applies `fix_up` on the way back up. `rbt_insert` forces the root black.


---


## block_decomposition/

Formal verification of the block decomposition formulas used in MPI parallel programs, in Rocq. Proves that the standard BLOCK_LOW and BLOCK_HIGH formulas form a correct partition of indices across processes. Motivated by the open problem of applying formal methods to HPC correctness.

### block_decomp.v
**Lemma 1.** `block_low_zero`. The first process always starts at index 0.

**Lemma 2.** `block_adjacent`. For any process i, the next process i+1 starts exactly one index after where process i ends.

---



## mergesort/

Formal verification of mergesort in rocq. defines `merge`, `split`, and `mergesort`, then proves that merging two sorted lists gives a sorted list. the proof took a while to get right and this directory has notes on exactly what broke and why.

### MergeSort.v

**Definitions.**

`sorted` is an inductive proposition with three constructors: `sorted_nil` for the empty list, `sorted_one` for a single element, and `sorted_cons` for two or more elements where the first is `<=` the second and the rest is also sorted.

`merge` uses a nested `let fix` because the naive two-argument version fails rocq's termination checker. the outer function recurses on `l1`, the inner helper `merge_aux` recurses on `l2`.

`mergesort_aux` takes an extra counter `n` as a fuel argument because after splitting, neither half is a syntactic subterm of the original list and rocq rejects the recursion. starting with `n = length l` and passing `n-1` each time gives rocq a structurally decreasing argument it can check.



**Lemma 1-2.** `merge_l_le`, `merge_r_lt`: explicit rewrite lemmas for the two branches of merge. needed because `simpl` does not always reduce the nested `let fix` cleanly inside proofs.

**Lemma 3-4.** `sorted_cons_inv`, `sorted_cons_inv'`: inversion helpers that extract inequalities and sub-sorted hypotheses from a sorted hypothesis.

**Lemma 5.** `le_of_leb`: converts `Nat.leb a b = true` (a Bool) to `a <= b` (a Prop) using `Compare_dec.leb_complete`.

**Lemma 6.** `merge_sorted_cons`: if `h <= hd h (merge l1 l2)` and `merge l1 l2` is sorted, then `h :: merge l1 l2` is sorted. used to reduce the main theorem to two cleaner subgoals.

**Lemmas 7.** `sorted_head_le`: if a list is sorted and `x` is anywhere in the tail, then the head is `<= x`. proved by induction on the tail. uses `lia` for the transitivity step rather than `le_trans` directly, which avoids version-specific naming issues.

**Lemmas 8.** `merge_In`: if `x` is in `merge l1 l2`, it came from `l1` or `l2`. proved by double induction, using `merge_l_le` and `merge_r_lt` to rewrite before each membership case split.

**Theorem 1.** `merge_sorted`. if `l1` and `l2` are both sorted, then `merge l1 l2` is sorted.

the proof does outer induction on `l1` and inner induction on `l2`. the two non-trivial cases are when both lists are non-empty. in each case, after rewriting with `merge_l_le` or `merge_r_lt`, the goal becomes `sorted (h :: merge ...)`. applying `merge_sorted_cons` splits this into two subgoals: proving the new head is `<=` the head of the merge result, and proving the merge result is sorted. the second subgoal is handled by the induction hypothesis. the first uses `merge_In` to trace where the head of the merge came from, then `sorted_head_le` to bound it.

---

## Tools

- [Rocq](https://rocq-prover.org/) (formerly Coq)
- [Lean4](https://lean-lang.org/)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Algorithms 4th Edition](https://algs4.cs.princeton.edu/)
