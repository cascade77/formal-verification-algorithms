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
├── bst/          # Binary Search Trees verified in Rocq
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

**Lemma 1.** `all_keys_insert`. If all keys in a tree satisfy predicate P,
and the inserted key also satisfies P, then all keys in the resulting tree
still satisfy P.

**Theorem 2.** `insert_bst`. If a tree satisfies the BST invariant, then
inserting any key produces a tree that also satisfies the BST invariant.

---

## Tools

- [Rocq](https://rocq-prover.org/) (formerly Coq)
- [Lean4](https://lean-lang.org/)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Algorithms 4th Edition](https://algs4.cs.princeton.edu/)
