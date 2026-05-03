this directory verifies insertion sort in Rocq. the interesting thing about it compared to the other directories is that the main theorems use `In` directly, which is the same `In` fixpoint from the **Software Foundations Logic chapter**. so the proofs here are a direct application of what that chapter builds up: existentials, biconditionals, and reasoning about list membership. `isort_sorted` says the output is always sorted. `isort_In` says every element of the input shows up in the output and vice versa, using `In` to express that.

---

the `sorted` predicate is the same inductive one from mergesort. three constructors: nil is sorted, a singleton is sorted, and a cons cell `x :: y :: l` is sorted if `x <= y` and `y :: l` is sorted.

`insert` takes a number `a` and a sorted list and puts `a` in the right place. you match on the list. empty list returns `[a]`. cons cell `x :: rest` checks `a <=? x`. if true, `a` goes in front and you are done. if false, you keep `x` and recurse into rest. the key thing is that in the false branch you write `x :: insert a rest` and not just `insert a rest`. x has to stay in the output. you are not removing it, you are just saying a does not go before x so go find where it belongs further along.

`isort` is then short. empty list is already sorted. for `a :: rest` you sort rest first and then insert a into the result. rocq accepts this because rest is smaller than `a :: rest` structurally.

---

the first place things got complicated was `insert_sorted`. the naive approach is to induct on `l`, which forces a three-case induction pattern `[| a' [| a'' l''] IHl']` to get enough structure for `sorted_cons`. this works but produces a long proof with a lot of branches and nested inversions.

the cleaner move is to induct on the proof that `l` is sorted, not on `l` itself. when you write `induction H` where `H : sorted l`, rocq gives you exactly the three cases of the `sorted` type: nil, one, and cons. in the cons case you already have `H : x <= y` and `H0 : sorted (y :: l)` as hypotheses from the constructor, so no inversion needed. the proof becomes three clean cases.

one tricky sub-case inside `insert_sorted` is when `a > x` and you need the induction hypothesis to handle the tail. the IH says `sorted (insert a (y :: l))` but after simpl the goal sometimes has an `if` still sitting inside it unexpanded. the fix was `simpl in IHsorted. rewrite E1 in IHsorted.` to force the reduction inside the IH before applying it.

for converting between the boolean `<=?` and the propositional `<=`, two standard library lemmas came up repeatedly. `leb_complete` goes from `(a <=? b) = true` to `a <= b`. `leb_complete_conv` goes from `(a <=? b) = false` to `b < a`. once you have `b < a` you just call `lia` to finish without worrying about what the exact lemma name is for that step.

---

`isort_sorted` is short once `insert_sorted` exists. induct on l. base case is `sorted []` by `sorted_nil`. inductive case: the IH says `sorted (isort l')`, and the goal is `sorted (insert a' (isort l'))`, which is exactly `insert_sorted` applied to the IH.

`isort_In` is the biconditional saying x is in l if and only if x is in isort l. split into two directions.

the forward direction says if x is in l then x is in isort l. induction on l. base case is impossible since l is empty. cons case: x is either the head a or somewhere in the tail l'. if x is the head then `insert_In` puts it into `insert a (isort l')`. if x is in the tail then the IH gives you x in isort l' and `insert_In` with right puts it further in.

the backward direction says if x is in isort l then x is in l. induction on l again. cons case: after simpl, the hypothesis becomes `In x (insert a (isort l'))`. apply `insert_In_rev` to get `In x (a :: isort l')`, then destruct. left branch gives x = a so x is the head of a :: l', done. right branch gives x in isort l' and the IH takes that to x in l', done.

---

one bullet depth issue came up. the proof of `isort_In` needed so many levels of nesting that the standard `+`, `-`, `*`, `--` bullets ran out. the fix was switching to `{ }` blocks at the deepest level, which rocq always accepts regardless of nesting depth.
