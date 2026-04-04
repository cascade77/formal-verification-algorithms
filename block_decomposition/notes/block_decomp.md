# block decomposition

this is a formal proof of the block decomposition formulas used in mpi parallel programs, written in rocq 9.1.0.

## what even is block decomposition

when you have `n` indices and `p` processes and you want to split the work evenly, block decomposition gives each process a contiguous chunk. so with `n = 12` and `p = 4`:

```
process 0 → 0, 1, 2
process 1 → 3, 4, 5
process 2 → 6, 7, 8
process 3 → 9, 10, 11
```
the formula for where each process starts and ends is:
```math
\text{block\_low}(i, p, n) = \left\lfloor \frac{i \times n}{p} \right\rfloor
```
```math
\text{block\_high}(i, p, n) = \left\lfloor \frac{(i+1) \times n}{p} \right\rfloor - 1
```

`block_low` is the starting index of process `i`, `block_high` is the ending index. these are the standard `BLOCK_LOW` and `BLOCK_HIGH` macros from parallel computing textbooks.


## proving

a correct partition means:

- the first process starts at index 0
- every process starts exactly where the previous one ended plus 1 (no gap, no overlap)
- the last process ends at index n-1

---

## how to find lemmas in rocq

when a tactic like `lia` or `reflexivity` fails, it usually means rocq needs a specific library lemma to make progress. the way to find it is the `Search` command. you give it a pattern that looks like the shape of your goal, and rocq lists every lemma it knows that matches.

for example when the goal was `0 / p = 0` and nothing worked, i ran:
```coq
Search (0 / _ = 0).
```

the `_` is a wildcard meaning "anything here". rocq returned `Nat.Div0.div_0_l` which was required.
when the goal was `(i+1)*n/p = (i+1)*n/p - 1 + 1` and i needed something about subtraction and addition cancelling, i ran:
```coq
Search (_ - _ + _ = _).
```

which returned `Nat.sub_add`. and when i needed to prove a division result is at least 1, i ran:
```coq
Search (Nat.div_str_pos).
```

to read its exact type and understand what precondition it needs.

the pattern is always: look at the shape of your goal, write a Search with wildcards for the parts that vary, read what comes back.

## whole process

### the definitions
```coq
Definition block_low (i p n : nat) : nat :=
  (i * n) / p.

Definition block_high (i p n : nat) : nat :=
  ((i + 1) * n) / p - 1.
```

one thing that matters a lot here: rocq's `nat` has no negative numbers. so `0 - 1 = 0` in rocq, not `-1`. this is called truncated subtraction. `block_high` has a `- 1` in it, so if the division ever gives 0, the subtraction truncates and the formula silently breaks. this comes up when proving things.

also the `/` on `nat` is already floor division. no need to write anything special, dividing two natural numbers in rocq automatically truncates toward zero.

---

### lemma 1: the first process always starts at 0

the first thing to prove is that `block_low(0, p, n) = 0`. putting `i = 0` into the formula: `floor(0 * n / p) = floor(0 / p) = 0`. obvious in math, but rocq needs a proof.
```coq
Lemma block_low_zero : forall p n : nat,
  block_low 0 p n = 0.
```

i first had `p <> 0` as a precondition because i thought dividing by zero would be a problem. turns out rocq defines `x / 0 = 0` by convention, so `0 / 0 = 0` too, and the lemma holds for any `p` including 0. so i removed the precondition. a lemma with fewer unnecessary conditions is better because it's easier to use later.

**what each step does:**

`intros p n` : the goal starts as `forall p n, ...`. this tactic moves `p` and `n` out of the goal and into the context so we have names to work with.

`unfold block_low` : replaces `block_low 0 p n` with its actual definition `(0 * n) / p`.

`simpl` : rocq computes `0 * n` to `0`, so the goal becomes `0 / p = 0`.

here i tried `reflexivity`. it failed because `p` is still unknown so rocq can't compute `0 / p` to a concrete number. then i tried `lia` (the automatic arithmetic solver). also failed because `lia` doesn't handle division.

so i used `Search (0 / _ = 0)` to find the right lemma. it returned `Nat.Div0.div_0_l` which says exactly that zero divided by anything is zero.

`apply Nat.Div0.div_0_l` — closes the goal.
```coq
Proof.
  intros p n.
  unfold block_low.
  simpl.
  apply Nat.Div0.div_0_l.
Qed.
```

---

### lemma 2: every process starts exactly where the previous one ended plus 1

this is the no-gap no-overlap condition. process 0 ends at 2, process 1 starts at 3. process 1 ends at 5, process 2 starts at 6. and so on. in formula form:
```math
\text{block\_low}(i+1, p, n) = \text{block\_high}(i, p, n) + 1
```
```coq
Lemma block_adjacent : forall i p n : nat,
  p <> 0 -> p <= n ->
  block_low (i + 1) p n = block_high i p n + 1.
```

**why these preconditions:**

`p <> 0` : there should be at least one process.

`p <= n` : this one i didn't have at first. i originally used `0 < n` (at least one element). but the proof broke when the goal `p <= (i+1)*n` appeared and couldn't be proved from just `0 < n`. consider `p = 100` and `n = 1`: then `(i+1)*n = 1` but `p = 100`, so `100 <= 1` is false. the condition `p <= n` makes sure each process actually gets at least one index.

**what happens when you unfold both definitions:**

the goal becomes:

`(i+1)*n/p = (i+1)*n/p - 1 + 1`

call `(i+1)*n/p` just `x`. the goal is `x = x - 1 + 1`. in normal math this is always true. but in `nat`, if `x = 0` then `0 - 1 = 0` (truncation), so `0 - 1 + 1 = 1` which is not `0`. so the cancellation only works when `x >= 1`.

`lia` and `omega` can't handle this because they don't do division.

i used `Search (_ - _ + _ = _)` and found `Nat.sub_add` which says: if `n <= m` then `m - n + n = m`. so for our case, if `1 <= x` then `x - 1 + 1 = x`. that's what we need.

**assert:**

`assert (H : 1 <= (i+1)*n/p)` pauses the current goal and says: first prove this smaller fact, then once it's proved it becomes hypothesis `H` available for the rest. this splits the proof into two parts:

- goal 1: prove `1 <= (i+1)*n/p`
- goal 2: the original goal, now with `H` available

for goal 1, `Nat.div_str_pos` says: if `0 < p <= (i+1)*n` then `0 < (i+1)*n/p` (same as `1 <= (i+1)*n/p`). applying it transforms the goal to `0 < p <= (i+1)*n`, which `lia` closes using `Hp` and `Hn`.

for goal 2, now that `H : 1 <= (i+1)*n/p` is in context, `lia` can prove `x = x - 1 + 1` because it knows `x >= 1` and understands truncated subtraction.
```coq
Proof.
  intros i p n Hp Hn.
  unfold block_low, block_high.
  assert (H : 1 <= (i + 1) * n / p).
  { apply Nat.div_str_pos. lia. }
  lia.
Qed.
```

---
