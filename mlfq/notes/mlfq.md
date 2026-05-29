the idea was to formalize MLFQ from [chapter 8](https://pages.cs.wisc.edu/~remzi/OSTEP/cpu-sched-mlfq.pdf) of OSTEP. three records, a few functions, four theorems. straightforward in concept but there were a few places where the Rocq details were genuinely non-obvious.

---

the process record ended up with three fields: `pid`, `remaining_work`, and `used_allotment`. the allotment limit does not go on the process, it goes on the queue, because every process sitting in a given queue shares the same limit. this distinction matters because when a process gets demoted, its `used_allotment` resets to 0 but the queue's `allotment_limit` is untouched.

the queue record has `processes` and `allotment_limit`. and `mlfq` is just `list queue`. no wrapper type needed, the list ordering already encodes priority.

---

`job_enters` was the first function. the match on the mlfq was clear enough but the body of the non-empty case needed some thought. `mlfq_queue (p :: head.(processes)) head.(allotment_limit)` looks like two things happening at once. it's not. it's just calling the constructor with two arguments: the updated process list and the unchanged allotment limit. the `.` field access syntax threw me off at first.

`job_executes` needed four let bindings before the if. `updated_p` for the stay case, `new_q0` wrapping it, `demoted_p` for the demotion case with `used_allotment` reset to `0`, `new_q1` wrapping it. the `0` for the reset was not obvious immediately. when a process gets demoted it starts fresh at the new level so its used budget has to go back to zero, not carry over.

---

the demotion proof `job_executes_demotion` was stated as an equality on the whole result rather than a membership statement. this made the proof short: `simpl`, `rewrite H`, `rewrite Nat.eqb_refl`, `reflexivity`. the key is that `H : used_allotment p = allotment_limit q0` lets you rewrite the boolean check into `allotment_limit q0 =? allotment_limit q0`, and `Nat.eqb_refl` collapses that to `true` so the two sides of the equality become identical.

`job_executes_same` was the symmetric case. needed `Nat.eqb_neq` which converts `a =? b = false` into `a ≠ b`, and then `lia` handles the step from `<` to `≠`. the assert block was the cleanest way to do it:

```
assert (used_allotment p =? allotment_limit q0 = false) as Hneq.
{ apply Nat.eqb_neq. lia. }
rewrite Hneq.
reflexivity.
```

---

`priority_boost` used `List.flat_map` to collect all processes from every queue into one flat list. this was genuinely new. `List.flat_map f l` applies `f` to every element of `l` and concatenates the results, so `List.flat_map (fun q => q.(processes)) m` walks every queue and joins their process lists. then `List.map` rebuilt the remaining queues with empty process lists but the same allotment limits.

`priority_boost_In` was the most involved proof. the theorem uses an existential: there exists some queue `q'` in the mlfq that contains `p`. the intro pattern `intros [q' [Hq' Hp]]` destructs the existential immediately into the witness and the two conjuncts. after simpl the goal becomes `In p (processes q ++ flat_map (...) rest)` and `in_or_app` splits it into two cases. if `q' = q` (the head), rewrite and close with `Hp`. if `q'` is in `rest`, go right and use `in_flat_map` with `q'` as the witness. `in_flat_map` says: to show something is in a flat_map, give an element of the original list that maps to something containing your target.

the `hd q` in the theorem statement was also new. `hd` in Rocq always needs a default value because the list could be empty. the default never actually gets used here since the mlfq is concretely `q :: rest`, but Rocq requires it at the type level.

---

more extension is needed. rules 1 and 2, the actual scheduling decision of which process runs next, are not formalized. that would need a `pick_next` function and a proof that it always selects from the highest non-empty queue. the interaction between `job_enters` and `job_executes` is also not proven explicitly, specifically that a freshly entered process with `used_allotment = 0` never gets demoted on its first step (this follows from `job_executes_same` but is not stated as its own corollary).
