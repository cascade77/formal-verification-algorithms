# Formal Sorting Verification Notes

## Basics
### Defining listLength



```lean
def listLength (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | head :: tail => 1 + listLength tail 

#eval listLength [1,2,3]

```
I started by defining a function called `listLength` that takes a list of natural numbers and returns a natural number. The purpose of this function is to calculate the length of the given list. The function works by pattern matching on the input list.
When the list is empty, represented as `[]`, the function returns `0` because there are no elements inside. In the case where the list is not empty, Lean separates it into two parts: the `head`,  which is the first element, and the `tail`, which is the rest of the list. The function then returns `1 + listLength tail`, meaning it counts the first element and then continues to count the length of the rest of the list recursively.
To see how this works in practice, I evaluated the function on the list `[1,2,3]`. First, the list is not empty, so it matches the second case. The head is `1` and the tail is `[2,3]`, so the result is `1 + listLength [2,3]`. Next, for `[2,3]`, again the list is not empty, so the head is `2` and the tail is `3`. This gives `1 + listLength [3]`. The list `[3]` and the tail is `[]`. Now we have `1 + listLength []`. Since `[]` is empty, the base case applies and it returns `0`. Adding everything up, we get `1 + (1 + (1 + 0)) = 3` 


### Defining sorted as a Boolean


```lean
def sorted (l : List Nat) : Bool := 
  match l with
  | [] => true
  | [single] => true
  | first :: second :: rest => (first ≤ second) && (sorted (second :: rest))

#eval sorted [1,2,3] -- true
#eval sorted [3,1,2] -- false
```

I defined a function called `sorted` that checks whether a list of natural numbers is in non-decreasing order. The function returns a Boolean value, either `true` or `false`. To do this, it uses a pattern matching to break down the structure of list.
If the list is empty, it is considered sorted, so the function returns `true`. If the list has exactly one element, it is also sorted, since there's nothing else to compare, and again the function returns `true`. The interesting case happens when the list has at least two elements. In this case, the function separates the list into the first element, the second element, and the rest of the list. It then checks whether the first element is less than or equal to the second, and at the same time recursively calls itself to check if the remaining part of the list is sorted. Both conditions must be true for the whole list to be sorted, which is why the function uses the Boolean `&&` operator.
When I evaluate the function on `[1,2,3]`, the result is `true`. This makes sense because each element is less than or equal to the one after it: `1 ≤ 2` and `2 ≤ 3`. The recursive call keeps moving forward until the list reduces to either a single element or an empty list, both of which return `true`. On the other hand, when I evaluate the function on `[3,1,2]`, the result is `false`. This is because the very first comparison fails: `3 ≤ 1` is false, so no matter what comes afterward, the whole result is false.

### Defining Sorted as a Proposition


```lean
-- defining sorted as a Proposition (for mathematical proofs)

def Sorted (l : List Nat) : Prop :=
  match l with
  | [] => True
  | [single] => True
  | first :: second :: rest => first ≤ second ∧ Sorted (second :: rest)

-- the difference
#eval sorted [1,2,3]
#eval Sorted [1,2,3]

-- Sorted [1, 2, 3] is a mathematical proposition (a statement that could be proved)
-- it needs to be proved for computing.

#check Sorted [1,2,3]
#check Sorted []
#check Sorted [5]
#reduce Sorted []

```

Here I defined `Sorted` as a proposition rather than as a Boolean function. The difference is subtle but important. When I used `sorted` earlier, the function returned either `true` or `false` directly, which made it computable in Lean’s evaluation system. Now, with `Sorted`, I am defining a logical property that a list may or may not satisfy, and this property is something I can prove about lists rather than just compute.
Looking at the definition, an empty list is considered sorted, so the proposition is `True`. A single-element list is also trivially sorted, so again the proposition is `True`. When the list has at least two elements, Lean requires two things to hold: the first element must be less than or equal to the second, and the rest of the list must itself satisfy the `Sorted` property. This time the connective is `∧`, meaning “and” in logic, rather than `&&` which was Boolean conjunction.
The difference shows up when evaluating. If I run `#eval sorted [1,2,3]`, Lean gives me `true` immediately because that’s just computation. If I run `#eval Sorted [1,2,3]`, Lean complains because `Sorted [1,2,3]` is not something that can be evaluated like a number or Boolean. Instead, it is a proposition, a logical statement that needs to be proved. With `#check Sorted [1,2,3]`, Lean tells me the type is `Prop`, confirming that it lives in the world of logic. Similarly, `#check Sorted []` and `#check Sorted [5]` show that these are propositions as well, both of which happen to be trivially true. Using `#reduce Sorted []` shows that Lean simplifies it to `True`.
So, the Boolean `sorted` is for computation: I can run it on a list and immediately get an answer. The propositional `Sorted` is for reasoning: I can now write and prove lemmas and theorems that use it, like showing that a particular sorting algorithm always produces a `Sorted` list. This separation of computation from proof is a key idea in Lean and in formal verification generally.

---

## Properties

### Empty and Single-Element Lists

```lean
-- Empty list is sorted
theorem empty_sorted : Sorted [] := by
  simp [Sorted]

-- Single element list is sorted
theorem single_sorted (x : Nat) : Sorted [x] := by
  simp [Sorted]
```

Here I began proving basic properties about sorted lists. First, I showed that an empty list is always sorted, which follows immediately from the definition since `Sorted []` reduces to `True`. Similarly, I proved that a single-element list is sorted for any natural number, which again holds trivially.

```lean
-- Two element sorted property
theorem two_sorted (a b : Nat) : Sorted [a, b] ↔ a ≤ b := by
 simp [Sorted]
```

Next, I looked at the two-element case. The theorem `two_sorted` shows that a list with two elements is sorted if and only if the first element is less than or equal to the second. This is the simplest non-trivial check of order in a list.

```lean
-- If a list is sorted, then its tail is also sorted
theorem sorted_tail {a : Nat} {l : List Nat} (h : Sorted (a :: l)) : Sorted l := by
  match l with
  | [] => simp [Sorted]
  | b :: rest =>
    simp [Sorted] at h
    exact h.2
```

I then moved on to the relationship between a list and its tail. The theorem `sorted_tail` says that if a non-empty list is sorted, then the tail of the list must also be sorted. The proof works by pattern matching on the tail. If the tail is empty, the result is trivial. If the tail has at least one element, the sortedness condition of the larger list splits into two parts: `a ≤ b` and `Sorted (b :: rest)`. From this, the second part directly gives the sortedness of the tail.

```lean
-- Sorted lists have a specific structure
theorem sorted_cons {a b : Nat} {l : List Nat} :
  Sorted (a :: b :: l) ↔ (a ≤ b ∧ Sorted (b :: l)) := by
  simp [Sorted]
```
Another structural result is given in `sorted_cons`. This theorem expresses sortedness of a list with at least two elements in a clean equivalence form: `Sorted (a :: b :: l)` is the same as saying `a ≤ b` and `Sorted (b :: l)`. This matches our intuition: a list is sorted if the first two elements are in the right order and the rest of the list is sorted.

```lean
-- A useful lemma: if we have a sorted list starting with two elements,
-- the first is ≤ the second
theorem sorted_head_le {a b : Nat} {l : List Nat} (h : Sorted (a :: b :: l)) : a ≤ b := by
   simp [Sorted] at h
   exact h.1
```

The lemma `sorted_head_le` extracts the inequality from a sorted list with at least two elements. If I know that `Sorted (a :: b :: l)` holds, then it must follow that `a ≤ b`. This will be useful when proving correctness of sorting algorithms, since we will often need to show that the first element is in the right position relative to the next.

```lean
-- length preservation (we'll use this later for sorting algorithms)
theorem sorted_length_eq (l : List Nat) : listLength l = l.length := by
  induction l with
  | nil => simp [listLength]
  | cons head tail ih =>
     simp [listLength, List.length]
     rw [ih]
     rw [Nat.add_comm]
```

I also included a small theorem `sorted_length_eq` about the `listLength` function I defined earlier. It shows that my recursive `listLength` agrees with Lean’s built-in `List.length`. The proof is by induction on the list. In the base case of the empty list, both functions return zero. In the inductive step, the recursive structure ensures the lengths match up, and I use `rw` to rewrite with the induction hypothesis. The final step requires swapping the addition order with `Nat.add_comm`.


