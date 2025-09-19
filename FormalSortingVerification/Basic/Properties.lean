import FormalSortingVerification.Basic.Definitions

#check Sorted
#check sorted

#check listLength


-- Basic properties of sorted Lists

-- Empty list is sorted

theorem empty_sorted : Sorted [] := by
  simp [Sorted]

-- Single element list is sorted

theorem single_sorted (x : Nat) : Sorted [x] := by
  simp [Sorted]

-- Two element sorted property

theorem two_sorted (a b : Nat) : Sorted [a, b] ↔ a ≤ b := by
 simp [Sorted]

-- If a list is sorted, then its tail is also sorted
theorem sorted_tail {a : Nat} {l : List Nat} (h : Sorted (a :: l)) : Sorted l := by
  match l with
  | [] => simp [Sorted]
  | b :: rest =>
    simp [Sorted] at h
    exact h.2

-- Sorted lists have a specific structure
theorem sorted_cons {a b : Nat} {l : List Nat} :
  Sorted (a :: b :: l) ↔ (a ≤ b ∧ Sorted (b :: l)) := by
  simp [Sorted]

-- A useful lemma: if we have a sorted list starting with two elements,
-- the first is ≤ the second

theorem sorted_head_le {a b : Nat} {l : List Nat} (h : Sorted (a :: b :: l)) : a ≤ b := by
   simp [Sorted] at h
   exact h.1

-- -- length preservation (we'll use this later for sorting algorithms)

theorem sorted_length_eq (l : List Nat) : listLength l = l.length := by
  induction l with
  | nil => simp [listLength]
  | cons head tail ih =>
     simp [listLength, List.length]
     rw [ih]
     rw [Nat.add_comm]


-- Testing

#check empty_sorted
#check single_sorted 5
#check two_sorted 3 7
#check sorted_cons

-- Some concrete proofs
example : Sorted [1, 2, 3] := by
  simp [Sorted]
