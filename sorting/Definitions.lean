def listLength (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | _ :: tail => 1 + listLength tail  -- Use _ instead of head since we don't use it

#eval listLength [1,2,3]

def sorted (l : List Nat) : Bool :=
 match l with
 | [] => true
 | [_] => true  -- Use _ instead of single since we don't use it
 | first :: second :: rest => (first ≤ second) && (sorted (second :: rest))

#eval sorted [1,2,3]
#eval sorted [3,1,2]
#eval sorted []
#eval sorted [2,1,3]
#eval sorted [1,3,2,4]
#eval sorted [1,2,2,2,3]
-- Remove the negative number line for now

-- for integers (includes negatives)
def sortedInt (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true  -- Use _ instead of single since we don't use it
  | first :: second :: rest => (first ≤ second) && (sortedInt (second :: rest))

#eval sortedInt [-1, 0, 1]
#eval sortedInt [-5, -2, 3]

-- defining sorted as a Proposition (for mathematical proofs)
def Sorted (l : List Nat) : Prop :=
   match l with
   | [] => True
   | [_] => True  -- Use _ instead of single since we don't use it
   | first :: second :: rest => first ≤ second ∧ Sorted (second :: rest)

-- Remove the #eval line for Sorted since it's a Prop, not a Bool
#check Sorted [1,2,3]
#check Sorted []
#check Sorted [5]
#reduce Sorted []
