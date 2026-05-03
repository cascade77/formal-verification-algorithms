From Coq Require Import Arith List.
Import ListNotations.
From Coq Require Import Lia.

(* sorted predicate *)

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_one : forall x, sorted [x]
  | sorted_cons : forall x y l,
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

(* insert and isort *)

Fixpoint insert (a : nat) (l : list nat) : list nat :=
match l  with
| [] => [a]
| x :: rest => if a <=? x then
                a :: x :: rest else
                 x  :: insert  a rest
end.  

(* sanity checks *)
Example insert_test1 : insert 2 [1;3;5] = [1;2;3;5].
Proof. reflexivity. Qed.


Example insert_test2 : insert 0 [1;2;3] = [0;1;2;3].
Proof. reflexivity. Qed.
    
    
Fixpoint isort (l : list nat) : list nat :=
match l with
|[] => []
| x :: rest => insert x (isort rest )
end.


(* sanity checks *)
Example isort_test1 : isort [2;7;5] = [2;5;7].
Proof. reflexivity. Qed.

Example isort_test2 : isort [4;1;3;2] = [1;2;3;4].
Proof. reflexivity. Qed.    


 (* lemmas  *)
 
 Lemma insert_In : forall (a x : nat) (l : list nat),
 In x (a :: l) -> In x (insert a l).
 Proof.
    intros a x l H.
    induction l as [| x' l' IHl'].
    -
    unfold insert.
    apply H.
    -
    simpl. destruct (a <=? x') eqn:E.
    + apply H.
    + simpl in H. destruct H as [H | [H | H]].
    * right. apply IHl'. left.
    apply H.
    * left. apply H.
    * right. apply IHl'. right. apply H.
 Qed.   




 Lemma insert_In_rev : forall (a x : nat) (l : list nat),
  In x (insert a l) -> In x (a :: l).
Proof. 

    intros a  x l H.
    induction l as [| x' l' IHl'].
    -
    simpl in H.
    apply H.
    -
    simpl in H.
    destruct (a <=? x') eqn:E.
    +
    apply H.
    +
    simpl.
    simpl in H.
    simpl in IHl'.
    (* rewrite IHl' in H. *)
    destruct H as [HA | HB].
    *
    right.
    left.
    apply HA.
    *
    apply  IHl' in HB.
    destruct HB as [HC | HD].
    --
    left.
    apply HC.
    --right.
    right.
    apply HD.
Qed.  
    
  
Search ((_ <=? _) = false).



Lemma insert_sorted : forall (a : nat) (l : list nat),
  sorted l -> sorted (insert a l).
Proof.
  intros a l H.
  induction H.
  -
  simpl. apply sorted_one.
  - simpl. destruct (a <=? x) eqn: E.
   +
   apply sorted_cons.   
   * apply leb_complete. apply E.
   * apply sorted_one.
   +
   apply sorted_cons.
   * apply leb_complete_conv in E. lia. 
   * apply sorted_one.
   - simpl. destruct (a <=? x) eqn: E.
   +
   apply sorted_cons. 
   * apply leb_complete. apply E.
   * apply sorted_cons. 
   -- apply H. 
   -- apply H0.
  +   destruct (a <=? y) eqn: E1.
   *
   apply sorted_cons.
   --
   apply leb_complete_conv in E.
   lia.
   --
   apply sorted_cons.
   { apply leb_complete. apply E1.
   }
   apply H0.
   *
   apply sorted_cons.
   --
   apply leb_complete_conv in E.
   lia.
   --
   simpl in IHsorted. rewrite E1 in IHsorted. apply IHsorted.

Qed.  



(* main theorems *)

Theorem isort_sorted : forall (l : list nat),
  sorted (isort l).
Proof. 
  intros l.
  induction l as [ | a' l' IHl'].
  -
  simpl. apply sorted_nil.
  -
  simpl.
  apply insert_sorted.
  apply IHl'.

Qed.



Theorem isort_In : forall (x : nat) (l : list nat),
  In x l <-> In x (isort l).
Proof. 
  intros x l.
  split.
  -
  intros H.
  induction l as [| a l' IHl'].
  +
  simpl in H. destruct H.
  +
  simpl in H. destruct H as [H | H].
    *
    simpl. apply insert_In. left. apply H.
    *
    simpl. apply insert_In. right.
    apply IHl'. apply H.
    -
    intros H.
    induction l as [| a l' IHl'].
   +
    simpl.
    destruct H.
    +
    apply insert_In_rev in H.
    destruct H as [H | H].
    *
    left.
    apply H.
    *
    right.
    apply IHl'.
    apply H.
Qed.   


     
  
  