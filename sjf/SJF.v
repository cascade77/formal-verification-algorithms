From Coq Require Import Arith List Lia.
Import ListNotations.

(* to represent one process
Inductive process : Type :=
  | mk_process : nat -> nat -> process.


(* manually extracting pid  *)
Definition get_pid (p : process) : nat :=
  match p with
  | mk_process id burst => id
  end.   

(* manually extracting burst  *)
Definition get_burst (p : process) : nat :=
  match p with
  | mk_process id burst => burst
  end. *)

(* this is tedious!  *)
(* record automates this *)

Record process : Type :=
 mk_process
 {
    pid  :  nat;
    burst :  nat
 }.


(* a process state tells where a process currently is *)

Inductive state : Type :=
| Ready   (* waiting in the queue *)
| Running (*  currently on the CPU*)
| Done.   (* finished execution*)


(* comparison utils *)

Definition process_eq (p1 p2 : process) : bool :=
match p1, p2 with
| mk_process id1 _, mk_process id2 _ => Nat.eqb id1 id2
end.

Definition shorter (p1 p2 : process) : bool :=
match p1, p2 with
|mk_process _  burst1 , mk_process _  burst2 => Nat.ltb burst1 burst2 
end.

(* sorted_by_burst predicate *)

Inductive sorted_by_burst : list process -> Prop :=
| sorted_nil : sorted_by_burst []
| sorted_one : forall p, sorted_by_burst [p]
| sorted_cons : forall p1 p2 l,
   p1.(burst) <= p2.(burst) ->
   sorted_by_burst (p2 :: l) ->
   sorted_by_burst (p1 :: p2 :: l).

(* schedule *)

Definition schedule := list process.

(* insert by burst (for sjf)  *)

Fixpoint insert_by_burst (p : process) (l : list process) : list process := 
match l with
| [] => [p]
| head  :: rest => if p.(burst) <=? head.(burst) then
                      p :: head :: rest else
                      head :: insert_by_burst p rest
end.                      

(* sanity checks *)

Definition p1 := mk_process 1 5.
Definition p2 := mk_process 2 3.
Definition p3 := mk_process 3 6.
Definition p4 := mk_process 4 1.

Example insert_test1 : insert_by_burst p4 [p1;p3] = [p4; p1; p3].
Proof. reflexivity. Qed.

Example insert_test2 : insert_by_burst p1 [] = [p1].
Proof. reflexivity. Qed.

                    
Fixpoint run_sjf (l : list process) : schedule :=
match l with
| [] => []
| head :: rest => insert_by_burst head (run_sjf rest)
end.

(* sanity checks *)

Example sjf_test1 :run_sjf [p3;p1;p2;p4] = [p4;p2;p1;p3].
Proof. reflexivity. Qed.

Example sjf_test2 : run_sjf [] = [].
Proof. reflexivity. Qed.
  
 (* metrics *)

 Definition turnaround_time (arrival completion : nat) : nat :=
  completion - arrival.

 Definition response_time (arrival first_run : nat) : nat :=
   first_run - arrival.

(* membership: every process in input appears in
    schedule  *)

 Lemma insert_by_burst_In: forall (p q : process) (l : list process),
  In q (p :: l) -> In q (insert_by_burst p l).
Proof.
    intros p q l H. 
    induction l as [| q' l' IHl'].
    -
    unfold insert_by_burst.
    apply H.
    -

    simpl. destruct (p.(burst) <=? q'.(burst) ) eqn:E.
    +
    apply H.
    +
    simpl in H. destruct H as [H | [H | H] ].
    *
    right. apply IHl'. left. apply H.
    *
    left. apply H.
    *
    right. apply IHl'. right. apply H.
Qed.


 Lemma insert_by_burst_In_rev : forall ( p q : process) (l : list process), In q (insert_by_burst p l) -> In q (p :: l).
Proof.
  intros p q l H.
  induction l as [| q' l' IHl'].
  -
simpl in H.
apply H.
-
simpl in H.
destruct (p.(burst) <=? q'.(burst) ) eqn:E.
+
apply H.
+
simpl.
simpl in H.
simpl in IHl'.
destruct H as [HA | HB].
*
right.
left.
apply HA.
*
apply IHl' in HB.
destruct HB as [HC | HD].
--
left.
apply HC.
-- 
right.
right.
apply HD.
Qed.

(* sjf preserves sortedness *)
Lemma insert_by_burst_sorted : forall (p : process) (l : list process), sorted_by_burst l -> sorted_by_burst (insert_by_burst p l).

Proof.
  intros p l H.
  induction H.
  -
  simpl. apply sorted_one.
  -
  simpl. destruct (p.(burst) <=? p0.(burst)) eqn:E. 
  +
  apply sorted_cons.
  * apply Nat.leb_le. apply E.
  * apply sorted_one.
  +
  apply sorted_cons.
  * apply Nat.leb_gt in E. lia.
  * apply sorted_one.
  -
  simpl.
  destruct (p.(burst) <=? p5.(burst)) eqn: E.
  + apply sorted_cons.
  *
  apply Nat.leb_le. apply E.
  *
  apply sorted_cons. apply H. apply H0.
  +
  destruct (p.(burst) <=? p6.(burst)) eqn: E2.
  * apply sorted_cons.
  { apply Nat.leb_gt in E. lia. }
  { apply sorted_cons. apply Nat.leb_le. apply E2. apply H0. }

  * apply sorted_cons.
  { apply H. }
  { simpl in IHsorted_by_burst. rewrite E2 in IHsorted_by_burst. apply IHsorted_by_burst. }

Qed.

(* main theorems *)

Theorem sjf_sorted : forall (l : list process), sorted_by_burst (run_sjf l).

Proof.
  intros l.
  induction  l as [| a l' IHl'].
  -
  simpl. 
  apply sorted_nil.
  -
  simpl.
  apply insert_by_burst_sorted.
  apply IHl'.
Qed.  

 Theorem sjf_no_starvation : forall (p : process) (l : list process),
In p l -> In p (run_sjf l).

Proof.
   intros p l H.
   induction l as [| a l' IHl'].
   -
   simpl in H. destruct H.
   -
   simpl in H. destruct H as [H | H].
   +
   simpl. apply insert_by_burst_In. left. apply H.
   +
   simpl. apply insert_by_burst_In. right. apply IHl'. apply H.
Qed.  

 Theorem sjf_no_starvation_rev : forall (p : process) (l : list process),
  In p (run_sjf l) -> In p l.

  Proof.
    intros p l H.
    induction l as [| a' l' IHl'].
    -
    simpl in H. destruct H.
    -
    simpl. 
    apply insert_by_burst_In_rev in H.
    destruct H as [H | H].
    *
    left.
    apply H.
    *
    right.
    apply IHl'.
    apply H.
  Qed.
  
  
  Fixpoint completion_times (l : list process) (current_time : nat) : list (process * nat) := 
  match l with
  | [] => []
  | head :: rest => (head, current_time + head.(burst)) :: completion_times rest (current_time + head.(burst))
 end. 


Example completion_test1 : completion_times (run_sjf [p1; p2; p3; p4]) 0 = [(p4, 1) ; (p2, 4) ; (p1, 9); (p3, 15)].
Proof. reflexivity. Qed.
  


 Inductive consecutive_completions : list (process * nat) -> Prop :=
 | cc_nil : consecutive_completions []
 | cc_one : forall x, consecutive_completions [x]
 | cc_cons : forall p c p' c' rest,
    c <= c' ->
    consecutive_completions ((p' , c') :: rest) ->
    consecutive_completions ((p, c) :: (p', c') :: rest).

 Theorem completion_times_decreasing : forall l t,
 sorted_by_burst l ->
 consecutive_completions (completion_times l t).    
 intros l t H.
 revert t.
 induction H. 
 -
 intros t. simpl. apply cc_nil.
 -
 intros t. simpl. apply cc_one.
 -
 intros t. simpl.
 apply cc_cons.
 +
 lia.
 +
 apply IHsorted_by_burst.
Qed. 


  





  
   
   












   



   



