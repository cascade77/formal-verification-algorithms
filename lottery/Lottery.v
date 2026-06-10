From Coq Require Import Arith List Lia.
Import List.
Import ListNotations.
Open Scope nat_scope.

(* data structures *)

Record process : Type :=
  lottery_process
  {
    pid : nat;
    remaining_work : nat;
    tickets : nat
  }.

Definition lottery := list process.

(* sanity checks === *)

Example p1 := lottery_process 0 30 70.
Example p2 := lottery_process 1 40 80.
Example p3 := lottery_process 2 50 90.

Definition lottery1 := [p1; p2; p3].

(* === invariant predicates === *)

Definition unique_pids (l : lottery) :=
  NoDup (map pid l).

Fixpoint sorted_by_pid (l : lottery) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | h :: t =>
      match t with
      | [] => True
      | h' :: _ => pid h <= pid h' /\ sorted_by_pid t
      end
  end.

Definition positive_work (l : lottery) :=
  Forall (fun p => 0 < remaining_work p) l.

Definition positive_tickets (l : lottery) :=
  Forall (fun p => 0 < tickets p) l.

(* helper functions *)

Fixpoint insert_process (p : process) (l : lottery) : lottery :=
  match l with
  | [] => [p]
  | h :: t =>
      if pid p <=? pid h then
        p :: l
      else
        h :: insert_process p t
  end.

Definition job_enters (p : process) (l : lottery) : lottery :=
  insert_process p l.

Fixpoint find_winner (l : lottery) (random_num : nat) (counter : nat) : option process :=
  match l with
  | [] => None
  | h :: t =>
      if Nat.ltb random_num (counter + tickets h) then
        Some h
      else
        find_winner t random_num (counter + tickets h)
  end.

Fixpoint remove_process_by_id (pid_to_remove : nat) (l : lottery) : lottery :=
  match l with
  | [] => []
  | h :: t =>
      if pid h =? pid_to_remove then
        t
      else
        h :: remove_process_by_id pid_to_remove t
  end.

Fixpoint replace_process (new_process : process) (l : lottery) : lottery :=
  match l with
  | [] => []
  | h :: t =>
      if pid h =? pid new_process then
        new_process :: t
      else
        h :: replace_process new_process t
  end.

Definition schedule (l : lottery) (random_num : nat) : lottery :=
  match find_winner l random_num 0 with
  | None => l
  | Some winner =>
      let updated_winner := lottery_process (pid winner) (remaining_work winner - 1) (tickets winner) in
      if remaining_work updated_winner =? 0 then
        remove_process_by_id (pid winner) l
      else
        replace_process updated_winner l
  end.

(* === Sanity Check Examples === *)

Example schedule_test1 : schedule [p1; p2; p3] 100 = 
  [p1; lottery_process 1 39 80; p3].
Proof. reflexivity. Qed.

Example schedule_test2 : schedule [p1; p2; p3] 50 =
  [lottery_process 0 29 70; p2; p3].
Proof. reflexivity. Qed.

Example job_enters_test : job_enters p1 [p2; p3] =
  [p1; p2; p3].
Proof. reflexivity. Qed.

(* === Lemmas === *)

Lemma remove_preserves_positive_tickets : forall l pid_to_remove,
  positive_tickets l ->
  positive_tickets (remove_process_by_id pid_to_remove l).
Proof.
  intros l pid_to_remove H.
  induction l as [| h t IH].
  - simpl. exact H.
  - simpl in H.
    unfold remove_process_by_id. simpl.
    destruct (pid h =? pid_to_remove).
    + exact (Forall_inv_tail H).
    + apply Forall_cons.
      * exact (Forall_inv H).
      * apply IH. exact (Forall_inv_tail H).
Qed.

Lemma replace_preserves_positive_tickets : forall l new_process,
  positive_tickets l ->
  0 < tickets new_process ->
  positive_tickets (replace_process new_process l).
Proof.
  intros l new_process H Htickets.
  induction l as [| h t IH].
  - simpl. exact H.
  - simpl in H.
    unfold replace_process. simpl.
    destruct (pid h =? pid new_process).
    + apply Forall_cons.
      * exact Htickets.
      * exact (Forall_inv_tail H).
    + apply Forall_cons.
      * exact (Forall_inv H).
      * apply IH. exact (Forall_inv_tail H).
Qed.

(* === Theorems === *)

Theorem job_enters_adds : forall p l,
  In p (job_enters p l).
Proof.
  intros p l.
  unfold job_enters.
  induction l as [| h t IH].
  - simpl. left. reflexivity.
  - simpl.
    destruct (pid p <=? pid h).
    + left. reflexivity.
    + right. exact IH.
Qed.

Theorem find_winner_in_list : forall l random_num counter winner,
  find_winner l random_num counter = Some winner ->
  In winner l.
Proof.
  intro l.
  induction l as [| h t IH].
  - intros random_num counter winner H.
    simpl in H. discriminate.
  - intros random_num counter winner H.
    simpl in H.
    destruct (Nat.ltb random_num (counter + tickets h)) eqn:E.
    + injection H. intro. rewrite <- H0. left. reflexivity.
    + right. apply IH with (random_num := random_num) (counter := counter + tickets h).
      exact H.
Qed.

Theorem schedule_no_winner : forall l,
  find_winner l 0 0 = None ->
  schedule l 0 = l.
Proof.
  intros l H.
  unfold schedule.
  rewrite H. reflexivity.
Qed.

Theorem schedule_length : forall l random_num,
  length (schedule l random_num) <= length l.
Proof.
  intros l random_num.
  unfold schedule.
  destruct (find_winner l random_num 0) as [winner |].
  - destruct (remaining_work (lottery_process (pid winner) (remaining_work winner - 1) (tickets winner)) =? 0).
    + induction l as [| h t IH].
      * simpl. lia.
      * simpl. destruct (pid h =? pid winner); simpl; lia.
    + induction l as [| h t IH].
      * simpl. lia.
      * simpl. destruct (pid h =? pid winner); simpl; lia.
  - simpl. lia.
Qed.  



