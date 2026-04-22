Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Arith.

(* sorted is a Prop, not a Bool function. one needs to build a proof of it, not just evaluate it. *)
Inductive sorted : list nat -> Prop :=
  | sorted_nil  : sorted []
  | sorted_one  : forall x, sorted [x]
  | sorted_cons : forall x y rest,
      x <= y ->
      sorted (y :: rest) ->
      sorted (x :: y :: rest).

Fixpoint count (x : nat) (l : list nat) : nat :=
  match l with
  | []         => 0
  | h :: rest  => if Nat.eqb h x
                  then 1 + count x rest
                  else count x rest
  end.

Example count_test1 : count 3 [1;3;2;3] = 2.
Proof. reflexivity. Qed.

Example count_test2 : count 5 [1;2;3] = 0.
Proof. reflexivity. Qed.

(* nested fixpoint because rocq needs one argument visibly shrinking per recursive function.
   outer merge shrinks l1, inner merge_aux shrinks l2. *)
Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1 with
  | []          => l2
  | h1 :: rest1 =>
      let fix merge_aux (l2 : list nat) : list nat :=
        match l2 with
        | []          => l1
        | h2 :: rest2 =>
            if Nat.leb h1 h2
            then h1 :: merge rest1 (h2 :: rest2)
            else h2 :: merge_aux rest2
        end
      in merge_aux l2
  end.

Example merge_test1 : merge [1;3;5] [2;4] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example merge_test2 : merge [] [1;2;3] = [1;2;3].
Proof. reflexivity. Qed.

Example merge_test3 : merge [1;2;3] [] = [1;2;3].
Proof. reflexivity. Qed.

(* alternating split: [1;2;3;4;5] -> ([1;3;5], [2;4]). * in return type is pair, not multiply. *)
Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | []             => ([], [])
  | [x]            => ([x], [])
  | x :: y :: rest =>
      let (l1, l2) := split rest in
      (x :: l1, y :: l2)
  end.

Example split_test1 : split [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example split_test2 : split [1;2;3;4] = ([1;3], [2;4]).
Proof. reflexivity. Qed.

Example split_test3 : split [] = ([], []).
Proof. reflexivity. Qed.

(* fuel argument n because split halves are not syntactic subterms of l,
   so rocq cannot confirm termination without it. start n = length l. *)
Fixpoint mergesort_aux (n : nat) (l : list nat) : list nat :=
  match n, l with
  | 0,    _        => l
  | _,    []       => []
  | _,    [x]      => [x]
  | S n', _        =>
      let (l1, l2) := split l in
      merge (mergesort_aux n' l1) (mergesort_aux n' l2)
  end.

Definition mergesort (l : list nat) : list nat :=
  mergesort_aux (length l) l.

Example mergesort_test1 : mergesort [5;3;8;1;4] = [1;3;4;5;8].
Proof. reflexivity. Qed.

Example mergesort_test2 : mergesort [] = [].
Proof. reflexivity. Qed.

Example mergesort_test3 : mergesort [1] = [1].
Proof. reflexivity. Qed.

Example mergesort_test4 : mergesort [3;3;1;1] = [1;1;3;3].
Proof. reflexivity. Qed.


(* ==========================*)
(*                            lemmas                                     *)
(*                                   =================================== *)

(* merge's nested let fix resists simpl. these give explicit rewrite rules for each branch. *)
Lemma merge_l_le : forall h1 h2 rest1 rest2,
  Nat.leb h1 h2 = true ->
  merge (h1 :: rest1) (h2 :: rest2) = h1 :: merge rest1 (h2 :: rest2).
Proof.
  intros h1 h2 rest1 rest2 H.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma merge_r_lt : forall h1 h2 rest1 rest2,
  Nat.leb h1 h2 = false ->
  merge (h1 :: rest1) (h2 :: rest2) = h2 :: merge (h1 :: rest1) rest2.
Proof.
  intros h1 h2 rest1 rest2 H.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(* inversion on sorted_cons gives both pieces. rocq won't let you pull them out directly. *)
Lemma sorted_cons_inv : forall x y l,
  sorted (x :: y :: l) -> x <= y /\ sorted (y :: l).
Proof.
  intros x y l H.
  inversion H.
  split; assumption.
Qed.

Lemma sorted_cons_inv' : forall x l,
  sorted (x :: l) -> sorted l.
Proof.
  intros x l H.
  inversion H.
  - apply sorted_nil.
  - assumption.
Qed.

(* Nat.leb is Bool, <= is Prop. same meaning, different worlds. *)
Lemma le_of_leb : forall a b,
  Nat.leb a b = true -> a <= b.
Proof.
  intros a b H.
  apply Compare_dec.leb_complete.
  assumption.
Qed.

(* factored out of merge_sorted so each case there reduces to two clean subgoals. *)
Lemma merge_sorted_cons : forall h l1 l2,
  h <= hd h (merge l1 l2) ->
  sorted (merge l1 l2) ->
  sorted (h :: merge l1 l2).
Proof.
  intros h l1 l2 Hle Hsorted.
  destruct (merge l1 l2) eqn:Heq.
  - apply sorted_one.
  - apply sorted_cons; assumption.
Qed.

Lemma sorted_head_le : forall h rest x,
  sorted (h :: rest) -> In x rest -> h <= x.
Proof.
  intros h rest.
  induction rest as [| a rest' IH].
  - intros x _ Hin.
    inversion Hin.
  - intros x Hs Hin.
    apply sorted_cons_inv in Hs.
    destruct Hs as [Hle Hs].
    simpl in Hin.
    destruct Hin as [-> | Hin].
    + assumption.
    + apply IH.
      * destruct rest' as [| b rest''].
        { inversion Hin. }
        { apply sorted_cons_inv in Hs.
          destruct Hs as [Hle2 Hs2].
          apply sorted_cons.
          lia.
          assumption. }
      * assumption.
Qed.

(* used in merge_sorted to trace where the head of a merged result came from. *)
Lemma merge_In : forall x l1 l2,
  In x (merge l1 l2) -> In x l1 \/ In x l2.
Proof.
  intros x l1.
  induction l1 as [| h1 rest1 IH1].
  - simpl.
    intros l2 H.
    right. assumption.
  - induction l2 as [| h2 rest2 IH2].
    + simpl.
      intros H.
      left. assumption.
    + destruct (Nat.leb h1 h2) eqn:Heq.
      * rewrite merge_l_le by assumption.
        intros H.
        simpl in H.
        destruct H as [-> | H].
        { left. simpl. left. reflexivity. }
        { apply IH1 in H.
          destruct H as [H | H].
          - left. simpl. right. assumption.
          - right. assumption. }
      * rewrite merge_r_lt by assumption.
        intros H.
        simpl in H.
        destruct H as [-> | H].
        { right. simpl. left. reflexivity. }
        { apply IH2 in H.
          destruct H as [H | H].
          - left. assumption.
          - right. simpl. right. assumption. }
Qed.


(* ============================ *)
(*                         main theorem                                  *)
(*                                      ================================ *)

Theorem merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  intros l1.
  induction l1 as [| h1 rest1 IH1].
  - intros l2 H1 H2.
    simpl.
    assumption.
  - intros l2 H1 H2.
    induction l2 as [| h2 rest2 IH2].
    + simpl.
      assumption.
    + destruct (Nat.leb h1 h2) eqn:Heq.
      * rewrite merge_l_le by assumption.
        apply merge_sorted_cons.
        { destruct (merge rest1 (h2 :: rest2)) eqn:Hm.
          - simpl. lia.
          - simpl.
            assert (Hin : In n (merge rest1 (h2 :: rest2))).
            { rewrite Hm. simpl. left. reflexivity. }
            apply merge_In in Hin.
            destruct Hin as [Hin | Hin].
            + apply sorted_head_le with (rest := rest1).
              * assumption.
              * assumption.
            + simpl in Hin.
              destruct Hin as [-> | Hin].
              * apply Compare_dec.leb_complete. assumption.
              * assert (H := sorted_head_le h2 rest2 n H2 Hin).
                apply Compare_dec.leb_complete in Heq.
                lia. }
        { apply IH1.
          - apply sorted_cons_inv' with (x := h1). assumption.
          - assumption. }
      * rewrite merge_r_lt by assumption.
        apply merge_sorted_cons.
        { destruct (merge (h1 :: rest1) rest2) eqn:Hm.
          - simpl. lia.
          - simpl.
            assert (Hin : In n (merge (h1 :: rest1) rest2)).
            { rewrite Hm. simpl. left. reflexivity. }
            apply merge_In in Hin.
            destruct Hin as [Hin | Hin].
            + simpl in Hin.
              destruct Hin as [-> | Hin].
              * apply Nat.leb_gt in Heq. lia.
              * assert (H := sorted_head_le h1 rest1 n H1 Hin).
                apply Nat.leb_gt in Heq.
                lia.
            + apply sorted_head_le with (rest := rest2).
              assumption.
              assumption. }
        { apply IH2.
          apply sorted_cons_inv' with (x := h2). assumption. }
Qed.