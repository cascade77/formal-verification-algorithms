Require Import Nat.
Require Import Arith.
Require Import Lia.

(* block decomposition distributes n indices across p processes.
  process i owns indices from block_low to block_high inclusive. *)

Definition block_low (i p n : nat) : nat :=
  (i * n) / p.

Definition block_high (i p n : nat) : nat :=
  ((i + 1) * n) / p - 1.

(* the first process always starts at index 0. *)

Lemma block_low_zero : forall p n : nat,
  block_low 0 p n = 0.
Proof.
  intros p n.
  unfold block_low.
  simpl.
  (* Search (0 / _ = 0). found: Nat.Div0.div_0_l *)
  apply Nat.Div0.div_0_l.
Qed.

(* every process starts exactly one index after the previous process ends. *)

Lemma block_adjacent2 : forall i p n : nat,
 p <> 0 -> p <=n -> 
 block_low (i + 1) p n = block_high i p n + 1.

Proof.
    intros i p n Hp Hn.
    unfold block_low, block_high.
    (* Search (_ - _ + _ = _). found: Nat.sub_add *)
  (* Search (Nat.div_str_pos). found the precondition shape i needed *)
    assert (H : 1 <= (i + 1) * n / p).
    { apply Nat.div_str_pos.
    lia.
    }    
    lia.
Qed.