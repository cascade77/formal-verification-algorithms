Require Import Arith.
Require Import Bool.
Require Import Lia.

From RBT Require Import BST.


(* ===================================================
   color and tree type
   =================================================== *)

(* color of the link from parent to this node *)
Inductive color : Type :=
  | Red   : color
  | Black : color.

(* rbt node carries a color, a key, left and right subtrees *)
Inductive rbtree : Type :=
  | RLeaf : rbtree
  | RNode : color -> nat -> rbtree -> rbtree -> rbtree.

Example rbtree_example : rbtree :=
  RNode Red 4 RLeaf RLeaf.


(* ===================================================
   helper
   =================================================== *)

(* returns true if the node has a red link from its parent *)
Definition is_red (t : rbtree) : bool :=
  match t with
  | RNode Red _ _ _ => true
  | _               => false
  end.


(* ===================================================
   invariants
   =================================================== *)

(* if a node is red, neither of its children can be red *)
Fixpoint no_red_red (t : rbtree) : Prop :=
  match t with
  | RLeaf          => True
  | RNode c _ l r  =>
      (c = Red -> is_red l = false /\ is_red r = false) /\
      no_red_red l /\
      no_red_red r
  end.

(* black counts as 1, red counts as 0 *)
Definition color_black (c : color) : nat :=
  match c with
  | Black => 1
  | Red   => 0
  end.

(* counts black links going left all the way down *)
Fixpoint black_height (t : rbtree) : nat :=
  match t with
  | RLeaf          => 0
  | RNode c _ l _  => color_black c + black_height l
  end.

(* every path from root to null must have equal black height *)
Fixpoint black_balanced (t : rbtree) : Prop :=
  match t with
  | RLeaf          => True
  | RNode _ _ l r  =>
      black_height l = black_height r /\
      black_balanced l /\
      black_balanced r
  end.

(* checks that all keys in a subtree satisfy predicate p *)
Fixpoint all_keys_rbt (P : nat -> Prop) (t : rbtree) : Prop :=
  match t with
  | RLeaf          => True
  | RNode _ k l r  => P k /\ all_keys_rbt P l /\ all_keys_rbt P r
  end.

(* bst ordering invariant for rbtrees *)
Inductive bst_rbt : rbtree -> Prop :=
  | BST_RLeaf : bst_rbt RLeaf
  | BST_RNode : forall c k l r,
      all_keys_rbt (fun x => x < k) l ->
      all_keys_rbt (fun x => x > k) r ->
      bst_rbt l ->
      bst_rbt r ->
      bst_rbt (RNode c k l r).


(* ===================================================
   fix operations
   =================================================== *)

(* fixes a right leaning red link by rotating left *)
Definition rotate_left (t : rbtree) : rbtree :=
  match t with
  | RNode h_color h_key x (RNode _ s_key m z) =>
      RNode h_color s_key (RNode Red h_key x m) z
  | _ => t
  end.

(* fixes two consecutive left red links by rotating right *)
Definition rotate_right (t : rbtree) : rbtree :=
  match t with
  | RNode h_color h_key (RNode _ e_key a m) z =>
      RNode h_color e_key a (RNode Red h_key m z)
  | _ => t
  end.

(* splits a 4-node by flipping colors, pushing middle key up *)
Definition flip_colors (t : rbtree) : rbtree :=
  match t with
  | RNode _ k (RNode _ lk ll lr) (RNode _ rk rl rr) =>
      RNode Red k
        (RNode Black lk ll lr)
        (RNode Black rk rl rr)
  | _ => t
  end.


(* ===================================================
   fix up
   =================================================== *)

(* applies all three fix operations in order at a single node *)
Definition fix_up (t : rbtree) : rbtree :=
  match t with
  | RLeaf => RLeaf
  | RNode c k l r =>
      let t1 := if is_red r && negb (is_red l)
                then rotate_left t
                else t in
      match t1 with
      | RLeaf => RLeaf
      | RNode c1 k1 l1 r1 =>
          let t2 := match l1 with
                    | RNode _ _ ll _ =>
                        if is_red l1 && is_red ll
                        then rotate_right t1
                        else t1
                    | RLeaf => t1
                    end in
          match t2 with
          | RLeaf => RLeaf
          | RNode c2 k2 l2 r2 =>
              if is_red l2 && is_red r2
              then flip_colors t2
              else t2
          end
      end
  end.


(* ===================================================
   insert
   =================================================== *)

(* inserts like bst but applies fix_up on the way back up *)
Fixpoint rbt_insert_aux (k : nat) (t : rbtree) : rbtree :=
  match t with
  | RLeaf => RNode Red k RLeaf RLeaf
  | RNode c x l r =>
      let t' := if k =? x then RNode c x l r
                else if k <? x then RNode c x (rbt_insert_aux k l) r
                else RNode c x l (rbt_insert_aux k r) in
      fix_up t'
  end.

(* forces root to black after insertion *)
Definition rbt_insert (k : nat) (t : rbtree) : rbtree :=
  match rbt_insert_aux k t with
  | RLeaf          => RLeaf
  | RNode _ x l r  => RNode Black x l r
  end.

