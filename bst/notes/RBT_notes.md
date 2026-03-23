# red-black trees

notes for formalizing red-black trees in rocq.
the formalization is in `RBT.v` and builds on top of `BST.v`.

reference: [sedgewick & wayne, algorithms 4th edition, section 3.3](https://algs4.cs.princeton.edu/33balanced/)

---

## why do we even need this

a plain bst can become a linked list if you insert keys in sorted order.
so searching takes o(n) worst case instead of o(log n). that's bad.

red-black trees fix this by keeping the tree balanced at all times,
guaranteeing o(log n) for search and insert no matter what.

---

## 2-3 trees first

before understanding rbts you need to understand 2-3 trees.

a normal bst node holds 1 key and has 2 children. a 2-3 tree relaxes this:

- **2-node**: 1 key, 2 children — exactly like a normal bst node
- **3-node**: 2 keys, 3 children

for a 3-node with keys `a` and `b` where `a < b`:
- left child: keys smaller than `a`
- middle child: keys between `a` and `b`
- right child: keys greater than `b`

the key thing about 2-3 trees: **all null links are at the same depth from the root**.
that's perfect balance. no path from root to bottom is longer than any other.

---

## how 2-3 trees become red-black trees

directly implementing 2-3 trees is annoying because you have to handle 2-nodes and
3-nodes as separate cases everywhere. red-black trees are a cleaner encoding.

the idea: represent a 3-node as two 2-nodes connected by a **red link**.
black links are the normal bst skeleton. red links mark the joined together nodes.

```
2-3 tree:           red-black bst:

  [E  J]                  J
  / | \                  / \
 A  H  L               E   L     (E--J is a red link leaning left)
                       / \
                      A   H
```

rule: smaller key of the 3-node becomes the red left child. larger key becomes the parent.
left and middle children of the 3-node attach to the red node, right child attaches to the parent.

---

## the three invariants

a valid rbt satisfies all three of these at the same time:

**1. no two consecutive red links**
if a node is red, neither of its children can be red.
red links only lean left in a left-leaning rbt.

**2. perfect black balance**
every path from root to a null link passes through the same number of black links.
this is what keeps the height at most 2 log n.

**3. bst ordering**
every key in the left subtree is smaller. every key in the right subtree is larger.
holds recursively throughout the whole tree.

---

## tree structure

each node carries:

```
RNode : color -> nat -> rbtree -> rbtree -> rbtree
         |        |       |           |
       color     key    left        right
```

the color is the color of the link **from the parent to this node**, not the node itself.
`RLeaf` is always black by convention. null links are always black.

---

## the three fix operations

when inserting we always color the new node red. this can temporarily break invariant 1
or create a right-leaning red link. we fix these with three operations applied on the
way back up to the root after insertion.

---

### left rotation

**when to use:** right child is red, left child is black.
this happens when you insert a key larger than the current node so it lands as a right child with a red link. right-leaning red links are illegal in a left-leaning rbt.

**the situation:**

```
  E (some color)
 / \
<E   S (red)
    / \
   M   Z
```

**after rotating:**

```
    S (takes E's color)
   / \
  E   Z
(red)
 / \
<E   M
```

**what moved:**
- s came up to take e's place
- e moved down to become s's left child, colored red
- m switched from being s's left child to being e's right child
- z stayed attached to s, never moved
- <e stayed attached to e, never moved

**the code:**

```rocq
Definition rotate_left (t : rbtree) : rbtree :=
  match t with
  | RNode h_color h_key x (RNode _ s_key m z) =>
      RNode h_color s_key (RNode Red h_key x m) z
  | _ => t
  end.
```

mapping every variable to the diagram:
- `h_color` — e's color (whatever it was, black usually)
- `h_key` — e's key
- `x` — the left subtree of e, which is `<e` in the diagram
- `_` — s's color, ignored because we are replacing it
- `s_key` — s's key
- `m` — s's left subtree, the stuff between e and s
- `z` — s's right subtree, the stuff greater than s

the result `RNode h_color s_key (RNode Red h_key x m) z` builds:
- s as the new root taking e's old color
- e as the left child colored red, keeping `x` on its left and taking `m` on its right
- z unchanged as s's right child

---

### right rotation

**when to use:** left child is red AND left child's left child is also red (two consecutive reds going left). this is a temporary 4-node in 2-3 tree terms.

**the situation:**

```
    S (some color)
   / \
  E   Z
(red)
 / \
A   M
(red)
```

**after rotating:**

```
    E (takes S's color)
   / \
  A   S (red)
(red) / \
     M   Z
```

**what moved:**
- e came up to take s's place, taking s's old color
- s moved down to become e's right child, colored red
- m switched from being e's right child to being s's left child
- a stayed attached to e, never moved
- z stayed attached to s, never moved

now we have a black node e with two red children a and s — exactly the setup for a color flip.

**the code:**

```rocq
Definition rotate_right (t : rbtree) : rbtree :=
  match t with
  | RNode h_color h_key (RNode _ e_key a m) z =>
      RNode h_color e_key a (RNode Red h_key m z)
  | _ => t
  end.
```

mapping every variable to the diagram:
- `h_color` — s's color, black usually
- `h_key` — s's key
- `_` — e's color, red, but ignored because we replace it
- `e_key` — e's key
- `a` — e's left subtree, which is a in the diagram (also red)
- `m` — e's right subtree, stuff between e and s
- `z` — s's right subtree

the result `RNode h_color e_key a (RNode Red h_key m z)` builds:
- e as the new root taking s's old color
- a unchanged as e's left child
- s as e's right child colored red, taking m on its left and z on its right

the only difference between rotate_left and rotate_right is which side the red child is on. in rotate_left the pattern matched the right child `(RNode _ s_key m z)`. in rotate_right the pattern matches the left child `(RNode _ e_key a m)`. everything else is the mirror image.

---

### color flip

**when to use:** both children are red. this is a 4-node in 2-3 tree terms that needs to be split. we push the middle key up to the parent.

**the situation:**

```
      E (black)
     / \
    A   S
  (red)(red)
  / \ / \
 ll lr rl rr
```

**after flipping:**

```
      E (red)
     / \
    A   S
 (black)(black)
  / \ / \
 ll lr rl rr
```

**what moved:** nothing. not a single subtree changes position. only the three colors change. e flips from black to red. a flips from red to black. s flips from red to black.

**the code:**

```rocq
Definition flip_colors (t : rbtree) : rbtree :=
  match t with
  | RNode _ k (RNode _ lk ll lr) (RNode _ rk rl rr) =>
      RNode Red k
        (RNode Black lk ll lr)
        (RNode Black rk rl rr)
  | _ => t
  end.
```

mapping every variable to the diagram:
- `_` — e's color, ignored because we replace it
- `k` — e's key
- first `_` — a's color, red, ignored because we replace it
- `lk` — a's key
- `ll` — a's left subtree
- `lr` — a's right subtree
- second `_` — s's color, red, ignored because we replace it
- `rk` — s's key
- `rl` — s's left subtree
- `rr` — s's right subtree

the result builds:
- `RNode Red k` — e becomes red
- `(RNode Black lk ll lr)` — a becomes black, ll and lr never moved
- `(RNode Black rk rl rr)` — s becomes black, rl and rr never moved

---

## fix_up

fix_up applies all three operations in the correct order at a single node.
it is called at every node on the way back up after insertion.

the order is always:
1. right child red and left child black → left rotate
2. left child red and left-left also red → right rotate  
3. both children red → color flip

```rocq
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
```

**check 1:** `is_red r && negb (is_red l)` — is right child red and left child not red? if yes, left rotate. result stored in t1.

**check 2:** peek inside l1 to get its left child ll. `is_red l1 && is_red ll` — is left child red and left-left also red? if yes, right rotate t1. result stored in t2. we need the inner match on l1 just to get access to ll.

**check 3:** `is_red l2 && is_red r2` — are both children red? if yes, color flip t2.

you might apply one, two, or all three at a single node depending on the situation.

---

## insert algorithm

**rbt_insert_aux** does the recursive insert and calls fix_up on the way back up:

```rocq
Fixpoint rbt_insert_aux (k : nat) (t : rbtree) : rbtree :=
  match t with
  | RLeaf => RNode Red k RLeaf RLeaf
  | RNode c x l r =>
      let t' := if k =? x then RNode c x l r
                else if k <? x then RNode c x (rbt_insert_aux k l) r
                else RNode c x l (rbt_insert_aux k r) in
      fix_up t'
  end.
```

- `RLeaf` case: hit an empty spot, place the new node here colored **red**. always red because in 2-3 tree terms we always start by stuffing the new key into an existing node.
- `RNode` case: exactly like bst insert — go left if smaller, go right if larger, do nothing if equal. but after inserting recursively, call `fix_up t'` on the way back up. this is the key difference from plain bst insert. every node on the path back to the root gets checked and fixed.

**rbt_insert** wraps it and forces the root to black:

```rocq
Definition rbt_insert (k : nat) (t : rbtree) : rbtree :=
  match rbt_insert_aux k t with
  | RLeaf          => RLeaf
  | RNode _ x l r  => RNode Black x l r
  end.
```

the `_` ignores whatever color the root ended up with after all the fix_ups and just sets it to black. root is always black.

---

## full insert example: insert S, E, A

**insert S.** empty tree, s becomes root, forced black.
```
S (black)
```

**insert E.** e < s, goes left with red link. check at s: no violations.
```
  S (black)
 /
E (red)
```

**insert A.** a < e, goes left of e with red link.
```
  S (black)
 /
E (red)
 /
A (red)   <-- two consecutive reds!
```

fix_up at e: right child red? no. left child red and left-left red? a is red but a has no children. both children red? no. nothing at e.

fix_up at s: right child red? no. left child e is red and e's left child a is also red? **yes** → right rotate at s.

```
  E (black, took S's color)
 / \
A   S
(red)(red)
```

fix_up continues at e: both children red? **yes** → color flip.

```
  E (red)
 / \
A   S
(black)(black)
```

e is root → force black.

```
  E (black)
 / \
A   S
```

_phew!_ clean balanced rbt encoding the 2-3 tree with e as root 2-node and a, s as children.

---
