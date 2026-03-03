Require Import Arith.
Require Import Bool.
Require Import Lia.

(* I'll start by defining tree type and for that i need to use inductive so that i can list all the ways for contructing a value of that type*)

Inductive tree : Type :=
  | Leaf : tree
  | Node : nat -> tree -> tree -> tree.

(* Leaf : tree because leaf is the child of the tree having no further children, so when we write leaf here, we get a tree, specifically the empty tree*)

(* Node : nat -> tree -> tree -> tree *)
(* reading from right to left, we know one thing that last tree written here is what node produces while all other trees are being passed as inputs *)
(* so what that means that Node takes three inputs and produces a tree:
- a nat : the key stored at this node
- a tree the left subtree
- a tree the right subtree *)


Example example_tree : tree :=
  Node 4 (Node 2 Leaf Leaf) (Node 6 Leaf Leaf).

(* Now here notice each node has three inputs nat Leaf Leaf because node always requires three arguments so, the shape of the tree is as follows:
                  4
                 / \
                2   6
               / \ / \
              ∅  ∅ ∅  ∅
                  *)
(* one more interesting thing this example
Node 4 (Node 2 Leaf Leaf) (Node 6 Leaf Leaf) 
4 is the nat while Node 2 and Node 6 are children, and those children can have children too, for now we wrote them as empty hence wrote Leaf but did give value of the nat key!*)


(* so we defined the shape of a tree, but goal is to make BST, and rule is already known which is key of left subtree should be smaller than the current node key while right subtree key should be larger than the current node.  *)

(* so, for this we do need a way to tell that every key in this tree satisfies some condition *)


Fixpoint all_keys (P : nat -> Prop) (t : tree) : Prop :=

match t with
| Leaf => True
| Node k l r => P k /\ all_keys P l /\ all_keys P r 
end.


(* Fixpoint means it's a recursive function, it takes two inputs: a predicate P (takes a  number nat and returns Prop (gives statement about it)) and a tree t, it returns a Prop (a statement that can be either true / False ) *)

(* Case 1 : the tree is leaf, an empty tree has no keys, so vacuosly all zero of its keys satisfy P, so return True *)
(* Case 2: the tree is Node k l r, need three things to all hold simultaneously, which is why we use /\ (and)
- P k  ; the key at this node satisfies P
- all_keys P l ; every key in the left subtree satisifies P 
- all_keys P r ; every key in the right subtree satisfies  P *)


(* It's reursive: in a way to check the whole tree, check the root, then recurse into left and then recurse into right *)


(* Without all_keys, we'd have no way to express that every key is in this subtree *)



(* now we can define the BST invariant inductively *)

Inductive bst : tree -> Prop :=
  | BST_Leaf : bst Leaf
  | BST_Node : forall k l r,
      all_keys (fun x => x < k) l -> 
      all_keys (fun x => x > k) r ->
      bst l ->
      bst r -> 
      bst (Node k l r).


(* bst isnt a tree here, but it's a proof-relevant property about a tree
specifically bst t is a statement that says tree is a valied bst, so bst takes a tree and give you a prop, (T/F)  *)
(* just like how tree had two constrctors, we are having constructors for bst too,
- BST_Leaf : bst Leaf ;  what it says that empty tree is always a BST, because no keys, no invariant to violate *)

(* now second constructor 
says if you can give me 4 things (because 4 arrows), then I'll give you a proof that Node k l r is a BST 
- a proof that every key in l is less than k
- a proof that every key in r is greater than k 
- a proof that l is itself a BST
- a proof that r is itself a BST *)



(* now time to prove our example *)

Example example_tree_is_bst : bst example_tree.

(* bst example_tree expands to 
bst (Node 4 (Node 2 Leaf Leaf) (Node 6 Leaf Leaf)) *)


(* now here remember how bst was defined, it exactly had two constructors, BST_Leaf and BST_Node, this example tree isn't a leaf, but it's a Node, so we can apply BST_Node here *)


Proof.
  apply BST_Node.

  (* okay so here, when i applied BST_Node, Rocq looks at what BST_Node requires and above we have already discussed what 4 things BST_Node requires and Rocq turn those all 4 requirements in 4 sub-goals   *)

 (* so what exactly happened that Rocq matched the goal with the conclusion of BST_Node, so in a way, apply worked backwards *)

 (* so, Rocq itself figures out that k = 4, l = Node 2 Leaf Leaf, r = Node 6 Leaf Leaf *)

 (* so, it gives 4 sub-goals by putting their values *)


  -
  simpl.

  (* now what simpl does that it runs the all_keys function and in that function, this sub-goal state matched with second constructor, and put the values into that 
  | Node k l r => P k /\ all_keys P l /\ all_keys P r *)

  (* and it does that by substituting
  P = fun x => x  < 4
  k = 2
  l = leaf
  r = leaf *)


  (* so, now P k becomes (fun x => x < 4) 2 which reduces to 2 < 4
  (* ( now here one can argue that isnt k = 2 , then how come x  = 2, its because when we call P 2 we are actually calling (fun x => x < 4) with input 2 so, Rocq substitutues x  = 2, because 2 is the argument i passed in, the x will get replaced by whatever value we pass in that function *)
  while all_keys P l and P r becomes all_keys (fun x => x < 4) Leaf and all_keys (fun x => x > 4) Leaf respectively*) 
(* ofc all keys on Leaf matched the first case which is True *)

  lia.


  (* lia replaced omega, and it acts as an arithmetic solver so, it solves 2 < 4 and that it is true *)
 
  -
  simpl. lia.
  -

  (* now goal is to prove that left subtree is itself a subtree, again BST_Node will be applied here, because the tree is a node here *)

  apply BST_Node.
     +  simpl. auto.
     +  simpl. auto.
     + apply BST_Leaf.
     + apply BST_Leaf.

  (* whooo, again 4 more subgoals to prove!

  but yes concept is already known, and according to that in this case 
  k => 2 , l => Leaf, r => Leaf
   so yes, simpl applies all_keys on Leaf giving true, and auto closes true trivially  *)
  
 - apply BST_Node;  simpl;  auto ; apply BST_Leaf.
Qed.


(* SEARCH! *)

(* idea is:
- if key equals k, found (return true)
- if key < k, search left
- if key > k, search right
- if Leaf, not found (return false!) *)


Fixpoint search (k : nat) ( t : tree) : bool := 
 match t with 
 | Leaf => false  
 (* because leaf is empty and has no key *)
 | Node x l r =>
     if k =? x then true
     else if k <? x then search k l
     else search k r
 end.    



Example search_4 : search 4 example_tree = true.
Proof. reflexivity. Qed.


Example search_5 : search 5 example_tree = false.
Proof. reflexivity. Qed.

Example search_6 : search 6 example_tree = true.
Proof. reflexivity. Qed.



(* Insertion! *)

(* And the idea is 
- if tree is empty, make a new Node
- if key < current key, insert into left subtree
- if key > current key, insert into right subtree 
- if key =  current key, do nothing (no duplicates)*)

(* and see this returns a new tree and we arent changing anything, something new is being produced, but the original t still exists unchanged *)

Fixpoint insert (k : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node k Leaf Leaf
  | Node x l r => 
      if k =? x then Node x l r 
      else if k <? x then Node x (insert k l) r
      else Node x l (insert k r)
   end.


(* Example: insert 3 into our tree
        4              4
       / \    -->     / \
      2   6          2   6
                      \
                       3
*)

   
Example insert_3 : insert 3 example_tree = Node 4 (Node 2 Leaf (Node 3 Leaf Leaf)) (Node 6 Leaf Leaf).

Proof. reflexivity. Qed.


(* so, here this idea comes that we checked conditions and boom we got a new tree! but how do we knoe that adding a key and passing through these conditions would preserve the BST invariant?!?

so, for that we need to prove this, and we need a helper lemma in this if all keys in t satisfy P, and we insert k where P k also holds then all the keys in the resulting tree still satisfy P*)


Lemma all_keys_insert : forall P k t,
 all_keys P t ->
 P k ->
 all_keys P (insert k t).


 (* if every key in tree satisfies P, and the new key being added in tree also satisfies P, then all the keys (after insertion) in newly formed tree satisfies P *)

Proof.
  intros P k t Hall Hk. 
  (* intros for pulling everything we have and to prove into context *)
  induction t as [| x l IHl r IHr].
  (* induction on t because insert is recursive over the tree, so proof needs to be recurisive too
  this splits into 2 cases just like the tree type has 2 constructors *)
  (* what i m actually saying here that I will prove this for all trees by proving it for smaller and smaller trees *)
  (* for the Node x l r case, Rocq says I will assume the thing you want to prove is already true for subtrees l and r and you just need to prove for the whole subtree x l r *)
  (* And that assuption is IHl and IHr *)

  -
    (* case-1 t = leaf *)
    (* so at this point, the goal is tree = leaf there's no IHl / IHr because induction hypothesis only exist for subtrees and Leaf has none  *)
    simpl. auto.
  -
     (* case-2 t = Node x l r *)
     (* here goal is in which tree = NOde x l r, having two subtrees l and r, so Rocq gives induction hypothesis for both of them *)

 (* so what IHl and IHr saying:
 IHl: if all keys in l satisfy P then after inserting k into l, all keys still satisfy P and same is the case with IHr*)

 (* and this proof has to be recursive because the insert fuction was using recursion to recurse into subtrees, remember when the tree is Node x l r and k < x, then insert calls itself on l *)

 (* so, to reason about all_keys P (insert k (Node x l r)) when k < x, you need to reason about all_keys P (insert k l) which is a smaller problem, that smaller problem is exactly what IHl gives you.*)

 simpl in Hall. destruct Hall as [Hx [Hl Hr]].

 (* now instead of one big Hall, we have three individual facts we can use separately *)

 simpl.

 (* now simpl unfolds insert k(Node x l r) in the goal, but insert on a node has three branches depending on whether k =? x, k <? x or neither, so simpl cannot fully reduce, it leaves you with an if expression in the goal  *)

 (* so now for if, we can't prove anything abt it without knowing which branch it takes, so we split into two subgoals(i) k =? x and (ii) k <? x in other words, one goal where k=? x is true and other where it is false, *)

 destruct (k =? x) eqn:Heq.

 (* eqn:Heq saves that case *)


 
 (* subcase: k = x (no change), the if is taking the true branch here so no change *)

   + simpl. auto.

  (* simpl expands to P x /\ all_keys P l /\ all_keys P r *)
  (* auto closes it using Hx, Hl, Hr which are already in context *)

  (* now goal still involves an if and we need to split it again *)

   + destruct (k <? x) eqn: Hlt.

   (* first subcase: insert goes to left, if takes the true branch *)
     *simpl. auto.

    (* simpl expands it and auto tries to close each piece: P x by Hx, all_keys, P r by Hr, all_keys P (insert k l) closed by IHl applied to Hl*)
    *simpl. auto.
    (* same is the case with this too closed by Hx, Hl, IHr *)


Qed.  



(* now theorem: insert preserves BST *)

(* the idea: if it is a BST, then (insert k t) is also a BST*)




Theorem insert_bst : forall k t,
   bst t -> bst (insert k t).

Proof.
  intros k t H.

  (* we'll do induction on H,the proof that t is a bst not on t directly, because bst is an inductive type with 2 constructors, BST_Leaf and BST_Node *)

  (* case-1 t = leaf, case-2 t = Node x l r, for case 2 Rocq gives u everything node requires *)

  induction H as [|x l r Hl_small Hr_large Hbst_l IHl Hbst_r IHr].

  (* u remember this was the bst :
  Inductive bst : tree -> Prop :=
  | BST_Leaf : bst Leaf
  | BST_Node : forall k l r,
      all_keys (fun x => x < k) l ->   (here it is Hl_small)
      all_keys (fun x => x > k) r -> (Hr_large)
      bst l -> (Hbst_l)
      bst r -> (Hbst_r)
      bst (Node k l r).  *)

  (* now here one can argue from where do these IHl and IHr came?!? huh
  
  because the pattern is always: recursive argument, then its IH, recursive argument, then its IH. that is why IHl comes right after Hbst_l, and IHr comes right after Hbst_r.
  *)


  (* one more thing to notice that why IH for bst l and bst r but not for Hl_small and Hr_large COZ
  induction hypotheses are only generated for places where the type you are doing induction on appears recursively, what we are doing here is induction on bst, so Rocq only generates IHs for the arguments whose type is bst. Hl_small and Hr_large have type all_keys ..., not bst, so no IH is generated for them. *)



  - 
  (* t = Leaf *)
  simpl. apply BST_Node; simpl; auto; apply BST_Leaf.

  (* BST_Node generates four subgoals. simpl unfolds all_keys on Leaf giving true. auto closes true. BST_Leaf closes the bst Leaf goals. *)
  -
  (* t = Node x l r *)
  simpl.
  destruct (k =? x) eqn: Heq.
     
    +apply BST_Node; auto.

    + destruct (k <? x) eqn: Hlt.
         * 
         (* k < x, insert into left subtree *)
         apply BST_Node; auto.
         (* out of 4 goals generated by BST_Node, the first one is not trivial. auto could not close it, so the remaining goal is:
         all_keys (fun z => z < x) (insert k l)
          *)
          apply all_keys_insert; auto.

    (* apply all_keys_insert generates two subgoals:

all_keys (fun z => z < x) l -- closed by Hl_small via auto
(fun z => z < x) k which reduces to k < x *)

apply Nat.ltb_lt in Hlt. auto.

(* Hlt is the hypothesis k <? x = true (coming from the destruct), Nat.ltb_lt converts this boolean fact into a propositional fact: k < x, and auto closes the goal. *)

*
(* k > x, insert into right subtree *)
apply BST_Node; auto.
apply all_keys_insert; auto.


(* we need to prove k > x and we have two hypotheses:

Heq : k =? x = false meaning k ≠ x
Hlt : k <? x = false meaning k is not less than x *)
(* so if k is not less than and equal to x then it means it must be greater than x  *)

apply Nat.ltb_nlt in Hlt.

(* Nat.ltb_nlt converts k <? x = false into ~ (k < x) meaning k is not less than x.
 *)

apply Nat.eqb_neq in Heq.

(* Nat.eqb_neq converts k =? x = false into k ≠ x. *)

lia.

(* Now lia has: ~ (k < x) and k ≠ x and needs to prove k > x. (pure arithmetic), lia sees this and closes the goal. *)



(* note: for finding these lemma about nat one can use:*)

Search ((_ <? _) = false).
Search ((_ <? _) = true).


Search ((_ =? _) = false).

Qed.

(* phew!!, bst done! *)





  



















  



   


   
   


  


















