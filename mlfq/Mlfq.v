(* Rule 1: If Priority(A) > Priority(B), A runs (B doesn’t).
• Rule 2: If Priority(A) = Priority(B), A & B run in RR *)
(* Rule 3: When a job enters the system, it is placed at the highest
priority (the topmost queue).
• Rule 4a: If a job uses up its allotment while running, its priority is
reduced (i.e., it moves down one queue).
• Rule 4b: If a job gives up the CPU (for example, by performing
an I/O operation) before the allotment is up, it stays at the same
priority level (i.e., its allotment is reset). 
• Rule 5: After some time period S, move all the jobs in the system to the topmost queue.*)


From Coq Require Import Arith List Lia.
Import List.
Import ListNotations.


(* a process carries its id, how much work it still needs, and how much
   of the current queue's allotment budget it has consumed so far *)
Record process : Type :=
 mlfq_process
 {
    pid  :  nat;
    remaining_work :  nat;
    used_allotment : nat
 }.


(* a queue holds a list of processes and the allotment limit for that
   priority level; every process in this queue shares the same limit *)
Record queue : Type  :=
mlfq_queue
{
   processes : list process;
   allotment_limit : nat
}.

(* the full mlfq is just a list of queues ordered from highest to lowest
   priority; the head is always the highest priority queue *)

Definition mlfq := list queue. 


(* sanity checks *)


Definition p1 := mlfq_process 1 10 0.

Definition p2 := mlfq_process 2 20 1.

Definition queue1 := mlfq_queue [p1;p2] 3.

Definition queue2 := mlfq_queue [p1;p2] 4.


Definition mlfq1 := [queue1; queue2].



(* functions *)

(* Rule 3 *)


Definition job_enters (p : process) (m : mlfq) : mlfq := 
match m with
| [] => []
| head :: rest => 
  mlfq_queue ( p :: head.(processes)) head.(allotment_limit) :: rest
end.


(* Rule 4 *)


Definition job_executes (p : process) (m : mlfq) : mlfq :=

match m with 
| [] => []
| [q0] => m
| q0 :: q1 :: rest =>
     let updated_p := mlfq_process (pid p) (remaining_work p - 1) (used_allotment p + 1) in
     let new_q0 := mlfq_queue (updated_p :: processes q0) (allotment_limit q0) in
     let demoted_p := mlfq_process (pid p) (remaining_work p - 1) 0  in
     let new_q1 := mlfq_queue (demoted_p :: processes q1) (allotment_limit q1) in
     if used_allotment p =? allotment_limit q0
     then q0 :: new_q1 :: rest
     else new_q0 :: q1 :: rest
 end. 
 

(* Rule 5:  *)

Definition priority_boost (m : mlfq) : mlfq :=
match m with
|[] => []
|head :: rest =>
   let all_processes := List.flat_map (fun q => q.(processes)) m in
    mlfq_queue all_processes (allotment_limit head) :: 
    List.map (fun q => mlfq_queue [] (allotment_limit q)) rest
end. 


(* examples *)
 
 Example job_enters_test : job_enters p1 mlfq1 = [mlfq_queue [p1;p1;p2] 3; queue2].
Proof. reflexivity. Qed.


  
Example job_executes_test : job_executes p1 mlfq1 =  [mlfq_queue [mlfq_process 1 9 1; p1; p2] 3; queue2].  
Proof. reflexivity. Qed.


Example priority_boost_test : priority_boost  mlfq1 = [mlfq_queue [p1;p2;p1;p2] 3 ; mlfq_queue [] 4].
Proof. reflexivity. Qed.


(* theorems  *)

(* Rule 3 correctness: the entering process always lands in the head queue *)

Theorem job_enters_in_head : forall (p : process) (q : queue) (rest : mlfq), In p (processes (hd q (job_enters p (q :: rest)))).
Proof.
   intros p q rest.
   simpl.
   left.
   reflexivity.
Qed.   

(* Rule 4 demotion: when allotment is exhausted, process moves to next queue
   with used_allotment reset to 0 *)


Theorem job_executes_demotion : forall (p : process) (q0 q1 : queue) (rest : mlfq),
  used_allotment p = allotment_limit q0 ->
  job_executes p (q0 :: q1 :: rest) = 
  q0 :: (mlfq_queue (mlfq_process (pid p) (remaining_work p - 1) 0 :: processes q1) (allotment_limit q1)) :: rest.
  
Proof.
   intros p q0 q1 rest H.
   simpl.
   rewrite H.
   rewrite Nat.eqb_refl.
   reflexivity.
Qed.

(* Rule 4 stay: when allotment is not exhausted, process stays in same queue
   with remaining_work decremented and used_allotment incremented *)

 
Theorem job_executes_same : forall (p : process) (q0 q1 : queue) (rest : mlfq),
used_allotment p < allotment_limit q0 ->
job_executes p (q0 :: q1 :: rest) =
mlfq_queue (mlfq_process (pid p) (remaining_work p - 1) (used_allotment p + 1) :: processes q0) (allotment_limit q0) :: q1 :: rest.

Proof.
   intros p q0 q1 rest H.
   simpl. 
   assert (used_allotment p =? allotment_limit q0 = false) as Hneq.
   { apply Nat.eqb_neq. lia. }
   rewrite Hneq.
   reflexivity.
Qed. 

(* Rule 5 correctness: every process that was anywhere in the mlfq before
   the boost ends up in the head queue's process list after the boost *)

Theorem priority_boost_In : forall (p : process) (q : queue) (rest : mlfq),
  (exists q', In q' (q :: rest) /\ In p (processes q')) ->
  In p (processes (hd q (priority_boost (q :: rest)))).
Proof.
 intros p q rest.
 intros [q' [Hq' Hp]].
 simpl.
 apply in_or_app.
 destruct Hq' as [Heq | Hin].
 - 
 left. rewrite Heq. apply Hp.
 -
 right. apply in_flat_map. exists q'. split.
 +
 apply Hin.
 +
 apply Hp.
Qed.






