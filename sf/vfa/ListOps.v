Require Import List Lia.
Import ListNotations.
Import Arith.

(** * Study practice for the midterm exam. *)

(** The midterm will involve some operations on lists. 
  These lemmas will help familiarize you with these
  operations in advance of the exam itself.  You 
  can prove these lemmas if you like -- they're all
  easy except skipn_skipn -- but even if you don't 
  prove them, just reading the lemma statements will
  help you learn about these operators. *)

About skipn.

Print skipn.

About nth.

Print nth.

About repeat.

Print repeat.

About length.

Print length.

About repeat_length.

(* It's in the standard library, but easy to prove anyway *)
Lemma repeat_length: forall (A : Type) (x : A) (n : nat),
       length (repeat x n) = n.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite IHn. auto. 

About skipn_nil.

(* It's in the standard library, but easy to prove anyway *)
Lemma skipn_nil: forall (A: Type) (i: nat),
  skipn i (@nil A) = nil.
Proof.
  intros.
  destruct i.
  - auto.
  - auto. 

About skipn_skipn.

(* It's in the standard library, but (almost) easy to prove anyway *)
Lemma skipn_skipn: forall (A : Type) (x y : nat)(l : list A),
       skipn x (skipn y l) = skipn (x + y) l. 
Proof.  
(* It's not obvious which variable to induct on.
   If you pick the right one, it's easy. *)
  intros.
  generalize dependent l.
  induction y.
  - intros. simpl. rewrite Nat.add_0_r. auto.
  - intros. destruct l. 
    + rewrite Nat.add_succ_r. simpl. apply skipn_nil.
    + rewrite Nat.add_succ_r. simpl. apply IHy. Qed. 

(* The rest of these proof are easy *)
Lemma nth_hd_skipn: forall [A: Type] (d: A) (i: nat) (al: list A),
  nth i al d = hd d (skipn i al).
Proof.
  intros. generalize dependent i. induction al.
  - intros. rewrite skipn_nil. destruct i; auto.
  - destruct i. 
    + auto.
    + simpl. apply IHal. Qed.

Lemma nth_skipn:  forall [A: Type] (d: A) (al: list A) (i j: nat),
  nth i (skipn j al) d = 
  nth (i+j) al d.
Proof.
  intros.
  generalize dependent i.
  generalize dependent j.
  induction al.
  - intros. rewrite skipn_nil. destruct i; destruct j; auto.
  - destruct i; destruct j.
    + auto.
    + simpl. apply IHal.
    + simpl. rewrite Nat.add_0_r. auto.
    + simpl. rewrite <- Nat.add_succ_comm. apply IHal. Qed.

Lemma skipn_repeat:
  forall [A: Type] (a: A) (i j: nat),
  skipn i (repeat a j) = repeat a (j-i).
Proof.
  intros A a i.
  induction i.
  - intros. simpl. rewrite Nat.sub_0_r. auto.
  - intros. destruct j.
    + auto.
    + simpl. apply IHi. Qed.

Lemma nth_repeat:
  forall [A: Type] (d a: A) i j,
  i<j -> 
  nth i (repeat a j) d = a.
Proof.
  intros A d a i.
  induction i.
  - intros. destruct j.
    + lia.
    + auto.
  - intros. destruct j.
    + lia.
    + simpl. apply Nat.succ_lt_mono in H. apply IHi. apply H. Qed.

Lemma skipn_app1:
  forall [A: Type] (i: nat) (al bl: list A),
  i <= length al ->
  skipn i (al++bl) = skipn i al ++ bl.
Proof.
  intros A i al.
  generalize dependent i.
  induction al.
  - intros. simpl in *. destruct i.
    + auto.
    + lia.
  - intros. simpl in *. destruct i.
    + auto.
    + simpl. apply Nat.succ_le_mono in H. apply IHal. apply H. Qed.

Lemma skipn_app2:
  forall [A: Type] (i: nat) (al bl: list A),
  i >= length al ->
  skipn i (al++bl) = skipn (i - length al) bl.
Proof.
  intros A i al.
  generalize dependent i.
  induction al.
  - intros. simpl. rewrite Nat.sub_0_r. auto.
  - intros. simpl. destruct i.
    + simpl in *. lia.
    + simpl in *. apply IHal. lia. Qed.

Lemma skipn_app:
  forall [A: Type] (i: nat) (al bl: list A),
  skipn i (al ++ bl) = skipn i al ++ skipn (i - length al) bl.
Proof.
  intros A i al.
  generalize dependent i.
  induction al.
  - intros. rewrite skipn_nil. simpl. rewrite Nat.sub_0_r. auto.
  - intros. simpl. destruct i.
    + auto.
    + simpl. apply IHal. Qed.

About Forall.
About Forall_impl.

(* It's in the standard library, but easy to prove anyway *)
Lemma Forall_impl:
  forall [A : Type] [P : A -> Prop] (Q : A -> Prop),
  (forall a : A, P a -> Q a) ->
  forall l : list A, Forall P l -> Forall Q l.
Proof.
  intros.
  induction l.
  - auto.
  - apply Forall_cons; inversion H0; subst.
    + apply H. apply H3.
    + apply IHl. apply H4. Qed. 

About Forall_forall.
 
(* It's in the standard library, but easy to prove anyway *)
Lemma Forall_forall: 
  forall [A : Type] (P : A -> Prop) (l : list A),
   Forall P l <-> (forall x : A, In x l -> P x).
Proof.
  intros. split.
  - intros. induction l.
    + simpl in H0. contradiction.
    + simpl in H0. destruct H0.
      * inversion H. subst. apply H3.
      * inversion H. subst. apply IHl. apply H4. apply H0.
  - intros. induction l.
    + apply Forall_nil.
    + apply Forall_cons.
      * simpl in H. apply H. left. auto.
      * simpl in H. apply IHl. intros. apply H. right. auto. Qed.   

Lemma example_Forall_impl:
  forall i j (al: list nat),
  Forall (fun x => i+j<x) al ->
  Forall (fun x => i<x) al.
Proof.
intros.
eapply Forall_impl.
2: apply H.
simpl.
lia.
Qed.

Lemma example_Forall_forall:
  forall i j (al: list nat),
  Forall (fun x => i+j<x) al ->
  Forall (fun x => i<x) al.
Proof.
  intros.
  rewrite Forall_forall in *.
  intros. apply H in H0. lia.
Qed.

Definition foo := nat.

Lemma stupid_Coq_trick_that_is_sometimes_necessary: 
  forall  (al: list foo) (n: nat),
   length al = n ->
   1 + @length nat al = S n.
Proof.
intros.
(** Examine the proof state here, and then try [rewrite H] *)
Fail rewrite H.
(** This is very annoying.  It looks like the rewrite should work!
   Here is the explanation:  *)
Set Printing Implicit.
(** In assumption H, the implicit argument of @length is [foo],
   but below the line, it is [nat].  Sometimes in this situation,
  Coq fails to see that it can do a rewrite.
      When this happens, you can do either one of:
  - unfold foo in H       (* above the line *)
  - change (@length nat) with (@length foo)  (* below the line *)
*)
unfold foo in H.
rewrite H.
auto.
Qed.

