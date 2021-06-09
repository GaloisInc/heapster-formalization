From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lists.List
     Lia.

From Heapster Require Import
     Utils
     Permissions.

Import ListNotations.

(* Memory model *)
Definition addr : Set := nat * nat.

Definition eqb (a b : addr) : bool :=
  Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Lemma addr_dec : forall (a b : addr), {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2].
  destruct (Nat.eq_dec a1 b1); destruct (Nat.eq_dec a2 b2); subst; auto.
  - right. intros H. inversion H; subst. apply n. reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
Qed.

Lemma addr_neq_cases (b b' o o' : nat) :
  (b, o) <> (b', o') -> b <> b' \/ o <> o'.
Proof.
  intros.
  destruct (Nat.eq_dec b b'); destruct (Nat.eq_dec o o'); subst; auto.
Qed.

Lemma eqb_spec : forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros [x1 x2] [y1 y2]. destruct (eqb (x1, x2) (y1, y2)) eqn:?; constructor.
  - unfold eqb in Heqb. simpl in Heqb. symmetry in Heqb. apply Bool.andb_true_eq in Heqb.
    destruct Heqb. symmetry in H, H0.
    apply (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H.
    apply (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in H0. subst. auto.
  - unfold eqb in Heqb. simpl in Heqb. apply Bool.andb_false_iff in Heqb.
    destruct Heqb.
    + intro. inversion H0. subst. rewrite Nat.eqb_refl in H. inversion H.
    + intro. inversion H0. subst. rewrite Nat.eqb_refl in H. inversion H.
Qed.

Inductive Value :=
| VNum : nat -> Value
| VPtr : addr -> Value.

Definition mem_block := nat -> option Value.

Variant logical_block :=
| LBlock (size : nat) (bytes : mem_block) : logical_block.

Definition memory := list (option logical_block).

(* is the block of ptr allocated and is the offset of ptr within bounds *)
Definition allocated (m : memory) (ptr : addr) : bool :=
  match nth_error m (fst ptr) with
  | Some (Some (LBlock size _)) => snd ptr <? size
  | _ => false
  end.

(* read c at memory location ptr. ptr must be a valid location and allocated. *)
Definition read (m : memory) (ptr : addr) : option Value :=
  if allocated m ptr
  then match nth_error m (fst ptr) with
       | Some (Some (LBlock _ bytes)) => bytes (snd ptr)
       | _ => None
       end
  else None.

(* returns the size of the block only if ptr has offset 0 *)
(* note if we used `allocated` here then it doesn't work for size 0 blocks... *)
Definition sizeof (m : memory) (ptr : addr) : option nat :=
  if snd ptr =? 0
  then match nth_error m (fst ptr) with
       | Some (Some (LBlock size _)) => Some size
       | _ => None
       end
  else None.

Definition write (m : memory) (ptr : addr) (v : Value) : option memory :=
  if allocated m ptr
  then match nth_error m (fst ptr) with
       | Some (Some (LBlock size bytes)) =>
         Some (replace_list_index
                 m
                 (fst ptr)
                 (Some (LBlock size (fun o => if o =? snd ptr
                                           then Some v
                                           else bytes o))))
       | _ => None
       end
  else None.

Lemma allocated_ptr_block m b o :
  allocated m (b, o) = true ->
  b < length m.
Proof.
  unfold allocated. simpl. intros.
  apply nth_error_Some. intro. rewrite H0 in H. inversion H.
Qed.

Lemma allocated_ptr_offset m b o size bytes :
  allocated m (b, o) = true ->
  nth_error m b = Some (Some (LBlock size bytes)) ->
  o < size.
Proof.
  unfold allocated. simpl. intros. rewrite H0 in H.
  rewrite <- (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H. auto.
Qed.

Lemma read_success_write m ptr v v' :
  read m ptr = Some v ->
  exists m', write m ptr v' = Some m'.
Proof.
  unfold read, write. intros.
  destruct (allocated m ptr), (nth_error m (fst ptr));
    try destruct o; try solve [inversion H].
  destruct l. eexists. reflexivity.
Qed.

Lemma write_success_read_eq m m' ptr v :
  write m ptr v = Some m' ->
  read m' ptr = Some v.
Proof.
  unfold read, write. intros.
  destruct (allocated m ptr) eqn:?, (nth_error m (fst ptr)) eqn:?;
           try destruct o; try solve [inversion H].
  destruct l. inversion H. clear H H1 m'. unfold allocated in *.
  rewrite nth_error_replace_list_index_eq; [| eapply allocated_ptr_block; eauto].
  rewrite Heqo in Heqb. clear Heqo. rewrite Heqb. rewrite Nat.eqb_refl; auto.
Qed.

Lemma write_success_read_neq m m' ptr v :
  write m ptr v = Some m' ->
  forall ptr', ptr <> ptr' -> read m ptr' = read m' ptr'.
Proof.
  destruct ptr as [b o].
  unfold write. unfold read. simpl. intros.
  destruct (allocated m (b, o)) eqn:?; try solve [inversion H].
  destruct (nth_error m b) eqn:?; try solve [inversion H].
  destruct o0 eqn:?; try solve [inversion H].
  destruct l. inversion H; subst; clear H. destruct ptr' as [b' o']. simpl.
  pose proof (allocated_ptr_block _ _ _ Heqb0).
  destruct (addr_neq_cases _ _ _ _ H0).
  - unfold allocated. simpl. erewrite nth_error_replace_list_index_neq; eauto.
  - destruct (Nat.eq_dec b b').
    + subst. unfold allocated. simpl. rewrite nth_error_replace_list_index_eq; auto.
      rewrite Heqo0. destruct (o' <? size) eqn:?; auto.
      rewrite <- Nat.eqb_neq in H1. rewrite Nat.eqb_sym. rewrite H1. auto.
    + unfold allocated. simpl. erewrite nth_error_replace_list_index_neq; eauto.
Qed.

Lemma write_success_sizeof m m' ptr v :
  write m ptr v = Some m' ->
  forall ptr', sizeof m ptr' = sizeof m' ptr'.
Proof.
  destruct ptr as [b o].
  unfold write. unfold read. simpl. intros.
  destruct (allocated m (b, o)) eqn:?; try solve [inversion H].
  destruct (nth_error m b) eqn:?; try solve [inversion H].
  destruct o0 eqn:?; try solve [inversion H].
  destruct l. inversion H; subst; clear H. destruct ptr' as [b' o']. simpl.
  pose proof (allocated_ptr_block _ _ _ Heqb0).
  unfold sizeof. simpl. destruct (o' =? 0) eqn:?; auto.
  destruct (Nat.eq_dec b b').
  - subst. simpl. rewrite nth_error_replace_list_index_eq; auto.
    rewrite Heqo0. auto.
  - erewrite nth_error_replace_list_index_neq; eauto.
Qed.

Lemma write_success_length m m' ptr v :
  write m ptr v = Some m' ->
  length m = length m'.
Proof.
  destruct ptr as [b o].
  unfold write. unfold read. simpl. intros.
  destruct (allocated m (b, o)) eqn:?; try solve [inversion H].
  destruct (nth_error m b) eqn:?; try solve [inversion H].
  destruct o0 eqn:?; try solve [inversion H].
  destruct l. inversion H; subst; clear H.
  pose proof (allocated_ptr_block _ _ _ Heqb0).
  simpl. apply replace_list_index_length; auto.
Qed.

(* mem_at ptr v creates a memory which is only defined at location ptr *)
Definition mem_at (ptr : addr) (v : Value) : memory :=
  repeat None (fst ptr) ++ [Some (LBlock
                                    (snd ptr + 1)
                                    (fun o => if o =? snd ptr
                                           then Some v
                                           else None))].

Lemma allocated_mem_at ptr v : allocated (mem_at ptr v) ptr = true.
  destruct ptr as [b o]. unfold allocated, mem_at. simpl.
  induction b; simpl; auto. apply Nat.ltb_lt. lia.
Qed.

Lemma nth_error_mem_at ptr v :
  nth_error (mem_at ptr v) (fst ptr) =
  Some (Some (LBlock
                (snd ptr + 1)
                (fun o => if o =? snd ptr
                       then Some v
                       else None))).
Proof.
  destruct ptr as [b o]. simpl. induction b; auto.
Qed.

Lemma read_mem_at ptr v : read (mem_at ptr v) ptr = Some v.
Proof.
  destruct ptr as [b o]. unfold read.
  rewrite allocated_mem_at. rewrite nth_error_mem_at.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma write_mem_at ptr v v' : write (mem_at ptr v) ptr v' = Some (mem_at ptr v').
Proof.
  destruct ptr as [b o]. unfold write.
  rewrite allocated_mem_at. rewrite nth_error_mem_at. f_equal.
  unfold mem_at. simpl.
  induction b; simpl; try solve [f_equal; auto].
  do 3 f_equal. apply functional_extensionality. intros.
  destruct (x =? o); auto.
Qed.
