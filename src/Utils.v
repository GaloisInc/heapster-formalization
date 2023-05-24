(* begin hide *)
From Coq Require Import
     Lists.List
     micromega.Lia.

Import ListNotations.
(* end hide *)

(** * Lens typeclass *)
Class Lens (A B:Type) : Type :=
  {
  lget: A -> B;
  lput: A -> B -> A;
  lGetPut: forall a b, lget (lput a b) = b;
  lPutGet: forall a, lput a (lget a) = a;
  lPutPut: forall a b b', lput (lput a b) b' = lput a b'
  }.

(** * [replace_list_index] *)
(** A function for replacing an element in a list, growing the list if needed. *)
Fixpoint replace_list_index {A : Type} (l : list A) (n : nat) (new : A) : list A :=
  match l with
  | [] => repeat new (n + 1)
  | h :: t => match n with
            | O => new :: t
            | S n => h :: replace_list_index t n new
            end
  end.

(** Some properties about [replace_list_index] and [nth_error] *)
Lemma replace_list_index_length A (l l' : list A) n (a : A) :
  length l = length l' ->
  n < length l ->
  length l = length (replace_list_index l' n a).
Proof.
  revert l l'. induction n; intros l l' Hlen Hlt.
  - destruct l, l'; try inversion Hlen; auto. inversion Hlt.
  - destruct l, l'; try inversion Hlen.
    + inversion Hlt.
    + cbn in Hlt. apply PeanoNat.Nat.succ_lt_mono in Hlt. cbn. f_equal. auto.
Qed.

Lemma replace_list_index_length_bound A (l : list A) n a :
  n < length (replace_list_index l n a).
Proof.
  revert l.
  induction n; intros.
  - destruct l; cbn; auto. apply PeanoNat.Nat.lt_0_succ.
  - destruct l; cbn; auto.
    + apply Arith_prebase.lt_n_S_stt. specialize (IHn []). auto.
    + apply Arith_prebase.lt_n_S_stt. auto.
Qed.

Lemma nth_error_replace_list_index_neq A n n' (l : list A) (a : A) :
  n' < length l ->
  n <> n' ->
  nth_error l n = nth_error (replace_list_index l n' a) n.
Proof.
  revert l n'.
  induction n; intros l n' Hl Hn; (destruct l; [inversion Hl |]);
    simpl; destruct n'; intuition.
Qed.

Lemma nth_error_replace_list_index_eq A n (l : list A) (a : A) :
  nth_error (replace_list_index l n a) n = Some a.
Proof.
  revert l. induction n; intros l.
  - destruct l; auto.
  - destruct l; simpl; auto.
    clear IHn. simpl. rewrite PeanoNat.Nat.add_1_r. induction n; auto.
Qed.

Lemma nth_error_replace_list_index_neq_before A n n' (l : list A) (a : A) :
  n < length l ->
  n' >= length l ->
  nth_error (replace_list_index l n' a) n = nth_error l n.
Proof.
  revert n' l. induction n; intros n' l.
  - destruct l; intros. inversion H.
    destruct n'. inversion H0. reflexivity.
  - intros. destruct l.
    + inversion H.
    + cbn. destruct n'. inversion H0.
      apply IHn; cbn in *; lia.
Qed.

Lemma nth_error_replace_list_index_neq_new A n n' (l : list A) (a : A) :
  n >= length l ->
  n' >= length l ->
  n < n' ->
  nth_error (replace_list_index l n' a) n = Some a.
Proof.
  revert n' l. induction n; intros n' l.
  - destruct l; intros. 2: inversion H.
    cbn. rewrite PeanoNat.Nat.add_1_r. reflexivity.
  - intros. destruct l.
    + clear IHn. cbn. rewrite PeanoNat.Nat.add_1_r. cbn.
      apply nth_error_repeat. lia.
    + cbn. destruct n'. inversion H0.
      apply IHn; cbn in *; lia.
Qed.

Lemma nth_error_replace_list_index_neq_after A n n' (l : list A) (a : A) :
  n' >= length l ->
  n > n' ->
  nth_error (replace_list_index l n' a) n = None.
Proof.
  revert n' l. induction n; intros n' l.
  - intros. destruct l; intros; inversion H0.
  - intros. destruct l.
    + clear IHn. cbn. rewrite PeanoNat.Nat.add_1_r. cbn.
      apply nth_error_None. rewrite repeat_length. lia.
    + cbn. destruct n'. inversion H.
      apply IHn; cbn in *; lia.
Qed.

Lemma replace_list_index_eq A (l : list A) n a :
  nth_error l n = Some a ->
  replace_list_index l n a = l.
Proof.
  intros. revert H. revert n. induction l; intros.
  - destruct n; inversion H.
  - destruct n; simpl; auto.
    + inversion H; auto.
    + f_equal; auto.
Qed.

Lemma replace_list_index_twice A (l : list A) n a :
  replace_list_index (replace_list_index l n a) n a = replace_list_index l n a.
Proof.
  cbn.
  revert l. induction n; intros l.
  - destruct l; cbn; reflexivity.
  - destruct l; cbn. 2: rewrite IHn; auto.
    rewrite PeanoNat.Nat.add_1_r. f_equal.
    rewrite replace_list_index_eq; auto.
    apply nth_error_repeat; auto.
Qed.

(** [nth_error] facts *)

Lemma nth_error_app_last A n (l : list A) (a : A) :
  length l = n ->
  nth_error (l ++ [a]) n = Some a.
Proof.
  revert l. induction n; intros [| l] Hl; inversion Hl; auto.
  simpl. remember (length l0). subst. apply IHn; auto.
Qed.

Lemma nth_error_app_early A n (l : list A) (a : A) :
  n < length l ->
  nth_error (l ++ [a]) n = nth_error l n.
Proof.
  revert l. induction n; intros l Hl.
  - destruct l; auto; inversion Hl.
  - destruct l; auto.
    + inversion Hl.
    + simpl in Hl. apply PeanoNat.Nat.succ_lt_mono in Hl. apply IHn; auto.
Qed.

Lemma nth_error_eq A (l l' : list A) :
  (forall n, nth_error l n = nth_error l' n) ->
  l = l'.
Proof.
  revert l'. induction l; intros.
  - destruct l'; auto.
    specialize (H 0). inversion H.
  - pose proof (H 0). destruct l'; inversion H0. subst.
    f_equal. apply IHl.
    intros. specialize (H (S n)). cbn in H. auto.
Qed.
