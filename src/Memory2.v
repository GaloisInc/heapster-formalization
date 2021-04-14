From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

Require Export Heapster.Permissions.

(* Memory model *)
Definition block := nat.
Definition offset := nat.
Definition addr : Set := block * offset.

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
| VPtr : addr -> Value
.
Definition mem_block := offset -> option Value.

Variant logical_block :=
| LBlock (size : offset) (bytes : mem_block) : logical_block.

Definition memory := list (option logical_block).
