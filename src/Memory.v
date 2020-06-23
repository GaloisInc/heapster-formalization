From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

Require Export Heapster.Permissions.

(* Memory model *)
Definition addr : Set := nat * nat.
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

Inductive SByte :=
| Byte : nat -> SByte
| Ptr : addr -> SByte
(* | SUndef : SByte. *)
.
Definition mem_block := nat -> option SByte.

Variant logical_block :=
| LBlock (size : nat) (bytes : mem_block) : logical_block.

Definition memory := nat -> option logical_block.
