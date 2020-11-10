From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

From Heapster Require Export
     Permissions
     Memory
     SepStep
     Functional
     Config
     PermType.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

Import MonadNotation.
Import ITreeNotations.

Context (Si Ss:Type).

Lemma TrueI (A : Type) P (xi : A) :
  P ⊑ (P * (xi : trueP Si Ss @ tt)).
Proof.
  simpl. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Lemma SumI1 (A1 A2 B1 B2 : Type) (xi : A1) (xs : B1) (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi : T1 @ xs ⊑ inl xi : T1 +T+ T2 @ inl xs.
Proof. reflexivity. Qed.

Lemma SumI2 (A1 A2 B1 B2 : Type) (xi : A2) (xs : B2) (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi : T2 @ xs ⊑ inr xi : T1 +T+ T2 @ inr xs.
Proof. reflexivity. Qed.

Lemma SumE (A1 A2 B1 B2 R1 R2 : Type)
      (xi : A1 + A2) (xs : B1 + B2) ti1 ti2 ts1 ts2
      (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) (P : Perms) (U : PermType Si Ss (A1 + A2) (B1 + B2)) :
  (forall yi ys, P * yi : T1 @ ys ⊢ ti1 ▷ ts1 ::: U) ->
  (forall yi ys, P * yi : T2 @ ys ⊢ ti2 ▷ ts2 ::: U) ->
  P * xi : T1 +T+ T2 @ xs ⊢ either (fun _ => ti1) (fun _ => ti2) xi ▷ either (fun _ => ts1) (fun _ => ts2) xs ::: U.
Proof.
  intros. simpl.
  destruct xi, xs; auto;
    rewrite sep_conj_Perms_commut; rewrite sep_conj_Perms_top_absorb; apply typing_top.
Qed.

Lemma ProdI (A1 A2 B1 B2 : Type) xi yi xs ys (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi : T1 @ xs * yi : T2 @ ys ⊑ (xi, yi) : T1 *T* T2 @ (xs, ys).
Proof. reflexivity. Qed.

Lemma ProdE (A1 A2 B1 B2 : Type) xi xs (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi : T1 *T* T2 @ xs ⊑ fst xi : T1 @ fst xs * snd xi : T2 @ snd xs.
Proof. reflexivity. Qed.

Lemma StarI (A B1 B2 : Type) xi xs ys (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi : T1 @ xs * xi : T2 @ ys ⊑ xi : (starPT _ _ T1 T2) @ (xs, ys).
Proof. reflexivity. Qed.

Lemma StarE (A B1 B2 : Type) xi xs (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi : (starPT _ _ T1 T2) @ xs ⊑ xi : T1 @ fst xs * xi : T2 @ snd xs.
Proof. reflexivity. Qed.

Lemma OrI1 (A B1 B2 : Type) xi xs (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi : T1 @ xs ⊑ xi : (or _ _ T1 T2) @ inl xs.
Proof. reflexivity. Qed.

Lemma OrI2 (A B1 B2 : Type) xi xs (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi : T2 @ xs ⊑ xi : (or _ _ T1 T2) @ inr xs.
Proof. reflexivity. Qed.

Lemma OrE (A B1 B2 R1 R2 : Type)
      (xi : A) (xs : B1 + B2) ti ts1 ts2
      (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) (P : Perms) (U : PermType Si Ss A (B1 + B2)) :
  (forall yi ys, P * yi : T1 @ ys ⊢ ti ▷ ts1 ::: U) ->
  (forall yi ys, P * yi : T2 @ ys ⊢ ti ▷ ts2 ::: U) ->
  P * xi : (or _ _ T1 T2) @ xs ⊢ ti ▷ either (fun _ => ts1) (fun _ => ts2) xs ::: U.
Proof.
  intros. destruct xs; simpl; auto.
Qed.

Notation "'ex' ( x 'uhh' A ) T" := (existsPT _ _ (As:=A) (fun x => T)) (at level 70).

Lemma ExI (A B : Type) (xi : A) xs ys (F : forall (a : A), PermType Si Ss A B) :
  xi : F ys @ xs ⊑ xi : ex (z uhh A) (F z) @ existT _ ys xs.
Proof. reflexivity. Qed.

Lemma ExE (A B : Type) (xi : A) xs (F : forall (a : A), PermType Si Ss A B) :
  xi : ex (z uhh A) (F z) @ xs ⊑ xi : F (projT1 xs) @ (projT2 xs).
Proof. reflexivity. Qed.
