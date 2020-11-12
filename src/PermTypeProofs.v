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

From Paco Require Import
     paco.

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

Lemma frame (A B : Type) (P1 P2 : Perms) ti ts (T : PermType Si Ss A B) :
  P1 ⊢ ti ▷ ts ::: T ->
  (P1 * P2) ⊢ ti ▷ ts ::: (T ∅ P2).
Proof. apply typing_frame. Qed.

Lemma PermsI (A B : Type) (P : Perms) xi xs (T : PermType Si Ss A B) :
  xi : T @ xs * P ⊑ xi : T ∅ P @ xs.
Proof. reflexivity. Qed.

Lemma PermsE (A B : Type) (P : Perms) xi xs (T : PermType Si Ss A B) :
  xi : T ∅ P @ xs ⊑ xi : T @ xs * P.
Proof. reflexivity. Qed.

Lemma Cast (A B : Type) (P : PermType Si Ss A B) xi yi xs ys :
  xi : P @ ys ⊑ xi : eqp _ _ yi @ xs * yi : P @ ys.
Proof.
  repeat intro. destruct H as (e & p' & Heq & Hp & Hlte).
  simpl in Heq. subst.
  eapply Perms_upwards_closed; eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
Qed.

Lemma EqDup (A : Type) (xi yi : A) :
  xi : eqp Si Ss yi @ tt * xi : eqp _ _ yi @ tt ⊑ xi : eqp _ _ yi @ tt.
Proof.
  repeat intro. simpl in *. subst. exists bottom_perm, bottom_perm.
  split; [| split]; auto. rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom.
Qed.

Lemma EqTrans (A : Type) (xi yi zi : A) :
    xi : eqp Si Ss zi @ tt ⊑ xi : eqp _ _ yi @ tt * yi : eqp _ _ zi @ tt.
Proof.
  repeat intro. destruct H as (? & ? & ? & ? & ?). simpl in *; subst. reflexivity.
Qed.

Lemma EqCtx (A B : Type) (xi yi : A) (f : A -> B) :
  f xi : eqp Si Ss (f yi) @ tt ⊑ xi : eqp _ _ yi @ tt.
Proof.
  repeat intro. simpl in *. congruence.
Qed.

Lemma EqSym (A : Type) (xi yi : A) :
  yi : eqp Si Ss xi @ tt ⊑ xi : eqp _ _ yi @ tt.
Proof.
  repeat intro; simpl in *; subst; reflexivity.
Qed.

Lemma Weak (A B : Type) P1 P2 (U1 U2 : PermType Si Ss A B) ts ti :
  P2 ⊑ P1 ->
  (forall xi xs, xi : U1 @ xs ⊑ xi : U2 @ xs) ->
  P2 ⊢ ts ▷ ti ::: U2 ->
  P1 ⊢ ts ▷ ti ::: U1.
Proof.
  intros. eapply typing_lte; eauto.
Qed.

(* TODO name conflicts with ITree Ret *)
Lemma Ret_ (A B : Type) xi xs (T : PermType Si Ss A B) :
  xi : T @ xs ⊢ Ret xi ▷ Ret xs ::: T.
Proof.
  repeat intro. pstep. constructor; auto.
Qed.

Lemma Bind (A B C : Type) P ti ts fi fs (T : PermType Si Ss A B) (U : PermType Si Ss B C) :
  P ⊢ ti ▷ ts ::: T ->
  (forall xi xs, xi : T @ xs ⊢ fi xi ▷ fs xs ::: U) ->
  P ⊢ ITree.bind ti fi ▷ ITree.bind ts fs ::: U.
Proof.
  intros. eapply typing_bind; eauto.
Qed.

Lemma GetNum xi yi :
  xi : eqp Si Ss (VNum yi) @ tt ⊢ getNum xi ▷ Ret tt ::: eqp _ _ yi.
Proof.
  repeat intro. simpl in *. subst. simpl. pstep. constructor; auto. reflexivity.
Qed.

Lemma Err (A B : Type) P (U : PermType Ss Si A B) :
  P ⊢ throw tt ▷ throw tt ::: U.
Proof.
  repeat intro. pstep. constructor.
Qed.

Lemma If (A B : Type) P ti1 ti2 ts1 ts2 (xi yi : bool) xs (U : PermType Ss Si A B) :
  P ⊢ ti1 ▷ ts1 ::: U ->
  P ⊢ ti2 ▷ ts2 ::: U ->
  P * xi : eqp _ _ yi @ xs ⊢ if xi then ti1 else ti2 ▷ if yi then ts1 else ts2 ::: U.
Proof.
  repeat intro. destruct H1 as (? & ? & ? & ? & ?); simpl in *; subst.
  destruct xi.
  - apply H; auto. eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
  - apply H0; auto. eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.
