From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Arith.Compare_dec
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

Context (Si' Ss:Type).
Definition Si := prod config Si'.

Program Definition lens_config' : Lens Si config :=
  {|
  lget := fst;
  lput p c := (c, snd p);
  |}.
Next Obligation.
  destruct a; auto.
Qed.
Instance lens_config : Lens Si config := lens_config'.

Lemma TrueI (A : Type) P (xi : A) :
  P * xi : trueP Si Ss @ tt ⊑ P.
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

Lemma ExI (A B C : Type) (xi : A) (xs : C) ys (F : forall (b : B), PermType Si Ss A C) :
  xi : ex (z uhh B) (F z) @ existT _ ys xs ⊑ xi : F ys @ xs.
Proof. reflexivity. Qed.

Lemma ExE (A B C : Type) (xi : A) (xs : sigT (fun b : B => C)) (F : forall (b : B), PermType Si Ss A C) :
   xi : F (projT1 xs) @ (projT2 xs) ⊑ xi : ex (z uhh B) (F z) @ xs.
Proof. reflexivity. Qed.

Lemma Frame (A B : Type) (P1 P2 : Perms) ti ts (T : PermType Si Ss A B) :
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

Lemma EqRefl A P (xi : A) :
  P * xi : eqp Si Ss xi @ tt ⊑ P.
Proof.
  repeat intro.
  exists p, bottom_perm. split; [| split]; simpl; eauto. rewrite sep_conj_perm_bottom. reflexivity.
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

Lemma Bind (A B C D : Type) P ti ts fi fs (T : PermType Si Ss A B) (U : PermType Si Ss C D) :
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

Lemma Err (A B : Type) P (U : PermType Si Ss A B) :
  P ⊢ throw tt ▷ throw tt ::: U.
Proof.
  repeat intro. pstep. constructor.
Qed.

Lemma If (A B : Type) P ti1 ti2 ts1 ts2 (xi yi : bool) xs (U : PermType Si Ss A B) :
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

Lemma Iter (A B C D : Type) (T : PermType Si Ss C D) xi xs fi fs (U : PermType Si Ss A B) :
  (forall yi ys, yi : T @ ys ⊢ fi yi ▷ fs ys ::: T +T+ U) ->
  xi : T @ xs ⊢ iter fi xi ▷ iter fs xs ::: U.
Proof.
Abort.

Definition ex1i xi : itree (sceE Si) Value :=
  x <- getNum xi;;
  Ret (VNum (Init.Nat.mul 5 x)).

Definition ex1s (xs : sigT (fun _ : nat => unit)) : itree (sceE Ss) (sigT (fun _ : nat => unit)) :=
  x <- Ret tt;;
  Ret (existT _ (Init.Nat.mul 5 (projT1 xs)) tt).

Definition IsNat : VPermType Si Ss (sigT (fun _ : nat => unit)) :=
  ex (n uhh nat) eqp Si Ss (VNum n).

Lemma ex1_typing xi xs :
  xi : IsNat @ xs ⊢ ex1i xi ▷ ex1s xs ::: IsNat.
Proof.
  (* ExE *)
  unfold IsNat. eapply Weak; [eapply ExE | reflexivity |].
  (* Bind *)
  unfold ex1s, ex1i. eapply Bind.
  (* GetNum *)
  apply GetNum.
  (* EqCtx *)
  intros yi []. clear xi.
  eapply Weak; [apply EqCtx with (f := fun x => VNum (Init.Nat.mul 5 x)) | reflexivity |].
  (* ExI *)
  eapply Weak. apply ExI with (F := fun n : nat => eqp Si Ss (VNum n)). reflexivity. fold IsNat.
  (* Ret *)
  apply Ret_.
Qed.

Lemma PtrI A xi yi xs ys rw o (T : VPermType Si Ss A) :
  xi : ptr _ _ (rw, o, T) @ ys ⊑ xi : ptr _ _ (rw, o, eqp Si Ss yi) @ xs * yi : T @ ys.
Proof.
  destruct xi; simpl.
  - rewrite sep_conj_Perms_top_absorb. reflexivity.
  - repeat intro. destruct a. rename p into p'.
    destruct H as (p & t & (P & (v & ?) & Hp) & Hp' & Hlte). subst.
    destruct Hp as (? & ? & ? & ? & ?). simpl in *. subst.
    eexists. split; [exists v; reflexivity |].
    eapply Perms_upwards_closed; eauto.
    do 2 eexists. split; [| split]; eauto.
    apply sep_conj_perm_monotone; intuition.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma ReadDup o xi yi xs:
  xi : ptr _ _ (R, o, eqp Si Ss yi) @ xs * xi : ptr _ _ (R, o, eqp _ _ yi) @ xs ⊑
  xi : ptr _ _ (R, o, eqp _ _ yi) @ xs.
Proof.
  repeat intro. simpl in *. destruct xi; [contradiction |].
  destruct a as [b o']. unfold offset in *.
  destruct H as (? & (v & ?) & ?). subst.
  exists (read_perm (b, o' + o) v), (read_perm (b, o' + o) v).
  destruct H0 as (pread & peq & Hpread & Hpeq & Hlte).
  simpl in Hpread, Hpeq. subst.
  assert (read_perm (b, o' + o) v ∈ ptr_Perms _ _ R (VPtr (b, o' + o)) xs (eqp Si Ss v)).
  {
    eexists. split; eauto. simpl in *. exists (read_perm (b, o' + o) v), bottom_perm.
    split; [| split]. 2: reflexivity.
    - split; intros; auto.
    - rewrite sep_conj_perm_bottom. reflexivity.
  }
  split; [| split]; auto.
  constructor; intros; eauto.
  - split; [| split]; auto. 1, 2: apply Hpread; apply Hlte; auto.
    split; intros; auto; destruct x0, y; simpl in H1; subst; reflexivity.
  - split; apply Hpread; apply Hlte; auto.
  - apply Hlte. constructor. left. apply Hpread. induction H0; auto.
    + destruct H0; auto.
    + etransitivity; eauto.
Qed.

Lemma PtrOff A xi xs rw o1 o2 (T : VPermType Si Ss A) :
  o1 >= o2 ->
  offset xi o2 : ptr _ _ (rw, o1 - o2, T) @ xs ⊑ xi : ptr _ _ (rw, o1, T) @ xs.
Proof.
  destruct xi; [reflexivity | destruct a].
  intros. simpl. rewrite <- Nat.add_assoc. rewrite (Minus.le_plus_minus_r _ _ H).
  reflexivity.
Qed.

Lemma PtrE A B C (P : Perms) rw o (T : VPermType Si Ss A) (xi yi : Value) xs ti ts (U : PermType Si Ss B C) :
  (forall yi, P * xi : ptr _ _ (rw, o, eqp Si Ss yi) @ tt * yi : T @ xs ⊢ ti ▷ ts ::: U) ->
  P * xi : ptr _ _ (rw, o, T) @ xs ⊢ ti ▷ ts ::: U.
Proof.
  repeat intro. rename p into p''. destruct H0 as (p & p' & Hp & Hptr & Hlte).
  destruct xi; [contradiction | destruct a].
  destruct Hptr as (? & (? & ?) & ?). subst.
  destruct H2 as (pptr & pt & Hptr & Hpt & Hlte').
  eapply H; eauto. exists (p ** pptr), pt.
  split; [| split]; eauto.
  - do 2 eexists. split; [| split]; eauto. 2: reflexivity. eexists.
    split; eauto.
    do 2 eexists. split; [| split]; eauto. reflexivity. apply sep_conj_perm_bottom'.
  - etransitivity; eauto. rewrite sep_conj_perm_assoc.
    apply sep_conj_perm_monotone; auto; reflexivity.
Qed.

Lemma Load xi yi xs rw :
  xi : ptr _ _ (rw, 0, eqp Si Ss yi) @ xs ⊢
  load xi ▷
  Ret tt :::
  eqp _ _ yi ∅ xi : ptr _ _ (rw, 0, eqp _ _ yi) @ xs.
Proof.
  repeat intro. pstep. unfold load. rewritebisim @bind_trigger.
  econstructor; eauto; try reflexivity.
  destruct xi as [? | [b o]]; try contradiction.
  simpl in H. unfold ptr_Perms in H.
  destruct H as (? & (v & ?) & ?); subst.
  destruct H1 as (? & ? & ? & ? & ?). simpl in H, H1. subst.
  assert (read (lget c1) (b, o) = Some v).
  {
    apply H2 in H0. destruct H0 as (? & _). apply H in H0.
    rewrite Nat.add_0_r in H0. destruct rw; auto.
  }
  rewrite H1. constructor; auto.
  (* TODO: these exists are kind of weird *)
  simpl. exists bottom_perm, x. split; [| split]; eauto. eexists. split; eauto.
  simpl. exists x, bottom_perm. split; [| split]; eauto.
  rewrite sep_conj_perm_bottom. reflexivity.
  rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom.
  etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma Store A xi yi xs (P : VPermType Si Ss A) :
  xi : ptr _ _ (W, 0, P) @ xs ⊢
  store xi yi ▷
  Ret tt :::
  (trueP Si Ss) ∅ xi : ptr _ _ (W, 0, eqp _ _ yi) @ tt.
Proof.
  repeat intro. pstep. unfold store. destruct xi as [| [b o]]; try contradiction.
  rewritebisim @bind_trigger.
  rename p into p'. rename H0 into Hpre.
  destruct H as (? & (v & ?) & Hwrite); subst.
  destruct Hwrite as (pw & p & Hwritelte & Hp & Hlte).
  rewrite Nat.add_0_r in Hwritelte.
  assert (exists val, read (lget c1) (b, o) = Some val).
  {
    apply Hlte in Hpre. destruct Hpre as (Hpre & _).
    apply Hwritelte in Hpre. eexists.
    apply Hpre.
  }
  destruct H as (val & Hread). eapply (read_success_write _ _ _ yi) in Hread.
  destruct Hread as (c' & Hwrite).
  assert (Hguar : guar p' (c1, c2) ((lput c1 c'), c2)).
  {
    apply Hlte. constructor 1. left. apply Hwritelte. simpl.
    split; [| split].
    + eapply write_success_other_ptr; eauto.
    + eapply write_success_allocation; eauto.
    + eapply write_success_others; eauto.
  }
  econstructor; eauto.
  3: {
    rewrite Hwrite. constructor; eauto.
    2: { simpl. exists bottom_perm. eexists. split; [| split]; auto.
         - eexists. split; eauto. simpl. eexists. exists bottom_perm.
           split; [| split]; eauto; try reflexivity.
         - rewrite sep_conj_perm_bottom. rewrite sep_conj_perm_commut.
           rewrite sep_conj_perm_bottom. reflexivity.
    }
    rewrite Nat.add_0_r. eapply write_read; rewrite lGetPut; eauto.
  }
  - rewrite Hwrite. auto.
  - rewrite Nat.add_0_r. eapply sep_step_lte; eauto.
    etransitivity.
    + eapply sep_step_lte; [| reflexivity]. apply lte_l_sep_conj_perm.
    + simpl in *. eapply sep_step_lte; eauto. intros ? []. constructor; auto.
Qed.

Definition ex2i xi yi : itree (sceE Si) Si :=
  x <- load xi;;
  store yi x.

Definition ex2s : itree (sceE Ss) unit :=
  Ret tt ;;
  Ret tt.

Lemma ex2_typing A (xi yi : Value) xs (T : VPermType Si Ss A) :
  xi : ptr _ _ (R, 0, T) @ xs * yi : ptr Si Ss (W, 0, trueP _ _) @ tt ⊢
  ex2i xi yi ▷
  ex2s :::
  (trueP _ _) ∅ yi : ptr _ _ (W, 0, T) @ xs ∅ xi : ptr _ _ (R, 0, trueP _ _) @ tt.
Proof.
  rewrite sep_conj_Perms_commut.
  eapply PtrE; eauto.
  intros zi. eapply Bind.
  - apply Frame. rewrite sep_conj_Perms_commut. apply Frame. apply Load.
  - intros wi [].
    eapply Weak with (P2 := yi : ptr _ _ (W, 0, trueP _ _) @ tt *
                            wi : T @ xs *
                            xi : ptr _ _ (R, 0, trueP _ _) @ tt)
                     (U2 := trueP _ _ ∅
                            yi : ptr _ _ (W, 0, eqp _ _ wi) @ tt ∅
                            wi : T @ xs ∅
                            xi : ptr _ _ (R, 0, trueP _ _) @ tt).

    + etransitivity.
      2: {
        etransitivity; [| apply PermsI]. rewrite sep_conj_Perms_commut.
        eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
        etransitivity; [| apply PermsI]. rewrite sep_conj_Perms_commut.
        eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
        etransitivity; [| apply PermsI]. rewrite sep_conj_Perms_commut. reflexivity.
      }
      rewrite (sep_conj_Perms_commut (zi : T @ xs) _).
      repeat rewrite <- sep_conj_Perms_assoc.
      apply sep_conj_Perms_monotone; [reflexivity |].
      rewrite sep_conj_Perms_commut.
      eapply sep_conj_Perms_monotone.
      * etransitivity; [apply PtrI | apply TrueI]. (* Weakening the content type *)
      * apply Cast.
    + intros ? [].
      etransitivity; [| apply PermsI]. rewrite sep_conj_Perms_commut.
      etransitivity; [apply PermsE |]. rewrite sep_conj_Perms_commut.
      eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
      etransitivity; [| apply PermsI].
      etransitivity; [apply PermsE |].
      etransitivity.
      2: {
        eapply sep_conj_Perms_monotone; [| reflexivity]. (* frame *)
        apply PermsI.
      }
      rewrite <- sep_conj_Perms_assoc.
      eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
      apply PtrI.
    + apply Frame. apply Frame. apply Store.
Qed.

Lemma IsNull1 A xi xs rw o (P : VPermType Si Ss A) :
  xi : ptr _ _ (rw, o, P) @ xs ⊢
  isNull xi ▷
  Ret tt :::
  eqp _ _ false ∅ xi : ptr _ _ (rw, o, P) @ xs.
Proof.
  repeat intro. pstep. unfold isNull. destruct xi; [contradiction |].
  destruct a as [b o']. simpl. constructor; auto.
  simpl. exists bottom_perm, p. split; [| split]; eauto.
  rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
Qed.

Lemma IsNull2 xi:
  xi : eqp Si Ss (VNum 0) @ tt ⊢
  isNull xi ▷
  Ret tt :::
  eqp _ _ true.
Proof.
  repeat intro. pstep. simpl in *. subst. constructor; simpl; auto.
Qed.

Lemma ArrPtr A xi xs rw o (P : VPermType Si Ss A) :
  xi : ptr _ _ (rw, o, P) @ Vector.hd xs ⊑ xi : arr (rw, o, 1, P) @ xs.
Proof.
  simpl. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Lemma PtrArr A xi xs rw o (P : VPermType Si Ss A) :
  xi : arr (rw, o, 1, P) @ vsingle xs ⊑ xi : ptr _ _ (rw, o, P) @ xs.
Proof.
  simpl. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Fixpoint trySplitPure {A} l1 (v:Vector.t A l1) : forall l2, option (Vector.t A l2 * Vector.t A (l1 - l2)).
Proof.
  induction v; intros; destruct l2.
  - apply Some; split; apply Vector.nil.
  - apply None.
  - apply Some; split; [ apply Vector.nil | apply Vector.cons; assumption ].
  - destruct (IHv l2) as [ [v1 v2] | ].
    + apply Some; split; [ apply Vector.cons; assumption | assumption ].
    + apply None.
Defined.

(*
Definition trySplit {A l1 R S} (v : Vector.t A l1) l2 (f : Vector.t A l2 -> Vector.t A (l1 - l2) -> itree (sceE S) R) : itree (sceE S) R.
  destruct (le_lt_dec l2 l1).
  - apply Minus.le_plus_minus in l. rewrite l in v.
    pose proof (Vector.splitat l2 v).
    apply (f (fst X) (snd X)).
  - apply (throw tt).
Defined.
Print trySplit.
*)

Definition trySplit {A l1 R S} (v : Vector.t A l1) l2 (f : Vector.t A l2 -> Vector.t A (l1 - l2) -> itree (sceE S) R) : itree (sceE S) R :=
  match trySplitPure _ v l2 with
  | Some (v1,v2) => f v1 v2
  | None => throw tt
  end.

Arguments trySplitPure {_} _ !v l2.

Lemma trySplitPureNone A l1 v l2: l1 < l2 -> @trySplitPure A l1 v l2 = None.
Admitted.

Lemma trySplitPureSome A l1 v l2:
  le l2 l1 ->
  exists v1 v2, @trySplitPure A l1 v l2 = Some (v1, v2).
Admitted.

Lemma ArrCombine_eq A xi rw o l1 l2 xs1 xs2 (P : VPermType Si Ss A) :
  eq_Perms (xi : arr (rw, o, l1 + l2, P) @ Vector.append xs1 xs2)
           (xi : arr (rw, o, l1, P) @ xs1 * xi : arr (rw, o + l1, l2, P) @ xs2).
Admitted.

(*
Lemma ArrSplit A R1 R2 P l1 l2 xi xs rw o (T : VPermType Si Ss A) U (ti : itree (sceE Si) R1) (fs : _ -> _ -> itree (sceE Ss) R2) :
  (forall xs1 xs2, P *
              xi : arr (rw, o, l2, T) @ xs1 *
              xi : arr (rw, o + l2, l1 - l2, T) @ xs2 ⊢
              ti ▷ fs xs1 xs2 ::: U) ->
  P * xi : arr (rw, o, l1, T) @ xs ⊢ ti ▷ trySplit xs l2 fs ::: U.
Proof.
  intros. unfold trySplit. destruct (le_lt_dec l2 l1).
  - destruct (trySplitPureSome _ l1 xs l2 l) as [ v1 [v2 e] ]. rewrite e.
    apply H.
(* rewrite trySplitPure -> Some (fst (splitat ...), snd (splitat ...)) *) admit.
  - (* rewrite trySplitPure -> None *) admit.
  rewrite (ArrCombine_eq)

revert o l2 fs H. unfold trySplit. induction xs; destruct l2; intros.
  - simpl. admit.
  - repeat intro; pstep; constructor.
  - simpl. destruct (trySplitPure n xs 0).
    + apply H.

destruct (le_lt_dec l2 l1). 2: repeat intro; pstep; constructor.
  assert ()
  induction l2.
  - simpl in *.
    setoid_rewrite <- sep_conj_Perms_assoc in H.
    setoid_rewrite sep_conj_Perms_bottom_identity in H.
    rewrite Nat.add_0_r in H. repeat intro. apply H; auto.
    destruct H0 as (? & ? & ? & ? & ?).
    exists x, x0. split; [| split]; auto. simpl.
    (* rewrite Nat.sub_0_r at 1. *)
    (* rewrite <- Eqdep.EqdepTheory.eq_rect_eq. *)
    admit.
  - simpl.
Abort.
*)

Lemma vector_tl_append A n m (v1 : Vector.t A (S n)) (v2 : Vector.t A m) :
  Vector.tl (Vector.append v1 v2) = Vector.append (Vector.tl v1) v2.
Proof.
  revert v1. revert n. apply Vector.caseS. intros; auto.
Qed.

Lemma vector_hd_append A n m (v1 : Vector.t A (S n)) (v2 : Vector.t A m) :
  Vector.hd (Vector.append v1 v2) = Vector.hd v1.
Proof.
  revert v1. revert n. apply Vector.caseS. intros; auto.
Qed.

Lemma ArrCombine A xi rw o l1 l2 xs1 xs2 (P : VPermType Si Ss A) :
  xi : arr (rw, o, l1 + l2, P) @ Vector.append xs1 xs2 ⊑
  xi : arr (rw, o, l1, P) @ xs1 * xi : arr (rw, o + l1, l2, P) @ xs2.
Proof.
  repeat intro. destruct H as (p1 & p2 & Hp1 & Hp2 & Hlte).
  revert Hp1 Hp2. revert o xi l2 xs2. revert Hlte. revert p p1 p2. induction l1; intros.
  - rewrite Nat.add_0_r in Hp2. simpl in *. revert xs1. apply Vector.case0. simpl.
    eapply Perms_upwards_closed; eauto. etransitivity; [apply lte_r_sep_conj_perm |]; eauto.
  - simpl. destruct Hp1 as (? & ? & ? & ? & ?).
    do 2 eexists. split; [| split].
    + rewrite vector_hd_append. apply H.
    + rewrite vector_tl_append. eapply IHl1. reflexivity.
      * eapply Perms_upwards_closed; eauto. reflexivity.
      * simpl. rewrite <- plus_n_Sm in Hp2. eauto.
    + rewrite <- sep_conj_perm_assoc. etransitivity; eauto.
      apply sep_conj_perm_monotone; eauto; reflexivity.
Qed.
