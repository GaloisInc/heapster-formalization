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
     SepStep
     Typing
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

Lemma ProdI (A1 A2 B1 B2 : Type) xi yi xs ys (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi :: T1 ▷ xs * yi :: T2 ▷ ys ⊨ (xi, yi) :: T1 *T* T2 ▷ (xs, ys).
Proof. reflexivity. Qed.

Lemma ProdE (A1 A2 B1 B2 : Type) xi xs (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi :: T1 *T* T2 ▷ xs ⊨ fst xi :: T1 ▷ fst xs * snd xi :: T2 ▷ snd xs.
Proof. reflexivity. Qed.

Lemma SumI1 (A1 A2 B1 B2 : Type) (xi : A1) (xs : B1) (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi :: T1 ▷ xs ⊨ inl xi :: T1 +T+ T2 ▷ inl xs.
Proof. reflexivity. Qed.

Lemma SumI2 (A1 A2 B1 B2 : Type) (xi : A2) (xs : B2) (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) :
  xi :: T2 ▷ xs ⊨ inr xi :: T1 +T+ T2 ▷ inr xs.
Proof. reflexivity. Qed.

Lemma SumE (A1 A2 B1 B2 R1 R2 : Type)
      (xi : A1 + A2) (xs : B1 + B2) ti1 ti2 ts1 ts2
      (T1 : PermType Si Ss A1 B1) (T2 : PermType Si Ss A2 B2) (P : Perms) (U : PermType Si Ss (A1 + A2) (B1 + B2)) :
  (forall yi ys, P * yi :: T1 ▷ ys ⊢ ti1 yi ⤳ ts1 ys ::: U) ->
  (forall yi ys, P * yi :: T2 ▷ ys ⊢ ti2 yi ⤳ ts2 ys ::: U) ->
  P * xi :: T1 +T+ T2 ▷ xs ⊢ sum_rect _ ti1 ti2 xi ⤳ sum_rect _ ts1 ts2 xs ::: U.
Proof.
  intros. simpl.
  destruct xi, xs; simpl; auto;
    rewrite sep_conj_Perms_commut; rewrite sep_conj_Perms_top_absorb; apply typing_top.
Qed.

Lemma StarI (A B1 B2 : Type) xi xs ys (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi :: T1 ▷ xs * xi :: T2 ▷ ys ⊨ xi :: starPT _ _ T1 T2 ▷ (xs, ys).
Proof. reflexivity. Qed.

Lemma StarE (A B1 B2 : Type) xi xs (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi :: starPT _ _ T1 T2 ▷ xs ⊨ xi :: T1 ▷ fst xs * xi :: T2 ▷ snd xs.
Proof. reflexivity. Qed.

Lemma PermsI (A B : Type) (P : Perms) xi xs (T : PermType Si Ss A B) :
  xi :: T ▷ xs * P ⊨ xi :: T ∅ P ▷ xs.
Proof. reflexivity. Qed.

Lemma PermsE (A B : Type) (P : Perms) xi xs (T : PermType Si Ss A B) :
  xi :: T ∅ P ▷ xs ⊨ xi :: T ▷ xs * P.
Proof. reflexivity. Qed.

Lemma Frame (A B : Type) (P1 P2 : Perms) ti ts (T : PermType Si Ss A B) :
  P1 ⊢ ti ⤳ ts ::: T ->
  P1 * P2 ⊢ ti ⤳ ts ::: T ∅ P2.
Proof. apply typing_frame. Qed.

Lemma OrI1 (A B1 B2 : Type) xi xs (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi :: T1 ▷ xs ⊨ xi :: or _ _ T1 T2 ▷ inl xs.
Proof. reflexivity. Qed.

Lemma OrI2 (A B1 B2 : Type) xi xs (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) :
  xi :: T2 ▷ xs ⊨ xi :: or _ _ T1 T2 ▷ inr xs.
Proof. reflexivity. Qed.

Lemma OrE (A B1 B2 C1 C2 D : Type)
      (xi : A) (xs : B1 + B2) ti ts1 ts2
      (T1 : PermType Si Ss A B1) (T2 : PermType Si Ss A B2) (P : Perms) (U : PermType Si Ss D (C1 + C2)) :
  (forall ys, P * xi :: T1 ▷ ys ⊢ ti ⤳ ts1 ys ::: U) ->
  (forall ys, P * xi :: T2 ▷ ys ⊢ ti ⤳ ts2 ys ::: U) ->
  P * xi :: or _ _ T1 T2 ▷ xs ⊢ ti ⤳ sum_rect _ ts1 ts2 xs ::: U.
Proof.
  intros. destruct xs; simpl; auto.
Qed.

Lemma TrueI (A : Type) P (xi : A) :
  P ⊨ P * xi :: trueP Si Ss ▷ tt.
Proof.
  simpl. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Lemma ExI (A B : Type) (C : B -> Type) (xi : A) (ys : B) (xs : C ys) (F : forall (b : B), PermType Si Ss A (C b)) :
  xi :: F ys ▷ xs ⊨ xi :: ex (z oftype B) (F z) ▷ existT (fun b : B => C b) ys xs.
Proof. reflexivity. Qed.

Lemma ExE (A B : Type) (C : B -> Type) (xi : A) (xs : sigT (fun b : B => C b)) (F : forall (b : B), PermType Si Ss A (C b)) :
  xi :: ex (z oftype B) (F z) ▷ xs ⊨ xi :: F (projT1 xs) ▷ (projT2 xs).
Proof. reflexivity. Qed.

(***********************************************************************)

Lemma EqRefl A P (xi : A) :
  P ⊨ P * xi :: eqp Si Ss xi ▷ tt.
Proof.
  repeat intro.
  exists p, bottom_perm. split; [| split]; simpl; eauto. rewrite sep_conj_perm_bottom. reflexivity.
Qed.

Lemma EqSym (A : Type) (xi yi : A) :
  xi :: eqp Si Ss yi ▷ tt ⊨ yi :: eqp _ _ xi ▷ tt.
Proof.
  repeat intro; simpl in *; subst; reflexivity.
Qed.

Lemma EqTrans (A : Type) (xi yi zi : A) :
   xi :: eqp _ _ yi ▷ tt * yi :: eqp _ _ zi ▷ tt ⊨ xi :: eqp Si Ss zi ▷ tt.
Proof.
  repeat intro. destruct H as (? & ? & ? & ? & ?). simpl in *; subst. reflexivity.
Qed.

Lemma EqCtx (A B : Type) (xi yi : A) (f : A -> B) :
  xi :: eqp _ _ yi ▷ tt ⊨ f xi :: eqp Si Ss (f yi) ▷ tt.
Proof.
  repeat intro. simpl in *. congruence.
Qed.

Lemma EqDup (A : Type) (xi yi : A) :
  xi :: eqp _ _ yi ▷ tt ⊨ xi :: eqp Si Ss yi ▷ tt * xi :: eqp _ _ yi ▷ tt.
Proof.
  repeat intro. simpl in *. subst. exists bottom_perm, bottom_perm.
  split; [| split]; auto. rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom.
Qed.

Lemma Cast (A B : Type) (P : PermType Si Ss A B) xi yi xs ys :
  xi :: eqp _ _ yi ▷ xs * yi :: P ▷ ys ⊨ xi :: P ▷ ys.
Proof.
  repeat intro. destruct H as (e & p' & Heq & Hp & Hlte).
  simpl in Heq. subst.
  eapply Perms_upwards_closed; eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
Qed.

(***********************************************************************)


(* TODO name conflicts with ITree Ret *)
Lemma Ret_ (A B : Type) xi xs (T : PermType Si Ss A B) :
  xi :: T ▷ xs ⊢ Ret xi ⤳ Ret xs ::: T.
Proof.
  repeat intro. pstep. constructor; auto.
Qed.

Lemma Bind (A B C D : Type) P ti ts fi fs (T : PermType Si Ss A B) (U : PermType Si Ss C D) :
  P ⊢ ti ⤳ ts ::: T ->
  (forall xi xs, xi :: T ▷ xs ⊢ fi xi ⤳ fs xs ::: U) ->
  P ⊢ ITree.bind ti fi ⤳ ITree.bind ts fs ::: U.
Proof.
  intros. eapply typing_bind; eauto.
Qed.

Lemma GetNum xi yi :
  xi :: eqp Si Ss (VNum yi) ▷ tt ⊢ getNum xi ⤳ Ret tt ::: eqp _ _ yi.
Proof.
  repeat intro. simpl in *. subst. simpl. pstep. constructor; auto. reflexivity.
Qed.

Lemma Iter (A B C D : Type) (T : PermType Si Ss C D) xi xs fi fs (U : PermType Si Ss A B) :
  (forall yi ys, yi :: T ▷ ys ⊢ fi yi ⤳ fs ys ::: T +T+ U) ->
  xi :: T ▷ xs ⊢ iter fi xi ⤳ iter fs xs ::: U.
Proof.
  revert xi xs fi fs U. pcofix CIH. intros.
  do 2 rewritebisim @unfold_iter_ktree.
  eapply sbuter_bind; eauto.
  - apply H0; auto.
  - simpl. intros. destruct r1, r2; try contradiction.
    + repeat intro. pstep. constructor 5; eauto.
    + pstep. constructor; auto.
Qed.

Lemma If (A B : Type) P ti1 ti2 ts1 ts2 (xi yi : bool) xs (U : PermType Si Ss A B) :
  P ⊢ ti1 ⤳ ts1 ::: U ->
  P ⊢ ti2 ⤳ ts2 ::: U ->
  P * xi :: eqp _ _ yi ▷ xs ⊢ if xi then ti1 else ti2 ⤳ if yi then ts1 else ts2 ::: U.
Proof.
  repeat intro. destruct H1 as (? & ? & ? & ? & ?); simpl in *; subst.
  destruct xi.
  - apply H; auto. eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
  - apply H0; auto. eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_l_sep_conj_perm.
Qed.

Lemma Err (A B : Type) P (U : PermType Si Ss A B) t :
  P ⊢ t ⤳ throw tt ::: U.
Proof.
  repeat intro. pstep. constructor.
Qed.

Lemma Weak (A B : Type) P1 P2 (U1 U2 : PermType Si Ss A B) ts ti :
  P1 ⊨ P2 ->
  (forall xi xs, xi :: U2 ▷ xs ⊨ xi :: U1 ▷ xs) ->
  P2 ⊢ ts ⤳ ti ::: U2 ->
  P1 ⊢ ts ⤳ ti ::: U1.
Proof.
  intros. eapply typing_lte; eauto.
Qed.

(***********************************************************************)

Definition ex1i xi : itree (sceE Si) Value :=
  x <- getNum xi;;
  Ret (VNum (Init.Nat.mul 5 x)).

Definition ex1s (xs : sigT (fun _ : nat => unit)) : itree (sceE Ss) (sigT (fun _ : nat => unit)) :=
  Ret tt;;
  Ret (existT _ (Init.Nat.mul 5 (projT1 xs)) tt).

Definition IsNat : VPermType Si Ss (sigT (fun _ : nat => unit)) :=
  ex (n oftype nat) eqp Si Ss (VNum n).

Lemma ex1_typing xi xs :
  xi :: IsNat ▷ xs ⊢ ex1i xi ⤳ ex1s xs ::: IsNat.
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
  eapply Weak; [apply ExI with (F := fun n : nat => eqp Si Ss (VNum n)) | reflexivity |]; fold IsNat.
  (* Ret *)
  apply Ret_.
Qed.

(***********************************************************************)

Lemma PtrI A xi yi xs ys rw o (T : VPermType Si Ss A) :
  xi :: ptr _ _ (rw, o, eqp Si Ss yi) ▷ xs * yi :: T ▷ ys ⊨ xi :: ptr _ _ (rw, o, T) ▷ ys.
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

Lemma PtrE A B C (P : Perms) rw o (T : VPermType Si Ss A) (xi : Value) xs ti ts (U : PermType Si Ss B C) :
  (forall yi, P * xi :: ptr _ _ (rw, o, eqp Si Ss yi) ▷ tt * yi :: T ▷ xs ⊢ ti ⤳ ts ::: U) ->
  P * xi :: ptr _ _ (rw, o, T) ▷ xs ⊢ ti ⤳ ts ::: U.
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

Lemma ReadDup o xi yi :
  xi :: ptr _ _ (R, o, eqp _ _ yi) ▷ tt ⊨
  xi :: ptr _ _ (R, o, eqp Si Ss yi) ▷ tt * xi :: ptr _ _ (R, o, eqp _ _ yi) ▷ tt.

Proof.
  repeat intro. simpl in *. destruct xi; [contradiction |].
  destruct a as [b o']. unfold offset in *.
  destruct H as (? & (v & ?) & ?). subst.
  exists (read_perm (b, o' + o) v), (read_perm (b, o' + o) v).
  destruct H0 as (pread & peq & Hpread & Hpeq & Hlte).
  simpl in Hpread, Hpeq. subst.
  assert (read_perm (b, o' + o) v ∈ ptr_Perms _ _ R (VPtr (b, o' + o)) tt (eqp Si Ss v)).
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
  xi :: ptr _ _ (rw, o1, T) ▷ xs ⊨ offset xi o2 :: ptr _ _ (rw, o1 - o2, T) ▷ xs.
Proof.
  destruct xi; [reflexivity | destruct a].
  intros. simpl. rewrite <- Nat.add_assoc. rewrite (Minus.le_plus_minus_r _ _ H).
  reflexivity.
Qed.
Lemma PtrOff' A xi xs rw o1 o2 (T : VPermType Si Ss A) :
  o1 >= o2 ->
  offset xi o2 :: ptr _ _ (rw, o1 - o2, T) ▷ xs ⊨ xi :: ptr _ _ (rw, o1, T) ▷ xs.
Proof.
  destruct xi; [reflexivity | destruct a].
  intros. simpl. rewrite <- Nat.add_assoc. rewrite (Minus.le_plus_minus_r _ _ H).
  reflexivity.
Qed.

Lemma Load xi yi xs rw :
  xi :: ptr _ _ (rw, 0, eqp Si Ss yi) ▷ xs ⊢
  load xi ⤳
  Ret tt :::
  eqp _ _ yi ∅ xi :: ptr _ _ (rw, 0, eqp _ _ yi) ▷ xs.
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
  xi :: ptr _ _ (W, 0, P) ▷ xs ⊢
  store xi yi ⤳
  Ret tt :::
  (trueP Si Ss) ∅ xi :: ptr _ _ (W, 0, eqp _ _ yi) ▷ tt.
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
    symmetry. apply Hpre.
  }
  destruct H as (val & Hread). eapply (read_success_write _ _ _ yi) in Hread.
  destruct Hread as (c' & Hwrite).
  assert (Hguar : guar p' (c1, c2) ((lput c1 c'), c2)).
  {
    apply Hlte. constructor 1. left. apply Hwritelte. simpl.
    split; [| split; [| split]].
    + eapply write_success_read; eauto.
    + eapply write_success_sizeof; eauto.
    + eapply write_success_length; eauto.
    + eapply write_success_others; eauto.
  }
  Unshelve. 2, 3, 4: exact Ss.
  econstructor; eauto.
  3: {
    rewrite Hwrite. constructor; eauto.
    2: { simpl. exists bottom_perm. eexists. split; [| split]; auto.
         - eexists. split; eauto. simpl. eexists. exists bottom_perm.
           split; [| split]; eauto; try reflexivity.
         - rewrite sep_conj_perm_bottom. rewrite sep_conj_perm_commut.
           rewrite sep_conj_perm_bottom. reflexivity.
    }
    rewrite Nat.add_0_r. symmetry. eapply write_read; rewrite lGetPut; eauto.
  }
  - rewrite Hwrite. auto.
  - rewrite Nat.add_0_r. eapply sep_step_lte; eauto.
    etransitivity.
    + eapply sep_step_lte; [| reflexivity]. apply lte_l_sep_conj_perm.
    + simpl in *. eapply sep_step_lte; eauto. intros ? []. constructor; auto.
Qed.

Lemma IsNull1 A xi xs rw o (P : VPermType Si Ss A) :
  xi :: ptr _ _ (rw, o, P) ▷ xs ⊢
  isNull xi ⤳
  Ret tt :::
  eqp _ _ false ∅ xi :: ptr _ _ (rw, o, P) ▷ xs.
Proof.
  repeat intro. pstep. unfold isNull. destruct xi; [contradiction |].
  destruct a as [b o']. simpl. constructor; auto.
  simpl. exists bottom_perm, p. split; [| split]; eauto.
  rewrite sep_conj_perm_commut. rewrite sep_conj_perm_bottom. reflexivity.
Qed.

Lemma IsNull2 xi:
  xi :: eqp Si Ss (VNum 0) ▷ tt ⊢
  isNull xi ⤳
  Ret tt :::
  eqp _ _ true.
Proof.
  repeat intro. pstep. simpl in *. subst. constructor; simpl; auto.
Qed.

(***********************************************************************)

Definition ex2i xi yi : itree (sceE Si) Si :=
  x <- load xi;;
  store yi x.

Definition ex2s : itree (sceE Ss) unit :=
  Ret tt ;;
  Ret tt.

Lemma ex2_typing A (xi yi : Value) xs (T : VPermType Si Ss A) :
  xi :: ptr _ _ (R, 0, T) ▷ xs * yi :: ptr Si Ss (W, 0, trueP _ _) ▷ tt ⊢
  ex2i xi yi ⤳
  ex2s :::
  (trueP _ _) ∅ yi :: ptr _ _ (W, 0, T) ▷ xs ∅ xi :: ptr _ _ (R, 0, trueP _ _) ▷ tt.
Proof.
  (* PtrE *)

  rewrite sep_conj_Perms_commut.
  eapply PtrE; eauto; intros zi.
  (* Bind *)
  eapply Bind.
  (* L: Frame and Load *)
  apply Frame. rewrite sep_conj_Perms_commut. apply Frame. apply Load.
  (* Weak *)
  intros wi [].
  eapply Weak with (P2 := yi :: ptr _ _ (W, 0, trueP _ _) ▷ tt *
                          wi :: T ▷ xs *
                          xi :: ptr _ _ (R, 0, trueP _ _) ▷ tt)
                   (U2 := trueP _ _ ∅
                          yi :: ptr _ _ (W, 0, eqp _ _ wi) ▷ tt ∅
                          wi :: T ▷ xs ∅
                          xi :: ptr _ _ (R, 0, trueP _ _) ▷ tt).
  (* Input type *)
  - etransitivity.
    (* PermsE *)
    {
      etransitivity; [apply PermsE |]. rewrite sep_conj_Perms_commut.
      eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
      etransitivity; [| apply PermsE]. rewrite sep_conj_Perms_commut.
      eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
      etransitivity; [| apply PermsE]. rewrite sep_conj_Perms_commut. reflexivity.
    }
    rewrite (sep_conj_Perms_commut (zi :: T ▷ xs) _).
    repeat rewrite <- sep_conj_Perms_assoc.
    apply sep_conj_Perms_monotone; [reflexivity |].
    rewrite sep_conj_Perms_commut.
    eapply sep_conj_Perms_monotone.
    (* Weakening the content type *)
    + etransitivity; [apply PtrI | apply TrueI].
    (* Cast *)
    + apply Cast.
  (* Output type *)
  - intros ? [].
    etransitivity; [apply PermsE |].
    etransitivity; [| apply PermsI].
    eapply sep_conj_Perms_monotone; [| reflexivity]. (* frame *)
    etransitivity; [| apply PermsE].
    etransitivity; [apply PermsI |].
    etransitivity.
    2: {
      eapply sep_conj_Perms_monotone; [| reflexivity]. (* frame *)
      apply PermsE.
    }
    rewrite <- sep_conj_Perms_assoc.
    eapply sep_conj_Perms_monotone; [reflexivity |]. (* frame *)
    (* PtrI *)
    apply PtrI.
    (* Frame and Store *)
  - apply Frame. apply Frame. apply Store.
Qed.

(***********************************************************************)

Fixpoint split_leq {A} l1 (v:Vector.t A l1) :
  forall l2, le l2 l1 -> (Vector.t A l2 * Vector.t A (l1 - l2)).
Proof.
  destruct v; intros; destruct l2.
  - split; apply Vector.nil.
  - elimtype False; inversion H.
  - split; [ apply Vector.nil | apply Vector.cons; assumption ].
  - edestruct (split_leq _ n v l2) as [v1 v2].
    + apply le_S_n; assumption.
    + split; [ apply Vector.cons; assumption | assumption ].
Defined.

Fixpoint append_leq {A} l1 l2 (l: le l2 l1)
         (v1:Vector.t A l2) (v2:Vector.t A (l1 - l2)) : Vector.t A l1.
Proof.
  revert l2 l v1 v2. destruct l1; intros.
  - constructor.
  - destruct l2.
    + apply v2.
    + constructor; [ apply (Vector.hd v1) | ]. apply (append_leq _ l1 l2).
      * apply le_S_n; assumption.
      * apply (Vector.tl v1).
      * apply v2.
Defined.

Arguments append_leq {A} !l1.
Arguments split_leq {A} l1 !v.

Lemma split_leq_append_leq A l1 v l2 (l: le l2 l1) :
  @append_leq A l1 l2 l (fst (split_leq l1 v l2 l)) (snd (split_leq l1 v l2 l)) = v.
Proof.
  revert l2 l; induction v; intros.
  - simpl. reflexivity.
  - destruct l2.
    + simpl. reflexivity.
    + simpl.
      rewrite (surjective_pairing (split_leq n v l2 (le_S_n l2 n l))). simpl.
      rewrite IHv. reflexivity.
Qed.

Definition trySplit {A l1 R S} (v : Vector.t A l1) l2 (f : Vector.t A l2 -> Vector.t A (l1 - l2) -> itree (sceE S) R) : itree (sceE S) R.
  destruct (le_lt_dec l2 l1).
  - exact (f (fst (split_leq l1 v l2 l)) (snd (split_leq l1 v l2 l))).
  - exact (throw tt).
Defined.

Lemma ArrCombine_eq A xi rw o l1 l2 (l:le l2 l1) xs1 xs2 (P : VPermType Si Ss A) :
  eq_Perms (xi :: arr (rw, o, l1, P) ▷ append_leq l1 l2 l xs1 xs2)
           (xi :: arr (rw, o, l2, P) ▷ xs1 * xi :: arr (rw, o + l2, l1 - l2, P) ▷ xs2).
Proof.
  revert o l2 l xs1 xs2; induction l1; intros.
  - inversion l. subst. simpl. rewrite sep_conj_Perms_bottom_identity. reflexivity.
  - destruct l2.
    + simpl. rewrite sep_conj_Perms_bottom_identity.
      rewrite Nat.add_0_r. reflexivity.
    + simpl. rewrite (IHl1 (S o) l2).
      simpl. rewrite Nat.add_succ_r.
      rewrite sep_conj_Perms_assoc.
      reflexivity.
Qed.

Lemma ArrSplit A R1 R2 P l1 l2 xi xs rw o (T : VPermType Si Ss A) U (ti : itree (sceE Si) R1) (fs : _ -> _ -> itree (sceE Ss) R2) :
  (forall xs1 xs2, P *
              xi :: arr (rw, o, l2, T) ▷ xs1 *
              xi :: arr (rw, o + l2, l1 - l2, T) ▷ xs2 ⊢
              ti ⤳ fs xs1 xs2 ::: U) ->
  P * xi :: arr (rw, o, l1, T) ▷ xs ⊢ ti ⤳ trySplit xs l2 fs ::: U.
Proof.
  intros. unfold trySplit. destruct (le_lt_dec l2 l1).
  - rewrite <- (split_leq_append_leq _ l1 xs l2 l).
    rewrite ArrCombine_eq. repeat rewrite split_leq_append_leq.
    rewrite sep_conj_Perms_assoc.
    apply H.
  - apply Err.
Qed.

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
  xi :: arr (rw, o, l1, P) ▷ xs1 * xi :: arr (rw, o + l1, l2, P) ▷ xs2 ⊨
  xi :: arr (rw, o, l1 + l2, P) ▷ Vector.append xs1 xs2 .
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

Lemma ArrPtr A xi xs rw o (P : VPermType Si Ss A) :
  xi :: arr (rw, o, 1, P) ▷ xs ⊨ xi :: ptr _ _ (rw, o, P) ▷ Vector.hd xs.
Proof.
  simpl. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

Lemma PtrArr A xi xs rw o (P : VPermType Si Ss A) :
  xi :: ptr _ _ (rw, o, P) ▷ xs ⊨ xi :: arr (rw, o, 1, P) ▷ vsingle xs.
Proof.
  simpl. rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
Qed.

(***********************************************************************)

Lemma MuFold A G X `{FixedPoint G X} (F:PermType Si Ss A X -> PermType Si Ss A (G X))
      {prp:Proper (lte_PermType _ _ ==> lte_PermType _ _) F}
      xi xs :
  xi :: F (mu _ _ F) ▷ xs ⊨ xi :: mu _ _ F ▷ foldFP xs.
Proof.
  (* FIXME: why can't we just rewrite with mu_fixed_point here? *)
  eapply Proper_eq_Perms_lte_Perms; [ | reflexivity | ].
  - apply Proper_eq_PermType_ptApp; [ apply mu_fixed_point | | ]; reflexivity.
  - simpl. rewrite foldUnfold. reflexivity.
Qed.

Lemma MuUnfold A G X `{FixedPoint G X} (F:PermType Si Ss A X -> PermType Si Ss A (G X))
      {prp:Proper (lte_PermType _ _ ==> lte_PermType _ _) F}
      xi xs :
   xi :: mu _ _ F ▷ xs ⊨ xi :: F (mu _ _ F) ▷ unfoldFP xs.
Proof.
  eapply Proper_eq_Perms_lte_Perms; [ reflexivity | | ].
  - apply Proper_eq_PermType_ptApp; [ apply mu_fixed_point | | ]; reflexivity.
  - simpl. reflexivity.
Qed.

(* Program Definition list_reach_perm r rw A (T : VPermType Si Ss A) : VPermType Si Ss (list A) := *)
(*   @mu _ _ _ (mu_list A) _ (fixed_point_list _) *)
(*       (fun U => or _ _ (eqp Si Ss r) (starPT _ _ (ptr _ _ (rw, 0, T)) (ptr _ _ (rw, 1, U)))) _. *)
(* Next Obligation. *)
(*   repeat intro. simpl. induction b; simpl in *; auto. *)
(*   destruct H0 as (? & ? & ? & ? & ?). exists x0, x1. split; [| split]; auto. *)
(*   clear H0. unfold ptr_Perms in *. destruct (offset a 1); auto. *)
(*   destruct H1. destruct H0. destruct H0. subst. destruct H1 as (? & ? & ? & ? & ?). *)
(*   eexists. split; eauto. do 2 eexists. split; eauto. split; eauto. apply H. auto. *)
(* Qed. *)

Lemma ReflR {A} x rw o (T : VPermType Si Ss A) :
  x :: trueP _ _ ▷ tt ⊨ x :: reach_perm _ _ x rw o T ▷ nil.
Proof.
  repeat intro. apply mu_fixed_point. reflexivity.
Qed.

Lemma TransR {A} x y z rw o (T : VPermType Si Ss A) xs ys :
  x :: reach_perm _ _ y rw o T ▷ xs * y :: reach_perm _ _ z rw o T ▷ ys ⊨
  x :: reach_perm _ _ z rw o T ▷ (xs ++ ys).
Proof.
  revert x.
  induction xs.
  - intros x p (p1 & p2 & Hp1 & Hp2 & Hlte).
    destruct Hp1 as (? & (U & HU & ?) & Hp1); subst.
    apply HU in Hp1. simpl in Hp1. subst. eapply Perms_upwards_closed; eauto.
    etransitivity; eauto. apply lte_r_sep_conj_perm.
  - intros x p (px' & py & Hpx' & Hpy & Hlte).
    eapply mu_fixed_point in Hpx'.
    destruct Hpx' as (pa & px & Hpa & Hpx & Hlte').
    (* x must be a pointer *)
    destruct x; try contradiction. destruct a0 as [b o'].
    destruct Hpx as (? & (v & ?) & Hpx); subst.
    destruct Hpx as (px'' & pv & Hpx'' & Hpv & Hlte'').

    apply mu_fixed_point.
    simpl.
    exists pa. exists (px'' ** (pv ** py)). split; [apply Hpa | split].
    2: { repeat rewrite <- sep_conj_perm_assoc.
         etransitivity; eauto.
         eapply sep_conj_perm_monotone; intuition.
         repeat rewrite sep_conj_perm_assoc.
         etransitivity; eauto.
         eapply sep_conj_perm_monotone; intuition.
    }
    eexists; split; [eexists; reflexivity |].
    apply sep_conj_Perms_perm; [apply Hpx'' |].
    simpl. exists (v :: reach_perm _ _ z rw o T ▷ (xs ++ ys)). split.
    2: { apply IHxs. apply sep_conj_Perms_perm; auto. }
    eexists; split; eauto.
    repeat intro. eapply mu_fixed_point in H; auto.
    Unshelve. all: apply reach_perm_proper.
Qed.

Lemma Free {A} xi len (xs : Vector.t A (S len) * unit) :
  xi :: starPT _ _ (arr (W, 0, (S len), trueP Si Ss)) (blockPT _ _ (S len)) ▷ xs ⊢
  free xi ⤳
  Ret tt :::
  trueP _ _.
Proof.
  intros p si ss (parr & pblock & Hparr & Hpblock & Hlte) Hpre.
  pstep. unfold free. destruct xi as [| ptr]; try contradiction.
  assert (Hoffset: snd ptr = 0).
  { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
    apply Hpblock in Hpre. simpl in Hpre. unfold sizeof in Hpre.
    rewrite (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)).
    destruct (snd ptr =? 0); inversion Hpre; auto.
  }
  rewrite Hoffset. simpl.
  (* read step *)
  rewritebisim @bind_trigger. econstructor; auto; try reflexivity.
  pose proof Hpre as Hpre'. apply Hlte in Hpre'.
  destruct Hpre' as (Hprewrite & Hpreblock & Hsep).
  apply Hpblock in Hpreblock. simpl in Hpreblock.
  unfold sizeof in Hpreblock. rewrite Hoffset in Hpreblock. simpl in Hpreblock.
  destruct (nth_error (m (fst si)) (fst ptr)) eqn:?; try solve [inversion Hpreblock].
  destruct o; try solve [inversion Hpreblock].
  destruct l. inversion Hpreblock; clear Hpreblock; subst.
  (* write step *)
  rewritebisim @bind_trigger. unfold id. econstructor; auto.
  - simpl in Hparr.
    (* apply Hlte. constructor 1. left. *)
    induction len.

    { simpl in *. (* should be ok *) admit. }
    { apply Hlte. constructor. left.


    apply Hlte'. constructor 1. left.
    apply Hpwrite. simpl.
    split; [| split; [| split]]; rewrite lGetPut; simpl; auto.
    + intros. unfold read. unfold allocated. simpl.
      destruct ptr as [b o]; destruct ptr' as [b' o'].
      apply addr_neq_cases in H. simpl.
      admit. (* break up the <> into cases, then use nth_error_replace_list_index_eq/neq *)
    + admit.
    + assert (fst ptr < length (m (lget si))).
      { apply nth_error_Some. intro. rewrite H in Heqo. inversion Heqo. }
      apply replace_list_index_length; auto.
  - apply sep_step_lte'. apply bottom_perm_is_bottom.
  - constructor; simpl; auto.
Qed.

Definition ex3i' : Value -> itree (sceE Si) Value :=
  iter (C := Kleisli _)
       (fun v => v' <- load (offset v 1);; (* continue with *(v + 1) *)
               Ret (inl v')).

Definition ex3s' {A} : list A -> itree (sceE Ss) unit :=
  iter (C := Kleisli _)
       (fun l => sum_rect (fun _ => itree (sceE Ss) (list A + unit)) (fun _ : unit => Ret (inr tt)) (fun '(h, t) => Ret (inl t)) (unfoldFP l)).

          (* match l with *)
          (*     | nil => Ret (inr tt) *)
          (*     | h :: t => Ret (inl t) *)
          (*     end). *)

Lemma ex3'_typing A xi xs (T : VPermType _ _ A) :
  xi :: list_perm _ _ R _ T ▷ xs ⊢
  ex3i' xi ⤳
  ex3s' xs :::
  (falseP _ _).
Proof.
  unfold ex3i', ex3s'. apply Iter.
  intros. unfold list_perm. eapply Weak; [| reflexivity |].
  (* etransitivity. eapply MuUnfold. apply (EqRefl _ _ 0). rewrite sep_conj_Perms_commut. *)
  eapply MuUnfold. rewrite <- sep_conj_Perms_bottom_identity.
  eapply OrE.
  - intros. admit.
  - intros (? & ?). rewrite sep_conj_Perms_bottom_identity.
    eapply Weak; [| reflexivity |].
    apply StarE.
    rewrite sep_conj_Perms_commut.
    (* eapply Weak; [| reflexivity |]. *)
    (* apply sep_conj_Perms_monotone. apply bottom_Perms_is_bottom. reflexivity. *)
    (* rewrite sep_conj_Perms_bottom_identity. *)

    (* eapply Weak; [| reflexivity |]. *)
    (* apply PtrOff with (o2 := 1); auto. *)
    replace (Ret (inl l)) with (Ret tt;; (Ret (inl l) : itree (sceE Ss) (list A + unit))).
    2: { rewritebisim @bind_ret_l. reflexivity. }
    (* rewrite <- sep_conj_Perms_bottom_identity. *)
    (* eapply PtrE. intros. rewrite sep_conj_Perms_bottom_identity. *)

    rewrite sep_conj_Perms_commut.
    eapply PtrE. intros zi.

    eapply Bind with (T := _).
    + rewrite <- sep_conj_Perms_assoc.
      rewrite sep_conj_Perms_commut.
      eapply Frame.
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone.
      apply PtrOff with (o2 := 1); auto. reflexivity.
      eapply Frame.
      eapply Load.
    + intros v [].
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone.
      apply PermsE. reflexivity.
      rewrite <- sep_conj_Perms_assoc.
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone.
      apply PermsE. reflexivity.

      rewrite sep_conj_Perms_assoc.
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone. reflexivity.
      apply bottom_Perms_is_bottom.

      rewrite <- sep_conj_Perms_assoc.
      eapply Weak; [| reflexivity |].
      apply sep_conj_Perms_monotone.
      {
        apply sep_conj_Perms_monotone. reflexivity.
        apply bottom_Perms_is_bottom.
      }
      rewrite sep_conj_Perms_commut.
      rewrite sep_conj_Perms_bottom_identity.
      reflexivity.

      repeat rewrite <- sep_conj_Perms_assoc.
      repeat rewrite sep_conj_Perms_bottom_identity.

      eapply Weak; [| reflexivity |].
      apply Cast.

      eapply Weak; [| reflexivity |].
      eapply SumI1.
      apply Ret_.
Admitted.
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       apply bottom_Perms_is_bottom. *)

(*       (* remove offset *) *)
(*       rewrite <- sep_conj_Perms_assoc. *)
(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       { *)
(*         apply sep_conj_Perms_monotone. *)
(*         replace 0 with (1 - 1) by auto. eapply PtrOff'; auto. *)
(*         reflexivity. *)
(*       } *)

(*       (* first mess around with the equality permission *) *)
(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. 2: reflexivity. *)
(*       etransitivity. 2: apply EqDup. *)
(*       apply sep_conj_Perms_monotone. *)
(*       reflexivity. apply EqSym. *)

(*       (* change zi to v in yi+1 permission *) *)
(*       rewrite sep_conj_Perms_assoc. *)
(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. 2: reflexivity. *)
(*       rewrite <- sep_conj_Perms_assoc. *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       rewrite sep_conj_Perms_commut. apply PtrI. *)

(*       (* combine zi and v permissions *) *)
(*       rewrite sep_conj_Perms_assoc. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       rewrite sep_conj_Perms_assoc. *)
(*       apply sep_conj_Perms_monotone. 2: reflexivity. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       apply Cast. *)

(*       (* combine yi+1 and v permissions *) *)
(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       apply PtrI. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       apply StarI. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       eapply OrI2. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       eapply MuFold. *)
(*       apply Ret_. *)
(*       (* etransitivity. *) *)
(*       (* apply sep_conj_Perms_monotone. apply EqSym. reflexivity. *) *)
(*       (* etransitivity. reflexivity. *) *)
(*       (* rewrite sep_conj_Perms_commut. eapply PtrI. *) *)
(*       (* apply sep_conj_Perms_commut. *) *)
(*       (* apply PtrI. *) *)
(*       (* erewrite sep_conj_Perms_commut at 2. apply PtrI. *) *)


(*       rewrite <- sep_conj_Perms_assoc. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       { *)
(*         (* rewrite sep_conj_Perms_commut. *) *)
(*         rewrite sep_conj_Perms_assoc. *)

(*         apply sep_conj_Perms_monotone. *)
(*         { *)
(*           etransitivity. *)
(*           apply sep_conj_Perms_monotone. apply EqSym. reflexivity. *)
(*           etransitivity. reflexivity. *)
(*           rewrite sep_conj_Perms_commut. eapply PtrI. *)
(*           apply sep_conj_Perms_commut. *)
(*           apply PtrI. *)
(*           erewrite sep_conj_Perms_commut at 2. apply PtrI. *)


(*         rewrite sep_conj_Perms_commut. *)
(*         rewrite sep_conj_Perms_assoc. *)
(*         rewrite sep_conj_Perms_commut. *)
(*         rewrite sep_conj_Perms_assoc. *)
(*         apply sep_conj_Perms_monotone. reflexivity. *)
(*         rewrite sep_conj_Perms_commut. *)

(*         rewrite sep_conj_Perms_assoc. *)

(*         apply sep_conj_Perms_monotone. *)
(*               { *)
(*         rewrite sep_conj_Perms_commut. *)

(*         apply Cast. *)
(*       } *)
(*       reflexivity. *)

(*       rewrite sep_conj_Perms_commut. *)
(*       rewrite sep_conj_Perms_assoc. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. *)
(*       apply StarI. reflexivity. *)

(*       rewrite sep_conj_Perms_commut. *)
(*       rewrite sep_conj_Perms_assoc. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       rewrite sep_conj_Perms_assoc. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)

(*       rewrite sep_conj_Perms_commut. *)
(*       rewrite sep_conj_Perms_assoc. *)
(*       rewrite <- sep_conj_Perms_assoc. *)

(*       eapply Weak; [| reflexivity |]. *)
(*       apply StarI. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       rewrite sep_conj_Perms_assoc. *)
(*       rewrite sep_conj_Perms_commut. *)
(*       (* rewrite sep_conj_Perms_assoc. *) *)
(*       apply sep_conj_Perms_monotone. reflexivity. *)
(*       rewrite sep_conj_Perms_commut. apply Cast. *)

(* Qed. *)

Definition ex3i (v : Value) : itree (sceE Si) Value :=
  iter (C := Kleisli _)
       (fun '(n, v) => b <- isNull v;;
                     if (b : bool)
                     then Ret (inr (VNum n)) (* v == NULL *)
                     else v' <- load (offset v 1);; (* continue with *(v + 1) *)
                          Ret (inl (n + 1, v')))
       (0, v).

Definition ex3s {A} (l : list A) : itree (sceE Ss) (sigT (fun _ : nat => unit)) :=
  iter (C := Kleisli _)
       (fun '(n, l) =>
          sum_rect (fun _ => itree (sceE Ss) (((sigT (fun _ : nat => unit)) * list A) +
                                             (sigT (fun _ : nat => unit))))
                   (fun _ : unit => Ret (inr n))
                   (fun '(h, t) => Ret (inl (existT _ (projT1 n + 1) tt, t)))
                   (unfoldFP l))
       (existT _ 0 tt, l).

Lemma ex3_typing A xi xs (T : VPermType _ _ A) :
  xi :: list_perm _ _ R _ T ▷ xs ⊢
  ex3i xi ⤳
  ex3s xs :::
  (trueP _ _).
Proof.
  eapply Weak with (P2 := xi :: list_perm _ _ R _ T ▷ xs *
                          0 :: ex (n oftype nat) eqp _ _ n ▷ (existT _ 0 tt)
                   ); [| reflexivity |].
  {
    etransitivity. apply EqRefl.
    eapply sep_conj_Perms_monotone; [reflexivity |].
    apply ExI.
  }
  eapply Weak; [| reflexivity |].
  rewrite sep_conj_Perms_commut.
  apply ProdI.
  eapply Iter. clear xi xs.
  intros [ni xi] [ns xs].
  eapply Weak; [| reflexivity |].
  apply ProdE.

  eapply Weak; [| reflexivity |].
  eapply sep_conj_Perms_monotone. reflexivity.
  { apply MuUnfold. }
  eapply OrE.
  - intros []. admit.
  - intros [a ys]. admit.
Abort.
