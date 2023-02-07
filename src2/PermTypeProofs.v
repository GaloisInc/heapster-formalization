(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Arith.Compare_dec
     Logic.FunctionalExtensionality
     Lia.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

From Heapster2 Require Export
     Utils
     Permissions
     PermissionsSpred2
     Memory
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
     Eq.Eqit
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import MonadNotation.
Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

Context (Si Ss:Type).
Context `{Lens Si memory}.
Context (Spred : Type).
Context (interp_spred : Spred -> Si * Ss -> Prop).
Notation "P ⊢ ti ⤳ ts ::: U" := (typing (Spred:=Spred) (interp_spred:=interp_spred) P (ptApp _ _ U) ti ts) (at level 60).

(** * Basic permission connective rules *)

Lemma Weak (A B : Type) P1 P2 (U1 U2 : @PermType Si Ss A B) ts ti :
  P1 ⊨2 P2 ->
  (forall xi xs, xi :: U2 ▷ xs ⊨2 xi :: U1 ▷ xs) ->
  P2 ⊢ ts ⤳ ti ::: U2 ->
  P1 ⊢ ts ⤳ ti ::: U1.
Proof.
  intros. eapply typing_lte; eauto.
Qed.

Lemma ProdI (A1 A2 B1 B2 : Type) xi yi xs ys (T1 : @PermType Si Ss A1 B1) (T2 : PermType A2 B2) :
  xi :: T1 ▷ xs *2 yi :: T2 ▷ ys ⊨2 (xi, yi) :: T1 ⊗ T2 ▷ (xs, ys).
Proof. reflexivity. Qed.

Lemma ProdE (A1 A2 B1 B2 : Type) xi xs (T1 : @PermType Si Ss A1 B1) (T2 : PermType A2 B2) :
  xi :: T1 ⊗ T2 ▷ xs ⊨2 (fst xi :: T1 ▷ fst xs *2 snd xi :: T2 ▷ snd xs).
Proof. reflexivity. Qed.

Lemma SumI1 (A1 A2 B1 B2 : Type) (xi : A1) (xs : B1) (T1 : @PermType Si Ss A1 B1) (T2 : PermType A2 B2) :
  xi :: T1 ▷ xs ⊨2 inl xi :: T1 ⊕ T2 ▷ inl xs.
Proof. reflexivity. Qed.

Lemma SumI2 (A1 A2 B1 B2 : Type) (xi : A2) (xs : B2) (T1 : @PermType Si Ss A1 B1) (T2 : PermType A2 B2) :
  xi :: T2 ▷ xs ⊨2 inr xi :: T1 ⊕ T2 ▷ inr xs.
Proof. reflexivity. Qed.

Lemma SumE (A1 A2 B1 B2 R1 R2 : Type)
      (xi : A1 + A2) (xs : B1 + B2) ti1 ti2 ts1 ts2
      (T1 : @PermType Si Ss A1 B1) (T2 : PermType A2 B2) (P : Perms2) (U : PermType (A1 + A2) (B1 + B2)) :
  (forall yi ys, P *2 yi :: T1 ▷ ys ⊢ ti1 yi ⤳ ts1 ys ::: U) ->
  (forall yi ys, P *2 yi :: T2 ▷ ys ⊢ ti2 yi ⤳ ts2 ys ::: U) ->
  P *2 xi :: T1 ⊕ T2 ▷ xs ⊢ sum_rect _ ti1 ti2 xi ⤳ sum_rect _ ts1 ts2 xs ::: U.
Proof.
  intros. simpl.
  destruct xi, xs; simpl; auto;
    rewrite sep_conj_Perms2_commut; rewrite sep_conj_Perms2_top_absorb; apply typing_top.
Qed.

Lemma StarI (A B1 B2 : Type) xi xs ys (T1 : @PermType Si Ss A B1) (T2 : PermType A B2) :
  xi :: T1 ▷ xs *2 xi :: T2 ▷ ys ⊨2 xi :: T1 ⋆ T2 ▷ (xs, ys).
Proof. reflexivity. Qed.

Lemma StarE (A B1 B2 : Type) xi xs (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
  xi :: T1 ⋆ T2 ▷ xs ⊨2 (xi :: T1 ▷ fst xs *2 xi :: T2 ▷ snd xs).
Proof. reflexivity. Qed.

Lemma PermsI (A B : Type) (P : Perms2) xi xs (T : @PermType Si Ss A B) :
  xi :: T ▷ xs *2 P ⊨2 xi :: T ∅ P ▷ xs.
Proof. reflexivity. Qed.

Lemma PermsE (A B : Type) (P : Perms2) xi xs (T : @PermType Si Ss A B) :
  xi :: T ∅ P ▷ xs ⊨2 (xi :: T ▷ xs *2 P).
Proof. reflexivity. Qed.

Lemma Frame (A B : Type) (P1 P2 : Perms2) ti ts (T : @PermType Si Ss A B) :
  P1 ⊢ ti ⤳ ts ::: T ->
  P1 *2 P2 ⊢ ti ⤳ ts ::: T ∅ P2.
Proof. apply typing_frame. Qed.

Lemma OrI1 (A B1 B2 : Type) xi xs (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
  xi :: T1 ▷ xs ⊨2 xi :: @or Si Ss _ _ _ T1 T2 ▷ inl xs.
Proof. reflexivity. Qed.

Lemma OrI2 (A B1 B2 : Type) xi xs (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
  xi :: T2 ▷ xs ⊨2 xi :: @or Si Ss _ _ _ T1 T2 ▷ inr xs.
Proof. reflexivity. Qed.

Lemma OrE (A B1 B2 C1 C2 D : Type)
      (xi : A) (xs : B1 + B2) ti ts1 ts2
      (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) (P : Perms2) (U : @PermType Si Ss D (C1 + C2)) :
  (forall ys, P *2 xi :: T1 ▷ ys ⊢ ti ⤳ ts1 ys ::: U) ->
  (forall ys, P *2 xi :: T2 ▷ ys ⊢ ti ⤳ ts2 ys ::: U) ->
  P *2 xi :: @or Si Ss _ _ _ T1 T2 ▷ xs ⊢ ti ⤳ sum_rect _ ts1 ts2 xs ::: U.
Proof.
  intros. destruct xs; simpl; auto.
Qed.

Lemma TrueI (A : Type) P (xi : A) :
  P ⊨2 (P *2 xi :: @trueP Si Ss _ _ ▷ tt).
Proof.
  simpl. rewrite sep_conj_Perms2_commut. rewrite sep_conj_Perms2_bottom_identity. reflexivity.
Qed.

Lemma ExI (A B : Type) (C : B -> Type) (xi : A) (ys : B) (xs : C ys) (F : forall (b : B), @PermType Si Ss A (C b)) :
  xi :: F ys ▷ xs ⊨2 xi :: ex (z oftype B) (F z) ▷ existT (fun b : B => C b) ys xs.
Proof. reflexivity. Qed.

Lemma ExE (A B : Type) (C : B -> Type) (xi : A) (xs : sigT (fun b : B => C b)) (F : forall (b : B), @PermType Si Ss A (C b)) :
  xi :: ex (z oftype B) (F z) ▷ xs ⊨2 xi :: F (projT1 xs) ▷ (projT2 xs).
Proof. reflexivity. Qed.

(** * Equality rules *)

Lemma EqRefl A P (xi : A) :
  P ⊨2 (P *2 xi :: @eqp Si Ss _ xi ▷ tt).
Proof.
  repeat intro.
  exists p, bottom_perm. split; [| split]; cbn; eauto. rewrite sep_conj_perm_bottom. reflexivity.
Qed.

Lemma EqSym (A : Type) (xi yi : A) :
  xi :: @eqp Si Ss _ yi ▷ tt ⊨2 yi :: @eqp _ _ _ xi ▷ tt.
Proof.
  repeat intro; cbn in *; subst; reflexivity.
Qed.

Lemma EqTrans (A : Type) (xi yi zi : A) :
   xi :: @eqp _ _ _ yi ▷ tt *2 yi :: @eqp _ _ _ zi ▷ tt ⊨2 xi :: @eqp Si Ss _ zi ▷ tt.
Proof.
  repeat intro. destruct H0 as (? & ? & ? & ? & ?). cbn in *; subst. reflexivity.
Qed.

Lemma EqCtx (A B : Type) (xi yi : A) (f : A -> B) :
  xi :: @eqp _ _ _ yi ▷ tt ⊨2 f xi :: @eqp Si Ss _ (f yi) ▷ tt.
Proof.
  repeat intro. cbn in *. congruence.
Qed.

Lemma EqDup (A : Type) (xi yi : A) :
  xi :: @eqp _ _ _ yi ▷ tt ⊨2 (xi :: @eqp Si Ss _ yi ▷ tt *2 xi :: @eqp _ _ _ yi ▷ tt).
Proof.
  repeat intro. cbn in *. subst. exists bottom_perm, bottom_perm.
  split; [| split]; auto. rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom.
Qed.

Lemma Cast (A B : Type) (P : @PermType Si Ss A B) xi yi xs ys :
  xi :: @eqp _ _ _ yi ▷ xs *2 yi :: P ▷ ys ⊨2 xi :: P ▷ ys.
Proof.
  repeat intro. destruct H0 as (e & p' & Heq & Hp & Hlte).
  simpl in Heq. subst.
  eapply Perms2_upwards_closed; eauto.
  eapply hlte_perm2_transitive.
  apply lte_r_sep_conj_perm.
  red. do 2 rewrite restrict_same. eauto.
  Unshelve. all: auto.
Qed.

(** * Instruction rules *)
(** Name conflicts with ITree Ret. *)
Lemma Ret_ (A B : Type) xi xs (T : @PermType Si Ss A B) :
  xi :: T ▷ xs ⊢ Ret xi ⤳ Ret xs ::: T.
Proof.
  repeat intro. pstep. econstructor; eauto.
Qed.

Lemma Bind (A B C D : Type) P ti ts fi fs (T : @PermType Si Ss A B) (U : @PermType Si Ss C D) :
  P ⊢ ti ⤳ ts ::: T ->
  (forall xi xs, xi :: T ▷ xs ⊢ fi xi ⤳ fs xs ::: U) ->
  P ⊢ ITree.bind ti fi ⤳ ITree.bind ts fs ::: U.
Proof.
  intros. eapply typing_bind; eauto.
Qed.

Lemma GetNum xi yi :
  xi :: @eqp Si Ss _ (VNum yi) ▷ tt ⊢ getNum xi ⤳ Ret tt ::: @eqp _ _ _ yi.
Proof.
  repeat intro. cbn in *. subst. cbn. pstep. econstructor; eauto. reflexivity.
Qed.

Lemma Iter (A B C D : Type) (T : @PermType Si Ss C D) xi xs fi fs (U : @PermType Si Ss A B) :
  (forall yi ys, yi :: T ▷ ys ⊢ fi yi ⤳ fs ys ::: T ⊕ U) ->
  xi :: T ▷ xs ⊢ iter fi xi ⤳ iter fs xs ::: U.
Proof.
  revert xi xs fi fs U. pcofix CIH. intros.
  do 2 rewritebisim @unfold_iter_ktree.
  eapply bisim_bind; eauto.
  - eapply H1; eauto.
  - cbn. intros. destruct r1, r2; try contradiction.
    + repeat intro. pstep. econstructor 5; eauto.
    + pstep. econstructor; eauto.
Qed.

Lemma If (A B : Type) P ti1 ti2 ts1 ts2 (xi yi : bool) xs (U : @PermType Si Ss A B) :
  P ⊢ ti1 ⤳ ts1 ::: U ->
  P ⊢ ti2 ⤳ ts2 ::: U ->
  P *2 xi :: @eqp _ _ _ yi ▷ xs ⊢ if xi then ti1 else ti2 ⤳ if yi then ts1 else ts2 ::: U.
Proof.
  repeat intro. destruct H2 as (? & ? & ? & ? & ?); cbn in *; subst.
  destruct xi.
  - eapply H0; eauto. eapply Perms2_upwards_closed; eauto.
    eapply hlte_perm2_transitive. apply lte_l_sep_conj_perm.
    red. do 2 rewrite restrict_same. eauto.
  - eapply H1; eauto. eapply Perms2_upwards_closed; eauto.
    eapply hlte_perm2_transitive. apply lte_l_sep_conj_perm.
    red. do 2 rewrite restrict_same. eauto.
    Unshelve. all: auto.
Qed.

Lemma Err (A B : Type) P (U : @PermType Si Ss A B) t :
  P ⊢ t ⤳ throw tt ::: U.
Proof.
  repeat intro. pstep. constructor.
Qed.

(** * Example 1 *)

Definition ex1i xi : itree (sceE Si) Value :=
  x <- getNum xi;;
  Ret (VNum (Init.Nat.mul 5 x)).

Definition ex1s (xs : sigT (fun _ : nat => unit)) : itree (sceE Ss) (sigT (fun _ : nat => unit)) :=
  Ret tt;;
  Ret (existT _ (Init.Nat.mul 5 (projT1 xs)) tt).

Definition IsNat : @VPermType Si Ss (sigT (fun _ : nat => unit)) :=
  ex (n oftype nat) @eqp Si Ss _ (VNum n).

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
  eapply Weak; [apply ExI with (F := fun n : nat => @eqp Si Ss _ (VNum n)) | reflexivity |]; fold IsNat.
  (* Ret *)
  apply Ret_.
Qed.

(*
(** * Pointer rules *)

Lemma PtrI A xi yi xs ys rw o (T : @VPermType Si Ss A) :
  xi :: ptr _ _ (rw, o, eqp Si Ss yi) ▷ xs * yi :: T ▷ ys ⊨ xi :: ptr _ _ (rw, o, T) ▷ ys.
Proof.
  destruct xi; simpl.
  - rewrite sep_conj_Perms_top_absorb. reflexivity.
  - repeat intro. destruct a. rename p into p'.
    destruct H0 as (p & t & (P & (v & ?) & Hp) & Hp' & Hlte). subst.
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
  repeat intro. rename p into p''. destruct H1 as (p & p' & Hp & Hptr & Hlte).
  destruct xi; [contradiction | destruct a].
  destruct Hptr as (? & (? & ?) & ?). subst.
  destruct H3 as (pptr & pt & Hptr & Hpt & Hlte').
  eapply H0; eauto. exists (p ** pptr), pt.
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
  destruct H0 as (? & (v & ?) & ?). subst.
  exists (read_perm (b, o' + o) v), (read_perm (b, o' + o) v).
  destruct H1 as (pread & peq & Hpread & Hpeq & Hlte).
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
    split; intros; auto; destruct x0, y; simpl in H2; subst; reflexivity.
  - split; apply Hpread; apply Hlte; auto.
  - apply Hlte. constructor. left. apply Hpread. induction H1; auto.
    + destruct H1; auto.
    + etransitivity; eauto.
Qed.

Lemma PtrOff A xi xs rw o1 o2 (T : VPermType Si Ss A) :
  o1 >= o2 ->
  xi :: ptr _ _ (rw, o1, T) ▷ xs ⊨ offset xi o2 :: ptr _ _ (rw, o1 - o2, T) ▷ xs.
Proof.
  destruct xi; [reflexivity | destruct a].
  intros. simpl. rewrite <- Nat.add_assoc. rewrite (Minus.le_plus_minus_r _ _ H0).
  reflexivity.
Qed.
Lemma PtrOff' A xi xs rw o1 o2 (T : VPermType Si Ss A) :
  o1 >= o2 ->
  offset xi o2 :: ptr _ _ (rw, o1 - o2, T) ▷ xs ⊨ xi :: ptr _ _ (rw, o1, T) ▷ xs.
Proof.
  destruct xi; [reflexivity | destruct a].
  intros. simpl. rewrite <- Nat.add_assoc. rewrite (Minus.le_plus_minus_r _ _ H0).
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
  simpl in H0. unfold ptr_Perms in H0.
  destruct H0 as (? & (v & ?) & ?); subst.
  destruct H2 as (? & ? & ? & ? & ?). simpl in H0, H2. subst.
  assert (read (lget c1) (b, o) = Some v).
  {
    apply H3 in H1. destruct H1 as (? & _).
    rewrite Nat.add_0_r in H0. apply H0 in H1. destruct rw; auto.
  }
  rewrite H2. constructor; auto.
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
  rename p into p'. rename H1 into Hpre.
  destruct H0 as (? & (v & ?) & Hwrite); subst.
  destruct Hwrite as (pw & p & Hwritelte & Hp & Hlte).
  rewrite Nat.add_0_r in Hwritelte.
  assert (exists val, read (lget c1) (b, o) = Some val).
  {
    apply Hlte in Hpre. destruct Hpre as (Hpre & _).
    apply Hwritelte in Hpre. eexists.
    symmetry. apply Hpre.
  }
  destruct H0 as (val & Hread). eapply (read_success_write _ _ _ yi) in Hread.
  destruct Hread as (c' & Hwrite).
  assert (Hguar : guar p' (c1, c2) ((lput c1 c'), c2)).
  {
    apply Hlte. constructor 1. left. apply Hwritelte. simpl.
    split; [| split]; rewrite lGetPut.
    + eapply write_success_read_neq; eauto.
    + eapply write_success_sizeof; eauto.
    + eapply write_success_length; eauto.
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
    rewrite Nat.add_0_r. symmetry. eapply write_success_read_eq; rewrite lGetPut; eauto.
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

(** * Example 2 *)

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

(** * Array rules *)

(** Some helper lemmas? TODO *)
Fixpoint split_leq {A} l1 (v:Vector.t A l1) :
  forall l2, le l2 l1 -> (Vector.t A l2 * Vector.t A (l1 - l2)).
Proof.
  destruct v; intros; destruct l2.
  - split; apply Vector.nil.
  - elimtype False; inversion H0.
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
    apply H0.
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
  repeat intro. destruct H0 as (p1 & p2 & Hp1 & Hp2 & Hlte).
  revert Hp1 Hp2. revert o xi l2 xs2. revert Hlte. revert p p1 p2. induction l1; intros.
  - rewrite Nat.add_0_r in Hp2. simpl in *. revert xs1. apply Vector.case0. simpl.
    eapply Perms_upwards_closed; eauto. etransitivity; [apply lte_r_sep_conj_perm |]; eauto.
  - simpl. destruct Hp1 as (? & ? & ? & ? & ?).
    do 2 eexists. split; [| split].
    + rewrite vector_hd_append. apply H0.
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


Lemma arr_offset {A} ptr rw o l (T : VPermType Si Ss A) (v : Vector.t A l) :
  VPtr ptr :: arr (rw, o, l, T) ▷ v ≡ offset (VPtr ptr) o :: arr (rw, 0, l, T) ▷ v.
Proof.
  revert ptr o. induction l; intros; try reflexivity.
  split.
  - simpl. apply sep_conj_Perms_monotone.
    + destruct ptr. simpl. rewrite Nat.add_0_r. reflexivity.
    + destruct ptr. rewrite (IHl _ _ 1). simpl.
      specialize (IHl (Vector.tl v) (n, n0) (o + 1)). simpl in IHl.
      rewrite Nat.add_assoc in IHl. rewrite Nat.add_1_r in IHl. apply IHl.
  - simpl. apply sep_conj_Perms_monotone.
    + destruct ptr. simpl. rewrite Nat.add_0_r. reflexivity.
    + destruct ptr. rewrite (IHl _ _ 1). simpl.
      specialize (IHl (Vector.tl v) (n, n0) (o + 1)). simpl in IHl.
      rewrite Nat.add_assoc in IHl. rewrite Nat.add_1_r in IHl. apply IHl.
Qed.

(** helper lemmas for Malloc *)
Fixpoint rely_post_malloc n b size x y : Prop :=
  match n with
  | 0 => rely (block_perm size (b, 0) ** malloc_perm (b + 1)) x y
  | S n => rely (@write_perm Si Ss _ (b, size - S n) (VNum 0)) x y /\
          rely_post_malloc n b size x y
  end.
Lemma PO_rely_post_malloc n b size :
  PreOrder (rely_post_malloc n b size).
Proof.
  constructor.
  - intros []; induction n; simpl; auto.
  - intros [] [] [] ? ?. induction n.
    + split; [| split]; try solve [etransitivity; [apply H0 | apply H1]].
      intros; split; (etransitivity; [apply H0 | apply H1]); auto.
    + split; try solve [etransitivity; [apply H0 | apply H1]].
      apply IHn; [apply H0 | apply H1].
Qed.

Fixpoint guar_post_malloc n b size x y : Prop :=
  match n with
  | 0 => guar (block_perm size (b, 0) ** malloc_perm (b + 1)) x y
  | S n => clos_trans _ (fun x y =>
                          guar (@write_perm Si Ss _ (b, size - S n) (VNum 0)) x y \/
                          guar_post_malloc n b size x y) x y
  end.
#[local] Instance PO_guar_post_malloc n b size :
  PreOrder (guar_post_malloc n b size).
Proof.
  constructor.
  - intros []. induction n; simpl; intuition.
  - intros [] [] [] ? ?.
    destruct n; econstructor 2; eauto.
Qed.

Definition pre_post_malloc n b size : Si * Ss -> Prop :=
  fun '(x, _) =>
    b + 1 = length (lget x) /\
    Some size = sizeof (lget x) (b, 0) /\
    forall o, o < size -> (size - n <= o)%nat -> Some (VNum 0) = read (lget x) (b, o).
Lemma pre_respects_post_malloc n b size :
  forall x y, rely_post_malloc (S n) b size x y -> (* we need the fact that n > 0 here *)
         pre_post_malloc (S n) b size x ->
         pre_post_malloc (S n) b size y.
Proof.
  intros [] [] Hrely (Hlen & Hsizeof & Hread).
  simpl in *.
  induction n; simpl in *.
  - destruct Hrely as (Hread' & Hsizeof' & Hlen' & Hptr).
    split; [rewrite <- Hlen' | split; [rewrite <- Hsizeof' |]]; auto.
    intros. assert (o = size - 1) by lia. subst.
    rewrite <- Hread'. auto.
  - destruct Hrely as (Hread' & Head'' & Hrely). split; [| split].
    + apply IHn; auto. intros. apply Hread; auto. lia.
    + apply IHn; auto. intros. apply Hread; auto. lia.
    + intros. assert (size - S (S n) = o \/ (size - S n <= o)%nat) by lia.
      destruct H2.
      * subst. rewrite <- Hread'. auto.
      * apply IHn; auto. intros. apply Hread; auto. lia.
Qed.

(** The intermediate permission for Malloc. *)
(** [n] is the number of unfoldings to do for the rely/guar. [size] is the size of the block.
    when we use this [n = size], but we need them separate to do induction on [n] *)
Program Definition post_malloc_perm n b size : @perm (Si * Ss) :=
  {|
  rely := rely_post_malloc (S n) b (S size);
  rely_PO := PO_rely_post_malloc (S n) b (S size);
  guar := guar_post_malloc (S n) b (S size);
  guar_PO := PO_guar_post_malloc (S n) b (S size);
  pre := pre_post_malloc (S n) b (S size);
  pre_respects := pre_respects_post_malloc n b (S size); (* S is applied inside this defn *)
  |}.

Lemma guar_malloc_post_malloc n b size x y :
  guar_post_malloc n b (S size) x y -> guar (malloc_perm b) x y.
Proof.
  revert x y. induction n; intros.
  - induction H0; try solve [etransitivity; eauto]. destruct H0.
    + destruct x, y. simpl in *. subst; auto.
    + destruct x, y. split; apply H0; lia.
  - induction H0; auto.
    + destruct H0.
      * destruct x, y. destruct H0 as (? & ? & ?). split; auto.
        apply H0. destruct ptr. intro. inversion H4. simpl in *. lia.
      * apply IHn; auto.
    + etransitivity; eauto.
Qed.

Lemma rely_malloc_post_malloc n b size x y :
  rely (malloc_perm b) x y -> rely_post_malloc n b (S size) x y.
Proof.
  destruct x, y. induction n; intros.
  - destruct H0 as (Hlen & Hptr).
    split; [| split]; simpl; auto.
    + apply Hptr; simpl; auto.
    + intros. apply Hptr; lia.
  - split; auto. simpl in *. apply H0. auto.
Qed.

Lemma sep_step_malloc n b size : sep_step (malloc_perm b)
                                          (post_malloc_perm n b size).
Proof.
  apply sep_step_rg.
  - apply guar_malloc_post_malloc.
  - apply rely_malloc_post_malloc.
Qed.

Lemma write_post_malloc_perm m n size b
      (Hsize : (m <= size)%nat)
      (Hm : m > n):
  write_perm (b, size - m) (VNum 0) ⊥ post_malloc_perm n b size.
Proof.
  constructor; auto; intros.
  - revert H0. revert x y. induction n; intros.
    + induction H0; try solve [etransitivity; eauto].
      destruct H0; [| induction H0; try solve [etransitivity; eauto]; destruct H0].
      * eapply write_write_sep; eauto. intro. inversion H1. lia.
      * eapply write_block; eauto.
      * eapply malloc_write; eauto. rewrite Nat.add_1_r in H0. auto.
    + induction H0; try solve [etransitivity; eauto].
      destruct H0. 2: apply IHn; auto; lia.
      eapply write_write_sep; eauto. intro. inversion H1. lia.
  - revert H0. revert x y. induction n; intros.
    + destruct x, y. split; [| split; [| split; [| split]]]; simpl in *; try apply H0.
      * intro. inversion H1. lia.
      * destruct ptr. intro. simpl in *. inversion H2. lia.
    + destruct x, y. simpl in H0. split; [| split]; simpl; try apply H0.
      * intro. inversion H1. lia.
      * intro. inversion H1. lia.
      * apply IHn. lia. auto.
Qed.

Lemma post_malloc_perm_extend b size n (Hn : (S n <= size)%nat) :
  write_perm (b, size - S n) (VNum 0) ** post_malloc_perm n b size <=
  post_malloc_perm (S n) b size.
Proof.
  constructor; auto.
  simpl in *; auto. intros [] H. destruct H as (Hlen & Hsizeof & Hread).
  split; [| split; [split; [| split] |]]; auto; try solve [intros; apply Hread; lia].
  apply write_post_malloc_perm; auto.
Qed.

Lemma post_malloc_perm_ok {A} n b size (xs : Vector.t A (S n))
  (Hn : (n <= size)%nat) :
  post_malloc_perm n b size (* the perm applies S to n and size inside *) ∈
  VPtr (b, size - n) :: arr_perm Si Ss W 0 (S n) (trueP Si Ss) ▷ xs *
  singleton_Perms (block_perm (S size) (b, 0)) *
  malloc_Perms.
Proof.
  simpl.
  induction n.
  - simpl. do 2 eexists. split; [| split].
    + do 2 eexists. split; [| split; reflexivity].
      eexists. exists bottom_perm. split; [| split; reflexivity].
      eexists. split; [exists (VNum 0); reflexivity |].
      eexists. exists bottom_perm. split; [| split; reflexivity]; simpl; reflexivity.
    + eexists. split; [exists (b + 1); reflexivity | simpl; reflexivity].
    + repeat rewrite sep_conj_perm_bottom. constructor; auto.
      { intros [] (? & ? & ?). simpl in *.
        rewrite Nat.sub_0_r in *. rewrite Nat.add_0_r in *.
        split; split; auto.
        - split; auto. symmetry. apply write_block.
        - symmetry. apply separate_sep_conj_perm.
          + apply malloc_write. simpl. lia.
          + apply malloc_block; simpl; lia.
          + apply write_block.
      }
      { intros [] [] (? & ? & ?). simpl in *.
        rewrite Nat.sub_0_r in *. rewrite Nat.add_0_r in *. auto. }
      { intros [] [] H. rewrite sep_conj_perm_assoc in H.
        rewrite Nat.sub_0_r in *. rewrite Nat.add_0_r in *.
        unfold post_malloc_perm. unfold guar. unfold guar_post_malloc.
        unfold "**". unfold guar. unfold guar in H. unfold "**" in H. unfold guar in H.
        replace (S size - 1) with size. 2: lia. apply H. (* TODO simplify this *)
      }
  - simpl.
    assert (Hn': (n <= size)%nat) by lia.
    specialize (IHn (Vector.tl xs) Hn').
    rewrite Nat.add_0_r in *.
    destruct IHn as (? & ? & ? & ? & ?).
    destruct H0 as (? & ? & ? & ? & ?).
    destruct H0 as (? & ? & ? & ? & ?).
    exists (write_perm (b, size - S n) (VNum 0) ** x).
    eexists. split; [| split]; eauto.
    {
      exists (write_perm (b, size - S n) (VNum 0) ** x1). eexists. split; [| split]. 2: apply H3.
      2: { rewrite sep_conj_perm_assoc. apply sep_conj_perm_monotone; auto. reflexivity. }
      do 2 eexists. split; [| split].
      - eexists. split. exists (VNum 0). reflexivity.
        eexists. exists bottom_perm. split; [| split]; simpl; reflexivity.
      - assert (Heq : size - S n + 1 = size - n) by lia. rewrite Heq. clear Heq.
        exists x3, x4. split; [| split]; eauto.
        rewrite arr_offset in *. simpl in *.
        assert (Heq : size - S n + 2 = size - n + 1) by lia. rewrite Heq. clear Heq. auto.
      - rewrite sep_conj_perm_bottom. reflexivity.
    }
    {
      etransitivity. 2: apply post_malloc_perm_extend; auto.
      rewrite sep_conj_perm_assoc. apply sep_conj_perm_monotone; auto. reflexivity.
    }
Qed.

Lemma Malloc xi xs size :
  xi :: eqp _ _ (S size) ▷ xs * malloc_Perms ⊢
  malloc xi ⤳
  Ret (Vector.const tt (S size), tt) :::
  (arr (W, 0, S size, trueP Si Ss)) ⋆ (blockPT _ _ (S size)) ∅ malloc_Perms.
Proof.
  intros p si ss Hp Hpre. pstep. unfold malloc.
  destruct Hp as (peq & pmalloc & Heq & Hpmalloc & Hlte). simpl in Heq. subst.
  destruct Hpmalloc as (? & (b & ?) & Hpmalloc); subst.
  (* read step *)
  rewritebisim @bind_trigger. econstructor; eauto; try reflexivity.
  (* write step *)
  rewritebisim @bind_trigger. unfold id. econstructor; eauto.
  { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & _).
    apply Hpmalloc in Hpre. apply Hlte. constructor 1. right. apply Hpmalloc.
    simpl in *.
    intros ptr Hb. split; rewrite lGetPut.
    - unfold read, allocated. subst. rewrite nth_error_app_early; auto.
    - unfold sizeof. subst. rewrite nth_error_app_early; auto.
  }
  (* return *)
  { eapply sep_step_lte. etransitivity. 2: apply Hlte.
    etransitivity. 2: apply lte_r_sep_conj_perm. apply Hpmalloc.
    apply sep_step_malloc with (size := size).
  }
  { apply Hlte in Hpre. destruct Hpre as (_ & Hpre & Hlte').
    apply Hpmalloc in Hpre. simpl in Hpre.
    constructor.
    - simpl. split; [| split]; rewrite lGetPut.
      + rewrite last_length. lia.
      + unfold sizeof. simpl.
        rewrite nth_error_app_last; auto.
      + intros. unfold read, allocated. simpl. rewrite nth_error_app_last; auto.
        rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H0. rewrite H0. auto.
    - unfold "∅", "⋆", ptApp.
      setoid_rewrite Hpre.
      replace 0 with (size - size) at 2. 2: lia.
      apply post_malloc_perm_ok; auto.
  }
Qed.

(* helper lemma for Free *)
Lemma combined_arr_guar {A} p parr b len n bytes (v : Vector.t A n) (si : Si) (ss : Ss)
      (Hb : b < length (lget si))
      (Hn: (n <= (S len))%nat)
      (Hlte : parr <= p)
      (Hblock: nth_error (lget si) b = Some (Some (LBlock (S len) bytes)))
      (Hparr: parr ∈ VPtr (b, 0) :: arr (W, (S len) - n, n, trueP Si Ss) ▷ v) :
  let si' := lput si (replace_n (lget si) b (S len) bytes n) in
  (forall ptr', b <> fst ptr' -> read (lget si) ptr' = read (lget si') ptr') ->
  (forall ptr', sizeof (lget si) ptr' = sizeof (lget si') ptr') ->
  length (lget si) = length (lget si') ->
  guar p (si, ss) (si', ss).
Proof.
  revert Hlte Hparr Hblock Hb Hn. revert b parr v. revert n.
  induction n; intros.
  - apply Hlte. subst si'. simpl in *.
    rewrite replace_n_0; auto. rewrite lPutGet. reflexivity.
  - destruct Hparr as (pptr & parr' & Hpptr & Hparr' & Hlte').
    etransitivity.
    {
      eapply IHn; try lia; try rewrite lGetPut.
      2: { simpl in Hparr'. rewrite Nat.sub_succ_l. eauto. lia. }
      - etransitivity; eauto. etransitivity; eauto. apply lte_r_sep_conj_perm.
      - simpl. auto.
      - lia.
      - simpl. intros. pose proof @read_replace_n_neq; eauto.
      - simpl. intros. pose proof sizeof_replace_n; eauto.
      - apply replace_list_index_length; auto.
    }
    {
      subst si'. simpl. apply Hlte. apply Hlte'. constructor 1. left.
      destruct Hpptr as (val & (? & ?) & Hpptr); subst.
      destruct Hpptr as (pwrite & p' & Hpwrite & _ & Hlte'').
      apply Hlte''. constructor 1. left.
      apply Hpwrite. simpl.
      split; [| split]; auto; repeat rewrite lGetPut in *.
      - intros. destruct (Nat.eq_dec b (fst ptr')).
        2: { pose proof read_replace_n_neq. simpl in H3. repeat rewrite <- H4; auto. }
        subst. destruct ptr' as [b o]. simpl in *.
        assert (Hneq: len - n <> o).
        { apply addr_neq_cases in H3. destruct H3; auto. }
        unfold replace_n, read, allocated. simpl.
        repeat rewrite nth_error_replace_list_index_eq; auto.
        destruct (o <? S len) eqn:?; auto.
        rewrite Bool.andb_true_l. simpl.
        destruct (S len - n <=? o) eqn:?.
        + pose proof Heqb1.
          assert (Himpl: (S len - n <= o -> len - n <= o)%nat) by lia.
          rewrite <- (Bool.reflect_iff _ _ (Nat.leb_spec0 _ _)) in H4. apply Himpl in H4.
          rewrite (Bool.reflect_iff _ _ (Nat.leb_spec0 _ _)) in H4.
          rewrite H4. simpl in Heqb1. rewrite Heqb1. auto.
        + pose proof Heqb1.
          simpl in Heqb1. rewrite Heqb1.
          apply Nat.leb_gt in H4.
          assert (len - n > o) by lia.
          apply leb_correct_conv in H5. rewrite H5. auto.
      - intros. pose proof sizeof_replace_n. simpl in H3. rewrite <- H3; auto.
      - unfold replace_n. erewrite <- replace_list_index_length; eauto.
    }
Qed.

Lemma Free {A} xi len (xs : Vector.t A (S len) * unit) :
  xi :: (arr (W, 0, (S len), trueP Si Ss)) ⋆ (blockPT _ _ (S len)) ▷ xs ⊢
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
  unfold memory in *.
  destruct (nth_error (lget si) (fst ptr)) eqn:?; try solve [inversion Hpreblock].
  destruct o; try solve [inversion Hpreblock].
  destruct l. inversion Hpreblock; clear Hpreblock; subst.
  (* write step *)
  rewritebisim @bind_trigger. unfold id. econstructor; auto.
  - apply Hlte. constructor 1. left.
    assert (Hb: fst ptr < length (lget si)).
    { apply nth_error_Some. intro. rewrite H0 in Heqo. inversion Heqo. }
    erewrite replace_n_same.
    eapply combined_arr_guar; eauto; try reflexivity; try rewrite lGetPut.
    + destruct ptr. simpl in Hoffset. subst. rewrite Nat.sub_diag. apply Hparr.
    + intros. erewrite read_replace_n_neq; eauto.
    + intros. erewrite sizeof_replace_n; eauto.
    + apply replace_list_index_length; auto.
  - apply sep_step_lte'. apply bottom_perm_is_bottom.
  - constructor; simpl; auto.
Qed.
*)

(** * Recursive and reachability rules *)

Lemma MuFold A G X `{FixedPoint G X} (F : @PermType Si Ss A X -> @PermType Si Ss A (G X))
      {prp : Proper (lte_PermType ==> lte_PermType) F}
      xi xs :
  xi :: F (mu F) ▷ xs ⊨2 xi :: mu F ▷ foldFP xs.
Proof.
  (* FIXME: why can't we just rewrite with mu_fixed_point here? *)
  eapply Proper_eq_Perms2_lte_Perms2; [ | reflexivity | ].
  - apply Proper_eq_PermType_ptApp; [ apply mu_fixed_point | | ]; reflexivity.
  - simpl. rewrite foldUnfold. reflexivity.
Qed.

Lemma MuUnfold A G X `{FixedPoint G X} (F : @PermType Si Ss A X -> @PermType Si Ss A (G X))
      {prp : Proper (lte_PermType ==> lte_PermType) F}
      xi xs :
   xi :: mu F ▷ xs ⊨2 xi :: F (mu F) ▷ unfoldFP xs.
Proof.
  eapply Proper_eq_Perms2_lte_Perms2; [ reflexivity | | ].
  - apply Proper_eq_PermType_ptApp; [ apply mu_fixed_point | | ]; reflexivity.
  - simpl. reflexivity.
Qed.

(* Program Definition list_reach_perm r rw A (T : VPermType Si Ss A) : VPermType Si Ss (list A) := *)
(*   @mu _ _ _ (mu_list A) _ (fixed_point_list _) *)
(*       (fun U => or _ _ (eqp Si Ss r) ((ptr _ _ (rw, 0, T)) ⋆ (ptr _ _ (rw, 1, U)))) _. *)
(* Next Obligation. *)
(*   repeat intro. simpl. induction b; simpl in *; auto. *)
(*   destruct H0 as (? & ? & ? & ? & ?). exists x0, x1. split; [| split]; auto. *)
(*   clear H0. unfold ptr_Perms in *. destruct (offset a 1); auto. *)
(*   destruct H1. destruct H0. destruct H0. subst. destruct H1 as (? & ? & ? & ? & ?). *)
(*   eexists. split; eauto. do 2 eexists. split; eauto. split; eauto. apply H. auto. *)
(* Qed. *)

(*
Lemma ReflR {A} x rw o (T : @VPermType Si Ss A) :
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
    repeat intro. eapply mu_fixed_point in H0; auto.
    Unshelve. all: apply reach_perm_proper.
Qed.

(*
   while (v != NULL)
         v = *(v + 1);
   return 0;
*)
Definition ex3i' : Value -> itree (sceE Si) Value :=
  iter (C := Kleisli _)
       (fun v =>  b <- isNull v;;
               if (b : bool)
               then Ret (inr (VNum 0)) (* v == NULL *)
               else v' <- load (offset v 1);; (* continue with *(v + 1) *)
               Ret (inl v')).

Definition ex3s' {A} : list A -> itree (sceE Ss) unit :=
  iter (C := Kleisli _)
       (fun l => sum_rect
                (fun _ => itree (sceE Ss) (list A + unit))
                (fun _ : unit => Ret tt;; Ret (inr tt))
                (fun '(h, t) => Ret (inl t))
                (unfoldFP l)).

Lemma ex3'_typing A xi xs (T : VPermType _ _ A) :
  xi :: list_perm _ _ R _ T ▷ xs ⊢
  ex3i' xi ⤳
  ex3s' xs :::
  (trueP _ _).
Proof.
  unfold ex3i', ex3s'. apply Iter.
  intros. unfold list_perm. eapply Weak; [| reflexivity |].
  eapply MuUnfold. rewrite <- sep_conj_Perms_bottom_identity.
  eapply OrE; setoid_rewrite sep_conj_Perms_bottom_identity.
  - intros []. eapply Bind; [apply IsNull2 |].
    intros ? []. remember true.
    assert ((Ret (inr tt) : itree (sceE Ss) ((list A) + unit)) =
            (if b then Ret (inr tt) else throw tt)) by (subst; auto).
    rewrite H0; clear H0. rewrite <- sep_conj_Perms_bottom_identity.
    eapply If; [| apply Err].
    eapply Weak; [| reflexivity | apply Ret_].
    etransitivity. 2: apply SumI2. reflexivity.
  - intros (? & ?).
    eapply Weak; [| reflexivity |].
    apply StarE.
    rewrite sep_conj_Perms_commut.
    replace (Ret (inl l)) with (Ret tt;; (Ret (inl l) : itree (sceE Ss) (list A + unit))).
    2: { rewritebisim @bind_ret_l. reflexivity. }
    rewrite sep_conj_Perms_commut.
    eapply PtrE. intros zi.
    eapply Bind.
    { (* isNull *)
      rewrite <- sep_conj_Perms_assoc.
      eapply Frame.
      apply IsNull1.
    }
    (* if *)
    intros ? [].
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone.
    apply PermsE. reflexivity.
    rewrite <- sep_conj_Perms_assoc.
    rewrite sep_conj_Perms_commut.
    remember false.
    assert ((Ret (inl l) : itree (sceE Ss) ((list A) + unit)) =
            (if b then throw tt else Ret (inl l))) by (subst; auto).
    rewrite H0; clear H0. apply If; [apply Err |].
    (* drop the 0 offset perm *)
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [apply bottom_Perms_is_bottom | reflexivity].
    rewrite sep_conj_Perms_bottom_identity.
    replace (Ret (inl l)) with (Ret tt;; (Ret (inl l) : itree (sceE Ss) (list A + unit))).
    2: { rewritebisim @bind_ret_l. reflexivity. }
    eapply Bind.
    (* load offset 1 *)
    eapply Frame.
    eapply Weak; [| reflexivity |].
    apply PtrOff with (o2 := 1); auto.
    eapply Load.
    (* iterate *)
    intros v [].
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone.
    apply PermsE. reflexivity.
    rewrite <- sep_conj_Perms_assoc.
    rewrite sep_conj_Perms_commut.
    rewrite <- sep_conj_Perms_assoc.
    eapply Weak; [| reflexivity |].
    apply sep_conj_Perms_monotone; [apply bottom_Perms_is_bottom | reflexivity].
    rewrite sep_conj_Perms_bottom_identity.
    rewrite sep_conj_Perms_commut.
    eapply Weak; [apply Cast | reflexivity |].
    eapply Weak; [| reflexivity | apply Ret_].
    etransitivity. 2: apply SumI1. reflexivity.
Qed.

(*
  n = 0;
  while (v != NULL) {
        v = *(v + 1);
        n++;
  }
*)
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
*)
