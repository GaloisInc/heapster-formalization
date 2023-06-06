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

From Heapster Require Export
     Utils
     Permissions
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

Section Rules.
  Context (Si Ss:Type).

  (** * Basic permission connective rules *)

  Lemma Weak (A B : Type) P1 P2 (U1 U2 : @PermType Si Ss A B) ts ti :
    P1 ⊨ P2 ->
    (forall xi xs, xi :: U2 ▷ xs ⊨ xi :: U1 ▷ xs) ->
    P2 ⊢ ts ⤳ ti ::: U2 ->
    P1 ⊢ ts ⤳ ti ::: U1.
  Proof.
    intros. eapply typing_lte; eauto.
  Qed.

  Lemma ProdI (A1 A2 B1 B2 : Type) xi yi xs ys (T1 : @PermType Si Ss A1 B1) (T2 : @PermType Si Ss A2 B2) :
    xi :: T1 ▷ xs * yi :: T2 ▷ ys ⊨ (xi, yi) :: T1 ⊗ T2 ▷ (xs, ys).
  Proof. reflexivity. Qed.

  Lemma ProdE (A1 A2 B1 B2 : Type) xi xs (T1 : @PermType Si Ss A1 B1) (T2 : @PermType Si Ss A2 B2) :
    xi :: T1 ⊗ T2 ▷ xs ⊨ fst xi :: T1 ▷ fst xs * snd xi :: T2 ▷ snd xs.
  Proof. reflexivity. Qed.

  Lemma SumI1 (A1 A2 B1 B2 : Type) (xi : A1) (xs : B1) (T1 : @PermType Si Ss A1 B1) (T2 : @PermType Si Ss A2 B2) :
    xi :: T1 ▷ xs ⊨ inl xi :: T1 ⊕ T2 ▷ inl xs.
  Proof. reflexivity. Qed.

  Lemma SumI2 (A1 A2 B1 B2 : Type) (xi : A2) (xs : B2) (T1 : @PermType Si Ss A1 B1) (T2 : @PermType Si Ss A2 B2) :
    xi :: T2 ▷ xs ⊨ inr xi :: T1 ⊕ T2 ▷ inr xs.
  Proof. reflexivity. Qed.

  Lemma SumE (A1 A2 B1 B2 R1 R2 : Type)
        (xi : A1 + A2) (xs : B1 + B2) ti1 ti2 ts1 ts2
        (T1 : @PermType Si Ss A1 B1) (T2 : @PermType Si Ss A2 B2) (P : Perms) (U : @PermType Si Ss (A1 + A2) (B1 + B2)) :
    (forall yi ys, P * yi :: T1 ▷ ys ⊢ ti1 yi ⤳ ts1 ys ::: U) ->
    (forall yi ys, P * yi :: T2 ▷ ys ⊢ ti2 yi ⤳ ts2 ys ::: U) ->
    P * xi :: T1 ⊕ T2 ▷ xs ⊢ sum_rect _ ti1 ti2 xi ⤳ sum_rect _ ts1 ts2 xs ::: U.
  Proof.
    intros. simpl.
    destruct xi, xs; cbn; auto;
      rewrite sep_conj_Perms_commut; rewrite sep_conj_Perms_top_absorb; apply typing_top.
  Qed.

  Lemma StarI (A B1 B2 : Type) xi xs ys (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
    xi :: T1 ▷ xs * xi :: T2 ▷ ys ⊨ xi :: T1 ⋆ T2 ▷ (xs, ys).
  Proof. reflexivity. Qed.

  Lemma StarE (A B1 B2 : Type) xi xs (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
    xi :: T1 ⋆ T2 ▷ xs ⊨ xi :: T1 ▷ fst xs * xi :: T2 ▷ snd xs.
  Proof. reflexivity. Qed.

  Lemma PermsI (A B : Type) (P : Perms) xi xs (T : @PermType Si Ss A B) :
    xi :: T ▷ xs * P ⊨ xi :: T ∅ P ▷ xs.
  Proof. reflexivity. Qed.

  Lemma PermsE (A B : Type) (P : Perms) xi xs (T : @PermType Si Ss A B) :
    xi :: T ∅ P ▷ xs ⊨ xi :: T ▷ xs * P.
  Proof. reflexivity. Qed.

  Lemma Frame (A B : Type) (P1 P2 : Perms) ti ts (T : @PermType Si Ss A B) :
    P1 ⊢ ti ⤳ ts ::: T ->
    P1 * P2 ⊢ ti ⤳ ts ::: T ∅ P2.
  Proof. apply typing_frame. Qed.

  Lemma OrI1 (A B1 B2 : Type) xi xs (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
    xi :: T1 ▷ xs ⊨ xi :: or T1 T2 ▷ inl xs.
  Proof. reflexivity. Qed.

  Lemma OrI2 (A B1 B2 : Type) xi xs (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) :
    xi :: T2 ▷ xs ⊨ xi :: or T1 T2 ▷ inr xs.
  Proof. reflexivity. Qed.

  Lemma OrE (A B1 B2 C1 C2 D : Type)
        (xi : A) (xs : B1 + B2) ti ts1 ts2
        (T1 : @PermType Si Ss A B1) (T2 : @PermType Si Ss A B2) (P : Perms) (U : @PermType Si Ss D (C1 + C2)) :
    (forall ys, P * xi :: T1 ▷ ys ⊢ ti ⤳ ts1 ys ::: U) ->
    (forall ys, P * xi :: T2 ▷ ys ⊢ ti ⤳ ts2 ys ::: U) ->
    P * xi :: or T1 T2 ▷ xs ⊢ ti ⤳ sum_rect _ ts1 ts2 xs ::: U.
  Proof.
    intros. destruct xs; cbn; auto.
  Qed.

  Lemma TrueI (A : Type) (P : @Perms (Si * Ss)) (xi : A) :
    P ⊨ P * xi :: trueP ▷ tt.
  Proof.
    rewrite sep_conj_Perms_commut. rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.

  Lemma ExI (A B : Type) (C : B -> Type) (xi : A) (ys : B) (xs : C ys)
        (F : forall (b : B), @PermType Si Ss A (C b)) :
    xi :: F ys ▷ xs ⊨ xi :: ex (z oftype B) (F z) ▷ existT (fun b : B => C b) ys xs.
  Proof. reflexivity. Qed.

  Lemma ExE (A B : Type) (C : B -> Type) (xi : A) (xs : sigT (fun b : B => C b))
        (F : forall (b : B), @PermType Si Ss A (C b)) :
    xi :: ex (z oftype B) (F z) ▷ xs ⊨ xi :: F (projT1 xs) ▷ (projT2 xs).
  Proof. reflexivity. Qed.

  (** * Equality rules *)

  Lemma EqRefl A (P : @Perms (Si * Ss)) (xi : A) :
    P ⊨ P * xi :: eqp xi ▷ tt.
  Proof.
    repeat intro.
    exists p, bottom_perm. split; [| split; [| split]]; cbn; eauto.
    - apply separate_bottom.
    - rewrite sep_conj_perm_bottom. reflexivity.
  Qed.

  Lemma EqSym (A : Type) (xi yi : A) :
    xi :: @eqp Si Ss _ yi ▷ tt ⊨ yi :: eqp xi ▷ tt.
  Proof.
    repeat intro; cbn in *; subst; reflexivity.
  Qed.

  Lemma EqTrans (A : Type) (xi yi zi : A) :
    xi :: @eqp Si Ss _ yi ▷ tt * yi :: eqp zi ▷ tt ⊨ xi :: eqp zi ▷ tt.
  Proof.
    repeat intro. destruct H as (? & ? & ? & ? & ? & ?). cbn in *; subst. reflexivity.
  Qed.

  Lemma EqCtx (A B : Type) (xi yi : A) (f : A -> B) :
    xi :: eqp yi ▷ tt ⊨ f xi :: @eqp Si Ss _ (f yi) ▷ tt.
  Proof.
    repeat intro. congruence.
  Qed.

  Lemma EqDup (A : Type) (xi yi : A) :
    xi :: @eqp Si Ss _ yi ▷ tt ⊨ xi :: eqp yi ▷ tt * xi :: eqp yi ▷ tt.
  Proof.
    repeat intro. cbn in *. subst. exists bottom_perm, bottom_perm.
    split; [| split; [| split]]; auto.
    - apply separate_bottom.
    - rewrite sep_conj_perm_bottom. apply bottom_perm_is_bottom.
  Qed.

  Lemma Cast (A B : Type) (P : @PermType Si Ss A B) xi yi xs ys :
    xi :: eqp yi ▷ xs * yi :: P ▷ ys ⊨ xi :: P ▷ ys.
  Proof.
    repeat intro. destruct H as (e & p' & Heq & Hp & Hsep & Hlte).
    cbn in Heq. subst.
    eapply Perms_upwards_closed; eauto. etransitivity. apply lte_r_sep_conj_perm. eauto.
  Qed.

  (** * Instruction rules *)
  (** Name conflicts with ITree Ret. *)
  Lemma Ret_ (A B : Type) xi xs (T : @PermType Si Ss A B) :
    xi :: T ▷ xs ⊢ Ret xi ⤳ Ret xs ::: T.
  Proof.
    repeat intro. pstep. constructor; auto.
  Qed.

  Lemma Bind (A B C D : Type) P ti ts fi fs (T : @PermType Si Ss A B) (U : @PermType Si Ss C D) :
    P ⊢ ti ⤳ ts ::: T ->
    (forall xi xs, xi :: T ▷ xs ⊢ fi xi ⤳ fs xs ::: U) ->
    P ⊢ ITree.bind ti fi ⤳ ITree.bind ts fs ::: U.
  Proof.
    intros. eapply typing_bind; eauto.
  Qed.

  Lemma GetNum xi yi :
    xi :: @eqp Si Ss _ (VNum yi) ▷ tt ⊢ getNum xi ⤳ Ret tt ::: eqp yi.
  Proof.
    repeat intro. cbn in *. subst. cbn. pstep. constructor; auto. reflexivity.
  Qed.

  Lemma Iter (A B C D : Type) (T : @PermType Si Ss C D) xi xs fi fs (U : @PermType Si Ss A B) :
    (forall yi ys, yi :: T ▷ ys ⊢ fi yi ⤳ fs ys ::: T ⊕ U) ->
    xi :: T ▷ xs ⊢ iter fi xi ⤳ iter fs xs ::: U.
  Proof.
    revert xi xs fi fs U. pcofix CIH. intros.
    do 2 rewritebisim @unfold_iter_ktree.
    eapply sbuter_bind; eauto.
    - apply H0; auto.
    - cbn. intros. destruct r1, r2; try contradiction.
      + repeat intro. pstep. constructor 5; eauto.
      + pstep. constructor; auto.
  Qed.

  Lemma If (A B : Type) P ti1 ti2 ts1 ts2 (xi yi : bool) xs (U : @PermType Si Ss A B) :
    P ⊢ ti1 ⤳ ts1 ::: U ->
    P ⊢ ti2 ⤳ ts2 ::: U ->
    P * xi :: eqp yi ▷ xs ⊢ if xi then ti1 else ti2 ⤳ if yi then ts1 else ts2 ::: U.
  Proof.
    repeat intro. destruct H1 as (p' & q & Hp' & ? & Hsep & Hlte); cbn in *; subst.
    destruct xi.
    - apply H; auto. eapply Perms_upwards_closed; eauto.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
    - apply H0; auto. eapply Perms_upwards_closed; eauto.
      etransitivity; eauto. apply lte_l_sep_conj_perm.
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
    ex (n oftype nat) eqp (VNum n).

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
    eapply Weak; [apply ExI with (F := fun n : nat => eqp (VNum n)) | reflexivity |]; fold IsNat.
    (* Ret *)
    apply Ret_.
  Qed.

  (** * Recursive and reachability rules *)

  Lemma MuFold A G X `{FixedPoint G X} (F : @PermType Si Ss A X -> @PermType Si Ss A (G X))
        {prp : Proper (lte_PermType ==> lte_PermType) F}
        xi xs :
    xi :: F (mu F) ▷ xs ⊨ xi :: mu F ▷ foldFP xs.
  Proof.
    (* FIXME: why can't we just rewrite with mu_fixed_point here? *)
    eapply Proper_eq_Perms_lte_Perms; [ | reflexivity | ].
    - apply Proper_eq_PermType_ptApp; [ apply mu_fixed_point | | ]; reflexivity.
    - simpl. rewrite foldUnfold. reflexivity.
  Qed.

  Lemma MuUnfold A G X `{FixedPoint G X} (F : @PermType Si Ss A X -> @PermType Si Ss A (G X))
        {prp : Proper (lte_PermType ==> lte_PermType) F}
        xi xs :
    xi :: mu F ▷ xs ⊨ xi :: F (mu F) ▷ unfoldFP xs.
  Proof.
    eapply Proper_eq_Perms_lte_Perms; [ reflexivity | | ].
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
   while (v != NULL)
         v = *(v + 1);
   return 0;
   *)
  (*
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
End Rules.
