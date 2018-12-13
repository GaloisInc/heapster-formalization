Require Import OrderedTypeEx.
Require Import FMapAVL FMapFacts.
Require Import BinNat ZArith.
Require Import Heapster.Integers.
Open Scope Z_scope.

Module Int64 := Integers.Int64.

Definition i64 := Int64.int.
Coercion Z_of := Int64.intval.

Module Int64MOrd <: MiniOrderedType.
  Definition t := Int64.int.
  Definition eq := fun (x y:t) => Int64.eq x y = true.
  Definition lt (x:t) (y:t) : Prop := Int64.lt x y = true.

  Lemma eq_refl : forall a : t, eq a a.
  Proof.
    unfold eq. apply Int64.eq_true. 
  Qed.

  Lemma eq_sym : forall a b : t, eq a b -> eq b a.
  Proof.
    unfold eq. intros a b H.
    rewrite Int64.eq_sym. assumption.
  Qed.

  Lemma eq_trans : forall a b c : t, eq a b -> eq b c -> eq a c.
  Proof.
    unfold eq.
    intros a b c H H0.
    pose (Int64.eq_spec a b). rewrite H in y. subst.
    pose (Int64.eq_spec b c). rewrite H0 in y. subst.
    apply Int64.eq_true.
  Qed.


  Lemma lt_trans : forall a b c : t, lt a b -> lt b c -> lt a c.
  Proof.
    unfold lt. unfold Int64.lt. 
    intros a b c H H0.
    destruct (Coqlib.zlt (Int64.signed a) (Int64.signed b)).
    - destruct (Coqlib.zlt (Int64.signed b) (Int64.signed c)).
      + destruct (Coqlib.zlt (Int64.signed a) (Int64.signed c)).
        * reflexivity.
        * cut False; [contradiction|omega].
      + inversion H0.
    - inversion H.
  Qed.

  Lemma lt_not_eq : forall a b:t, lt a b -> ~eq a b.
  Proof.
    unfold lt. unfold eq.
    unfold Int64.lt.
    intros a b H.
    destruct (Coqlib.zlt (Int64.signed a) (Int64.signed b)).
    - unfold not. intros. 
      pose (Int64.eq_spec a b). rewrite H0 in y. 
      subst. omega.
    - inversion H.
  Qed.

  Lemma signed_unsigned_eq : forall a b, (Int64.signed a = Int64.signed b) <-> (Int64.unsigned a = Int64.unsigned b).
  Proof.
    intros a b. unfold Int64.signed. unfold Int64.unsigned.
    destruct a. destruct b. simpl. 
    split.
    - intros. destruct (Coqlib.zlt intval Int64.half_modulus).
      destruct (Coqlib.zlt intval0 Int64.half_modulus).
      assumption.
      subst. omega.
      destruct (Coqlib.zlt intval0 Int64.half_modulus).
      omega. omega.
    - intros. subst. reflexivity.
  Qed.



  Program Definition compare (a:t) (b:t) : Compare lt eq a b :=
    match Coqlib.zlt (Int64.signed a) (Int64.signed b) with
    | left x => LT _
    | right y => match Coqlib.zlt (Int64.signed b) (Int64.signed a) with
                | left x1 => GT _
                | right y1 => EQ _
                end
    end.
  Next Obligation.
    unfold lt. unfold Int64.lt. rewrite <- Heq_anonymous. reflexivity.
  Defined.
  Next Obligation.
    unfold lt. unfold Int64.lt. rewrite <- Heq_anonymous. reflexivity.
  Defined.
  Next Obligation.
    unfold eq.
    assert (Int64.signed a = Int64.signed b).
    omega.
    apply signed_unsigned_eq in H.
    destruct a. destruct b.
    unfold Int64.eq. simpl in *. subst. 
    rewrite Coqlib.zeq_true. reflexivity.
  Defined.

End Int64MOrd.

Module Int64Ord := MOT_to_OT(Int64MOrd).

Module IM := FMapAVL.Make(Int64Ord).
Module IMFacts := FMapFacts.WFacts_fun(Int64Ord)(IM).
Module IMOrdFacts := FMapFacts.OrdProperties(IM).

Definition Int64Map := IM.t.

Definition size {a} (m : IM.t a) : N := N.of_nat (IM.cardinal m).
Definition insert {a} k (v:a) := IM.add k v.
Definition delete {a} k (m:Int64Map a) := IM.remove k m.
Definition member {a} k (m:Int64Map a) := IM.mem k m.
Definition lookup {a} k (m:Int64Map a) := IM.find k m.
Definition empty {a} := @IM.empty a.
Definition defined_at {a} (m:Int64Map a) (k:Int64.int) : Prop := member k m = true.

