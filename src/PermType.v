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
     Config
     Functional.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import MonadNotation.

Section permType.
  Context (Si Ss:Type).
  Context `{Lens Si config}.

  Record PermType (A B:Type) : Type :=
    { ptApp : A -> B -> @Perms (Si*Ss) }.
  Definition VPermType A := PermType Value A.
  Notation "xi : T @ xs" := (ptApp _ _ T xi xs) (at level 35).

  Definition withPerms {Ai As} (T: PermType Ai As) (P:@Perms (Si * Ss)) : PermType Ai As:=
    {| ptApp:= fun ai abs => ai : T @ abs * P|}.
  Notation "T ∅ P" := (withPerms T P) (at level 40).

  Definition starPT {Ai As Bs} (T:PermType Ai As) (U:PermType Ai Bs)
    : PermType Ai (As * Bs) :=
    {| ptApp := fun ai abs => ai : T @ fst abs * ai : U @ snd abs |}.

  Definition existsPT {Ai As} {Bs:As -> Type}
             (F : forall a, PermType Ai (Bs a)) : PermType Ai (sigT Bs) :=
    {| ptApp := fun ai abs => ai : F (projT1 abs) @ (projT2 abs) |}.
  Notation "'ex' ( x : A ) . T" := (existsPT (As:=A) (fun x => T)) (at level 70).

  Definition either {A B C} (f:A -> C) (g:B -> C) (x:A+B): C :=
    match x with inl a => f a | inr b => g b end.
  Definition or {Ai As Bs} (T1:PermType Ai As)
             (T2:PermType Ai Bs) : PermType Ai (As + Bs) :=
    {| ptApp := fun ai abs =>
                  either (ptApp _ _ T1 ai) (ptApp _ _ T2 ai) abs |}.


  Variant RW: Type := R | W.

  Definition trueP {A B} : PermType A B :=
    {| ptApp := fun _ _ => bottom_Perms |}.
  Definition falseP {A B} : PermType A B :=
    {| ptApp := fun _ _ => top_Perms |}.

  Definition offset (v : Value) (o : nat) : Value :=
    match v with
    | VNum n => VNum n
    | VPtr (blk, n) => VPtr (blk, n + o)
    end.

  Definition ptr_Perms {A} (rw : RW) (p : Value) (a : A) T : @Perms (Si * Ss) :=
    match p with
    | VNum _ => top_Perms
    | VPtr p =>
      meet_Perms (fun P => exists v, P = singleton_Perms (match rw with
                                                  | R => read_perm p v
                                                  | W => write_perm p v
                                                  end)
                                 * (v : T @ a))
    end.

  Definition ptr {A} '(rw, o, T) : VPermType A :=
    {|
    ptApp := fun x a => ptr_Perms rw (offset x o) a T;
    |}.

  Fixpoint arr_perm {A} rw o l T
    : VPermType (Vector.t A l) :=
    match l with
    | 0 => trueP
    | S l' =>
      {| ptApp := fun xi xss =>
                    xi : ptr (rw, o, T) @ Vector.hd xss *
                    xi : arr_perm rw (S o) l' T @ Vector.tl xss
      |}
    end.
  Notation "'arr' ( rw , o , l , T )":=(arr_perm rw o l T).

  Definition plusPT {A1 A2 B1 B2}
             (T1:PermType A1 B1) (T2:PermType A2 B2) : PermType (A1+A2) (B1+B2) :=
    {| ptApp := fun eithA eithB =>
                  match (eithA,eithB) with
                  | (inl a1, inl b1) => a1 : T1 @ b1
                  | (inr a2, inr b2) => a2 : T2 @ b2
                  | _ => top_Perms
                  end |}.
  Notation "T1 +T+ T2" := (plusPT T1 T2) (at level 50).

  Definition timesPT {A1 A2 B1 B2}
             (T1:PermType A1 B1) (T2:PermType A2 B2) : PermType (A1*A2) (B1*B2) :=
    {| ptApp := fun a12 b12 =>  fst a12 : T1 @ fst b12 * snd a12 : T2 @ snd b12 |}.
  Notation "T1 *T* T2" := (timesPT T1 T2) (at level 40).

  Program Definition equals_perm {A} (a1 a2 : A): @perm (Si*Ss) := {|
    rely _ _ := True; guar s1 s2 := s1=s2; pre _ := a1=a2; |}.
  Next Obligation.
     repeat constructor.
  Defined.
  Next Obligation.
    repeat constructor. intros x y z e1 e2. transitivity y; assumption.
  Defined.

  Program Definition eqp {A} (a:A): PermType A unit :=
    {| ptApp := fun a' _ => {| in_Perms _ := a=a' |} |}.

  Definition vsingle {A} (a:A) : Vector.t A 1 :=
    Vector.cons _ a _ (Vector.nil _).

  Definition ifz {A} n (x y:A) : A :=
    if Nat.eqb n 0 then x else y.

  Definition getNum {S} v : itree (sceE S) nat :=
    match v with VNum n => Ret n | VPtr _ => throw tt end.
  (* Definition addOff v o : Value := *)
  (*   match v with VNum n => VNum (n+o) *)
  (*           | VPtr (blk,n) => VPtr (blk,n+o) end. *)

  Definition isNull {S} v: itree (sceE S) bool :=
    match v with
    | VNum n => if Nat.eqb n 0 then Ret true else throw tt
    | VPtr _ => Ret false
    end.

  Definition meetF_Perms {A S} (F:A -> @Perms S) : @Perms S :=
    meet_Perms (fun P => exists a, P = F a).

  Fixpoint mapN {A} n (f:A -> A) (a:A) : A :=
    match n with 0 => a | S n' => f (mapN n' f a) end.
  Definition muPT {A B} (G:PermType A B -> PermType A B) : PermType A B :=
    {| ptApp := fun a b =>
                  meet_Perms (fun P => exists n, P = a : mapN n G falseP @ b) |}.
  Class FixedPoint (G:Type -> Type) X : Type :=
    { foldFP : G X -> X;
      unfoldFP : X -> G X;
      foldUnfold : forall gx, unfoldFP (foldFP gx) = gx;
      unfoldFold : forall x, foldFP (unfoldFP x) = x; }.
  Definition unmaprPT {A B C} (f:B -> C) (T:PermType A C) : PermType A B :=
    {| ptApp := fun a b => a : T @ (f b) |}.
  Definition mu {A G X} `{FixedPoint G X}
             (F:forall Y, PermType A Y -> PermType A (G Y)) : PermType A X :=
    muPT (fun T => unmaprPT unfoldFP (F X T)).
End permType.

Notation "P ⊢ ti ▷ ts ::: U" := (typing P (ptApp _ _ _ _ U) ti ts) (at level 60).
Notation "xi : T @ xs" := (ptApp _ _ _ _ T xi xs) (at level 35).
Notation "T1 +T+ T2" := (plusPT _ _ T1 T2) (at level 50).
Notation "T1 *T* T2" := (timesPT _ _ T1 T2) (at level 40).
(* Notation "'ex' ( x : A ) . T" := (existsPT _ _ (As:=A) (fun x => T)) (at level 70). *)
Notation "T ∅ P" := (withPerms _ _ T P) (at level 40).
Notation "'arr' ( rw , o , l , T )" := (arr_perm _ _ rw o l T) (at level 40).
