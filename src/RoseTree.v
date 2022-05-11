(** printing now %\coqdockw{now}% *)
(** printing simp %\coqdoctac{simp}% *)
(** printing by %\coqdockw{by}% *)
(** printing rec %\coqdockw{rec}% *)
(* begin hide *)
From Equations Require Import Equations.

Require Import Lia Utf8 List.

From Coq Require Import
     Arith.PeanoNat
     Bool.

Import ListNotations.
Set Keyed Unification.

Section list_size.
  Context {A : Type} (f : A -> nat).
  Equations list_size (l : list A) : nat :=
  list_size nil := 0;
  list_size (cons x xs) := S (f x + list_size xs).
  Global Transparent list_size.

  Context {B : Type}.
  Equations? list_map_size (l : list A)
           (g : forall (x : A), f x < list_size l -> B) : list B :=
  list_map_size nil _ := nil;
  list_map_size (cons x xs) g := cons (g x _) (list_map_size xs (fun x H => g x _)).

  Proof. auto with arith. lia. Defined.

  Lemma list_map_size_spec (g : A -> B) (l : list A) :
    list_map_size l (fun x _ => g x) = List.map g l.
  Proof.
    funelim (list_map_size l (λ (x : A) (_ : f x < list_size l), g x)); simpl; trivial.
    now rewrite H.
  Qed.
End list_size.

Require Import List.
(* end hide *)
(** To solve measure subgoals *)
#[local] Hint Extern 4 (_ < _) => simpl; lia : rec_decision.
Obligation Tactic := CoreTactics.equations_simpl; try (simpl; lia); try typeclasses eauto with rec_decision.

(* begin hide *)
Section RoseTree.
(* end hide *)
  (* Context {A : Type}. *)

  Inductive rose : Type :=
  | node (n : nat) (l : list rose) : rose.

  (** This is a nested inductive type we can measure assuming a
      [list_size] function for measuring lists. Here we use the usual
      guardedness check of %\Coq% that is able to unfold the
      definition of [list_size] to check that this definition is terminating. *)

  Equations size (r : rose) : nat :=
    size (node _ l) := S (list_size size l).

  (* begin hide *)
  Transparent size.
  Derive NoConfusion for rose.

  (* end hide *)
  Section Induction.
    Variable P : rose -> Prop.
    Hypothesis IH_NODE : forall n children, (forall u, In u children -> P u) -> P (node n children).

    Lemma rose_ind_strong : forall (t : rose), P t.
    Proof.
      fix IH 1.
      destruct t.
      apply IH_NODE.
      revert l.
      fix IHNODES 1. intros [|u children'].
      - intros. inversion H.
      - intros u' [<-|Hin].
        + apply IH.
        + eapply IHNODES. apply Hin.
    Qed.
  End Induction.

  Equations rose_eqb (r1 r2 : rose) : bool by wf (size r1) lt :=
    rose_eqb (node n1 []) (node n2 []) := Nat.eqb n1 n2;
    rose_eqb (node n1 (x :: xs)) (node n2 (y :: ys)) := rose_eqb (node n1 xs) (node n2 ys) && rose_eqb x y;
    rose_eqb _ _ := false.

  Lemma rose_eqb_refl : forall a, rose_eqb a a = true.
  Proof.
    induction a using rose_ind_strong.
    induction children; simp rose_eqb.
    - rewrite Nat.eqb_refl. reflexivity.
    - rewrite IHchildren. rewrite H; auto.
      + left. auto.
      + intros. apply H. right. auto.
  Qed.

  Lemma rose_eqb_n : forall l l' n n', rose_eqb (node n l) (node n' l') = true -> n = n'.
  Proof.
    induction l; intros; simp rose_eqb in H; try inversion H.
    2: {
      destruct l'. inversion H.
      simp rose_eqb in H. apply andb_prop in H. destruct H.
      eapply IHl; eauto.
    }
    destruct l'. simp rose_eqb in H. apply EqNat.beq_nat_true in H. auto.
    inversion H.
  Qed.

  Lemma rose_eqb_eq : forall a b, rose_eqb a b = true -> a = b.
  Proof.
    induction a using rose_ind_strong. induction children.
    - intros. destruct b. destruct l. 2: inversion H0.
      f_equal. apply rose_eqb_n in H0. auto.
    - intros. destruct b. destruct l. inversion H0.
      pose proof (rose_eqb_n _ _ _ _ H0). subst.
      simp rose_eqb in H0. f_equal.
      apply andb_prop in H0. destruct H0.
      f_equal.
      + apply H; auto. left. auto.
      + epose proof (IHchildren _).
        Unshelve.
        2: { intros. apply H; auto. right. auto. }
        specialize (H2 _ H0). inversion H2. auto.
  Qed.

  Lemma rose_eqb_spec : forall a b, reflect (a = b) (rose_eqb a b).
  Proof.
    intros. destruct (rose_eqb a b) eqn:?.
    - constructor 1. apply rose_eqb_eq; auto.
    - constructor 2. intro. subst. rewrite rose_eqb_refl in Heqb0. inversion Heqb0.
  Qed.

  Lemma rose_eq_dec : forall (a b : rose), {a = b} + {a <> b}.
  Proof.
    intros. apply (reflect_dec _ _ (rose_eqb_spec _ _)).
  Qed.

  Lemma rose_eqb_trans : forall a b c,
      rose_eqb a b = true ->
      rose_eqb b c = true ->
      rose_eqb a c = true.
  Proof.
    intros. apply rose_eqb_eq in H, H0. subst. apply rose_eqb_refl.
  Qed.

  Equations parent (r1 : rose) (r2 : rose) : bool by wf (size r2) lt :=
    parent r1 (node n l) := match find (rose_eqb r1) l with
                           | Some _ => true (* found directly at this level *)
                           | None => aux r1 l _ (* find at a lower level *)
                           end
  (* find in the lists in each [rose] in [l'] *)
  where aux r1' (l' : list rose) (H : list_size size l' < size (node _ l)) : bool
    by wf (list_size size l') lt :=
    aux _ nil _ := false;
    aux r1' (x :: xs) H := parent r1' x || aux r1' xs _.

  Goal parent (node 1 nil) (node 1 [node 1 [node 2 nil; node 1 nil]]) = true. auto. Qed.
  Goal parent (node 1 nil) (node 1 [node 1 [node 2 nil; node 3 nil]]) = false. auto. Qed.
  Goal parent (node 1 [node 2 nil; node 3 nil])
       (node 1 [node 1 [node 2 nil; node 3 nil]]) = true. auto. Qed.
  Goal parent (node 1 [node 2 nil])
       (node 1 [node 1 [node 2 nil; node 3 nil]]) = false. auto. Qed.

  Lemma parent_foo r n x xs :
    parent r (node n xs) = true ->
    parent r (node n (x :: xs)) = true.
  Proof.
    simp parent. simpl.
    intros. destruct (rose_eqb r x); auto. destruct (find (rose_eqb r) xs); auto.
  Abort.

  (* todo: rewrite this with parent in last case, then try using parents_elim *)
  Lemma parent_cases r n x xs :
    parent r (node n (x :: xs)) = true ->
    (exists i, find (rose_eqb r) (x :: xs) = Some i) \/ parent r x = true \/
      parent_unfold_clause_1_aux r n (x :: xs) r xs
        (parent_obligations_obligation_3 n (x :: xs) x xs
           (parent_obligations_obligation_5 n (x :: xs))) = true.
  Proof.
    intros. simp parent in H.
    destruct (find (rose_eqb r) (x :: xs)) eqn:Hfind; auto.
    left. eexists. auto.
    right.
    apply orb_prop in H. destruct H.
    left; auto. right. auto.
  Qed.

  Lemma parent_trans (r1 r2 r3 : rose) :
    parent r1 r2 = true ->
    parent r2 r3 = true ->
    parent r1 r3 = true.
  Proof.
    revert r2.
    (* revert r1 r2 r3. *)
    eapply (parent_elim
              (fun r1 r2 b => forall r',
                   parent r1 r' = true ->
                   parent r' r2 = true ->
                   (* parent r1 r2 = b -> *)
                   b = true)
              (fun r1 n l r' l' H b => forall r'',
                   r1 = r' ->
                   parent r1 r'' = true ->
                   parent r'' (node n l') = true ->
                   match find (rose_eqb r1) l' with
                   | Some _ => true
                   | None => b
                   end = true
           )).
    - intros. eapply H; eauto.
    - intros. inversion H2.
    - clear r1 r3. intros. subst. unfold find. fold (find (rose_eqb r1') xs).
      destruct (rose_eqb r1' x) eqn:Heqb; auto.
      destruct (find (rose_eqb r1') xs) eqn:Hfind; auto.
      apply parent_cases in H4. destruct H4 as [? | [? | ?]].
      + destruct H2. unfold find in H2. fold (find (rose_eqb r'') xs) in H2.
        destruct (rose_eqb r'' x) eqn:?.
        * inversion H2. subst.
          rewrite <- (reflect_iff _ _ (rose_eqb_spec r'' x0)) in Heqb0. subst.
          rewrite H3. auto.
        * erewrite H1; eauto.
          rewrite orb_true_r. auto.
          simp parent. rewrite H2. auto.
      + erewrite H0; eauto.
      + erewrite H1; eauto. rewrite orb_true_r. auto.
        (* eapply parent_foo. *)
          (* simp parent in H4. rewrite H *)
      (* erewrite H1. admit. *)
      (* apply H2. *)

      (* simp parent in H3. unfold find in H3. fold (find (rose_eqb r'') xs) in H3. rewrite Hfind in H3. *)
  Admitted.

    (** As explained at the beginning of this section, however, if we want
      to program more complex recursions, or rearrange our terms
      slightly and freely perform dependent pattern-matching, the
      limited syntactic guardness check will quickly get in our way.

      Using a _nested_ [where] clause and the support of %\Equations% for
      well-founded recursion, we can define the following function
      gathering the elements in a rose tree efficiently: *)

  Equations elements (r : rose) (acc : list rose) : list rose by wf (size r) lt :=
  elements (node n l) acc := aux l _
    where aux x (H : list_size size x < size (node _ l)) : list rose by wf (list_size size x) lt :=
    aux nil _ := acc;
    aux (cons x xs) H := elements x (aux xs _).

  Definition elems r := elements r nil.

  (** The function is nesting a well-founded recursion inside
    another one, based on the measure of [rose] trees and lists ([MR R
    f] is a combinator for [λ x y, R (f x) (f y)]).  The termination
    of this definition is ensured solely by logical means, it does not
    require any syntactic check. Note that the auxiliary definition's
    type mentions the variable [l] bound by the enclosing
    pattern-matching, to pass around information on the size of
    arguments. Local [where] clauses allow just that.
    This kind of nested pattern-matching and well-founded recursion was not
    supported by previous definition packages for %\Coq% like
    %\textsc{Function}% or %\textsc{Program}%, and due to the required
    dependencies it is not supported by %\textsc{Isabelle}%'s
    %\texttt{Function}% package either (see %\cite{BoveKraussSozeau2011}% for
    a survey of the treatment of recursion in type-theory based tools). *)

  (** We can show that [elems] is actually computing the same thing as
      the naïve algorithm concatenating elements of each tree in each forest. *)

  Equations elements_spec (r : rose) : list rose :=
    elements_spec (node _ l) := concat (List.map elements_spec l).

  (** As [elements] takes an accumulator, we first have to prove a generalized
      lemma, typical of tail-recursive functions: *)

  Lemma elements_correct (r : rose) acc : elements r acc = elements_spec r ++ acc.
  Proof.
    apply (elements_elim (fun r acc f => f = elements_spec r ++ acc)
                         (fun n l acc x H r => r = concat (List.map elements_spec x) ++ acc));
      intros; simp elements_spec; simpl; trivial. now rewrite H1, H0, app_assoc. Qed.

  (** We apply the eliminator providing the predicate for the nested
      recursive call and simplify using the [simp elements_spec] tactic
      which is rewriting with the defining equations of [elements_spec].
      The induction hypotheses and associativity of concatenation are
      enough to solve the remaining goal which involves the two
      recursive calls to [elements] and [aux]. The above proof is very
      quick as the eliminator frees us from redoing all the nested
      recursive reasoning and the proofs that the induction hypotheses
      can be applied. It is now trivial to prove the correctness of our
      fast implementation: *)

  Lemma elems_correct (r : rose) : elems r = elements_spec r.
  (* begin hide *)
  Proof. now unfold elems; rewrite elements_correct, app_nil_r. Qed.
  (* end hide *)
(* begin hide *)
End RoseTree.
(* end hide *)
