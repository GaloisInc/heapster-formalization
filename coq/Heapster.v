Require Import ZArith List String Omega.

From Coq Require Import
 Setoids.Setoid
 Classes.Morphisms
 Relations.Relations
 Relations.Relation_Operators.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.Monads.OptionMonad.

Require Import FSets.FMapAVL.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Require Import Heapster.Int64.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope list_scope.

Set Implicit Arguments.

(* Maps from Z to values.  Used for contexts and environments *)
Module ZM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Definition ZMap := ZM.t.

Definition IMap := Int64.IM.t.

(* Syntax ------------------------------------------------------------------- *)

Definition reg := Z.

Inductive arg :=
| Reg (z:reg)
| Lit (i:i64)
.

Definition val := i64.

Inductive op :=
| Add | Sub | Eq | Lt.

Definition ctxt := ZMap arg.

Definition lbl := i64.  (* Or i64? *)

Inductive stmt :=
| Load  (r:reg) (a:arg)   (*  r <- *a *)
| Store (r:reg) (a:arg)   (*  *r <- a *)
| BinOp (r:reg) (o:op) (a1 a2:arg)
| Alloca (r:reg) (a:arg)
| Malloc (r:reg) (a:arg)
| Free   (a:arg)
| Call   (r:reg) (a:arg) (c:ctxt)
.

Definition tgt := (lbl * ctxt)%type.

Inductive term :=
| Jmp (t:tgt)
| Brz (a:arg) (t1 t2:tgt)
| Ret (a:arg)
| Hlt (a:arg).

Inductive cd  :=
| T (t:term)
| I (s:stmt) (c:cd)
.

(* Operational Semantics ---------------------------------------------------- *)

Definition regs := ZMap val.

Definition tag := Z.

Inductive hv :=
| Uninit (l:tag) (root:i64)
| Init (l:tag) (root:i64) (v:i64)
| Code (c:cd)
.

Definition heap := IMap hv.

Definition frame := (regs * tag * reg * cd)%type.

Definition stack := list frame.

Definition used := list tag.  (* Maybe make a set? *)

Definition config := (heap * used * stack * regs * tag * cd)%type.

Definition store_f (H:heap) (a:val) (v:val) : option heap :=
  match lookup a H with
  | None
  | Some (Code _) => None    (* Trying to write to code aborts. *)
  | Some (Uninit l root)
  | Some (Init l root _)  => Some (insert a (Init l root v) H)
  end.

Inductive store (H:heap) (a:val) (v:val) : heap -> Prop :=
| store_val : forall H' (Heq: store_f H a v = Some H'), store H a v H'.

Inductive load (H:heap) (a:val) : val -> Prop :=
| load_init : forall l root v (Heq: lookup a H = Some (Init l root v)), load H a v
| load_uninit : forall l root v (Heq: lookup a H = Some (Uninit l root)), load H a v.
(* Note: unalloacted and code cause loads to crash.  Could cause Load to be nondet for code. *)

(* bits is the _logarithm_ of the alignment, which must be a power of 2
   So, aligned p 3 means that *)
Definition aligned (p:i64) (bits:Z) : bool :=
  let z := Int64.repr bits in
  Int64.eq p (Int64.shl (Int64.shru p z) z).

Definition in_range (i base bnd : i64) : bool :=
  andb (Int64.cmpu Integers.Cle base i)
       (Int64.cmpu Integers.Cle i bnd).


Inductive allocate (H:heap) (bytes:i64) (l:tag) : val -> heap -> Prop :=
| allocate_ctr : forall (p:val) (H':heap)
                   (Hp_aligned: aligned p 3 = true)
                   (Hbytes_mul8 : aligned bytes 3 = true)
                   (Hbytes_nz : Int64.ltu Int64.zero bytes = true)
                   (HFree: forall i, in_range i p (Int64.add p bytes) = true ->
                                lookup i H = None)
                   (HFresh: forall i, in_range i p (Int64.add p bytes) = true ->
                                 lookup i H' = Some (Uninit l p))
                   (HSame: forall i, in_range i p (Int64.add p bytes) = false ->
                                lookup i H' = lookup i H),
    allocate H bytes l p H'.


Definition eval_arg_f (r:regs) (a:arg) : option val :=
 match a with
 | Lit v => Some v
 | Reg rv => ZM.find rv r
 end.

Inductive eval_arg (r:regs) (a:arg) : val -> Prop :=
| eval_a : forall v (Heq: eval_arg_f r a = Some v), eval_arg r a v.


Definition eval_binding (R:regs) (r:Z) (a:arg) (oR':option regs) : option regs :=
  v <- eval_arg_f R a ;;
  R' <- oR' ;;
  ret (ZM.add r v R').

Definition eval_ctxt_f (R:regs) (c:ctxt) : option regs :=
  ZM.fold (eval_binding R) c (Some (@ZM.empty val)).

Inductive eval_ctxt R c : regs -> Prop :=
| eval_ctxt_a : forall R' (Heq: eval_ctxt_f R c = Some R'), eval_ctxt R c R'.

Inductive eval_op : op -> val -> val -> val -> Prop :=
| eval_add : forall (x y z : i64) (Heq: Int64.add x y = z), eval_op Add x y z
| eval_sub : forall (x y z : i64) (Heq: Int64.sub x y = z), eval_op Sub x y z
| eval_eqt : forall (x y : i64) (Heq: Int64.eq x y = true), eval_op Eq x y Int64.one
| eval_eqf : forall (x y : i64) (Heq: Int64.eq x y = false), eval_op Eq x y Int64.zero
| eval_ltt : forall (x y : i64) (Heq: Int64.lt x y = true), eval_op Lt x y Int64.one
| eval_ltf : forall (x y : i64) (Heq: Int64.lt x y = false), eval_op Lt x y Int64.zero.

Definition used_in_heapval (h:hv) (l:tag) : bool :=
  match h with
  | Code _ => false
  | Uninit l' _ => Z.eqb l l'
  | Init l' _ _ => Z.eqb l l'
  end.

Definition fresh_for_heapval (h:hv) (l:tag) : bool :=
  negb (used_in_heapval h l).

Definition used_in_heap (H:heap) (l:tag) : bool :=
  IM.fold (fun _ h b => orb b (used_in_heapval h l)) H false.

Definition fresh_for_heap (H:heap) (l:tag) : bool :=
  negb (used_in_heap H l).

Definition lbls_in_stack (s:stack) : list tag :=
  List.map (fun '(_, l', _, _) => l') s.

Definition used_in_stack (s:stack) (l:tag) : bool :=
  List.existsb (Z.eqb l) (lbls_in_stack s).

Definition fresh_for_stack (s:stack) (l:tag) : bool :=
  negb (used_in_stack s l).

Definition used_in_config (c:config) (l:tag) : bool :=
  let '(H, u, s, _, l', _) := c in
  used_in_heap H l || used_in_stack s l || List.existsb (Z.eqb l) u || Z.eqb l l'.

Definition fresh (c:config) (l:tag) : Prop :=
  used_in_config c l = false.


(* SAZ: todo rewrite this using a filter, which would be more pleasant *)
Definition free_heap (H:heap) (l:tag) : heap :=
  IM.fold (fun k h heap' =>
             match h with
             | Code _ => insert k h heap'
             | Uninit l' _ => if Z.eqb l l' then heap' else insert k h heap'
             | Init l' _ _ => if Z.eqb l l' then heap' else insert k h heap'
             end)
          H (@IM.empty hv).

Inductive heap_root (H:heap) (p:i64) : tag -> Prop :=
| heap_root_uninit : forall l (Hl: lookup p H = Some (Uninit l p)), heap_root H p l
| heap_root_init : forall l v (Hl: lookup p H = Some (Init l p v)), heap_root H p l
.

Inductive step : config -> config -> Prop :=
| step_op : forall H u s R l cd op r a1 a2 x y z,
    eval_arg R a1 x ->
    eval_arg R a2 y ->
    eval_op op x y z ->
    step (H, u, s, R, l, I (BinOp r op a1 a2) cd)
         (H, u, s, ZM.add r z R, l, cd)

| step_load : forall H u s R l cd r a1 x z,
    eval_arg R a1 x ->
    load H x z ->
    step (H, u, s, R, l, I (Load r a1) cd)
         (H, u, s, ZM.add r z R, l, cd)

| step_store : forall H H' u s R l cd r p a1 x,
    eval_arg R (Reg r) p ->
    eval_arg R a1 x ->
    store H p x H' ->
    step (H, u, s, R, l, I (Store r a1) cd)
         (H', u, s, R, l, cd)

| step_alloca : forall H H' u s R l cd r p a1 x,
    eval_arg R a1 x ->
    allocate H x l p H' ->
    step (H, u, s, R, l, I (Alloca r a1) cd)
         (H', u, s, ZM.add r p R, l, cd)

| step_malloc : forall H H' u s R l l' cd r p a1 x,
    eval_arg R a1 x ->
    fresh (H, u, s, R, l, I (Alloca r a1) cd) l' ->
    allocate H x l' p H' ->
    step (H, u, s, R, l, I (Alloca r a1) cd)
         (H', u, s, ZM.add r p R, l, cd)

| step_free : forall H u s R l l' cd a1 x,
    eval_arg R a1 x ->
    heap_root H x l' ->
    step (H, u, s, R, l, I (Free a1) cd)
         (free_heap H l', l'::u, s, R, l, cd)

| step_call : forall H u s R R'  l l' cd cd' r a1 args x,
    eval_arg R a1 x ->
    lookup x H = Some (Code cd') ->
    eval_ctxt R args R' ->
    fresh (H, u, s, R, l, I (Call r a1 args) cd) l' ->
    step (H, u, s, R, l, I (Call r a1 args) cd)
         (H, u, (R, l, r, cd)::s, R', l', cd')

| step_ret : forall H u s R R'  l l' cd' r' a1 x,
    eval_arg R a1 x ->
    step (H, u, (R', l', r', cd')::s, R, l, T (Ret a1))
         (free_heap H l, l::u, s, ZM.add r' x R', l', cd')

| step_jmp :  forall H u s R R'  l lbl cd' args,
    lookup lbl H = Some (Code cd') ->
    eval_ctxt R args R' ->
    step (H, u, s, R, l, T (Jmp (lbl, args) ))
         (H, u, s, R', l, cd')

| step_brz0 : forall H u s R R'  l a1 lbl0 cd' args0 lbl_nz args_nz,
    eval_arg R a1 Int64.zero ->
    lookup lbl0 H = Some (Code cd') ->
    eval_ctxt R args0 R' ->
    step (H, u, s, R, l, T (Brz a1 (lbl0, args0) (lbl_nz, args_nz)))
         (H, u, s, R', l, cd')

| step_brz_nz : forall H u s R R'  l a1 x lbl0 cd' args0 lbl_nz args_nz,
    eval_arg R a1 x ->
    Int64.eq x Int64.zero = false ->
    lookup lbl_nz H = Some (Code cd') ->
    eval_ctxt R args_nz R' ->
    step (H, u, s, R, l, T (Brz a1 (lbl0, args0) (lbl_nz, args_nz)))
         (H, u, s, R', l, cd')

.

(* NOTE: There is no transition rule for Hlt *)


(* Defining characteristics of configurations ------------------------------- *)

Definition cd_ (C:config) :=
  let '(_, _, _, _, _, c) := C in c.

Inductive finished (x:i64) : config -> Prop :=
| finished_c : forall H u S R l a,
    eval_arg R a x ->
    finished x (H, u, S, R, l, T (Hlt a)).

Definition pc_at_cd (c:cd) : config -> Prop :=
  fun C => cd_ C = c.


Definition stuck (c:config) :=
 (~ exists x, finished x c) /\ ~ exists c', step c c'.

(* Stream of configuration semantics ---------------------------------------- *)

Inductive streamF {X:Type} (A:Type) :=
| snil : streamF A
| scons : A -> X -> streamF A.


CoInductive stream (A:Type) := go {
  observe : @streamF (stream A) A
}.

Notation "#" := (@go _ (@snil _ _)).
Notation "x >> s" := (@go _ (@scons _ _ x s)) (at level 100).

Inductive runF (P : config -> stream config -> Prop) : config -> stream config -> Prop :=
 | run_done : forall c1 c2, ~ step c1 c2 -> runF P c1 (c1 >> #)
 | run_step : forall c1 c2 s, step c1 c2 -> P c2 s -> runF P c1 (c1 >> s)
.

CoInductive runC (c:config) (s:stream config) : Prop := goRun {
  run_ : runF runC c s
}.


Module Permissions.

  (* Syntax of permission expression. *)

  (* Should this be coinductive? *)
  Inductive splitting_set : Set :=
  | s_var (n:N)
  | s_all
  | s_none
  | s_1 (s:splitting_set)
  | s_0 (s:splitting_set)
  | s_prod (s1 s2:splitting_set)
  | s_diff (s1 s2:splitting_set)
  .

  Inductive cnd : Set :=
  | cnd_eq (n:Z)
  | cnd_neq (ns:list Z)
  .

  Inductive lifetime : Set :=
  | l_before (t:tag)
  | l_after  (t:tag)
  | l_prod   (t1 t2:tag)
  | l_always
  .

  Inductive value_perm : Set :=
  | vp_word
  | vp_none
  | vp_ptr  (S:splitting_set) (θ:value_perm)
  | vp_free (n:N)
  | vp_cnd  (C:cnd) (θ:value_perm)
  | vp_offs (e1 e2 : arg) (θ:value_perm)
  | vp_life (L:lifetime) (θ:value_perm)
  | vp_prod (θ1 θ2 : value_perm)
  | vp_mu   (θ:value_perm)
  | vp_fv   (x:nat)
  | vp_bv   (y:nat)  (* de Bruijn index *)
  .

  Inductive perm_atom : Set :=
  | p_val (r:reg) (θ:value_perm)    (* x : θ *)
  | p_deref (x:reg) (e:arg)         (* x = *e *)
  | p_eq  (r:reg) (e:arg)           (* r = e *)
  | p_neq (r:reg) (e:arg)           (* r <> e *)
  .

  Definition perm_set := list perm_atom.


  (* Denotation of permissions *)
  Record perm := mkPerm {
    view : config -> config -> Prop;  (* PER over configs *)
    upd  : config -> config -> Prop;  (* allowed transitions *)
  }.

  Record goodPerm (p:perm) : Prop := {
     view_PER   : PER config (view p) ;
     upd_PO     : PreOrder (upd p) ;
  }.

  Record lte_perm (p q:perm) : Prop := {
     view_inc : forall x y, (view q) x y -> (view p) x y;
     upd_inc : forall x y, (upd p) x y -> (upd q) x y;
  }.

  Definition join_perm (p q:perm) : perm := {|
     view := clos_trans config (fun x y => (view p x y) \/ (view q x y)) ;  (* disjunction *)
     upd  := fun x y => (upd p x y) /\ (upd q x y) ;    (* conjunction *)
  |}.

  Definition bottom_perm : perm := {|
     view := fun x y => False ;
     upd  := fun x y => True ;
  |}.

  Definition top_perm : perm := {|
     view := fun x y => True ;
     upd  := fun x y => False ;
  |}.

  Record sep_at (p q:perm) (x:config) : Prop := {
    upd1: forall y:config, (upd p) x y -> (view q) x y;
    upd2: forall y:config, (upd q) x y -> (view p) x y;
  }.

  Definition separate (p q : perm) : Prop := forall x, sep_at p q x.

  Inductive pairwise {A:Type} (P : A -> A -> Prop) : list A -> Prop :=
  | pw_nil : pairwise P nil
  | pw_one : forall (a:A), pairwise P [a]
  | pw_cons : forall (a:A) (l:list A), pairwise P l -> (forall b, In b l -> P a b) -> pairwise P (a::l)
  .

  Record goodPermSet (Π : list perm ) : Prop := {
    good_atoms : forall p, In p Π -> goodPerm p ;
    apart : pairwise separate Π ;
  }.

  Lemma separate_anti_monotone : forall (p1 p2 q : perm) (HSep: separate p2 q) (Hlt: lte_perm p1 p2),
      separate p1 q.
  Proof.
    intros p1 p2 q HSep Hlt.
    destruct Hlt.
    unfold separate in HSep.
    unfold separate.
    intros. constructor; intuition.
    apply HSep. intuition.
    apply view_inc0. apply HSep. assumption.
  Qed.

  (* Permission difference:  if p <= q then q - p is defined and p * (q - p) = q *)
  (* implies fractional permission *)

  (* TODO: denotation of permission syntax *)
  Inductive perm_denote : perm_atom -> perm -> Prop := .


End Permissions.

Import Permissions.
Section RelationalSemantics.
  (* Definition config := (heap * used * stack * regs * tag * cd)%type. *)

Definition judgment X := perm_set -> X -> perm_set -> Prop.

Inductive term_judgment : judgment term :=
    (* Should have:  Π |- a *)
  | j_halt : forall (x:val) Π, term_judgment Π (Hlt (Lit x)) Π.


(* VACUOUS, SO TRIVIALLY SOUND! *)
Inductive stmt_judgment : judgment stmt := .

(*
Definition judgment X := perm_set -> X -> list perm_set -> Prop.
Inductive code_judgment : judgment cd :=
| trm_judgment : forall Π Πl t, term_judgment Π t Πl -> code_judgment Π (T t) Πl
| stm_judgment : forall Π1 Πl1 Πl2 s cd, stmt_judgment Π1 s Πl1
                               -> (forall Π Πl, In Π Πl1 -> code_judgment Π cd Πl /\
                                                    (forall x, In x Πl -> In x Πl2))
                               -> code_judgment Π1 (I s cd) Πl2
.
*)

Inductive code_judgment : judgment cd :=
| trm_judgment : forall Π Πl t, term_judgment Π t Πl -> code_judgment Π (T t) Πl
| stm_judgment : forall Π1 Π2 Π3 s cd, stmt_judgment Π1 s Π2
                                    -> code_judgment Π2 cd Π3
                                    -> code_judgment Π1 (I s cd) Π3
.

Definition list_equiv {A} (X Y : list A) := List.incl X Y /\ List.incl Y X.

Definition sound_code_judgment : (judgment cd) -> Prop :=
  fun J : judgment cd =>
    forall Πin prog Πout, J Πin (prog:cd) Πout ->
      forall (P : perm_atom), In P Πin ->
                    forall (p:perm), perm_denote P p ->
                                forall (C:config)
                                  (Hcd: cd_ C = prog)
                                  (HC: (view p) C C),
         (exists x, finished x C /\ list_equiv Πin Πout)
         \/
         (forall (q:perm), sep_at p q C ->
                      forall C', step C C' ->
                            exists Π' P', In P' Π'
                                     /\ J Π' (cd_ C') Πout
                                     /\ (upd p C C')
                                     /\ forall (p':perm), perm_denote P' p'
                                                    -> (view p') C' C'
                                                      /\ sep_at p' q C').


End RelationalSemantics.

Lemma sound_code_judgment_Rules : sound_code_judgment code_judgment.
Proof.
  unfold sound_code_judgment.
  intros.
  induction H.
  - inversion H. left. exists x. split. 
    destruct C as [[[[[Hp u] stk]  R] l] cd ]. subst. simpl in Hcd. subst.
    econstructor. econstructor. simpl. reflexivity.
    split. apply incl_refl. apply incl_refl.

  - right. intros. inversion H. (* stmt_judgment is VACUOUS!! *)
Abort.

Section Examples.


Lemma looping_config :
  forall H lbl args u s R l,
    lookup lbl H = Some (Code (T (Jmp (lbl, args)))) ->
    eval_ctxt R args R ->
    step (H, u, s, R, l, T (Jmp (lbl, args))) (H, u, s, R, l, T (Jmp (lbl, args))).
Proof.
  intros H lbl0 args u s R l H0 H1.
  apply step_jmp; assumption.
Qed.



Lemma used_store_f_monotonic : forall H a v l H'
                                 (Hused: used_in_heap H l = true)
                                 (Hstore: store_f H a v = Some H'),
    used_in_heap H' l = true.
Proof.
Admitted.

Lemma used_allocate_monotonic1 : forall H a v l l0 H'
                                 (Hused: used_in_heap H l = true)
                                 (Hstore: allocate H a l0 v H'),
    used_in_heap H' l = true.
Proof.
  intros H a v l l0 H' Hused Hstore.
  inversion Hstore. subst.
Admitted.

Lemma used_allocate_monotonic2 : forall H a v l0 H'
                                 (Hstore: allocate H a l0 v H'),
    used_in_heap H' l0 = true.
Proof.
  intros H a v l0 H' Hstore.
  inversion Hstore. subst.
Admitted.



Lemma used_monotonic : forall l c1 c2
                         (Hused: (used_in_config c1 l = true) )
                         (Hstep: step c1 c2),
    used_in_config c2 l = true.
Proof.
  intros l c1 c2 Hused Hstep.
  inversion Hstep; subst; simpl in *; try assumption.
  - inversion H2.
    subst.
    destruct (used_in_heap H l) eqn:Hheap.
    assert (used_in_heap H' l = true).
    eapply used_store_f_monotonic; eauto. subst.
    rewrite H3. assumption.
    destruct (used_in_heap H' l) eqn:Hheap'.
    reflexivity. assumption.
Admitted.
