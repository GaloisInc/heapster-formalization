Require Import ZArith List String Omega.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Programming.Eqv.
Require Import FSets.FMapAVL.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Require Import Heapster.Int64.


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

Definition lbl := Z.  (* Or i64? *)

Inductive stmt :=
| Load  (r:reg) (a:arg)   (*  r <- *a *)
| Store (r:reg) (a:arg)   (*  *r <- a *)
| BinOp (r:reg) (o:op) (a1 a2:arg)
| Alloca (r:reg) (a:arg)
| Malloc (r:reg) (a:arg)
| Free   (a:arg)
| Call   (l:lbl) (c:ctxt)
.

Definition tgt := (lbl * ctxt)%type.

Inductive term :=
| Jmp (t:tgt)
| Brz (a:arg) (t1 t2:tgt)
| Ret (a:arg).

Inductive cd  :=
| T (t:term)
| I (s:stmt) (c:cd)
.

Definition prog := ZMap cd.

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

Definition used := list Z.  (* Maybe make a set? *)

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
                   (HFree: forall i, in_range i p (Int64.add i bytes) = true ->
                                lookup i H = None)
                   (HFresh: forall i, in_range i p (Int64.add i bytes) = true ->
                                 lookup i H' = Some (Uninit l p))
                   (HSame: forall i, in_range i p (Int64.add i bytes) = false ->
                                lookup i H' = lookup i H),
    allocate H bytes l p H'.


Definition eval_arg_f (r:regs) (a:arg) : option val :=
 match a with
 | Lit v => Some v
 | Reg rv => ZM.find rv r
 end.

Inductive eval_arg (r:regs) (a:arg) : val -> Prop :=
| eval_a : forall v (Heq: eval_arg_f r a = Some v), eval_arg r a v.

Inductive eval_op : op -> val -> val -> val -> Prop :=
| eval_add : forall (x y z : i64) (Heq: Int64.add x y = z), eval_op Add x y z
| eval_sub : forall (x y z : i64) (Heq: Int64.sub x y = z), eval_op Sub x y z
| eval_eqt : forall (x y : i64) (Heq: Int64.eq x y = true), eval_op Eq x y Int64.one
| eval_eqf : forall (x y : i64) (Heq: Int64.eq x y = false), eval_op Eq x y Int64.zero
| eval_ltt : forall (x y : i64) (Heq: Int64.lt x y = true), eval_op Lt x y Int64.one
| eval_ltf : forall (x y : i64) (Heq: Int64.lt x y = false), eval_op Lt x y Int64.zero.

Definition fresh_for_heapval (h:hv) (l:tag) : bool :=
  match h with
  | Code _ => true
  | Uninit l' _ => negb (Z.eqb l l')
  | Init l' _ _ => negb (Z.eqb l l')
  end.

Definition fresh_for_heap (H:heap) (l:tag) : bool :=
  IM.fold (fun _ h b => andb b (fresh_for_heapval h l)) H true.

Definition fresh_for_stack (s:stack) (l:tag) : Prop :=
  not (In l (List.map (fun '(_, l', _, _) => l') s)).

Definition fresh (c:config) (l:tag) : Prop :=
  let '(H, u, s, _, l', _) := c in
  fresh_for_heap H l = true /\
  fresh_for_stack s l /\
  not (In l u) /\
  l <> l'.

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
         (free_heap H l', l'::u, s, R, l, cd).









