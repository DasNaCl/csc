Set Implicit Arguments.
Require Import Strings.String Lists.List Program.Equality.
Require Import CSC.Sets CSC.Util.

(** * Syntax *)

(** The type used for variable names. *)
Definition vart := string.
Definition vareq := fun x y => (x =? y)%string.

(** The only values we have in S are natural numbers. *)
Inductive value : Type :=
| Vnat : nat -> value
.
Coercion Vnat : nat >-> value.
(** Locerences are not values. In fact, they cannot be represented syntactically. *)
Inductive loc : Type :=
| addr : nat -> loc
.
(** Final Result (without error) *)
Inductive fnoerr : Type :=
| Fval : value -> fnoerr
| Fvar : vart -> fnoerr
.
Coercion Fval : value >-> fnoerr.
(** Final Result (with error) *)
Inductive ferr : Type :=
| Fres : fnoerr -> ferr
| Fabrt : ferr
.
Coercion Fres : fnoerr >-> ferr.
(** Possible binary operations. *)
Variant binopsymb : Type :=
| BAdd : binopsymb
| BSub : binopsymb
| Bmul : binopsymb
| Bless : binopsymb
.
(** Pointer Type Qualifiers *)
Inductive qual : Type :=
| Qfull : qual
| Qhalf : qual
.
(** Types of S *)
Inductive ty : Type :=
| Tnat : ty
| Tnatptr : qual -> ty
.
Notation "'Tptr'" := (Tnatptr Qfull).
Notation "'Twptr'" := (Tnatptr Qhalf).
Inductive expr : Type :=
| Xres (f : ferr) : expr
| Xbinop (symb : binopsymb) (lhs rhs : expr) : expr
| Xget (x : vart) (e : expr) : expr
| Xset (x : vart) (e0 e1 : expr) : expr
| Xlet (x : vart) (e0 e1 : expr) : expr
| Xnew (x : vart) (e0 e1 : expr) : expr
| Xdel (x : vart) : expr
| Xreturning (e : expr) : expr
| Xcalling (e : expr) : expr
| Xifz (c e0 e1 : expr) : expr
| Xabort : expr
| Xhole (x : vart) (τ1 τ2 : ty) : expr
.
Coercion Xres : ferr >-> expr.

(** The following is a helper function to easily define functions over the syntax of S, e.g. substitution. *)
Definition exprmap (h : expr -> expr) (e : expr) :=
  match e with
  | Xbinop b lhs rhs => Xbinop b (h lhs) (h rhs)
  | Xget x e => Xget x (h e)
  | Xset x e0 e1 => Xset x (h e0) (h e1)
  | Xlet x e0 e1 => Xlet x (h e0) (h e1)
  | Xnew x e0 e1 => Xnew x (h e0) (h e1)
  | Xreturning e => Xreturning (h e)
  | Xcalling e => Xcalling (h e)
  | Xifz c e0 e1 => Xifz (h c) (h e0) (h e1)
  | _ => e
  end
.

(** * Dynamics *)

(** Evaluation of binary expressions. Note that 0 means `true` in S, so `5 < 42` evals to `0`. *)
Definition eval_binop (b : binopsymb) (v0 v1 : value) :=
  let '(Vnat n0) := v0 in
  let '(Vnat n1) := v1 in
  match b with
  | Bless => Vnat (if Nat.ltb n0 n1 then 0 else 1)
  | BAdd => Vnat (n0 + n1)
  | BSub => Vnat (n0 - n1)
  | BMul => Vnat (n0 * n1)
  end
.
(** Poison used to mark locations in our operational state. *)
Inductive poison : Type :=
| poisonless : poison
| poisoned : poison
.
Notation "'◻'" := (poisonless).
Notation "'☣'" := (poisoned).

Definition dynloc : Type := loc * poison.
Notation "ℓ '⋅' ρ" := (((ℓ : loc), (ρ : poison)) : dynloc) (at level 81).

(** Stores map variables to potentially poisoned locations. *)
Inductive store : Type :=
| Snil : store
| Scons (x : vart) (ℓ : dynloc) (Δ : store) : store
.
Notation "x '↦' dl '◘' Δ" := (Scons x (dl : dynloc) Δ) (at level 81, dl at next level).
Fixpoint append (Δ1 Δ2 : store) : store :=
  match Δ1 with
  | Snil => Δ2
  | Scons x ℓ Δ1' => x ↦ ℓ ◘ (append Δ1' Δ2)
  end
.
Notation "Δ1 '◘' Δ2" := (append Δ1 Δ2) (at level 82, Δ2 at next level).
(** In this model, heaps are just a snoc-style list of natural numbers. *)
Inductive heap : Type :=
| Hnil : heap
| Hcons (H : heap) (n : nat) : heap
.
Fixpoint Hsize (H : heap) : nat :=
  match H with
  | Hnil => 0
  | Hcons H' _ => 1 + Hsize H'
  end
.
Fixpoint Hget (H : heap) (i : nat) : option nat :=
  match H with
  | Hnil => None
  | Hcons H' m =>
      match i with
      | 0 => Some m
      | S j => Hget H' j
      end
  end
.
Fixpoint Hset (H : heap) (i v : nat) : option heap :=
  match H with
  | Hnil => None
  | Hcons H' m =>
      match i with
      | 0 => Some(Hcons H' v)
      | S j => match Hset H' j v with
              | None => None
              | Some H'' => Some(Hcons H'' m)
              end
      end
  end
.
Fixpoint Hgrow (H : heap) (s : nat) : heap :=
  match s with
  | 0 => H
  | S s' => Hcons (Hgrow H s') 0
  end
.
Definition state : Type := heap * store.
Notation "H ';' Δ" := ((H : heap), (Δ : store)) (at level 81).

Inductive context (e0 e1 : expr) : Type := Ccontext.
Inductive component (ep : expr) : Type := Ccomponent.
Inductive prog (e0 ep e1 : expr) : Type := Cprog.

(** Types of events that may occur in a trace. *)
Variant event : Type :=
| Sε : event
| Salloc (ℓ : loc) (n : nat) : event
| Sdealloc (ℓ : loc) : event
| Sget (ℓ : loc) (n : nat) : event
| Sset (ℓ : loc) (n : nat) : event
| Scrash : event
| Scall (f : fnoerr) : event
| Sret (f : fnoerr) : event
.
Definition tracepref := CSC.Util.tracepref event.
Definition Tnil := CSC.Util.Tnil event.
Definition Tcons (a : event) (t : tracepref) := @CSC.Util.Tcons event a t.

(** A runtime program is a state plus an expression. *)
Definition rtexpr : Type := (option state) * expr.
Notation "Ω '▷' e" := ((((Some (Ω)) : option state), (e : expr)) : rtexpr) (at level 81).
Notation "↯ '▷' 'stuck'" := (((None : option state), (Fabrt : expr)) : rtexpr).

(** Substitution, which assumes that the given expression is closed. *)
Definition subst (what : vart) (inn forr : expr) : expr :=
  let substid := match forr with
                 | Xres(Fres(Fvar y)) => Some y
                 | _ => None
                 end
  in
  let isubst := (fix isubst e :=
    let R := exprmap isubst in
    match e with
    | Xlet x e0 e1 => if vareq what x then Xlet x (R e0) e1 else Xlet x (R e0) (R e1)
    | Xnew x e0 e1 => if vareq what x then Xlet x (R e0) e1 else Xlet x (R e0) (R e1)
    | Xget x e' => match substid with
                  | None => Xget x
                  | Some y => Xget y
                  end (R e')
    | Xset x e0 e1 => match substid with
                     | None => Xset x
                     | Some y => Xset y
                     end (R e0) (R e1)
    | Xdel x => match substid with
               | None => Xdel x
               | Some y => Xdel y
               end
    | Xres(Fres(Fvar x)) => if vareq what x then forr else e
    | Xhole x τ1 τ2 => match substid with
                      | None => Xhole x
                      | Some y => Xhole y
                      end τ1 τ2
    | _ => e
    end)
  in
  isubst inn
.

Reserved Notation "r0 '--[' a ']-->' r1" (at level 82, r1 at next level).
Inductive pstep : rtexpr -> event -> rtexpr -> Prop :=
| e_returning : forall (Ω : state) (f : fnoerr),
    Ω ▷ Xreturning f --[ Sret f ]--> Ω ▷ f
| e_calling : forall (Ω : state) (f : fnoerr),
    Ω ▷ Xcalling f  --[ Scall f ]--> Ω ▷ f
| e_binop : forall (Ω : state) (n1 n2 n3 : nat) (b : binopsymb),
    Vnat n3 = eval_binop b n1 n2 ->
    Ω ▷ Xbinop b n1 n2 --[ Sε ]--> Ω ▷ n3
| e_ifz_true : forall (Ω : state) (e1 e2 : expr),
    Ω ▷ Xifz 0 e1 e2 --[ Sε ]--> Ω ▷ e1
| e_ifz_false : forall (Ω : state) (e1 e2 : expr) (n : nat),
    Ω ▷ Xifz (S n) e1 e2 --[ Sε ]--> Ω ▷ e2
| e_abort : forall (Ω : state),
    Ω ▷ Xabort --[ Scrash ]--> ↯ ▷ stuck
| e_get : forall (H : heap) (Δ1 Δ2 : store) (x : vart) (ℓ n v : nat) (ρ : poison),
    forall (H0a : ℓ + n < Hsize H -> Some v = Hget H (ℓ + n))
      (H0b : ℓ + n >= Hsize H -> v = 1729),
    (H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xget x n --[ Sget (addr ℓ) n ]--> (H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ v
| e_set : forall (H H' : heap) (Δ1 Δ2 : store) (x : vart) (ℓ n v : nat) (ρ : poison),
    forall (H0a : ℓ + n < Hsize H -> Some H' = Hset H (ℓ + n) v)
      (H0b : ℓ + n >= Hsize H -> H' = H),
    (H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xset x n v --[ Sget (addr ℓ) n ]--> (H' ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ v
| e_delete : forall (H : heap) (Δ1 Δ2 : store) (x : vart) (ℓ : nat) (ρ : poison),
    (H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xdel x --[ Sdealloc (addr ℓ) ]--> (H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ☣) ◘ Δ2)) ▷ 0
| e_alloc : forall (H H' : heap) (Δ : store) (x z : vart) (ℓ n : nat) (e : expr),
    (*TODO: fresh var*)
    H' = Hgrow H n ->
    (H ; Δ) ▷ Xnew x n e --[ Salloc (addr ℓ) n ]--> (H' ; (z ↦ ((addr ℓ) ⋅ ◻) ◘ Δ)) ▷ (subst x (Fvar z) e)
where "r0 '--[' a ']-->' r1" := (pstep r0 a r1)
.

(** We proceed to define the dynamic semantics via evaluation contexts/environments. *)
Inductive evalctx : Type :=
| Khole : evalctx
| KbinopL (b : binopsymb) (K : evalctx) (e : expr) : evalctx
| KbinopR (b : binopsymb) (v : value) (K : evalctx) : evalctx
| Kget (x : vart) (K : evalctx) : evalctx
| KputL (x : vart) (K : evalctx) (e : expr) : evalctx
| KputR (x : vart) (e : expr) (K : evalctx) : evalctx
| Klet (x : vart) (K : evalctx) (e : expr) : evalctx
| Knew (x : vart) (K : evalctx) (e : expr) : evalctx
| Kifz (K : evalctx) (e0 e1 : expr) : evalctx
| Kcalling (K : evalctx) : evalctx
| Kreturning (K : evalctx) : evalctx
.
Fixpoint insert (K : evalctx) (withh : expr) : expr :=
  withh
.

Reserved Notation "r0 '==[' a ']==>' r1" (at level 82, r1 at next level).
Inductive estep : rtexpr -> event -> rtexpr -> Prop :=
| E_ctx : forall (Ω Ω' : state) (e e' e0 e0' : expr) (a : event) (K : evalctx),
    e0 = insert K e ->
    e0' = insert K e' ->
    Ω ▷ e --[ a ]--> Ω' ▷ e' ->
    Ω ▷ e0 ==[ a ]==> Ω' ▷ e0'
| E_abrt_ctx : forall (Ω : state) (e e0 : expr) (K : evalctx),
    e0 = insert K e ->
    Ω ▷ e --[ Scrash ]--> ↯ ▷ stuck ->
    Ω ▷ e0 ==[ Scrash ]==> ↯ ▷ stuck
where "r0 '==[' a ']==>' r1" := (estep r0 a r1)
.

Reserved Notation "r0 '==[' As ']==>*' r1" (at level 82, r1 at next level).
Inductive star_step : rtexpr -> tracepref -> rtexpr -> Prop :=
| ES_refl : forall (r1 : rtexpr),
    r1 ==[ Tnil ]==>* r1
| ES_trans_important : forall (r1 r2 r3 : rtexpr) (a : event) (As : tracepref),
    a <> Sε ->
    r1 ==[ a ]==> r2 ->
    r2 ==[ As ]==>* r3 ->
    r1 ==[ Tcons a As ]==>* r3
| ES_trans_unimportant : forall (r1 r2 r3 : rtexpr) (As : tracepref),
    r1 ==[ Sε ]==> r2 ->
    r2 ==[ As ]==>* r3 ->
    r1 ==[ As ]==>* r3
where "r0 '==[' As ']==>*' r1" := (star_step r0 As r1)
.
