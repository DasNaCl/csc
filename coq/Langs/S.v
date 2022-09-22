Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef.
Require Import CSC.Sets CSC.Util CSC.Fresh CSC.Langs.Util.

(** * Syntax *)

(** The type used for variable names. *)
Definition vart := string.
Definition vareq := fun x y => (x =? y)%string.
Definition dontcare := "_"%string.

#[local]
Instance varteq__Instance : HasEquality vart := vareq.

(** The only values we have in S are natural numbers. *)
Inductive value : Type :=
| Vnat : nat -> value
.
Coercion Vnat : nat >-> value.
(** References are not values. In fact, they cannot be represented syntactically. *)
Inductive loc : Type :=
| addr : nat -> loc
.
Definition loc_eqb :=
  fun ℓ1 ℓ2 =>
    match ℓ1, ℓ2 with
    | addr n1, addr n2 => Nat.eqb n1 n2
    end
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
| Badd : binopsymb
| Bsub : binopsymb
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
Notation "'Tℕ'" := (Tnat).
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
| Xreturn (e : expr) : expr
| Xcall (foo : vart) (e : expr) : expr
| Xifz (c e0 e1 : expr) : expr
| Xabort : expr
.
Coercion Xres : ferr >-> expr.
#[local]
Instance expr__Instance : ExprClass expr := {}.

Fixpoint string_of_expr (e : expr) :=
  match e with
  | Xres(Fabrt) => "abort"%string
  | Xres(Fres(Fval(Vnat n))) => string_of_nat n
  | Xres(Fres(Fvar x)) => x
  | Xbinop _symb e0 e1 =>
    let s0 := string_of_expr e0 in
    let s1 := string_of_expr e1 in
    String.append (String.append (String.append ("("%string) s0) (String.append (") ⊕ ("%string) s1)) (")"%string)
  | Xget x e =>
    let s := string_of_expr e in
    String.append x (String.append (String.append ("["%string) s) "]"%string)
  | Xset x e0 e1 =>
    let s0 := string_of_expr e0 in
    let s1 := string_of_expr e1 in
    String.append x (String.append ("["%string) (String.append s0 (String.append "] <- " s1)))
  | Xlet x e0 e1 =>
    let s0 := string_of_expr e0 in
    let s1 := string_of_expr e1 in
    if vareq dontcare x then
      String.append s0 (String.append ";" s1)
    else
      String.append ("let "%string) (String.append x (String.append " = " (String.append s0 (String.append (";"%string) s1))))
  | Xnew x e0 e1 =>
    let s0 := string_of_expr e0 in
    let s1 := string_of_expr e1 in
    String.append ("let "%string) (String.append x (String.append " = new " (String.append s0 (String.append (";"%string) s1))))
  | Xdel x => String.append ("delete "%string) x
  | Xreturn e =>
    let s := string_of_expr e in
    String.append ("return "%string) s
  | Xcall f e =>
    let s := string_of_expr e in
    String.append (String.append (String.append ("call "%string) f) " "%string) s
  | Xifz c e0 e1 =>
    let cs := string_of_expr c in
    let s0 := string_of_expr e0 in
    let s1 := string_of_expr e1 in
    String.append (String.append (String.append ("ifz "%string) cs) (String.append (" then "%string) s0)) (String.append (" else "%string) s1)
  | Xabort => "abort"%string
  end
.

(** The following is a helper function to easily define functions over the syntax of S, e.g. substitution. *)
Definition exprmap (h : expr -> expr) (e : expr) :=
  match e with
  | Xbinop b lhs rhs => Xbinop b (h lhs) (h rhs)
  | Xget x e => Xget x (h e)
  | Xset x e0 e1 => Xset x (h e0) (h e1)
  | Xlet x e0 e1 => Xlet x (h e0) (h e1)
  | Xnew x e0 e1 => Xnew x (h e0) (h e1)
  | Xreturn e => Xreturn (h e)
  | Xcall f e => Xcall f (h e)
  | Xifz c e0 e1 => Xifz (h c) (h e0) (h e1)
  | _ => e
  end
.

(** We proceed to define the dynamic semantics via evaluation contexts/environments. *)
(** The reason we introduce them here is to define functions, since we model them simply as evaluation contexts. *)
Inductive evalctx : Type :=
| Khole : evalctx
| KbinopL (b : binopsymb) (K : evalctx) (e : expr) : evalctx
| KbinopR (b : binopsymb) (v : value) (K : evalctx) : evalctx
| Kget (x : vart) (K : evalctx) : evalctx
| KsetL (x : vart) (K : evalctx) (e : expr) : evalctx
| KsetR (x : vart) (v : value) (K : evalctx) : evalctx
| Klet (x : vart) (K : evalctx) (e : expr) : evalctx
| Knew (x : vart) (K : evalctx) (e : expr) : evalctx
| Kifz (K : evalctx) (e0 e1 : expr) : evalctx
| Kreturn (K : evalctx) : evalctx
| Kcall (foo : vart) (K : evalctx) : evalctx
.
#[local]
Instance evalctx__Instance : EvalCtxClass evalctx := {}.
Inductive ety : Type :=
| Tarrow : ty -> ty -> ety
.

(** * Freshness *)

(** In here, we define a helper judgement that gives us fresh variables. *)
Inductive fresh (A : Type) (eq : A -> A -> bool) (xs : list A) (x : A) : Prop :=
| Cfresh : List.find (eq x) xs = (None : option A) -> @fresh A eq xs x
.
Definition fresh_loc := @fresh loc loc_eqb.
Definition fresh_tvar := @fresh string String.eqb.


(** * Statics *)
Inductive Ty : Type :=
| Texpr : ty -> Ty
| Tectx : ety -> Ty
.
#[local]
Instance TheTy__Instance : TyClass Ty := {}.
Coercion Texpr : ty >-> Ty.
Coercion Tectx : ety >-> Ty.

(** Interface types *)
Inductive int : ty -> Prop :=
| intℕ : int Tℕ
| intwptr : int Twptr
.
(** Context splitting *)
Reserved Notation "Γ '≡' Γ1 '∘' Γ2" (at level 81, Γ1 at next level, Γ2 at next level).
Inductive splitting : Gamma -> Gamma -> Gamma -> Prop :=
| splitEmpty : [⋅] ≡ [⋅] ∘ [⋅]
| splitEmptyL : forall (Γ : Gamma), [⋅] ≡ [⋅] ∘ Γ
| splitEmptyR : forall (Γ : Gamma), [⋅] ≡ Γ ∘ [⋅]
| ℕsplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    x ↦ (Texpr Tℕ) ◘ Γ ≡ x ↦ (Texpr Tℕ) ◘ Γ1 ∘ (x ↦ (Texpr Tℕ) ◘ Γ2)
| weakPtrSplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    x ↦ (Texpr Twptr) ◘ Γ ≡ x ↦ (Texpr Twptr) ◘ Γ1 ∘ (x ↦ (Texpr Twptr) ◘ Γ2)
| ptrLSplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    x ↦ (Texpr Tptr) ◘ Γ ≡ x ↦ (Texpr Tptr) ◘ Γ1 ∘ Γ2
| ptrRSplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    x ↦ (Texpr Tptr) ◘ Γ ≡ x ↦ (Texpr Twptr) ◘ Γ1 ∘ (x ↦ (Texpr Tptr) ◘ Γ2)
| ArrowSplit : forall (x : vart) (τ0 τ1 : ty) (Γ Γ1 Γ2 : Gamma),
    int τ0 -> int τ1 ->
    Γ ≡ Γ1 ∘ Γ2 ->
    x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ ≡ x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ1 ∘ (x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ2)
where "Γ '≡' Γ1 '∘' Γ2" := (splitting Γ Γ1 Γ2)
.

(** Typechecking *)
Definition NoOwnedPtr (Γ : Gamma) := forall (x : vart) (τ : ty), mget Γ x = Some(Texpr τ) -> τ <> Tptr.
Inductive check : VDash :=
| CTvar : forall (x : vart) (Γ1 Γ2 : Gamma) (τ : Ty),
    NoOwnedPtr Γ1 ->
    NoOwnedPtr (x ↦ τ ◘ [⋅]) ->
    NoOwnedPtr Γ2 ->
    (Γ1 ◘ x ↦ τ ◘ Γ2) ⊦ Xres(Fvar x) : τ
| CTℕ : forall (Γ : Gamma) (n : nat),
    NoOwnedPtr Γ ->
    Γ ⊦ Xres n : Tℕ
| CToplus : forall (Γ1 Γ2 Γ3 : Gamma) (e1 e2 : expr) (b : binopsymb),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    (Γ1 ⊦ e1 : (Texpr Tℕ)) ->
    (Γ2 ⊦ e2 : (Texpr Tℕ)) ->
    (Γ3 ⊦ Xbinop b e1 e2 : (Texpr Tℕ))
| CTget : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (e : expr),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    (Γ2 ⊦ Xres(Fvar x) : (Texpr Twptr)) ->
    (Γ1 ⊦ e : (Texpr Tℕ)) ->
    (Γ3 ⊦ Xget x e : (Texpr Tℕ))
| CTset : forall (Γ1 Γ2 Γ3 Γ12 Γ4 : Gamma) (x : vart) (e1 e2 : expr),
    Γ12 ≡ Γ1 ∘ Γ2 ->
    Γ4 ≡ Γ12 ∘ Γ3 ->
    (Γ3 ⊦ (Xres(Fvar x)) : (Texpr Twptr)) ->
    (Γ1 ⊦ e1 : (Texpr Tℕ)) ->
    (Γ2 ⊦ e2 : (Texpr Tℕ)) ->
    (Γ4 ⊦ Xset x e1 e2 : (Texpr Tℕ))
| CTlet : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (e1 e2 : expr) (τ1 τ2 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    (Γ1 ⊦ e1 : (Texpr τ1)) ->
    (x ↦ (Texpr τ1) ◘ Γ2 ⊦ e2 : (Texpr τ2)) ->
    (Γ3 ⊦ Xlet x e1 e2 : (Texpr τ2))
| CTnew : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (e1 e2 : expr) (τ : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    (Γ1 ⊦ e1 : (Texpr Tℕ)) ->
    (x ↦ (Texpr Tptr) ◘ Γ2 ⊦ e2 : (Texpr τ)) ->
    (Γ3 ⊦ Xnew x e1 e2 : (Texpr τ))
| CTdel : forall (Γ1 Γ2 : Gamma) (x : vart),
    (Γ1 ◘ x ↦ (Texpr Tptr) ◘ Γ2 ⊦ Xdel x : (Texpr Tℕ))
| CTcall : forall (Γ : Gamma) (foo : vart) (arg : expr) (τ0 τ1 : ty),
    int τ0 -> int τ1 ->
    (Γ ⊦ Xres(Fvar foo) : (Tectx(Tarrow τ0 τ1))) ->
    (Γ ⊦ arg : (Texpr τ0)) ->
    (Γ ⊦ Xcall foo arg : (Texpr τ1))
| CTret : forall (Γ : Gamma) (e : expr) (τ : ty), (*TODO: intuitively, this should yield ⊥...?*)
    int τ ->
    (Γ ⊦ e : (Texpr τ)) ->
    (Γ ⊦ Xreturn e : (Texpr τ))
| CTifz : forall (Γ1 Γ2 Γ3 : Gamma) (c e1 e2 : expr) (τ : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    (Γ1 ⊦ c : (Texpr Tℕ)) ->
    (Γ2 ⊦ e1 : (Texpr τ)) ->
    (Γ2 ⊦ e2 : (Texpr τ)) ->
    (Γ3 ⊦ Xifz c e1 e2 : (Texpr τ))
.
#[local]
Hint Constructors check : core.

(** Symbols are pairs consisting of the function and its type. *)
Definition symbol : Type := evalctx * Ty.
#[local]
Instance symbol__Instance : SymbolClass symbol := {}.

(** A program is just a collection of symbols. The symbol `main` is the associated entry-point. *)
Inductive prog : Type := Cprog : symbols -> prog.
#[local]
Instance prog__Instance : ProgClass prog := Cprog.

Definition string_of_prog (p : prog) :=
  let '(Cprog s) := p in
  "prog"%string (*TODO*)
.

(** Typechecking evaluation contexts, which represent functions. *)
Inductive ectx_check (s : symbols) : @Gamma vart Ty TheTy__Instance varteq__Instance -> evalctx -> Ty -> Prop :=
| EThole : forall (Γ : Gamma) (τ0 : ty),
    int τ0 ->
    NoOwnedPtr Γ ->
    ectx_check s Γ Khole (Tectx(Tarrow τ0 τ0))
| ETbinopL : forall (Γ1 Γ2 Γ3 : Gamma) (b : binopsymb) (K : evalctx) (e : expr) (τ0 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    ectx_check s Γ1 K (Tectx(Tarrow τ0 Tℕ)) ->
    check Γ2 e Tℕ ->
    ectx_check s Γ3 (KbinopL b K e) (Tectx(Tarrow τ0 Tℕ))
| ETbinopR : forall (Γ1 Γ2 Γ3 : Gamma) (b : binopsymb) (K : evalctx) (v : value) (τ0 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    check Γ1 v Tℕ ->
    ectx_check s Γ2 K (Tectx(Tarrow τ0 Tℕ)) ->
    ectx_check s Γ3 (KbinopR b v K) (Tectx(Tarrow τ0 Tℕ))
| ETget : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (K : evalctx) (τ0 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    check Γ2 (Fvar x) Twptr ->
    ectx_check s Γ1 K (Tectx(Tarrow τ0 Tℕ)) ->
    ectx_check s Γ3 (Kget x K) (Tectx(Tarrow τ0 Tℕ))
| ETsetL : forall (Γ1 Γ2 Γ3 Γ12 Γ4 : Gamma) (x : vart) (K : evalctx) (e2 : expr) (τ0 : ty),
    Γ12 ≡ Γ1 ∘ Γ2 ->
    Γ4 ≡ Γ12 ∘ Γ3 ->
    check Γ3 (Fvar x) Twptr ->
    ectx_check s Γ1 K (Tectx(Tarrow τ0 Tℕ)) ->
    check Γ2 e2 Tℕ ->
    ectx_check s Γ4 (KsetL x K e2) (Tectx(Tarrow τ0 Tℕ))
| ETsetR : forall (Γ1 Γ2 Γ3 Γ12 Γ4 : Gamma) (x : vart) (K : evalctx) (v : value) (τ0 : ty),
    Γ12 ≡ Γ1 ∘ Γ2 ->
    Γ4 ≡ Γ12 ∘ Γ3 ->
    check Γ3 (Fvar x) Twptr ->
    check Γ1 v Tℕ ->
    ectx_check s Γ2 K (Tectx(Tarrow τ0 Tℕ)) ->
    ectx_check s Γ4 (KsetR x v K) (Tectx(Tarrow τ0 Tℕ))
| ETlet : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (K : evalctx) (e : expr) (τ0 τ1 τ2 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    ectx_check s Γ1 K (Tectx(Tarrow τ0 τ1)) ->
    check (x ↦ (Texpr τ1) ◘ Γ2) e τ2 ->
    ectx_check s Γ3 (Klet x K e) (Tectx(Tarrow τ0 τ2))
| ETnew : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (K : evalctx) (e : expr) (τ0 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    ectx_check s Γ1 K (Tectx(Tarrow τ0 Tℕ)) ->
    check (x ↦ (Texpr Tptr) ◘ Γ2) e Tℕ ->
    ectx_check s Γ3 (Knew x K e) (Tectx(Tarrow τ0 Tℕ))
| ETifz : forall (Γ1 Γ2 Γ3 : Gamma) (K : evalctx) (e1 e2 : expr) (τ0 τ1 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ->
    ectx_check s Γ1 K (Tectx(Tarrow τ0 Tℕ)) ->
    check Γ2 e1 τ1 ->
    check Γ2 e2 τ1 ->
    ectx_check s Γ3 (Kifz K e1 e2) (Tectx(Tarrow τ0 τ1))
| ETcall : forall (Γ : Gamma) (foo : vart) (K : evalctx) (τ0 τ1 τ2 : ty),
    int τ1 -> int τ2 ->
    check Γ (Xres(Fvar foo)) (Tectx(Tarrow τ1 τ2)) ->
    ectx_check s Γ K (Tectx(Tarrow τ0 τ1)) ->
    ectx_check s Γ (Kcall foo K) (Tectx(Tarrow τ0 τ2))
| ETret : forall (Γ : Gamma) (K : evalctx) (τ0 τ1 : ty), (*TODO: intuitively, this should yield ⊥...?*)
    int τ1 ->
    ectx_check s Γ K (Tectx(Tarrow τ0 τ1)) ->
    ectx_check s Γ (Kreturn K) (Tectx(Tarrow τ0 τ1))
.
#[local]
Hint Constructors ectx_check : core.

Fixpoint interfaces (s : symbols) : option(Gamma) :=
  match s with
  | mapNil _ _ => Some [⋅]
  | mapCons name EL s' =>
    let* a := interfaces s' in
    match EL with
    | (E, Tectx(Tarrow τ0 τ1)) => Some(name ↦ Tectx(Tarrow τ0 τ1) ◘ a)
    | _ => None
    end
  end
.

Definition prog_check (p : prog) : Prop :=
  let '(Cprog symbs) := p in
  let intt := interfaces symbs in
  match intt with
  | Some ints =>
    let fix doo (stack : symbols) :=
      match stack with
      | mapNil _ _ => True
      | mapCons foo (E, Tectx(Tarrow τ0 τ1)) xs => ectx_check symbs ints E (Tectx(Tarrow τ0 τ1)) /\ doo xs
      | _ => False
      end
    in doo symbs
  | None => False
  end
.

(** * Dynamics *)

(** Evaluation of binary expressions. Note that 0 means `true` in S, so `5 < 42` evals to `0`. *)
Definition eval_binop (b : binopsymb) (v0 v1 : value) :=
  let '(Vnat n0) := v0 in
  let '(Vnat n1) := v1 in
  Vnat(match b with
       | Bless => (if Nat.ltb n0 n1 then 0 else 1)
       | Badd => (n0 + n1)
       | Bsub => (n0 - n1)
       | Bmul => (n0 * n1)
       end)
.
(** Poison used to mark locations in our operational state. *)
Inductive poison : Type :=
| poisonless : poison
| poisoned : poison
.
Notation "'◻'" := (poisonless).
Notation "'☣'" := (poisoned).

Definition dynloc : Type := loc * poison.
(* '⋅' is `\cdot` *)
Notation "ℓ '⋅' ρ" := (((ℓ : loc), (ρ : poison)) : dynloc) (at level 81).

(** Stores map variables to potentially poisoned locations. *)
Definition store := mapind varteq__Instance dynloc.
Definition sNil : store := mapNil varteq__Instance dynloc.

#[local]
Instance nateq__Instance : HasEquality nat := Nat.eqb.
Definition heap := mapind nateq__Instance nat.
Definition hNil : heap := mapNil nateq__Instance nat.
Fixpoint Hgrow (H : heap) (s : nat) : heap :=
  match s with
  | 0 => H
  | S s' => mapCons s' 0 (Hgrow H s')
  end
.
(** We assume a mild axiom about the shape of heaps.
    It simply restricts the keys to be less than the length of a heap. *)
Axiom heap_axiom0 : forall (H : heap), forall (n : nat), n >= length H -> mget H n = None /\ forall v, mset H n v = None.
Axiom heap_axiom1 : forall (H : heap), forall (n : nat), n < length H -> mget H n <> None /\ forall v, mset H n v <> None.

Definition active_ectx := list evalctx.

#[local]
Existing Instance varteq__Instance | 0.
Definition state : Type := CSC.Fresh.fresh_state * symbols * active_ectx * heap * store.
Notation "F ';' Ξ ';' ξ ';' H ';' Δ" := ((F : CSC.Fresh.fresh_state), (Ξ : symbols),
                                         (ξ : active_ectx), (H : heap), (Δ : store))
                                         (at level 81, ξ at next level, Ξ at next level, H at next level, Δ at next level).

(** Store splitting. We don't need a case for nat, since identifiers with type nat get substituted at runtime. *)
Inductive store_split (Ξ : symbols) : store -> Gamma -> Prop :=
| TemptyΔ : forall (Γ : Gamma), interfaces Ξ = Some Γ -> store_split Ξ sNil Γ
| Tref1ℕ : forall (Γ : Gamma) (Δ : store) (x : vart) (ℓ : loc),
    store_split Ξ Δ Γ ->
    store_split Ξ (x ↦ (ℓ ⋅ ◻) ◘ Δ) (x ↦ (Texpr Tptr) ◘ Γ)
| Tref1ℕpoison : forall (Γ : Gamma) (Δ : store) (x : vart) (ℓ : loc),
    store_split Ξ Δ Γ ->
    store_split Ξ (x ↦ (ℓ ⋅ ☣) ◘ Δ) (x ↦ (Texpr Twptr) ◘ Γ)
| Tsplitign : forall (Γ : Gamma) (Δ : store) (x : vart) (τ0 τ1 : ty),
    store_split Ξ Δ Γ ->
    store_split Ξ Δ (x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ)
.
Inductive state_split : state -> Gamma -> Prop :=
| TΩ : forall F Ξ ξ H Δ (Γ : Gamma), store_split Ξ Δ Γ -> state_split (F ; Ξ ; ξ ; H ; Δ) Γ
.

(** Types of events that may occur in a trace. *)
Variant event : Type :=
| Salloc (ℓ : loc) (n : nat) : event
| Sdealloc (ℓ : loc) : event
| Sget (ℓ : loc) (n : nat) : event
| Sset (ℓ : loc) (n : nat) (v : value) : event
| Scrash : event
| Scall (foo : vart) (arg : fnoerr) : event
| Sret (f : fnoerr) : event
.
Definition eventeq (e1 e2 : event) : bool :=
  match e1, e2 with
  | Salloc(addr ℓ0) n0, Salloc(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sdealloc(addr ℓ0), Sdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Sget(addr ℓ0) n0, Sget(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sset(addr ℓ0) n0 (Vnat v0), Sset(addr ℓ1) n1 (Vnat v1) => andb (andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1))
                                                                  (Nat.eqb v0 v1)
  | Scrash, Scrash => true
  | Scall foo (Fval(Vnat v0)), Scall bar (Fval(Vnat v1)) => andb (String.eqb foo bar) (Nat.eqb v0 v1)
  | Scall foo (Fvar x), Scall bar (Fvar y) => andb (String.eqb foo bar) (String.eqb x y)
  | Sret (Fval(Vnat v0)), Sret (Fval(Vnat v1)) => Nat.eqb v0 v1
  | Sret (Fvar x), Sret (Fvar y) => String.eqb x y
  | _, _ => false
  end
.
#[local]
Instance Event__Instance : TraceEvent event := {}.
(** Pretty-printing function for better debuggability *)
Definition string_of_event (e : event) :=
  match e with
  | (Salloc (addr ℓ) n) => String.append
                      (String.append ("Alloc ℓ"%string) (string_of_nat ℓ))
                      (String.append (" "%string) (string_of_nat n))
  | (Sdealloc (addr ℓ)) => String.append ("Dealloc ℓ"%string) (string_of_nat ℓ)
  | (Sget (addr ℓ) n) => String.append
                    (String.append ("Get ℓ"%string) (string_of_nat ℓ))
                    (String.append (" "%string) (string_of_nat n))
  | (Sset (addr ℓ) n (Vnat m)) => String.append
                             (String.append
                               (String.append ("Set ℓ"%string) (string_of_nat ℓ))
                               (String.append (" "%string) (string_of_nat n)))
                             (String.append (" "%string) (string_of_nat m))
  | (Scrash) => "↯"%string
  | (Scall foo (Fval(Vnat n))) => String.append (String.append (String.append ("Call ?"%string) foo) " "%string) (string_of_nat n)
  | (Scall foo (Fvar x)) => String.append (String.append (String.append ("Call ?"%string) foo) " "%string) x
  | (Sret (Fval(Vnat n))) => String.append ("Ret !"%string) (string_of_nat n)
  | (Sret (Fvar x)) => String.append ("Ret !"%string) x
  end
.

(** A runtime program is a state plus an expression. *)
Definition rtexpr : Type := (option state) * expr.
#[local]
Instance rtexpr__Instance : RuntimeExprClass rtexpr := {}.
(* '▷' is `\triangleright and '↯' is `\lightning`` *)
Notation "Ω '▷' e" := ((((Some (Ω)) : option state), (e : expr)) : rtexpr) (at level 81).
Notation "↯ '▷' 'stuck'" := (((None : option state), (Fabrt : expr)) : rtexpr).

(** Substitution, which assumes that the given expression is closed. *)
Definition subst (what : vart) (inn forr : expr) : expr :=
  let substid := match forr with
                 | Xres(Fres(Fvar y)) => Some y
                 | _ => None
                 end
  in
  let fix isubst e :=
    let R := isubst in
    match e with
    | Xlet x e0 e1 => if vareq what x then Xlet x (R e0) e1 else Xlet x (R e0) (R e1)
    | Xnew x e0 e1 => if vareq what x then Xnew x (R e0) e1 else Xnew x (R e0) (R e1)
    | Xget x e' => match substid with
                  | None => Xget x
                  | Some y => if vareq what x then Xget y else Xget x
                  end (R e')
    | Xset x e0 e1 => match substid with
                     | None => Xset x
                     | Some y => if vareq what x then Xset y else Xset x
                     end (R e0) (R e1)
    | Xdel x => match substid with
               | None => Xdel x
               | Some y => if vareq what x then Xdel y else Xdel x
               end
    | Xres(Fres(Fvar x)) => if vareq what x then forr else e
    | Xbinop b e1 e2 => Xbinop b (R e1) (R e2)
    | Xifz c e1 e2 => Xifz (R c) (R e1) (R e2)
    | Xreturn e => Xreturn (R e)
    | Xcall foo e => Xcall foo (R e)
    | _ => e
    end
  in
  isubst inn
.

Inductive pstep : PrimStep :=
| e_binop : forall (Ω : state) (n1 n2 n3 : nat) (b : binopsymb),
    Vnat n3 = eval_binop b n1 n2 ->
    Ω ▷ Xbinop b n1 n2 --[]--> Ω ▷ n3
| e_ifz_true : forall (Ω : state) (e1 e2 : expr),
    Ω ▷ Xifz 0 e1 e2 --[]--> Ω ▷ e1
| e_ifz_false : forall (Ω : state) (e1 e2 : expr) (n : nat),
    Ω ▷ Xifz (S n) e1 e2 --[]--> Ω ▷ e2
| e_abort : forall (Ω : state),
    Ω ▷ Xabort --[ (Scrash) ]--> ↯ ▷ stuck
| e_get : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : active_ectx) (H : heap) (Δ1 Δ2 : store) (x : vart) (ℓ n v : nat) (ρ : poison),
    forall (H0a : ℓ + n < length H -> Some v = mget H (ℓ + n))
      (H0b : ℓ + n >= length H -> v = 1729),
    (F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xget x n --[ (Sget (addr ℓ) n) ]--> (F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ v
| e_set : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : active_ectx) (H H' : heap) (Δ1 Δ2 : store) (x : vart) (ℓ n v : nat) (ρ : poison),
    forall (H0a : ℓ + n < length H -> Some H' = mset H (ℓ + n) v)
      (H0b : ℓ + n >= length H -> H' = H),
    (F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xset x n v --[ (Sset (addr ℓ) n v) ]--> (F ; Ξ ; ξ ; H' ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ v
| e_delete : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : active_ectx) (H : heap) (Δ1 Δ2 : store) (x : vart) (ℓ : nat) (ρ : poison),
    (F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xdel x --[ (Sdealloc (addr ℓ)) ]--> (F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ☣) ◘ Δ2)) ▷ 0
| e_let : forall (Ω : state) (x : vart) (f : fnoerr) (e e' : expr),
    e' = subst x e f ->
    Ω ▷ Xlet x f e --[]--> Ω ▷ e'
| e_alloc : forall (F F' F'' : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : active_ectx) (H H' : heap) (Δ : store) (x z : vart) (ℓ n : nat) (e : expr),
    ℓ = Fresh.fresh F ->  F' = Fresh.advance F ->
    z = Fresh.freshv F' -> F'' = Fresh.advance F' ->
    (*TODO: fresh_loc (Δimg Δ) (addr ℓ) ->*)
    (*fresh_tvar (Δdom Δ) z ->*)
    H' = Hgrow H n ->
    (F ; Ξ ; ξ ; H ; Δ) ▷ Xnew x n e --[ (Salloc (addr ℓ) n) ]--> (F'' ; Ξ ; ξ ; H' ; (z ↦ ((addr ℓ) ⋅ ◻) ◘ Δ)) ▷ (subst x e (Fvar z))
.
#[local]
Existing Instance pstep.
#[local]
Hint Constructors pstep : core.

(** functional version of the above *)
Definition pstepf (r : rtexpr) : option (option event * rtexpr) :=
  let '(oΩ, e) := r in
  let* Ω := oΩ in
  match e with
  | Xbinop b n1 n2 => (* e-binop *)
    match n1, n2 with
    | Xres(Fres(Fval(Vnat m1))), Xres(Fres(Fval(Vnat m2))) =>
      let n3 := eval_binop b m1 m2 in
      Some(None, Ω ▷ n3)
    | _, _ => None
    end
  | Xifz 0 e1 e2 => (* e-ifz-true *)
    Some(None, Ω ▷ e1)
  | Xifz (S _) e1 e2 => (* e-ifz-false *)
    Some(None, Ω ▷ e2)
  | Xabort => (* e-abort *)
    Some(Some(Scrash), ↯ ▷ stuck)
  | Xget x en => (* e-get *)
    match en with
    | Xres(Fres(Fval(Vnat n))) =>
      let '(F, Ξ, ξ, H, Δ) := Ω in
      let* (Δ1, x, (L, ρ), Δ2) := splitat Δ x in
      let '(addr ℓ) := L in
      let v := match mget H (ℓ + n) with
              | None => 1729
              | Some w => w
              end
      in
        Some(Some(Sget (addr ℓ) n), F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2) ▷ v)
    | _ => None
    end
  | Xset x en ev => (* e-set *)
    match en, ev with
    | Xres(Fres(Fval(Vnat n))), Xres(Fres(Fval(Vnat v))) =>
      let '(F, Ξ, ξ, H, Δ) := Ω in
      let* (Δ1, x, (L, ρ), Δ2) := splitat Δ x in
      let '(addr ℓ) := L in
      match mset H (ℓ + n) v with
      | Some H' =>
        Some(Some(Sset (addr ℓ) n v), F ; Ξ ; ξ ; H' ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2) ▷ v)
      | None =>
        Some(Some(Sset (addr ℓ) n v), F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2) ▷ v)
      end
    | _, _ => None
    end
  | Xdel x => (* e-delete *)
    let '(F, Ξ, ξ, H, Δ) := Ω in
    let* (Δ1, x, (L, ρ), Δ2) := splitat Δ x in
    let '(addr ℓ) := L in
    Some(Some(Sdealloc (addr ℓ)), F ; Ξ ; ξ ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ☣) ◘ Δ2) ▷ 0)
  | Xlet x ef e' => (* e-let *)
    match ef with
    | Xres(Fres f) =>
      let e'' := subst x e' f in
      Some(None, Ω ▷ e'')
    | _ => None
    end
  | Xnew x ef e' => (* e-new *)
    match ef with
    | Xres(Fres(Fval(Vnat n))) =>
      let '(F, Ξ, ξ, H, Δ) := Ω in
      let H' := Hgrow H n in
      let ℓ := CSC.Fresh.fresh F in
      let F' := Fresh.advance F in
      let z := CSC.Fresh.freshv F' in
      let e'' := subst x e' (Fvar z) in
      Some(Some(Salloc (addr ℓ) n), Fresh.advance F' ; Ξ ; ξ ; H' ; (z ↦ ((addr ℓ) ⋅ ◻) ◘ Δ) ▷ e'')
    | _ => None
    end
  | _ => None (* no matching rule *)
  end
.
(** We show that the functional style semantics an dthe relational style are equivalent. *)
Ltac crush_interp :=
    match goal with
    | [H: match ?oΩ with | Some _ => _ | None => None end = Some _ |- _] =>
        let Ω := fresh "Ω" in destruct oΩ as [|]; inversion H
    end.
Ltac grab_value e :=
  (destruct e as [[[[e]|]|]| | | | | | | | | |]; try congruence)
.
Ltac grab_value2 e1 e2 := (grab_value e1; grab_value e2).
Ltac grab_final e :=
  (destruct e as [[e|]| | | | | | | | | | ]; try congruence)
.

Lemma splitat_elim (Δ1 Δ2 : store) (x : vart) (ℓ : loc) (ρ : poison) :
  splitat (Δ1 ◘ x ↦ (ℓ ⋅ ρ) ◘ Δ2) x = Some (Δ1, x, (ℓ ⋅ ρ), Δ2).
Proof. Admitted.
Lemma splitat_base (Δ : store) (x : vart) :
  splitat Δ x <> None -> exists Δ1 ℓ ρ Δ2, Δ = (Δ1 ◘ x ↦ (ℓ ⋅ ρ) ◘ Δ2).
Proof.
  intros H; apply not_eq_None_Some in H as [[[[Δ1 y] [ℓ ρ]] Δ2] H].
  exists Δ1. exists ℓ. exists ρ. exists Δ2.
Admitted.
Lemma splitat_none_or_not_none (Δ : store) (x : vart) :
  splitat Δ x = None \/ splitat Δ x <> None.
Proof. destruct (option_dec (splitat Δ x)); now (left + right). Qed.
Lemma Hget_none (H : heap) (n : nat) :
  n >= length H -> mget H n = None.
Proof. eapply heap_axiom0. Qed.
Lemma Hget_some (H : heap) (n : nat) :
  n < length H -> exists v, mget H n = Some v.
Proof.
  intros H0; apply heap_axiom1 in H0 as [H0 _]; apply not_eq_None_Some in H0;
  unfold is_Some in H0; deex; eauto.
Qed.
Lemma Hset_none (H : heap) (n : nat) v :
  n >= length H -> mset H n v = None.
Proof. intros H0; eapply heap_axiom0; trivial. Qed.
Lemma Hset_some (H : heap) (n : nat) v :
  n < length H -> exists H', mset H n v = Some H'.
Proof.
  intros H0; apply heap_axiom1 in H0 as [_ H0]; specialize (H0 v); apply not_eq_None_Some in H0;
  unfold is_Some in H0; deex; eauto.
Qed.

(** We use an alternative notation of pstep here that does not constrain a to be *either* Some/None *)
Lemma equiv_pstep (r0 : rtexpr) (a : option event) (r1 : rtexpr) :
  r0 --[, a ]--> r1 <-> pstepf r0 = Some(a, r1).
Proof.
  split.
  - induction 1.
    + (* e-binop *) rewrite H; now cbn.
    + (* e-ifz-true *) now cbn.
    + (* e-ifz-false *) now cbn.
    + (* e-abort *) now cbn.
    + (* e-get *) cbn.
      destruct (Arith.Compare_dec.lt_dec (ℓ + n) (length H)) as [H1a | H1b]; rewrite splitat_elim.
      * now specialize (H0a H1a) as H0a'; inv H0a'.
      * apply Arith.Compare_dec.not_lt in H1b; specialize (H0b H1b) as H1b'.
        now rewrite (@Hget_none H (ℓ + n) H1b); subst.
    + (* e-set *) cbn.
      destruct (Arith.Compare_dec.lt_dec (ℓ + n) (length H)) as [H1a | H1b]; rewrite splitat_elim.
      * now rewrite <- (H0a H1a).
      * apply Arith.Compare_dec.not_lt in H1b; specialize (H0b H1b) as H1b'; subst.
        now rewrite (@Hset_none H (ℓ + n) v H1b).
    + (* e-delete *) now cbn; rewrite splitat_elim.
    + (* e-let *) now subst; cbn.
    + (* e-new *) now rewrite H3; subst; cbn.
  - intros H; destruct r0 as [oΩ e], r1 as [Ω' e']; destruct e; cbn in H; crush_interp; clear H.
    + (* e = e1 ⊕ e2 *)
      now grab_value2 e1 e2; inv H1; eapply e_binop.
    + (* e = x[e] *)
      grab_value e. destruct s as [[[[F Ξ] ξ] H] Δ].
      destruct (splitat_none_or_not_none Δ x) as [H0|H0]; try (rewrite H0 in H1; congruence).
      apply splitat_base in H0 as [Δ1 [[ℓ] [ρ [Δ2 H0]]]]. rewrite H0 in H1.
      rewrite splitat_elim in H1. inv H1. eapply e_get; intros H0.
      * now apply Hget_some in H0 as [v ->].
      * now apply Hget_none in H0 as ->.
    + (* e = x[e1] <- e2 *)
      grab_value2 e1 e2. destruct s as [[[[F Ξ] ξ] H] Δ].
      destruct (splitat_none_or_not_none Δ x) as [H0|H0]; try (rewrite H0 in H1; congruence).
      apply splitat_base in H0 as [Δ1 [[ℓ] [ρ [Δ2 H0]]]]. rewrite H0 in H1.
      rewrite splitat_elim in H1.
      destruct (Arith.Compare_dec.lt_dec (ℓ + e1) (length H)) as [H2|H2].
      * apply (@Hset_some H (ℓ + e1) e2) in H2 as [H' H2]. rewrite H2 in H1.
        inv H1. eapply e_set; intros H0; subst; try easy.
        eapply (@Hset_none H (ℓ + e1) e2) in H0; congruence.
      * apply Arith.Compare_dec.not_lt in H2. apply (@Hset_none H (ℓ + e1) e2) in H2; subst; rewrite H2 in H1.
        inv H1. eapply e_set; intros H0; try easy. apply (@Hset_some H (ℓ + e1) e2) in H0 as [H' H0]; congruence.
    + (* e = let x = e1 in e2 *)
      grab_final e1; inv H1; now eapply e_let.
    + (* e = let x = new e1 in e2 *)
      grab_value e1; destruct s as [[[[F Ξ] ξ] H] Δ]; inv H1; eapply e_alloc; eauto.
    + (* e = delete x *)
      destruct s as [[[[F Ξ] ξ] H] Δ]; inv H1.
      destruct (splitat_none_or_not_none Δ x) as [H0|H0]; try (rewrite H0 in H2; congruence).
      apply splitat_base in H0 as [Δ1 [[ℓ] [ρ [Δ2 H0]]]]. rewrite H0 in H2.
      rewrite splitat_elim in H2; subst. inv H2. apply e_delete.
    + (* e = ifz c e0 e1 *)
      grab_value e1. destruct e1; inv H1; apply e_ifz_true || apply e_ifz_false.
    + (* e = abort *)
      apply e_abort.
Qed.
(** convert an expression to evalctx in order to execute it functionally + "contextually" *)
(** this function returns an eval context K and an expr e' such that K[e'] = e given some e *)
Fixpoint evalctx_of_expr (e : expr) : option (evalctx * expr) :=
  match e with
  | Xres _ => None
  | Xdel x => Some(Khole, Xdel x)
  | Xabort => Some(Khole, Xabort)
  | Xbinop b e1 e2 =>
    match e1, e2 with
    | Xres(Fres(Fval(Vnat n1))), Xres(Fres(Fval(Vnat n2))) =>
      Some(Khole, Xbinop b n1 n2)
    | Xres(Fres(Fval(Vnat n1))), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KbinopR b n1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KbinopL b K e2, e1')
    end
  | Xget x en =>
    match en with
    | Xres(Fres(Fval(Vnat n))) =>
      Some(Khole, Xget x n)
    | _ => let* (K, en') := evalctx_of_expr en in
          Some(Kget x K, en')
    end
  | Xset x en ev =>
    match en, ev with
    | Xres(Fres(Fval(Vnat n))), Xres(Fres(Fval(Vnat v))) =>
      Some (Khole, Xset x n v)
    | Xres(Fres(Fval(Vnat n))), ev =>
      let* (K, ev') := evalctx_of_expr ev in
      Some(KsetR x n K, ev')
    | en, ev =>
      let* (K, en') := evalctx_of_expr en in
      Some(KsetL x K ev, en')
    end
  | Xlet x e1 e2 =>
    match e1 with
    | Xres(Fres f) =>
      Some(Khole, Xlet x f e2)
    | _ => let* (K, e1') := evalctx_of_expr e1 in
          Some(Klet x K e2, e1')
    end
  | Xnew x e1 e2 =>
    match e1 with
    | Xres(Fres(Fval(Vnat n))) =>
      Some(Khole, Xnew x n e2)
    | _ => let* (K, e1') := evalctx_of_expr e1 in
          Some(Knew x K e2, e1')
    end
  | Xreturn e =>
    match e with
    | Xres f =>
      Some(Khole, Xreturn f)
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kreturn K, e')
    end
  | Xcall foo e =>
    match e with
    | Xres f =>
      Some(Khole, Xcall foo f)
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kcall foo K, e')
    end
  | Xifz c e0 e1 =>
    match c with
    | Xres(Fres(Fval(Vnat v))) =>
      Some(Khole, Xifz v e0 e1)
    | _ => let* (K, c') := evalctx_of_expr c in
          Some(Kifz K e0 e1, c')
    end
  end
.
Fixpoint insert (K : evalctx) (withh : expr) : expr :=
  let R := fun k => insert k withh in
  match K with
  | Khole => withh
  | KbinopL b K' e => Xbinop b (R K') e
  | KbinopR b v K' => Xbinop b v (R K')
  | Kget x K' => Xget x (R K')
  | KsetL x K' e => Xset x (R K') e
  | KsetR x v K' => Xset x v (R K')
  | Klet x K' e => Xlet x (R K') e
  | Knew x K' e => Xnew x (R K') e
  | Kifz K' e0 e1 => Xifz (R K') e0 e1
  | Kcall foo K' => Xcall foo (R K')
  | Kreturn K' => Xreturn (R K')
  end
.
(* Checks wether the thing that is filled into the hole is somehow structurually compatible with pstep *)
Definition pstep_compatible (e : expr) : option expr :=
  match e with
  | Xifz 0 e0 e1 => Some (Xifz 0 e0 e1)
  | Xifz (S n) e0 e1 => Some (Xifz (S n) e0 e1)
  | Xabort => Some (Xabort)
  | Xdel x => Some (Xdel x)
  | Xbinop b (Xres(Fres(Fval(Vnat n1)))) (Xres(Fres(Fval(Vnat n2)))) => Some (Xbinop b n1 n2)
  | Xget x (Xres(Fres(Fval(Vnat n)))) => Some(Xget x n)
  | Xset x (Xres(Fres(Fval(Vnat n1)))) (Xres(Fres(Fval(Vnat n2)))) => Some(Xset x n1 n2)
  | Xnew x (Xres(Fres(Fval(Vnat n)))) e => Some(Xnew x n e)
  | Xlet x (Xres(Fres f)) e => Some(Xlet x f e)
  | _ => None
  end
.
Definition pestep_compatible (e : expr) : option expr :=
  match e with
  | Xifz 0 e0 e1 => Some (Xifz 0 e0 e1)
  | Xifz (S n) e0 e1 => Some (Xifz (S n) e0 e1)
  | Xabort => Some (Xabort)
  | Xdel x => Some (Xdel x)
  | Xbinop b (Xres(Fres(Fval(Vnat n1)))) (Xres(Fres(Fval(Vnat n2)))) => Some (Xbinop b n1 n2)
  | Xget x (Xres(Fres(Fval(Vnat n)))) => Some(Xget x n)
  | Xset x (Xres(Fres(Fval(Vnat n1)))) (Xres(Fres(Fval(Vnat n2)))) => Some(Xset x n1 n2)
  | Xnew x (Xres(Fres(Fval(Vnat n)))) e => Some(Xnew x n e)
  | Xlet x (Xres(Fres f)) e => Some(Xlet x f e)
  | Xcall foo (Xres(Fres f)) => Some(Xcall foo f)
  | Xreturn (Xres(Fres f)) => Some(Xreturn f)
  | _ => None
  end
.
Lemma return_pestep_compat (f : fnoerr) :
  Some(Xreturn f) = pestep_compatible (Xreturn f).
Proof. now cbn. Qed.
Lemma call_pestep_compat foo (f : fnoerr) :
  Some(Xcall foo f) = pestep_compatible (Xcall foo f).
Proof. now cbn. Qed.
Lemma pstep_compat_weaken e :
  Some e = pstep_compatible e ->
  Some e = pestep_compatible e.
Proof. induction e; now cbn. Qed.
#[local]
Hint Resolve pstep_compat_weaken call_pestep_compat return_pestep_compat : core.

(** Environment Semantics extended with context switches *)
Inductive estep : CtxStep :=
| E_return : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : active_ectx) (H : heap) (Δ : store)
               (E E__foo : evalctx) (f : fnoerr),
    (F ; Ξ ; E__foo :: ξ ; H ; Δ ▷ insert E (Xreturn f) ==[ Sret f ]==> F ; Ξ ; ξ ; H ; Δ ▷ insert E__foo f)
| E_call : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : active_ectx) (H : heap) (Δ : store)
             (E E__foo : evalctx) (τ__int : Ty) (foo : vart) (f : fnoerr),
    Some (E__foo,τ__int) = mget Ξ foo ->
    (F ; Ξ ; ξ ; H ; Δ ▷ insert E (Xcall foo f) --[ Scall foo f ]--> F ; Ξ ; E :: ξ ; H ; Δ ▷ insert (Kreturn E__foo) f)
| E_ctx : forall (Ω Ω' : state) (e e' e0 e0' : expr) (a : option event) (K : evalctx),
    (*Some(K,e) = evalctx_of_expr e0 ->*)
    Some e = pstep_compatible e ->
    e0 = insert K e ->
    e0' = insert K e' ->
    Ω ▷ e --[, a ]--> Ω' ▷ e' ->
    Ω ▷ e0 ==[, a ]==> Ω' ▷ e0'
| E_abrt_ctx : forall (Ω : state) (e e0 : expr) (K : evalctx),
    (*Some(K,e) = evalctx_of_expr e0 ->*)
    Some e = pstep_compatible e ->
    e0 = insert K e ->
    Ω ▷ e --[ Scrash ]--> ↯ ▷ stuck ->
    Ω ▷ e0 ==[ Scrash ]==> ↯ ▷ stuck
.
#[local]
Existing Instance estep.
#[local]
Hint Constructors estep : core.

Local Set Warnings "-cast-in-pattern".
Ltac crush_estep := (match goal with
                     | [H: _ ▷ (Xres ?f) ==[ ?a ]==> ?r |- _] =>
                       inv H
                     | [H: _ ▷ (Xres ?f) ==[]==> ?r |- _] =>
                       inv H
                     | [H: _ ▷ (Xres ?f) ==[, ?a ]==> ?r |- _] =>
                       inv H
                     end);
  (repeat match goal with
   | [H: insert ?E (Xreturn (Xres(Fres ?f0))) = Xres ?f |- _] => induction E; try congruence; inv H
   | [H: insert ?E (Xcall ?foo (Xres(Fres ?f0))) = Xres ?f |- _] => induction E; try congruence; inv H
   | [H: Xres ?f = insert ?K ?e |- _] =>
     induction K; cbn in H; try congruence; inv H
   | [H: _ ▷ (Xres ?f) --[]--> ?r |- _] =>
     inv H
   | [H: _ ▷ (Xres ?f) --[, ?a ]--> ?r |- _] =>
     inv H
   | [H: _ ▷ (Xres ?f) --[ ?a ]--> ?r |- _] =>
     inv H
   end)
.
Ltac unfold_estep := (match goal with
                      | [H: _ ▷ _ ==[ _ ]==> _ ▷ _ |- _ ] => inv H
                      end);
  (match goal with
   | [H: _ = insert ?K _ |- _] =>
     induction K; cbn in H; try congruence; inv H
   end).

Definition estepf (r : rtexpr) : option (option event * rtexpr) :=
  let '(oΩ, e) := r in
  let* Ω := oΩ in
  let* (K, e0) := evalctx_of_expr e in
  match e0 with
  | Xcall foo (Xres(Fres f)) =>
    let '(F, Ξ, ξ, H, Δ) := Ω in
    match mget Ξ foo with
    | None => None
    | Some (K__foo,_) =>
    Some(Some(Scall foo f), (F ; Ξ ; (K :: ξ) ; H ; Δ ▷ (insert (Kreturn K__foo) (Xres(Fres f)))))
    end
  | Xreturn(Xres(Fres f)) =>
    let '(F, Ξ, ξ', H, Δ) := Ω in
    match ξ' with
    | nil => None
    | K__foo :: ξ =>
      Some(Some(Sret f), F ; Ξ ; ξ ; H ; Δ ▷ insert K__foo f)
    end
  | _ =>
    let* _ := pstep_compatible e0 in
    let* (a, (oΩ, e0')) := pstepf (Ω ▷ e0) in
    match oΩ with
    | None => Some(Some(Scrash), ↯ ▷ stuck)
    | Some Ω' => Some(a, Ω' ▷ insert K e0')
    end
  end
.

Ltac crush_insert :=
  match goal with
  | [H: insert ?K ?e = ?f |- _] => symmetry in H
  | _ => trivial
  end;
  (match goal with
   | [H: ?f = insert ?K ?e |- _] =>
     let H' := fresh "H" in
     assert (H':=H); generalize dependent e; induction K; intros; cbn in H; try congruence; inv H
   end)
.

Inductive is_val : expr -> Prop :=
| Cfres : forall e f, e = Xres(Fres(Fval(Vnat f))) -> is_val e
.

Lemma expr_val_dec e :
  { is_val e } + { ~is_val e }.
Proof.
  induction e.
  1: destruct f. destruct f. destruct v. left; eauto using Cfres.
  all: right; intros H; inv H; inv H0.
Qed.
#[local]
Ltac crush_grab_ectx :=
      (repeat match goal with
      | [H: Some(Xres ?f) = pestep_compatible(Xres ?f) |- _] => inv H
      | [H: Some(?e) = pestep_compatible ?e |- _] => cbn in H
      | [H: Some(_) = match ?e with
                      | Xres _ => _
                      | _ => _
                      end |- _] => grab_value e
      | [H: Some _ = None |- _] => inv H
      end; try now cbn;
      match goal with
      | [v : value |- _] => destruct v
      | [ |- _ ] => trivial
      end;
      cbn; repeat match goal with
           | [H1: _ = insert _ _ |- _] => cbn in H1
           | [H: Some ?e0 = pestep_compatible ?e0 |- match insert ?K ?e0 with
                                                   | Xres _ => _
                                                   | _ => _
                                                   end = _] => let ek := fresh "ek" in
                                                              let H2 := fresh "H2" in
                                                              remember (insert K e0) as ek;
                                                              destruct (expr_val_dec ek) as [H2|H2];
                                                              try (inv H2; crush_insert; match goal with
                                                              | [H: Some ?f = pestep_compatible ?f, f: nat |- _] => inv H
                                                              end)
           | [H: Some(?e0) = pestep_compatible ?e0,
             H1: _ = insert _ _ |- _] => cbn in H
           end;
      match goal with
      | [K: evalctx, e0: expr, ek: expr,
         H: Some ?e0 = pestep_compatible ?e0,
         Heqek: ?ek = insert ?K ?e0,
         IHe: (forall (K' : evalctx) (e0' : expr), Some e0' = pestep_compatible e0' ->
                                              ?ek = insert K' e0' ->
                                              evalctx_of_expr ?ek = Some(K', e0'))
         |- _] =>
         specialize (IHe K e0 H Heqek) as ->
      end;
      repeat match goal with
      | [H: ~ is_val ?ek |- match ?ek with
                           | Xres _ => _
                           | _ => _
                           end = _] => destruct ek; trivial
      | [H: ~ is_val (Xres ?f) |- match ?f with
                          | Fres _ => _
                          | _ => _
                          end = _] => destruct f; trivial
      | [H: ~ is_val (Xres(Fres ?f)) |- match ?f with
                          | Fval _ => _
                          | _ => _
                          end = _] => destruct f; trivial
      | [H: ~ is_val (Xres(Fres(Fval ?v))) |- _ ] => destruct v; destruct H; eauto using Cfres
      end).
Lemma grab_ectx e K e0 :
  Some e0 = pestep_compatible e0 ->
  e = insert K e0 ->
  evalctx_of_expr e = Some(K, e0)
.
Proof.
  revert K e0; induction e; intros; crush_insert; crush_grab_ectx.
  cbn. remember (insert K e0) as ek.
  destruct (expr_val_dec ek) as [H2|H2];
  try (inv H2; crush_insert; inv H).
  specialize (IHe1 K e0 H Heqek) as ->.
  destruct ek; trivial. destruct f; trivial.
  induction K; cbn in Heqek; try congruence; inv Heqek; inv H.

  cbn; remember (insert K e0) as ek.
  destruct (expr_val_dec ek) as [H2|H2];
  try (inv H2; crush_insert; inv H).
  specialize (IHe K e0 H Heqek) as ->;
  destruct ek; trivial.
  induction K; cbn in Heqek; try congruence; inv Heqek; inv H.

  cbn; remember (insert K e0) as ek.
  destruct (expr_val_dec ek) as [H2|H2];
  try (inv H2; crush_insert; inv H).
  specialize (IHe K e0 H Heqek) as ->;
  destruct ek; trivial.
  induction K; cbn in Heqek; try congruence; inv Heqek; inv H.
Qed.

Lemma easy_ectx e0 :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e0 = Some(Khole, e0).
Proof. induction e0; cbn in *; intros H; crush_grab_ectx. Qed.

Lemma injective_ectx e0 K e e' :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e = Some(K, e0) ->
  evalctx_of_expr e' = Some(K, e0) ->
  e = e'.
Proof. Admitted.

Lemma ungrab_ectx e K e0 :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e = Some(K, e0) ->
  e = insert K e0.
Proof.
  intros H H1; remember (insert K e0) as e1;
  eapply grab_ectx in Heqe1 as H2; eauto;
  eapply injective_ectx; eauto.
Qed.
Lemma pstep_compatible_some e e' :
  pstep_compatible e = Some e' -> e = e'.
Proof.
  revert e'; induction e; intros; cbn in H; try congruence.
  - (* binop *) grab_value2 e1 e2.
  - (* get *) grab_value e.
  - (* set *) grab_value2 e1 e2.
  - (* let *) grab_value e1.
  - (* new *) grab_value e1.
  - (* ifz *) grab_value e1; destruct e1; now inv H.
Qed.
Lemma pestep_compatible_some e e' :
  pestep_compatible e = Some e' -> e = e'.
Proof.
  revert e'; induction e; intros; cbn in H; try congruence.
  - (* binop *) grab_value2 e1 e2.
  - (* get *) grab_value e.
  - (* set *) grab_value2 e1 e2.
  - (* let *) grab_value e1.
  - (* new *) grab_value e1.
  - (* ret *) grab_value e.
  - (* call *) grab_value e.
  - (* ifz *) grab_value e1; destruct e1; now inv H.
Qed.
Lemma elim_ectx_ret K (f : fnoerr) :
  evalctx_of_expr (insert K (Xreturn f)) = Some(K, Xreturn f).
Proof. remember (insert K (Xreturn f)); eapply grab_ectx in Heqe; eauto. Qed.
Lemma elim_ectx_call K foo (f : fnoerr) :
  evalctx_of_expr (insert K (Xcall foo f)) = Some(K, Xcall foo f).
Proof. remember (insert K (Xcall foo f)); eapply grab_ectx in Heqe; eauto. Qed.

Lemma equiv_estep r0 a r1 :
  r0 ==[, a ]==> r1 <-> estepf r0 = Some(a, r1).
Proof.
  split.
  - induction 1.
    + (* ret *)
      unfold estepf.
      rewrite (get_rid_of_letstar (F, Ξ, E__foo :: ξ, H, Δ)).
      rewrite elim_ectx_ret.
      now rewrite (get_rid_of_letstar (E, Xreturn f)).
    + (* call *)
      unfold estepf.
      rewrite (get_rid_of_letstar (F, Ξ, E__foo :: ξ, H, Δ)).
      rewrite elim_ectx_call.
      rewrite (get_rid_of_letstar (E, Xcall foo f)).
      change ((fun o => match o with
                    | Some(K__foo, _) => Some(Some (Scall foo f), (Some (F, Ξ, E :: ξ, H, Δ), insert (Kreturn K__foo) f))
                    | None => None
                    end = Some(Some(Scall foo f), (Some(F, Ξ, E :: ξ, H, Δ), insert (Kreturn E__foo) f))) (mget Ξ foo)).
      now rewrite <- H0.
    + (* normal step *) assert (H':=H); eapply pstep_compat_weaken in H.
      apply (@grab_ectx e0 K e H) in H0 as H0';
      unfold estepf; rewrite H0'; rewrite equiv_pstep in H2;
      rewrite (get_rid_of_letstar Ω). rewrite (get_rid_of_letstar (K, e)).
      inv H'. rewrite (get_rid_of_letstar e);
      rewrite H2; rewrite (get_rid_of_letstar (a, (Some Ω', e')));
      destruct e; trivial; inv H4.
    + (* crash *) assert (H':=H); eapply pstep_compat_weaken in H.
      apply (@grab_ectx e0 K e H) in H0 as H0'.
      unfold estepf; rewrite H0'; rewrite equiv_pstep in H1;
      rewrite (get_rid_of_letstar Ω). rewrite (get_rid_of_letstar (K, e)).
      inv H'. rewrite (get_rid_of_letstar e);
      rewrite H1; destruct e; trivial; inv H3.
  - destruct r0 as [Ω e], r1 as [Ω' e'].
    intros H; unfold estepf in H.
    destruct Ω as [Ω|].
    destruct (option_dec (evalctx_of_expr e)) as [Hx0 | Hy0]; try rewrite Hy0 in H.
    2,3: inv H.
    rewrite (get_rid_of_letstar Ω) in H.
    apply not_eq_None_Some in Hx0 as [[K e0] Hx0].
    rewrite Hx0 in H.
    rewrite (get_rid_of_letstar (K, e0)) in H.
    destruct (option_dec (pstep_compatible e0)) as [Hx1 | Hy1]; try rewrite Hy1 in H.
    + apply not_eq_None_Some in Hx1 as [e0p Hx1].
      rewrite Hx1 in H.
      rewrite (get_rid_of_letstar e0p) in H.
      destruct (option_dec (pstepf (Some Ω, e0))) as [Hx|Hy].
      -- apply (not_eq_None_Some) in Hx as [[ap [oΩ' oe0']] Hx].
         rewrite Hx in H.
         rewrite (get_rid_of_letstar (ap, (oΩ', oe0'))) in H.
         destruct oΩ' as [oΩ'|].
         * apply pstep_compatible_some in Hx1 as Hx1'; subst.
           destruct (e0p); try inversion Hx1;
           assert (H':=H); inv H; eapply E_ctx; eauto using ungrab_ectx;
           apply equiv_pstep; try eapply Hx.
         * apply pstep_compatible_some in Hx1 as Hx1'; subst.
           destruct e0p; try inversion Hx1; inv H;
           eapply E_abrt_ctx; eauto using ungrab_ectx;
           apply equiv_pstep in Hx; inv Hx; try apply e_abort.
      -- rewrite Hy in H; inv H.
         destruct e0; try congruence; inv Hx1.
    + destruct e0; try congruence; inv Hy1; inv H.
      * (* ret *)
        grab_value e0.
        -- destruct Ω as [[[[F Ξ] [|K__foo ξ]] H] Δ]; try congruence.
           inv H1;
           eapply ungrab_ectx in Hx0; subst; eauto using E_return.
        -- destruct Ω as [[[[F Ξ] [|K__foo ξ]] H] Δ]; try congruence.
           inv H1;
           eapply ungrab_ectx in Hx0; subst; eauto using E_return.
      * (* call *)
        grab_value e0.
        -- destruct Ω as [[[[F Ξ] ξ] H] Δ].
           destruct (option_dec (mget Ξ foo)) as [Hx|Hy]; try (rewrite Hy in H1; congruence).
           apply (not_eq_None_Some) in Hx as [[E__foo τ__int] Hx].
           rewrite Hx in H1. inv H1.
           eapply ungrab_ectx in Hx0; try rewrite Hx0; eauto. eapply E_call; symmetry; eassumption.
        -- destruct Ω as [[[[F Ξ] ξ] H] Δ].
           destruct (option_dec (mget Ξ foo)) as [Hx|Hy]; try (rewrite Hy in H1; congruence).
           apply (not_eq_None_Some) in Hx as [[E__foo τ__int] Hx].
           rewrite Hx in H1. inv H1.
           eapply ungrab_ectx in Hx0; subst; eauto. eapply E_call; symmetry; eassumption.
Qed.

Module ModAux <: CSC.Langs.Util.MOD.
  Definition State := rtexpr.
  Definition Ev := event.
  Definition ev_eq := eventeq.
  Definition step := estep.
  Definition string_of_event := string_of_event.
  Definition is_value := fun (r : rtexpr) => match r with
                                          | (Some _, Xres(Fres _)) => true
                                          | (_, _) => false
                                          end.
End ModAux.
Module SMod := CSC.Langs.Util.Mod(ModAux).
Import SMod.

(** Functional style version of star step from above. We need another parameter "fuel" to sidestep termination. *)
Definition star_stepf (fuel : nat) (r : rtexpr) : option (tracepref * rtexpr) :=
  let fix doo (fuel : nat) (r : rtexpr) :=
    let (oΩ, e) := r in
    let* Ω := oΩ in
    match fuel, e with
    | 0, Xres(Fres _) => (* refl *)
      Some(Tnil, r)
    | S fuel', _ => (* trans *)
      let* (a, r') := estepf r in
      let* (As, r'') := doo fuel' r' in
      match a with
      | None => Some(As, r'')
      | Some(a') => Some(Tcons a' As, r'')
      end
    | _, _ => None
    end
  in doo fuel r
.

(** Finds the amount of fuel necessary to run an expression. *)
Fixpoint get_fuel (e : expr) : option nat :=
  match e with
  | Xres _ => Some(0)
  | Xbinop symb lhs rhs =>
    let* glhs := get_fuel lhs in
    let* grhs := get_fuel rhs in
    Some(1 + glhs + grhs)
  | Xget x e =>
    let* ge := get_fuel e in
    Some(1 + ge)
  | Xset x e0 e1 =>
    let* ge0 := get_fuel e0 in
    let* ge1 := get_fuel e1 in
    Some(1 + ge0 + ge1)
  | Xlet x e0 e1 =>
    let* ge0 := get_fuel e0 in
    let* ge1 := get_fuel e1 in
    Some(1 + ge0 + ge1)
  | Xnew x e0 e1 =>
    let* ge0 := get_fuel e0 in
    let* ge1 := get_fuel e1 in
    Some(1 + ge0 + ge1)
  | Xdel x => Some(1)
  | Xreturn e =>
    match e with
    | Xreturn e' => let* ge := get_fuel e' in Some(S ge)
    | _ =>
      let* ge := get_fuel e in
      Some(1 + ge)
    end
  | Xcall foo e =>
    let* ge := get_fuel e in
    Some(1 + ge)
  | Xifz c e0 e1 =>
    let* gc := get_fuel c in
    let* ge0 := get_fuel e0 in
    let* ge1 := get_fuel e1 in
    Some(1 + gc + ge0 + ge1)
  | Xabort => Some(1)
  end
.
Ltac crush_option :=
    match goal with
    | [H: Some _ = None |- _] => inv H
    | [H: _ <> None |- _] =>
      let n := fresh "n" in
      apply (not_eq_None_Some) in H as [n H]
    | [H: _ = None |- _] => trivial
    end.
Ltac crush_fuel := (match goal with
| [H: Some _ = Some _ |- _] => inv H
| [H: Some ?fuel = match (get_fuel ?e1) with Some _ => _ | None => None end |- _] =>
  let Hx := fresh "Hx" in
  let Hy := fresh "Hy" in
  let n := fresh "n" in
  destruct (option_dec (get_fuel e1)) as [Hx|Hy];
  crush_option; try rewrite Hx in *; try rewrite Hy in *
end).

Lemma atleast_once Ω e r a fuel :
  Some fuel = get_fuel e ->
  Ω ▷ e ==[, a ]==> r ->
  exists fuel', fuel = S fuel'.
Proof.
  revert fuel; induction e; cbn; intros fuel H; intros Ha.
  - crush_fuel; crush_estep.
  - repeat (crush_fuel + crush_option); now exists (n0 + n1).
  - crush_fuel; try crush_option; exists n0; now inv H.
  - repeat (crush_fuel + crush_option); now exists (n0 + n1).
  - repeat (crush_fuel + crush_option); now exists (n0 + n1).
  - repeat (crush_fuel + crush_option); now exists (n0 + n1).
  - crush_fuel; now exists 0.
  - destruct e; crush_fuel; try crush_option; exists n0; now inv H.
  - crush_fuel; try crush_option; exists n0; now inv H.
  - repeat (crush_fuel + crush_option); now exists (n0 + n1 + n2).
  - exists 0; now inv H.
Qed.
Lemma star_stepf_one_step Ω e r r' a As fuel :
  Some (S fuel) = get_fuel e ->
  estep (Ω ▷ e) (Some a) r ->
  star_stepf fuel r = Some(As, r') ->
  star_stepf (S fuel) (Ω ▷ e) = Some(Tcons a As, r')
.
Proof. Admitted.
Lemma star_stepf_one_unimportant_step Ω e r r' As fuel :
  Some (S fuel) = get_fuel e ->
  Ω ▷ e ==[]==> r ->
  star_stepf fuel r = Some(As, r') ->
  star_stepf (S fuel) (Ω ▷ e) = Some(As, r')
.
Proof. Admitted.
Lemma estep_good_fuel Ω e r a fuel :
  Some(S fuel) = get_fuel e ->
  Ω ▷ e ==[, a ]==> r ->
  Some fuel = get_fuel (let '(_, e') := r in e').
Proof. Admitted.
Lemma fuel_step oΩ e a oΩ' e' fuel :
  Some(S fuel) = get_fuel e ->
  (oΩ, e) ==[, a ]==> (oΩ', e') ->
  Some fuel = get_fuel e'.
Proof. Admitted.
Lemma equiv_starstep Ω e r1 As fuel :
  Some fuel = get_fuel e ->
  Ω ▷ e ==[ As ]==>* r1 <-> star_stepf fuel (Ω ▷ e) = Some(As, r1).
Proof.
  intros Hf; split; intros H.
  - destruct r1 as [oΩ' e'].
    change (Some fuel = get_fuel match (Ω ▷ e) with
                          | (_, e') => e'
                          end) in Hf.
    revert fuel Hf; induction H; intros fuel Hf; cbn in Hf.
    + destruct r1 as [[Ω0|] e0]; cbn in *; try congruence.
      destruct e0; cbn in H; try congruence; destruct f; try congruence.
      inv Hf; now cbn.
    + clear Ω e oΩ' e'; destruct r1 as [[oΩ1|] e1].
      * assert (H':=H); apply (@atleast_once oΩ1 e1 r2 (Some a) fuel Hf) in H as [fuel' ->];
        eapply star_stepf_one_step; eauto;
        eapply IHstar_step; eapply estep_good_fuel; eauto.
      * inv H.
    + clear Ω e oΩ' e'; destruct r1 as [[oΩ1|] e1].
      * assert (H':=H); apply (@atleast_once oΩ1 e1 r2 None fuel Hf) in H as [fuel' ->].
        eapply star_stepf_one_unimportant_step; eauto;
        eapply IHstar_step; eapply estep_good_fuel; eauto.
      * inv H.
  - revert Ω e r1 As Hf H; induction fuel; intros Ω e r1 As Hf H.
    + destruct e; cbn in Hf; repeat destruct (get_fuel _); try congruence;
      cbn in H; inv H; destruct f; try congruence; inv H1; now apply ES_refl.
    + unfold star_stepf in H.
      rewrite (get_rid_of_letstar Ω) in H.
      destruct (option_dec (estepf (Some Ω, e))) as [Hx|Hy]; try rewrite Hy in H.
      2: inv H.
      apply not_eq_None_Some in Hx as [[a [Ω' e']] Hx].
      rewrite Hx in H.
      rewrite (get_rid_of_letstar (a, (Ω', e'))) in H.
      destruct (option_dec ((
fix doo (fuel : nat) (r : rtexpr) {struct fuel} : option (tracepref * rtexpr) :=
            let (oΩ, e) := r in
            let* _ := oΩ
            in match fuel with
               | 0 => match e with
                      | Xres(Fres _) => Some (Tnil, r)
                      | _ => None
                      end
               | S fuel' =>
                   let* (a, r') := estepf r
                   in let* (As, r'') := doo fuel' r'
                      in match a with
                         | Some a' => Some (Tcons a' As, r'')
                         | None => Some (As, r'')
                         end
               end
                ) fuel (Ω', e'))) as [Hx0|Hy0]; try rewrite Hy0 in H.
      2: inv H.
      apply not_eq_None_Some in Hx0 as [[As0 r1'] Hx0]; rewrite Hx0 in H.
      rewrite (get_rid_of_letstar (As0, r1')) in H.
      rewrite <- equiv_estep in Hx;
      destruct a as [a|]; inv H.
      * eapply ES_trans_important; eauto.
        destruct Ω' as [Ω'|].
        2: destruct fuel; inv Hx0.
        apply (fuel_step Hf) in Hx.
        eapply IHfuel; eauto.
      * eapply ES_trans_unimportant; eauto.
        destruct Ω' as [Ω'|].
        2: destruct fuel; inv Hx0.
        apply (fuel_step Hf) in Hx.
        eapply IHfuel; eauto.
Qed.

(** Evaluation of programs *)
(*TODO: add typing*)
Inductive wstep : prog -> tracepref -> rtexpr -> Prop :=
| e_wprog : forall (symbs : symbols) (As : tracepref) (r : rtexpr),
    (* typing -> *)
    (Fresh.empty_fresh ; symbs ; nil ; hNil ; sNil ▷ Xcall "main"%string 0 ==[ As ]==>* r) ->
    wstep (Cprog symbs) As r
.

Fixpoint get_fuel_fn_aux (E : evalctx) {struct E} : option nat :=
  match E with
  | Khole => Some 0
  | KbinopL b K e =>
    let* gK := get_fuel_fn_aux K in
    let* ge := get_fuel e in
    Some(ge + gK + 1)
  | KbinopR b v K =>
    let* gK := get_fuel_fn_aux K in
    Some(gK + 1)
  | Kget x K =>
    let* gK := get_fuel_fn_aux K in
    Some(gK + 1)
  | KsetL x K e =>
    let* gK := get_fuel_fn_aux K in
    let* ge := get_fuel e in
    Some(ge + gK + 1)
  | KsetR x v K =>
    let* gK := get_fuel_fn_aux K in
    Some(gK + 1)
  | Klet x K e =>
    let* gK := get_fuel_fn_aux K in
    let* ge := get_fuel e in
    Some(ge + gK + 1)
  | Knew x K e =>
    let* gK := get_fuel_fn_aux K in
    let* ge := get_fuel e in
    Some(ge + gK + 1)
  | Kifz K e0 e1 =>
    let* gK := get_fuel_fn_aux K in
    let* ge0 := get_fuel e0 in
    let* ge1 := get_fuel e1 in
    Some(ge0 + ge1 + gK + 1)
  | Kreturn K =>
    let* gK := get_fuel_fn_aux K in
    Some(gK + 1)
  | Kcall foo K =>
    let* gK := get_fuel_fn_aux K in
    Some(gK + 1)
  end
.
Fixpoint collect_callsites (ξ : symbols) (e : expr) : option symbols :=
  match e with
  | Xbinop _ e0 e1 =>
    let* r0 := collect_callsites ξ e0 in
    let* r1 := collect_callsites ξ e1 in
    Some(r0 ◘ r1)
  | Xget _ e => collect_callsites ξ e
  | Xset _ e0 e1 =>
    let* r0 := collect_callsites ξ e0 in
    let* r1 := collect_callsites ξ e1 in
    Some(r0 ◘ r1)
  | Xlet _ e0 e1 =>
    let* r0 := collect_callsites ξ e0 in
    let* r1 := collect_callsites ξ e1 in
    Some(r0 ◘ r1)
  | Xnew _ e0 e1 =>
    let* r0 := collect_callsites ξ e0 in
    let* r1 := collect_callsites ξ e1 in
    Some(r0 ◘ r1)
  | Xreturn e' => collect_callsites ξ e'
  | Xcall foo e' =>
    let* res := collect_callsites ξ e' in
    let* K := mget ξ foo in
    Some(foo ↦ K ◘ res)
  | Xifz c e0 e1 =>
    let* cr := collect_callsites ξ c in
    let* r0 := collect_callsites ξ e0 in
    let* r1 := collect_callsites ξ e1 in
    Some(cr ◘ r0 ◘ r1)
  | _ => Some(nosymb)
  end
.
(** Compute the total amount of fuel necessary to run a complete program. Each context corresponding to a call
    artificially gets a return in the semantics (estep), so add 1.
    Also, add 1 to the final result, because the top-level performs a call to "main". *)
Definition get_fuel_toplevel (ξ : symbols) (foo : vart) : option nat :=
  let* Kτ := mget ξ foo in
  let '(K,_) := Kτ in
  let e := insert K 0 in
  let* ge := get_fuel e in
  let* symbs := collect_callsites ξ e in
  let* res := List.fold_left (fun acc Eτ =>
                                let '(E,_) := Eτ in
                                let* a := acc in
                                let* b := get_fuel_fn_aux E in
                                Some(1 + a + b)) (img symbs) (Some ge) in
  Some(S res)
.

Definition wstepf (p : prog) : option (tracepref * rtexpr) :=
  let '(Cprog symbs) := p in
  let e := Xcall "main"%string 0 in
  let* fuel := get_fuel_toplevel symbs "main"%string in
  let R := Fresh.empty_fresh ; symbs ; nil ; hNil ; sNil ▷ e in
  star_stepf fuel R
.
Definition debug_eval (p : prog) :=
  let* (As, _) := wstepf p in
  Some(string_of_tracepref As)
.

(* let x = [] in
     let z = new x in
     let w = z[1337] in
     let _ = delete z in
     w*)
Definition smsunsafe_ep : evalctx :=
  Klet "x"%string
    Khole
    (Xnew "z"%string
        (Fvar "x"%string)
        (Xlet "w"%string
              (Xget "z"%string 1337)
              (Xlet "_"%string
                    (Xdel "z"%string)
                    (Fvar "w"%string))
        ))
.
(* let x = 3 in call foo x *)
Definition smsunsafe_ctx : evalctx :=
  Kreturn (Klet ("_"%string)
    Khole
    (Xlet ("x"%string)
          3
          (Xcall ("foo"%string) (Fvar "x"%string))))
.

Definition smsunsafe_prog_aux : symbols :=
  ("foo"%string ↦ (smsunsafe_ep, Tectx(Tarrow Tℕ Tℕ)) ◘ ("main"%string ↦ (smsunsafe_ctx, Tectx(Tarrow Tℕ Tℕ)) ◘ nosymb)).
Definition smsunsafe_prog := Cprog smsunsafe_prog_aux.

Tactic Notation "splitΓfor" :=
try do 2 match goal with
| [|- _ ⊦ _ : _] => unfold "_ ⊦ _ : _"
| [|- check ?P (Xdel ?x) ?τ] =>
  match P with
  | context E__Γ [(x ↦ ?H ◘ ?R)] =>
    let nP := constr:([⋅] ◘ (x ↦ H ◘ R)) in
    let NP := constr:(ltac:(let t := context E__Γ [[⋅]] in exact t)) in
    let nnP := constr:(NP ◘ nP) in
    let G := constr:(check nnP (Xdel x) τ) in
    change G
  end
| [|- check ?P (Xres(Fres(Fvar ?x))) ?τ] =>
  match P with
  | context E__Γ [(x ↦ ?H ◘ ?R)] =>
    let nP := constr:([⋅] ◘ (x ↦ H ◘ R)) in
    let NP := constr:(ltac:(let t := context E__Γ [[⋅]] in exact t)) in
    let nnP := constr:(NP ◘ nP) in
    let G := constr:(check nnP (Xres(Fres(Fvar x))) τ) in
    change G
  end
end.

Lemma ownedptrsplit Γ1 Γ2 : NoOwnedPtr Γ1 -> NoOwnedPtr Γ2 -> NoOwnedPtr (Γ1 ◘ Γ2).
Proof.
Admitted.
Lemma ownedptrcons x y Γ2 : NoOwnedPtr (x ↦ y ◘ [⋅]) -> NoOwnedPtr Γ2 -> NoOwnedPtr (x ↦ y ◘ Γ2).
Proof.
Admitted.

Goal prog_check smsunsafe_prog.
Proof.
  assert (NoOwnedPtr ("foo"%string ↦ (Tectx(Tarrow Tℕ Tℕ)) ◘ ("main"%string ↦ (Tectx(Tarrow Tℕ Tℕ)) ◘ [⋅]))) as G.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0;
    destruct a; inv H1; destruct b, b0, b1, b2, b3, b4, b5, b6; inv H0;
    destruct x; inv H1; destruct a; inv H0; destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1;
    destruct x; inv H0; destruct a; inv H1; destruct b, b0, b1, b2, b3, b4, b5, b6; inv H0.
    destruct x; inv H1.
  cbn; repeat split; trivial.
  - eapply ETlet. repeat (eapply ArrowSplit; try eapply intℕ); eapply splitEmpty. eapply EThole.
    eapply intℕ. exact G.
    eapply CTnew. eapply ℕsplit, ArrowSplit, ArrowSplit, splitEmpty; try eapply intℕ.
    splitΓfor.
    eapply CTvar. easy. unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; inv H0. easy.
    exact G.
    eapply CTlet. eapply ptrRSplit, ℕsplit, ArrowSplit, ArrowSplit, splitEmpty; try eapply intℕ.
    eapply CTget. eapply weakPtrSplit, ℕsplit, ArrowSplit, ArrowSplit, splitEmpty; try eapply intℕ.
    splitΓfor.
    eapply CTvar. easy. unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; inv H0. easy.
    eapply ownedptrcons; trivial.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; inv H0. easy.
    eapply CTℕ. do 2 eapply ownedptrcons; try easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    eapply CTlet. eapply ℕsplit, ptrLSplit, ℕsplit, ArrowSplit, ArrowSplit, splitEmpty; eapply intℕ.
    instantiate (1:=Tℕ).
    splitΓfor.
    eapply CTdel.
    splitΓfor.
    eapply CTvar.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    eapply ownedptrcons; try easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
  - eapply ETret. eapply intℕ. eapply ETlet. eapply ArrowSplit, ArrowSplit, splitEmpty; eapply intℕ.
    eapply EThole. eapply intℕ. assumption.
    eapply CTlet. eapply ℕsplit, ArrowSplit, ArrowSplit, splitEmpty; eapply intℕ. eapply CTℕ.
    eapply ownedptrcons; try easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    eapply CTcall. eapply intℕ. eapply intℕ.
    splitΓfor. eapply CTvar; try easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a; destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; inv H0.
    destruct a; destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    splitΓfor.
    eapply CTvar. easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    eapply ownedptrcons; try easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
Qed.

Goal exists As R,
    wstep smsunsafe_prog As R.
Proof.
  do 2 eexists.
  econstructor.
  econstructor 2. rewrite equiv_estep; now cbn.
  econstructor 3. rewrite equiv_estep; now cbn.
  econstructor 3. rewrite equiv_estep; now cbn.
  econstructor 2. rewrite equiv_estep; now cbn.
  econstructor 3. rewrite equiv_estep; now cbn.
  econstructor 2. rewrite equiv_estep; now cbn.
  econstructor 2. rewrite equiv_estep; now cbn.
  econstructor 3. rewrite equiv_estep; now cbn.
  econstructor 2. rewrite equiv_estep; now cbn.
  econstructor 3. rewrite equiv_estep; now cbn.
  econstructor 2. rewrite equiv_estep; now cbn.
  econstructor 2. rewrite equiv_estep; now cbn.
  now econstructor.
Qed.

Compute (let '(Cprog symbs) := smsunsafe_prog in get_fuel_toplevel symbs "main"%string).

Compute (debug_eval smsunsafe_prog).


Variant msevent : Type :=
| MSalloc (ℓ : loc) (n : nat) : msevent
| MSdealloc (ℓ : loc) : msevent
| MSuse (ℓ : loc) (n : nat) : msevent
| MScrash : msevent
.
#[local]
Instance msevent__Instance : TraceEvent msevent := {}.
Definition mseventeq (e1 e2 : msevent) : bool :=
  match e1, e2 with
  | MSalloc(addr ℓ0) n0, MSalloc(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | MSdealloc(addr ℓ0), MSdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | MSuse(addr ℓ0) n0, MSuse(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | MScrash, MScrash => true
  | _, _ => false
  end
.
(** Pretty-printing function for better debuggability *)
Definition string_of_msevent (e : msevent) :=
  match e with
  | (MSalloc (addr ℓ) n) => String.append
                      (String.append ("MsAlloc ℓ"%string) (string_of_nat ℓ))
                      (String.append (" "%string) (string_of_nat n))
  | (MSdealloc (addr ℓ)) => String.append ("MsDealloc ℓ"%string) (string_of_nat ℓ)
  | (MSuse (addr ℓ) n) => String.append
                    (String.append ("MsUse ℓ"%string) (string_of_nat ℓ))
                    (String.append (" "%string) (string_of_nat n))
  | (MScrash) => "↯"%string
  end
.

Module MSModAux <: CSC.Langs.Util.MOD.
  Definition State := True.
  Definition Ev := msevent.
  Definition ev_eq := mseventeq.
  Definition step := fun (_ : State) (o : option msevent) (_ : State) => True.
  Definition string_of_event := string_of_msevent.
  Definition is_value := fun (r : State) => true.
End MSModAux.
Module SMSMod := CSC.Langs.Util.Mod(MSModAux).

Definition msev_of_ev (ev : event) : option msevent :=
  match ev with
  | Salloc ℓ n => Some(MSalloc ℓ n)
  | Sdealloc ℓ => Some(MSdealloc ℓ)
  | Sget ℓ n => Some(MSuse ℓ n)
  | Sset ℓ n _ => Some(MSuse ℓ n)
  | Scrash => Some(MScrash)
  | Scall _ _ => None
  | Sret _ => None
  end
.
Fixpoint mstracepref_of_tracepref (tr : tracepref) : SMSMod.tracepref :=
  match tr with
  | Tnil => SMSMod.Tnil
  | Tcons a tr' =>
    match msev_of_ev a with
    | Some a' => SMSMod.Tcons a' (mstracepref_of_tracepref tr')
    | None => mstracepref_of_tracepref tr'
    end
  end
.

Require CSC.Langs.TMMon.
Module TMMon := CSC.Langs.TMMon.
Module TMMonM := TMMon.TMSMod.

#[local]
Instance loceq__Instance : HasEquality loc := loc_eqb.
Definition deltamap := mapind loceq__Instance TMMon.loc.

(** Trace agreement between memory specific events and TMS monitor events. *)
Inductive ev_eq (δ : deltamap) : msevent -> TMMon.event -> Prop :=
| TMSAuthAlloc : forall ℓ ℓ' n, mget δ ℓ = Some ℓ' -> ev_eq δ (MSalloc ℓ n) (TMMon.Salloc ℓ')
| TMSAuthDealloc : forall ℓ ℓ', mget δ ℓ = Some ℓ' -> ev_eq δ (MSdealloc ℓ) (TMMon.Sdealloc ℓ')
| TMSAuthUse : forall ℓ ℓ' n, mget δ ℓ = Some ℓ' -> ev_eq δ (MSuse ℓ n) (TMMon.Suse ℓ')
.
Inductive mstracepref_eq (δ : deltamap) : SMSMod.tracepref -> TMMonM.tracepref -> Prop :=
| TMSAuthRefl : mstracepref_eq δ SMSMod.Tnil TMMonM.Tnil
| TMSAuthTrans : forall a a' As As', ev_eq δ a a' ->
                                mstracepref_eq δ As As' ->
                                mstracepref_eq δ (SMSMod.Tcons a As) (TMMonM.Tcons a' As')
.

Import TMMon.TMMonNotation.
(** Store agreement between our stores and the TMS monitor. *)
Inductive store_agree (δ : deltamap) : TMMon.TMSMonitor -> store -> Prop :=
| EmptyAgree : store_agree δ TMMon.emptytmsmon sNil
| ConsAgree : forall (x : vart) (ℓ : loc) (ℓ' : TMMon.loc) (T__TMS : TMMon.TMSMonitor) (Δ : store),
    mget δ ℓ = Some ℓ' ->
    ~(List.In ℓ' (TMMon.F T__TMS)) ->
    store_agree δ T__TMS Δ ->
    store_agree δ ({ℓ'} ∪ T__TMS) (x ↦ (ℓ ⋅ ◻) ◘ Δ)
| PoisonAgree : forall (x : vart) (ℓ : loc) (ℓ' : TMMon.loc) (T__TMS : TMMon.TMSMonitor) (Δ : store),
    mget δ ℓ = Some ℓ' ->
    store_agree δ T__TMS Δ ->
    store_agree δ ({ℓ'} ∪ T__TMS) (x ↦ (ℓ ⋅ ☣) ◘ Δ)
.
