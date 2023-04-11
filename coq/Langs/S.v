Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef.
Require Import CSC.Sets CSC.Util CSC.Fresh CSC.Langs.Util.
Require CSC.Langs.TMMon.

(** * Syntax *)

(** The type used for variable names. *)
Definition vart := string.
Definition vareq := fun x y => (x =? y)%string.
Definition dontcare := "_"%string.

#[local]
Instance varteq__Instance : HasEquality vart := {
  eq := vareq ;
  eq_refl := String.eqb_refl ;
  eqb_eq := String.eqb_eq ;
  neqb_neq := String.eqb_neq
}.

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
Lemma loc_eqb_refl ℓ :
  loc_eqb ℓ ℓ = true.
Proof. destruct ℓ as [n]; induction n; now cbn. Qed.
Lemma loc_eqb_eq ℓ0 ℓ1 :
  loc_eqb ℓ0 ℓ1 = true <-> ℓ0 = ℓ1.
Proof.
  destruct ℓ0 as [n0], ℓ1 as [n1]; split; intros H.
  - cbn in H; rewrite Nat.eqb_eq in H; now subst.
  - inv H; apply loc_eqb_refl.
Qed.
Lemma loc_eqb_neq ℓ0 ℓ1 :
  loc_eqb ℓ0 ℓ1 = false <-> ℓ0 <> ℓ1.
Proof.
  destruct ℓ0 as [n0], ℓ1 as [n1]; split; intros H.
  - cbn in H; rewrite Nat.eqb_neq in H; congruence.
  - destruct (Nat.eq_dec n0 n1).
    + subst; congruence.
    + now rewrite <- Nat.eqb_neq in n.
Qed.
#[local]
Instance loceq__Instance : HasEquality loc := {
  eq := loc_eqb ;
  eq_refl := loc_eqb_refl ;
  eqb_eq := loc_eqb_eq ;
  neqb_neq := loc_eqb_neq
}.
#[local]
Existing Instance varteq__Instance.
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
Definition qual_eqb (q1 q2 : qual) : bool :=
  match q1, q2 with
  | Qfull, Qfull | Qhalf, Qhalf => true
  | _, _ => false
  end
.
Lemma qual_eqb_refl q :
  qual_eqb q q = true.
Proof. destruct q; now cbn. Qed.
Lemma qual_eqb_eq q0 q1 :
  qual_eqb q0 q1 = true <-> q0 = q1.
Proof. destruct q0, q1; split; intros H; easy. Qed.
Lemma qual_eqb_neq q0 q1 :
  qual_eqb q0 q1 = false <-> q0 <> q1.
Proof. destruct q0, q1; split; intros H; easy. Qed.
#[local]
Instance qualeq__Instance : HasEquality qual := {
  eq := qual_eqb ;
  eq_refl := qual_eqb_refl ;
  eqb_eq := qual_eqb_eq ;
  neqb_neq := qual_eqb_neq
}.
#[local]
Existing Instance varteq__Instance.
(** Types of S *)
Inductive ty : Type :=
| Tnat : ty
| Tnatptr : qual -> ty
.
Notation "'Tℕ'" := (Tnat).
Notation "'Tptr'" := (Tnatptr Qfull).
Notation "'Twptr'" := (Tnatptr Qhalf).
Definition ty_eqb (t1 t2 : ty) : bool :=
  match t1, t2 with
  | Tnat, Tnat => true
  | Tnatptr q1, Tnatptr q2 => eq q1 q2
  | _, _ => false
  end
.
Lemma ty_eqb_refl t :
  ty_eqb t t = true.
Proof. destruct t; cbn; trivial; apply qual_eqb_refl. Qed.
Lemma ty_eqb_eq t0 t1 :
  ty_eqb t0 t1 = true <-> t0 = t1.
Proof.
  destruct t0, t1; split; intros H; trivial; destruct q; cbn in *; try easy.
  all: destruct q0; easy.
Qed.
Lemma ty_eqb_neq t0 t1 :
  ty_eqb t0 t1 = false <-> t0 <> t1.
Proof.
  destruct t0, t1; split; intros h; try easy; destruct q, q0; cbn in *; try easy.
Qed.
#[local]
Instance tyeq__Instance : HasEquality ty := {
  eq := ty_eqb ;
  eq_refl := ty_eqb_refl ;
  eqb_eq := ty_eqb_eq ;
  neqb_neq := ty_eqb_neq
}.
#[local]
Existing Instance varteq__Instance.

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
#[global]
Instance expr__Instance : ExprClass expr := {}.

(** Checks wether a given expression contains a delete of the given var *)
Fixpoint find_del (x : vart) (e : expr) : option True :=
  match e with
  | Xdel y => if eq x y then Some I else None
  | Xreturn e' => find_del x e'
  | Xcall _ e' => find_del x e'
  | Xget _ e' => find_del x e'
  | Xset _ e1 e2 =>
    match find_del x e1, find_del x e2 with
    | Some _, Some _ => None (* won't typecheck *)
    | Some _, None => Some I
    | None, Some _ => Some I
    | None, None => None (* won't typecheck *)
    end
  | Xbinop _ e1 e2 =>
    match find_del x e1, find_del x e2 with
    | Some _, Some _ => None (* won't typecheck *)
    | Some _, None => Some I
    | None, Some _ => Some I
    | None, None => None (* won't typecheck *)
    end
  | Xlet y e1 e2 =>
    if eq x y then
      find_del x e1
    else
      match find_del x e1, find_del x e2 with
      | Some _, Some _ => None (* won't typecheck *)
      | Some _, None => Some I
      | None, Some _ => Some I
      | None, None => None (* won't typecheck *)
      end
  | Xnew y e1 e2 =>
    if eq x y then
      find_del x e1
    else
      match find_del x e1, find_del x e2 with
      | Some _, Some _ => None (* won't typecheck *)
      | Some _, None => Some I
      | None, Some _ => Some I
      | None, None => None (* won't typecheck *)
      end
  | Xifz c e1 e2 =>
    match find_del x c, find_del x e1, find_del x e2 with
    | Some _, Some _, Some _ | Some _, Some _, None | Some _, None, Some _ | None, Some _, Some _ => None (* won't typecheck *)
    | Some _, None, None | None, Some _, None | None, None, Some _ => Some I
    | None, None, None => None (* won't typeheck*)
    end
  | _ => None
  end
.

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
#[global]
Instance evalctx__Instance : EvalCtxClass evalctx := {}.
Inductive ety : Type :=
| Tarrow : ty -> ty -> ety
.

(** * Statics *)
Inductive Ty : Type :=
| Texpr : ty -> Ty
| Tectx : ety -> Ty
| Treturn : ty -> Ty (* τ → ⊥ *)
.
#[local]
Instance TheTy__Instance : TyClass Ty := {}.
Coercion Texpr : ty >-> Ty.
Coercion Tectx : ety >-> Ty.
Definition Ty_eqb (t1 t2 : Ty) : bool :=
  match t1, t2 with
  | Treturn t1', Treturn t2' => eq t1' t2'
  | Tectx(Tarrow ta tb), Tectx(Tarrow ta' tb') => andb (eq ta ta') (eq tb tb')
  | Texpr ta, Texpr tb => eq ta tb
  | _, _ => false
  end
.
Lemma Ty_eqb_refl t :
  Ty_eqb t t = true.
Proof.
  destruct t; cbn; trivial; try apply ty_eqb_refl; destruct e; now repeat rewrite ty_eqb_refl.
Qed.
Lemma Ty_eqb_eq t0 t1 :
  Ty_eqb t0 t1 = true <-> t0 = t1.
Proof.
  destruct t0, t1; split; intros H; try easy.
  cbn in H; apply ty_eqb_eq in H; subst; easy.
  rewrite H; apply Ty_eqb_refl; easy.
  cbn in H. destruct e; congruence.
  destruct e, e0; cbn in H. remember (ty_eqb t t1) as b0; remember (ty_eqb t0 t2) as b1.
  symmetry in Heqb0, Heqb1. destruct b0, b1; cbn in H; try congruence; clear H.
  now apply ty_eqb_eq in Heqb0, Heqb1; subst.
  rewrite H. now apply Ty_eqb_refl.
  destruct e; now cbn in H.
  cbn in H. apply ty_eqb_eq in H; rewrite H; easy.
  inv H. apply Ty_eqb_refl.
Qed.
Lemma Ty_eqb_neq t0 t1 :
  Ty_eqb t0 t1 = false <-> t0 <> t1.
Proof.
  split; intros H.
  - intros H1; subst. now rewrite Ty_eqb_refl in H.
  - destruct t0, t1; cbn; try easy;
    try (apply ty_eqb_neq; congruence);
    try (destruct e; try congruence).
    destruct e0. remember (ty_eqb t t1) as b0; remember (ty_eqb t0 t2) as b1.
    symmetry in Heqb0, Heqb1; destruct b0, b1; try now cbn.
    apply ty_eqb_eq in Heqb0, Heqb1; subst. contradiction.
Qed.
#[local]
Instance Tyeq__Instance : HasEquality Ty := {
  eq := Ty_eqb ;
  eq_refl := Ty_eqb_refl ;
  eqb_eq := Ty_eqb_eq ;
  neqb_neq := Ty_eqb_neq
}.
#[local]
Existing Instance varteq__Instance.

(** Interface types *)
Inductive int : ty -> Prop :=
| intℕ : int Tℕ
| intwptr : int Twptr
.
Definition intf (τ : ty) : option ty :=
  match τ with
  | Tℕ => Some Tℕ
  | Twptr => Some Twptr
  | _ => None
  end
.
Lemma intf_refl τ τ' :
  intf τ = Some τ' -> τ = τ'.
Proof. induction τ; cbn; intros; inv H; try easy. destruct q; try easy. now inv H1. Qed.
Lemma int_equiv_intf τ :
  int τ <-> intf τ = Some τ
.
Proof.
  induction τ; cbn.
  - split; try easy; constructor.
  - destruct q; split; intros H; inv H; try easy; constructor.
Qed.
Ltac crush_intf τ :=
  let Hx' := fresh "Hx'" in
  let Hx := fresh "Hx" in
  let x := fresh "x" in
  destruct (option_dec (intf τ)) as [Hx | Hx];
  try (rewrite Hx in *; congruence);
  try (apply not_eq_None_Some in Hx as [x Hx]; eapply intf_refl in Hx as Hx'; rewrite <- Hx' in Hx; clear Hx'; rewrite Hx in *)
.
Lemma int_equiv_intf_none τ :
  (~ int τ) <-> intf τ = None
.
Proof.
  split; intros H.
  - crush_intf τ; apply int_equiv_intf in Hx; contradiction.
  - intros H0%int_equiv_intf; congruence.
Qed.

(** marker for which gamma the owned pointer should be moved to *)
Variant Pos : Type :=
| PosL : Pos
| PosR : Pos
.
(** returns Pos by looking which expression uses a given var in a delete *)
Definition determine_pos (x : vart) (e : expr) : Pos :=
  match find_del x e with
  | Some _ => PosL
  | None => PosR
  end
.
(** Context splitting *)
Reserved Notation "Γ '≡' Γ1 '∘' Γ2 '⊣' e" (at level 81, Γ1 at next level, Γ2 at next level, e at next level).
Inductive splitting : Gamma -> Gamma -> Gamma -> expr -> Prop :=
| splitEmpty : forall (e : expr), [⋅] ≡ [⋅] ∘ [⋅] ⊣ e
| ℕsplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma) (e : expr),
    Γ ≡ Γ1 ∘ Γ2 ⊣ e ->
    x ↦ (Texpr Tℕ) ◘ Γ ≡ x ↦ (Texpr Tℕ) ◘ Γ1 ∘ (x ↦ (Texpr Tℕ) ◘ Γ2) ⊣ e
| weakPtrSplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma) (e : expr),
    Γ ≡ Γ1 ∘ Γ2 ⊣ e ->
    x ↦ (Texpr Twptr) ◘ Γ ≡ x ↦ (Texpr Twptr) ◘ Γ1 ∘ (x ↦ (Texpr Twptr) ◘ Γ2) ⊣ e
| ptrLSplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma) (e : expr),
    determine_pos x e = PosL ->
    Γ ≡ Γ1 ∘ Γ2 ⊣ e ->
    x ↦ (Texpr Tptr) ◘ Γ ≡ x ↦ (Texpr Tptr) ◘ Γ1 ∘ Γ2 ⊣ e
| ptrRSplit : forall (x : vart) (Γ Γ1 Γ2 : Gamma) (e : expr),
    determine_pos x e = PosR ->
    Γ ≡ Γ1 ∘ Γ2 ⊣ e ->
    x ↦ (Texpr Tptr) ◘ Γ ≡ x ↦ (Texpr Twptr) ◘ Γ1 ∘ (x ↦ (Texpr Tptr) ◘ Γ2) ⊣ e
| ArrowSplit : forall (x : vart) (τ0 τ1 : ty) (Γ Γ1 Γ2 : Gamma) (e : expr),
    int τ0 -> int τ1 ->
    Γ ≡ Γ1 ∘ Γ2 ⊣ e ->
    x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ ≡ x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ1 ∘ (x ↦ (Tectx(Tarrow τ0 τ1)) ◘ Γ2) ⊣ e
where "Γ '≡' Γ1 '∘' Γ2 '⊣' e" := (splitting Γ Γ1 Γ2 e)
.

(** Typechecking *)
Fixpoint NoOwnedPtr (Γ : Gamma) :=
  match Γ with
  | mapNil _ _ => True
  | mapCons x τ Γ' => τ <> Tptr /\ NoOwnedPtr Γ'
  end
.
Lemma noownedptr_cons Γ x τ :
  NoOwnedPtr (x ↦ τ ◘ Γ) ->
  NoOwnedPtr (x ↦ τ ◘ (mapNil _ _)) /\ NoOwnedPtr Γ
.
Proof. intros H; inv H; now repeat split. Qed.
Lemma noownedptr_split Γ1 Γ2 :
  NoOwnedPtr (Γ1 ◘ Γ2) <->
  NoOwnedPtr Γ1 /\ NoOwnedPtr Γ2
.
Proof.
  induction Γ1; cbn; split; intros H; try easy; fold (append Γ1 Γ2) in *.
  - destruct H as [Ha Hb]. apply IHΓ1 in Hb as [Hb1 Hb2]; repeat split; auto.
  - destruct H as [[Ha Hb] Hc]; split; trivial; apply IHΓ1; auto.
Qed.

Inductive check : VDash :=
| CTvar : forall (x : vart) (Γ1 Γ2 : Gamma) (τ : Ty),
    nodupinv (Γ1 ◘ x ↦ τ ◘ Γ2) ->
    NoOwnedPtr Γ1 ->
    NoOwnedPtr (x ↦ τ ◘ [⋅]) ->
    NoOwnedPtr Γ2 ->
    (Γ1 ◘ x ↦ τ ◘ Γ2) ⊦ Xres(Fvar x) : τ
| CTℕ : forall (Γ : Gamma) (n : nat),
    NoOwnedPtr Γ ->
    Γ ⊦ Xres n : Tℕ
| CToplus : forall (Γ1 Γ2 Γ3 : Gamma) (e1 e2 : expr) (b : binopsymb),
    Γ3 ≡ Γ1 ∘ Γ2 ⊣ e1 ->
    (Γ1 ⊦ e1 : (Texpr Tℕ)) ->
    (Γ2 ⊦ e2 : (Texpr Tℕ)) ->
    (Γ3 ⊦ Xbinop b e1 e2 : (Texpr Tℕ))
| CTget : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (e : expr),
    Γ3 ≡ Γ1 ∘ Γ2 ⊣ (Fvar x) ->
    (Γ2 ⊦ Xres(Fvar x) : (Texpr Twptr)) ->
    (Γ1 ⊦ e : (Texpr Tℕ)) ->
    (Γ3 ⊦ Xget x e : (Texpr Tℕ))
| CTset : forall (Γ1 Γ2 Γ3 Γ12 Γ4 : Gamma) (x : vart) (e1 e2 : expr),
    Γ12 ≡ Γ1 ∘ Γ2 ⊣ e1 ->
    Γ4 ≡ Γ12 ∘ Γ3 ⊣ (Xbinop Badd e1 e2) ->
    (Γ3 ⊦ (Xres(Fvar x)) : (Texpr Twptr)) ->
    (Γ1 ⊦ e1 : (Texpr Tℕ)) ->
    (Γ2 ⊦ e2 : (Texpr Tℕ)) ->
    (Γ4 ⊦ Xset x e1 e2 : (Texpr Tℕ))
| CTlet : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (e1 e2 : expr) (τ1 τ2 : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ⊣ e1 ->
    (Γ1 ⊦ e1 : (Texpr τ1)) ->
    (x ↦ (Texpr τ1) ◘ Γ2 ⊦ e2 : (Texpr τ2)) ->
    (Γ3 ⊦ Xlet x e1 e2 : (Texpr τ2))
| CTnew : forall (Γ1 Γ2 Γ3 : Gamma) (x : vart) (e1 e2 : expr) (τ : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ⊣ e1 ->
    (Γ1 ⊦ e1 : (Texpr Tℕ)) ->
    (x ↦ (Texpr Tptr) ◘ Γ2 ⊦ e2 : (Texpr τ)) ->
    (Γ3 ⊦ Xnew x e1 e2 : (Texpr τ))
| CTdel : forall (Γ1 Γ2 : Gamma) (x : vart),
    nodupinv (Γ1 ◘ x ↦ (Texpr Tptr) ◘ Γ2) ->
    (Γ1 ◘ x ↦ (Texpr Tptr) ◘ Γ2 ⊦ Xdel x : (Texpr Tℕ))
| CTcall : forall (Γ : Gamma) (foo : vart) (arg : expr) (τ0 τ1 : ty),
    int τ0 -> int τ1 ->
    (Γ ⊦ Xres(Fvar foo) : (Tectx(Tarrow τ0 τ1))) ->
    (Γ ⊦ arg : (Texpr τ0)) ->
    (Γ ⊦ Xcall foo arg : (Texpr τ1))
| CTret : forall (Γ : Gamma) (e : expr) (τ : ty), (*TODO: intuitively, this should yield ⊥...?*)
    int τ ->
    (Γ ⊦ e : (Texpr τ)) ->
    (Γ ⊦ Xreturn e : (Treturn τ))
| CTifz : forall (Γ1 Γ2 Γ3 : Gamma) (c e1 e2 : expr) (τ : ty),
    Γ3 ≡ Γ1 ∘ Γ2 ⊣ c ->
    (Γ1 ⊦ c : (Texpr Tℕ)) ->
    (Γ2 ⊦ e1 : (Texpr τ)) ->
    (Γ2 ⊦ e2 : (Texpr τ)) ->
    (Γ3 ⊦ Xifz c e1 e2 : (Texpr τ))
.
#[local]
Hint Constructors check : core.

(** splits Γ backtracking style. We do this, because input/output contexts have proven more difficult to reason about *)
Fixpoint splitf (Γ : Gamma) (e : expr) : option (Gamma * Gamma) :=
  match Γ with
  | mapNil _ _ => (* splitEmpty *) Some([⋅], [⋅])
  | mapCons x τ Γ' =>
    match τ with
    | Texpr τ__e =>
      match τ__e with
      | (Tℕ | Twptr) => (* ℕsplit, weakPtrSplit *)
        let* (Γ1, Γ2) := splitf Γ' e in
        Some(mapCons x τ Γ1, mapCons x τ Γ2)
      | Tptr =>
        let* (Γ1, Γ2) := splitf Γ' e in
        match determine_pos x e with
        | PosL => (* ptrLsplit *)
          Some(mapCons x τ Γ1, Γ2)
        | PosR => (* ptrRsplit *)
          Some(mapCons x (Texpr Twptr) Γ1, mapCons x τ Γ2)
        end
      end
    | Tarrow τ1 τ2 => (* ArrowSplit *)
      let* _ := intf τ1 in
      let* _ := intf τ2 in
      let* (Γ1, Γ2) := splitf Γ' e in
      Some(mapCons x τ Γ1, mapCons x τ Γ2)
    | Treturn _ => None
    end
  end
.
Lemma splitf_sound (Γ Γ1 Γ2 : Gamma) (e : expr) :
  splitf Γ e = Some(Γ1, Γ2) -> (Γ ≡ Γ1 ∘ Γ2 ⊣ e)
.
Proof.
  revert Γ1 Γ2; induction Γ; intros Γ1 Γ2 H2; cbn in H2.
  - someinv; constructor.
  - destruct b; try congruence.
    + destruct t; crush_option (splitf Γ e); try destruct x as [Γ1' Γ2']; someinv.
      * constructor; now apply IHΓ.
      * destruct q. remember (determine_pos a e) as q; symmetry in Heqq; destruct q; someinv.
        -- constructor; auto.
        -- constructor; auto.
        -- someinv; constructor; now apply IHΓ.
      * destruct q; now rewrite Hx in H2.
    + destruct e0 as [τ1 τ2]; crush_intf τ1; crush_intf τ2; crush_option (splitf Γ e);
      destruct x1 as [Γ1' Γ2']; someinv.
      constructor; try now apply int_equiv_intf. now apply IHΓ.
Qed.
Lemma splitf_complete (Γ Γ1 Γ2 : Gamma) (e : expr) :
  (Γ ≡ Γ1 ∘ Γ2 ⊣ e) ->
  splitf Γ e = Some(Γ1, Γ2)
.
Proof.
  induction 1; cbn; try easy.
  - rewrite IHsplitting; easy.
  - rewrite IHsplitting; easy.
  - now rewrite IHsplitting, H.
  - now rewrite IHsplitting, H.
  - rewrite IHsplitting. now apply int_equiv_intf in H as ->; apply int_equiv_intf in H0 as ->.
Qed.
Lemma splitf_equiv_splitting (Γ Γ1 Γ2 : Gamma) (e : expr) :
  splitf Γ e = Some(Γ1, Γ2) <-> (Γ ≡ Γ1 ∘ Γ2 ⊣ e)
.
Proof. split; eauto using splitf_complete, splitf_sound. Qed.

Fixpoint noownedptrf (Γ : Gamma) : option Gamma :=
  match Γ with
  | mapNil _ _ => Some Γ
  | mapCons x (Texpr τ) Γ' =>
    let* _ := intf τ in
    let* Γ'' := noownedptrf Γ' in
    Some Γ
  | mapCons x _ Γ' =>
    let* Γ'' := noownedptrf Γ' in
    Some Γ
  end
.
Lemma noownedptrf_refl Γ Γ' :
  noownedptrf Γ = Some Γ' -> Γ = Γ'
.
Proof.
  revert Γ'; induction Γ; intros; inv H; try easy.
  destruct b; inv H1.
  - destruct (intf t); inv H0.
    destruct (option_dec (noownedptrf Γ)) as [Hx | Hx]; try (rewrite Hx in H1; inv H1).
    apply not_eq_None_Some in Hx as [x Hx]; rewrite Hx in H1.
    now inv H1.
  - destruct (option_dec (noownedptrf Γ)) as [Hx | Hx]; try (rewrite Hx in H0; inv H0).
    apply not_eq_None_Some in Hx as [x Hx]; rewrite Hx in H0. now inv H0.
  - destruct (option_dec (noownedptrf Γ)) as [Hx | Hx]; try (rewrite Hx in H0; inv H0).
    apply not_eq_None_Some in Hx as [x Hx]; rewrite Hx in H0. now inv H0.
Qed.
Ltac crush_noownedptrf_aux Γ :=
  let Hx' := fresh "Hx'" in
  let Hx := fresh "Hx" in
  let x := fresh "x" in
  destruct (option_dec (noownedptrf Γ)) as [Hx | Hx];
  try (rewrite Hx in *; congruence);
  try (apply not_eq_None_Some in Hx as [x Hx]; eapply noownedptrf_refl in Hx as Hx'; rewrite <- Hx' in Hx; clear Hx'; rewrite Hx in *)
.
Lemma noownedptr_equiv_noownedptrf Γ :
  NoOwnedPtr Γ <-> noownedptrf Γ = Some Γ
.
Proof.
  induction Γ; cbn; split; intros H; try easy.
  - destruct b; destruct H as [Ha Hb].
    + crush_intf t.
      * apply IHΓ in Hb. now rewrite Hb.
      * apply int_equiv_intf_none in Hx.
        exfalso; apply Hx. destruct t; try congruence; try constructor. destruct q; try constructor; contradiction.
    + now apply IHΓ in Hb as ->.
    + now apply IHΓ in Hb as ->.
  - destruct b; crush_noownedptrf_aux Γ.
    + crush_intf t. destruct t; inv Hx; split; try apply IHΓ; try easy; destruct q; easy.
    + crush_intf t. rewrite Hx in H. inv H.
    + destruct e; split; try apply IHΓ; easy.
    + split; try apply IHΓ; easy.
Qed.
Ltac crush_noownedptrf Γ :=
  crush_noownedptrf_aux Γ;
  try (match goal with
  | [H0: NoOwnedPtr ?Γ1, H1: NoOwnedPtr (?x ↦ ?τ ◘ [⋅]), H2: NoOwnedPtr ?Γ2 |- _] =>
    let H01 := fresh "H01" in
    let H012 := fresh "H012" in
    assert (NoOwnedPtr Γ1 /\ NoOwnedPtr (x ↦ τ ◘ [⋅])) as H01%noownedptr_split by now split
  end;
  match goal with
  | [H0: NoOwnedPtr (?Γ1 ◘ ?x ↦ ?τ ◘ [⋅]), H2: NoOwnedPtr ?Γ2 |- _] =>
    let H012 := fresh "H012" in
    assert (NoOwnedPtr (Γ1 ◘ x ↦ τ ◘ [⋅]) /\ NoOwnedPtr Γ2) as H012%noownedptr_split by now split
  end;
  match goal with
  | [ H0: NoOwnedPtr ?Γ1, H1: NoOwnedPtr (?x ↦ ?τ ◘ [⋅]), H2: NoOwnedPtr ?Γ2,
      H01: NoOwnedPtr (?Γ1 ◘ ?x ↦ ?τ ◘ [⋅]), H012: NoOwnedPtr ((?Γ1 ◘ ?x ↦ ?τ ◘ [⋅]) ◘ ?Γ2) |- _] =>
    clear H0 H1 H2 H01; repeat rewrite append_assoc in H012; cbn in H012; apply noownedptr_equiv_noownedptrf in H012; congruence
  end)
.
Definition inferf_var (Γ : Gamma) (x : vart) : option Ty :=
  let* _ := undup Γ in
  let* (Γ__a, _, τ, Γ__b) := splitat Γ x in
  let* _ := noownedptrf Γ in
  Some τ
.

Fixpoint inferf (Γ : Gamma) (e : expr) : option Ty :=
  match e with
  | Xres(Fres(Fvar x)) => inferf_var Γ x
  | Xres(Fres(Fval(Vnat n))) =>
    let* _ := noownedptrf Γ in
    Some(Texpr Tℕ)
  | Xbinop _ e1 e2 =>
    let* (Γ1, Γ2) := splitf Γ e1 in
    let* τ1 := inferf Γ1 e1 in
    let* τ2 := inferf Γ2 e2 in
    match τ1, τ2 with
    | Texpr Tℕ, Texpr Tℕ => Some(Texpr Tℕ)
    | _, _ => None
    end
  | Xdel x =>
    let* _ := undup Γ in
    let* (Γ1, y, τ, Γ2) := splitat Γ x in
    match τ with
    | Texpr Tptr => Some(Texpr Tℕ)
    | _ => None
    end
  | Xcall foo arg =>
    let* τ__f := inferf_var Γ foo in
    let* τ0' := inferf Γ arg in
    match τ0', τ__f with
    | Texpr τ0__e', Tectx(Tarrow τ0 τ1) =>
      let* _ := intf τ0 in
      let* _ := intf τ1 in
      if ty_eqb τ0 τ0__e' then
        Some(Texpr τ1)
      else
        None
    | _, _ => None
    end
  | Xreturn e' =>
    let* τ := inferf Γ e' in
    match τ with
    | Texpr τ' =>
      let* _ := intf τ' in
      Some(Treturn τ')
    | _ => None
    end
  | Xifz c e1 e2 =>
    let* (Γ1, Γ2) := splitf Γ c in
    let* τ__c := inferf Γ1 c in
    let* τ1 := inferf Γ2 e1 in
    let* τ2 := inferf Γ2 e2 in
    match τ__c, τ1, τ2 with
    | Texpr Tℕ, Texpr τ1', Texpr τ2' => if eq τ1' τ2' then Some(Texpr τ1') else None
    | _, _, _ => None
    end
  | Xget x e' =>
    let* (Γ1, Γ2) := splitf Γ (Fvar x) in
    let* τ__x := inferf_var Γ2 x in
    let* τ__e := inferf Γ1 e' in
    match τ__x, τ__e with
    | Texpr Twptr, Texpr Tℕ => Some(Texpr Tℕ)
    | _, _ => None
    end
  | Xset x e1 e2 =>
    let* (Γ12, Γ3) := splitf Γ (Xbinop Badd e1 e2) in
    let* (Γ1, Γ2) := splitf Γ12 e1 in
    let* τ1 := inferf Γ1 e1 in
    let* τ2 := inferf Γ2 e2 in
    let* τ3 := inferf_var Γ3 x in
    match τ1, τ2, τ3 with
    | Texpr Tℕ, Texpr Tℕ, Texpr Twptr => Some(Texpr Tℕ)
    | _, _, _ => None
    end
  | Xlet x e1 e2 =>
    let* (Γ1, Γ2) := splitf Γ e1 in
    let* τ1 := inferf Γ1 e1 in
    let* τ2 := inferf (x ↦ τ1 ◘ Γ2) e2 in
    match τ1, τ2 with
    | Texpr _, Texpr _ => Some τ2
    | _, _ => None
    end
  | Xnew x e1 e2 =>
    let* (Γ1, Γ2) := splitf Γ e1 in
    let* τ1 := inferf Γ1 e1 in
    let* τ2 := inferf (x ↦ (Texpr Tptr) ◘ Γ2) e2 in
    match τ1, τ2 with
    | Texpr Tℕ, Texpr _ => Some τ2
    | _, _ => None
    end
  | _ => None
  end
.
Lemma checkf_refinement (Γ : Gamma) (e : expr) (τ : Ty) :
  inferf Γ e = Some τ ->
  check Γ e τ
.
Proof.
  revert Γ τ; induction e; intros Γ τ H0; cbn in H0.
  - destruct f as [[]|].
    + (* value *) destruct v. crush_noownedptrf Γ. someinv. constructor. now apply noownedptr_equiv_noownedptrf.
    + (* variable *) crush_undup Γ; apply nodupinv_equiv_undup in Hx.
      recognize_split; elim_split.
      crush_noownedptrf (m1 ◘ v ↦ v0 ◘ m2). someinv. apply noownedptr_equiv_noownedptrf in Hx0.
      apply noownedptr_split in Hx0 as [Hx0__a Hx0__b]. apply noownedptr_cons in Hx0__b as [Hx0__b Hx0__c].
      constructor; auto.
    + (* abort *) congruence.
  - (* binop *) crush_option (splitf Γ e1); destruct x as [Γ1 Γ2].
    crush_option (inferf Γ1 e1); crush_option (inferf Γ2 e2).
    destruct x as [[]| |]; try congruence; destruct x0 as [[]| |]; try congruence; someinv.
    specialize (IHe1 Γ1 _ Hx0) as IHe1'; specialize (IHe2 Γ2 _ Hx1).
    erewrite splitf_equiv_splitting in Hx; eauto.
    eapply CToplus; eauto.
  - (* get *) crush_option (splitf Γ (Fvar x)); destruct x0 as [Γ1 Γ2].
    crush_undup Γ2. apply nodupinv_equiv_undup in Hx0.
    recognize_split; elim_split; crush_noownedptrf (m1 ◘ x ↦ v ◘ m2).
    crush_option (inferf Γ1 e); destruct v as [[]| |]; try congruence; destruct q; try congruence.
    destruct x2 as [[]| |]; try congruence; someinv.
    eapply splitf_equiv_splitting in Hx; eauto.
    eapply CTget; eauto. constructor; apply noownedptr_equiv_noownedptrf in Hx1;
    apply noownedptr_split in Hx1 as [Hx1__a Hx1__b]; apply noownedptr_cons in Hx1__b as [Hx1__b Hx1__c]; auto.
    eapply IHe; eauto.
  - (* set *) crush_option (splitf Γ (Xbinop Badd e1 e2)); destruct x0 as [Γ12 Γ3].
    crush_option (splitf Γ12 e1); destruct x0 as [Γ1 Γ2].
    crush_option (inferf Γ1 e1); crush_option (inferf Γ2 e2). crush_undup Γ3.
    apply nodupinv_equiv_undup in Hx3; recognize_split; elim_split.
    crush_noownedptrf (m1 ◘ x ↦ v ◘ m2). destruct x0; try congruence; destruct t; try congruence.
    destruct x1; try congruence; destruct t; try congruence. destruct v; try congruence; destruct t; try congruence.
    destruct q; try congruence; someinv.
    eapply splitf_equiv_splitting in Hx, Hx0. eapply CTset; eauto; try now (eapply IHe1 + eapply IHe2).
    constructor; apply noownedptr_equiv_noownedptrf in Hx4;
    apply noownedptr_split in Hx4 as [Hx4__a Hx4__b]; apply noownedptr_cons in Hx4__b as [Hx4__b Hx4__c]; auto.
  - (* let *) crush_option (splitf Γ e1); destruct x0 as [Γ1 Γ2].
    crush_option (inferf Γ1 e1); crush_option (inferf (x ↦ x0 ◘ Γ2) e2). destruct x0; try congruence.
    destruct x1; try congruence; someinv. eapply splitf_equiv_splitting in Hx.
    econstructor; eauto. eapply IHe1; eassumption. eapply IHe2; eassumption.
  - (* new *) crush_option (splitf Γ e1); destruct x0 as [Γ1 Γ2].
    crush_option (inferf Γ1 e1); crush_option (inferf (x ↦ (Texpr Tptr) ◘ Γ2) e2). destruct x0; try congruence.
    destruct x1; try congruence; destruct t; try congruence. someinv. eapply splitf_equiv_splitting in Hx.
    econstructor; eauto. eapply IHe1; eassumption. eapply IHe2; eassumption.
  - (* del *) crush_undup Γ; apply nodupinv_equiv_undup in Hx.
    recognize_split; elim_split. subst. destruct v as [[]| |]; try congruence. destruct q; try congruence.
    someinv; constructor; easy.
  - (* ret *) crush_option (inferf Γ e); destruct x; try congruence; someinv.
    crush_intf t; someinv. constructor. now apply int_equiv_intf. now eapply IHe.
  - (* call *) crush_undup Γ; eapply nodupinv_equiv_undup in Hx.
    recognize_split; elim_split; crush_noownedptrf (m1 ◘ foo ↦ v ◘ m2).
    crush_option (inferf (m1 ◘ foo ↦ v ◘ m2) e).
    destruct x1; try congruence. destruct v; try congruence. destruct e0; try congruence.
    crush_intf t0; crush_intf t1. destruct (eq_dec t0 t); subst; try (apply ty_eqb_neq in H1; rewrite H1 in H0; congruence).
    rewrite ty_eqb_refl in H0; someinv. apply int_equiv_intf in Hx2, Hx3.
    eapply CTcall. exact Hx2. exact Hx3.
    apply noownedptr_equiv_noownedptrf in Hx0; apply noownedptr_split in Hx0 as [Hx0__a Hx0__b];
    apply noownedptr_cons in Hx0__b as [Hx0__b Hx0__c]; eauto.
    eapply IHe; eauto.
  - (* ifz *) crush_option (splitf Γ e1); destruct x as [Γ1 Γ2].
    crush_option (inferf Γ1 e1); crush_option (inferf Γ2 e2); crush_option (inferf Γ2 e3).
    destruct x; try congruence. destruct t; try congruence. destruct x0, x1; try congruence.
    destruct (eq_dec t t0); subst; try (apply ty_eqb_neq in H; rewrite H in H0; congruence).
    rewrite ty_eqb_refl in H0; someinv. apply splitf_equiv_splitting in Hx; eapply CTifz; eauto;
    try ((apply IHe1 + apply IHe2 + apply IHe3); eauto).
  - (* abort *) congruence.
Qed.

Lemma checkf_correctness (Γ : Gamma) (e : expr) (τ : Ty) :
  check Γ e τ ->
  inferf Γ e = Some τ
.
Proof.
  induction 1; cbn.
  - (* CTvar *) crush_undup (Γ1 ◘ x ↦ τ ◘ Γ2); try (apply nodupinv_equiv_undup in H; congruence).
    crush_option (splitat (Γ1 ◘ x ↦ τ ◘ Γ2) x); try (apply splitat_elim in H; congruence).
    destruct x1 as [[[]]]; crush_noownedptrf (Γ1 ◘ x ↦ τ ◘ Γ2).
    apply nodupinv_equiv_undup in Hx; apply splitat_elim in Hx; rewrite Hx in Hx0; someinv; reflexivity.
  - (* CTℕ *) crush_noownedptrf Γ; auto; apply noownedptr_equiv_noownedptrf in H; congruence.
  - (* CToplus *) crush_option (splitf Γ3 e1); apply (splitf_equiv_splitting _ _ _ e1) in H; try congruence.
    destruct x as [Γ1' Γ2']; rewrite H in Hx; someinv.
    now rewrite IHcheck, IHcheck0.
  - (* CTget *) crush_option (splitf Γ3 (Fvar x)); apply (splitf_equiv_splitting _ _ _ (Fvar x)) in H; try congruence.
    destruct x0 as [Γ1' Γ2']; rewrite H in Hx; someinv.
    inv H0; crush_undup (Γ1 ◘ x ↦ (Texpr Twptr) ◘ Γ2).
    apply nodupinv_equiv_undup in Hx; recognize_split; elim_split.
    crush_noownedptrf (m1 ◘ x ↦ v ◘ m2); rewrite <- H0 in *; clear H0.
    rewrite IHcheck0. apply splitat_elim in H3; rewrite H3 in H'; someinv; reflexivity.
  - (* CTset *) crush_option (splitf Γ4 (Xbinop Badd e1 e2)); apply (splitf_equiv_splitting _ _ _ (Xbinop Badd e1 e2)) in H0; try congruence.
    destruct x0 as [Γ12' Γ3']; rewrite H0 in Hx; someinv.
    crush_option (splitf Γ12' e1); apply (splitf_equiv_splitting _ _ _ e1) in H; try congruence.
    destruct x0 as [Γ1' Γ2']; rewrite H in Hx; someinv.
    rewrite IHcheck0, IHcheck1. inv H1; crush_undup (Γ1 ◘ x ↦ (Texpr Twptr) ◘ Γ2).
    apply nodupinv_equiv_undup in Hx; recognize_split; elim_split.
    crush_noownedptrf (m1 ◘ x ↦ v ◘ m2); rewrite <- H1 in *; clear H1.
    apply splitat_elim in H5; rewrite H5 in H'; someinv; reflexivity.
  - (* CTlet *) crush_option (splitf Γ3 e1); apply (splitf_equiv_splitting _ _ _ e1) in H; try congruence.
    destruct x0 as [Γ1' Γ2']; rewrite H in Hx; someinv. rewrite IHcheck, IHcheck0; reflexivity.
  - (* CTnew *) crush_option (splitf Γ3 e1); apply (splitf_equiv_splitting _ _ _ e1) in H; try congruence.
    destruct x0 as [Γ1' Γ2']; rewrite H in Hx; someinv. rewrite IHcheck, IHcheck0; reflexivity.
  - (* CTdel *) crush_undup (Γ1 ◘ x ↦ (Texpr Tptr) ◘ Γ2); now apply splitat_elim in H as ->.
  - (* CTcall *) inv H1; crush_undup (Γ1 ◘ foo ↦ (Tectx (Tarrow τ0 τ1)) ◘ Γ2).
    recognize_split; elim_split. crush_noownedptrf (m1 ◘ foo ↦ v ◘ m2); rewrite <- H1 in *.
    apply splitat_elim in H4; rewrite H4 in H'; rewrite IHcheck0; someinv.
    apply int_equiv_intf in H as ->; apply int_equiv_intf in H0 as ->. now rewrite ty_eqb_refl.
  - (* CTret *) rewrite IHcheck. now apply int_equiv_intf in H as ->.
  - (* CTifz *) crush_option (splitf Γ3 c); apply (splitf_equiv_splitting _ _ _ c) in H; try congruence.
    destruct x as [Γ1' Γ2']; rewrite H in Hx; someinv. rewrite IHcheck, IHcheck1, IHcheck0.
    now rewrite ty_eqb_refl.
Qed.

Theorem checkf_equiv_check (Γ : Gamma) (e : expr) (τ : Ty) :
  inferf Γ e = Some τ <-> (check Γ e τ)
.
Proof. split; now (eapply checkf_refinement + eapply checkf_correctness). Qed.

(** Symbols look like `fn foo x : τ := e` *)
Definition symbol : Type := vart * Ty * expr.
Definition symbols := mapind varteq__Instance symbol.

(** Type for list of relevant functions, i.e. those that are part of the component. *)
Definition commlib := list vart.

(** A program is just a collection of symbols. The symbol `main` is the associated entry-point. *)
Inductive prog : Type := Cprog : symbols -> commlib -> prog.


Definition string_of_prog (p : prog) :=
  let '(Cprog s ξ) := p in
  "prog"%string (*TODO*)
.
(** Fill hole in evaluation context. *)
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

Fixpoint interfaces (s : symbols) : option(Gamma) :=
  match s with
  | mapNil _ _ => Some [⋅]
  | mapCons name EL s' =>
    match EL with
    | (x, Tectx(Tarrow τ0 τ1), _e) =>
      let* a := interfaces s' in
      Some(name ↦ Tectx(Tarrow τ0 τ1) ◘ a)
    | _ => None
    end
  end
.

Definition prog_check (p : prog) : Prop :=
  let '(Cprog symbs ξ) := p in
  let inttt := interfaces symbs in
  match inttt with
  | Some intt =>
    match mget intt ("main"%string) with
    | Some(Tectx(Tarrow Tℕ Tℕ)) =>
      match noownedptrf intt with
      | Some ints =>
        let fix doo (stack : symbols) :=
          match stack with
          | mapNil _ _ => True
          | mapCons foo (x, Tectx(Tarrow τ0 τ1), e) xs =>
            int τ0 /\ int τ1 /\
            doo xs /\
            check (x ↦ (Texpr τ0) ◘ ints) e (Treturn τ1)
          | _ => False
          end
        in doo symbs
      | None => False
      end
    | _ => False
    end
  | None => False
  end
.

(** * Dynamics *)

(* TODO: add ability to do n-steps *)
(* TODO: mark locations with function, remove when returning *)

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

(* A "dynamic" location contains the location and its poison *)
Definition dynloc : Type := loc * poison.
Definition dynloc_eqb :=
  fun (dℓ1 dℓ2 : dynloc) =>
    match dℓ1, dℓ2 with
    | (ℓ1, ☣), (ℓ2, ☣) => loc_eqb ℓ1 ℓ2
    | (ℓ1, ◻), (ℓ2, ◻) => loc_eqb ℓ1 ℓ2
    | (ℓ1, ☣), (ℓ2, ◻) => false
    | (ℓ1, ◻), (ℓ2, ☣) => false
    end
.
Lemma dynloc_eqb_refl (dℓ1 : dynloc) :
  dynloc_eqb dℓ1 dℓ1 = true.
Proof. destruct dℓ1; destruct p; cbn; now apply loc_eqb_refl. Qed.
Lemma dynloc_eqb_eq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = true <-> dℓ0 = dℓ1.
Proof.
  destruct dℓ0, dℓ1; destruct p, p0; split; cbn; intros H; try apply loc_eqb_eq in H; subst; eauto;
  inv H; apply loc_eqb_refl; inv H.
Qed.
Lemma dynloc_eqb_neq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = false <-> dℓ0 <> dℓ1.
Proof.
  destruct dℓ0, dℓ1; destruct p, p0; split; cbn; intros H; try apply loc_eqb_neq in H; subst; eauto;
  try (intros H'; apply H; now inv H').
  1,4: apply loc_eqb_neq; intros H'; apply H; inversion H'; now subst.
  1,2: congruence.
Qed.
#[local]
Instance dynloceq__Instance : HasEquality dynloc := {
  eq := dynloc_eqb ;
  eq_refl := dynloc_eqb_refl ;
  eqb_eq := dynloc_eqb_eq ;
  neqb_neq := dynloc_eqb_neq
}.
Notation "ℓ '⋅' ρ" := (((ℓ : loc), (ρ : poison)) : dynloc) (at level 81).

(** Stores map variables to potentially poisoned locations. *)
Definition store := mapind varteq__Instance dynloc.
Definition sNil : store := mapNil varteq__Instance dynloc.

Fixpoint δ_of_Δ (Δ : store) :=
  match Δ with
  | mapNil _ _ => mapNil _ _
  | mapCons _ ((addr ℓ), _) Δ' => mapCons (addr ℓ) (TMMon.addr ℓ) (δ_of_Δ Δ')
  end
.

Inductive snodupinv : store -> Prop :=
| snodupmapNil : snodupinv (sNil)
| snodupmapCons : forall (x : vart) (ℓ : loc) (ρ : poison) (Δ : store),
    ~(List.In x (dom Δ)) ->
    ~(List.In ℓ (dom(δ_of_Δ Δ))) ->
    snodupinv Δ ->
    snodupinv (x ↦ (ℓ ⋅ ρ) ◘ Δ)
.
Lemma nodupinv_of_snodupinv (Δ : store) :
  snodupinv Δ ->
  nodupinv Δ
.
Proof. induction 1; constructor; eauto. Qed.

Fixpoint sundup (Δ : store) : option(store) :=
  match Δ with
  | mapNil _ _ => Some(mapNil _ _)
  | mapCons a (ℓ, ρ) Δ' =>
    let thedom := dom Δ' in
    let theimg := img Δ' in
    match List.find (fun x => eq a x) thedom, List.find (fun x => let '(ℓ', _) := x in loc_eqb ℓ' ℓ) theimg, sundup Δ' with
    | None, None, Some Δ'' => Some(mapCons a (ℓ,ρ) Δ'')
    | _, _, _ => None
    end
  end
.
Lemma sundup_refl (Δ Δ' : store) :
  sundup Δ = Some Δ' -> Δ = Δ'.
Proof.
  revert Δ'; induction Δ; cbn; intros; try (inv H; easy).
  destruct b. destruct (option_dec (List.find (fun x : vart => vareq a x) (dom Δ))) as [Hx|Hy].
  - apply not_eq_None_Some in Hx as [Δ__x Hx]; rewrite Hx in H; congruence.
  - rewrite Hy in H.
    destruct (option_dec (List.find (fun '(ℓ', _) => loc_eqb ℓ' l) (img Δ))) as [Hx0|Hy0].
    + apply not_eq_None_Some in Hx0 as [Δ__x Hx0]; rewrite Hx0 in H; congruence.
    + rewrite Hy0 in H. destruct (option_dec (sundup Δ)) as [Hx1|Hy1].
      * apply not_eq_None_Some in Hx1 as [Δ__x Hx1]; rewrite Hx1 in H.
        specialize (IHΔ Δ__x Hx1) as ->; now inv H.
      * rewrite Hy1 in H; congruence.
Qed.
Lemma δ_of_Δ_in_dom (Δ : store) ℓ :
  In ℓ (dom (δ_of_Δ Δ)) ->
  exists ρ, In (ℓ ⋅ ρ) (img Δ)
.
Proof.
  revert ℓ; induction Δ; cbn; intros; try easy.
  destruct b, l; destruct H as [H|H].
  - inv H. exists p; now left.
  - specialize (IHΔ ℓ H); deex; exists ρ; now right.
Qed.
Lemma δ_of_Δ_in_img (Δ : store) ℓ ρ :
  In (ℓ ⋅ ρ) (img Δ) ->
  In ℓ (dom (δ_of_Δ Δ))
.
Proof.
  induction Δ; cbn; intros H; try easy.
  destruct H as [H|H]; destruct b, l.
  - inv H. now left.
  - specialize (IHΔ H). now right.
Qed.
Lemma snodupinv_equiv_sundup (Δ : store) :
  sundup Δ = Some Δ <-> snodupinv Δ.
Proof.
  split; intros H.
  - induction Δ; cbn; try constructor.
    cbn in H. destruct b. destruct (option_dec (List.find (fun x : vart => vareq a x) (dom Δ))) as [Hx|Hy].
    + apply not_eq_None_Some in Hx as [Δ__x Hx]; rewrite Hx in H; congruence.
    + rewrite Hy in H. destruct (option_dec (List.find (fun '(ℓ', _) => loc_eqb ℓ' l) (img Δ))) as [Hx0|Hy0].
      * apply not_eq_None_Some in Hx0 as [Δ__x0 Hx0]; rewrite Hx0 in H; congruence.
      * rewrite Hy0 in H. destruct (option_dec (sundup Δ)) as [Hx1|Hy1].
        -- apply not_eq_None_Some in Hx1 as [Δ__x Hx1]; rewrite Hx1 in H.
           rewrite <- (sundup_refl _ Hx1) in Hx1. specialize (IHΔ Hx1).
           econstructor; eauto.
           intros H__a. eapply find_none in Hy as Hy__f; eauto. unfold vareq in Hy__f.
           now rewrite String.eqb_refl in Hy__f.
           intros H__a.
           apply δ_of_Δ_in_dom in H__a as H__a'; deex.
           eapply find_none in Hy0 as Hy0__f; eauto; cbn in Hy0__f; now rewrite loc_eqb_refl in Hy0__f.
        -- rewrite Hy1 in H; congruence.
  - induction H; cbn; try easy.
    destruct (option_dec (List.find (fun x0 : vart => vareq x x0) (dom Δ))) as [Hx|Hy].
    + apply not_eq_None_Some in Hx as [x__x Hx].
      apply find_some in Hx as [Hx1 Hx2]. unfold vareq in Hx2. apply String.eqb_eq in Hx2; subst. contradiction.
    + rewrite Hy. destruct (option_dec (List.find (fun '(ℓ', _) => loc_eqb ℓ' ℓ) (img Δ))) as [Hx0|Hy0].
      * apply not_eq_None_Some in Hx0 as [[ℓ__x ρ__x] Hx0].
        apply find_some in Hx0 as [Hx1 Hx2]. apply loc_eqb_eq in Hx2; subst.
        apply δ_of_Δ_in_img in Hx1. contradiction.
      * rewrite Hy0. rewrite IHsnodupinv. easy.
Qed.
Definition spush (x : vart) (dℓ : dynloc) (Δ : store) : option (store) :=
  match sundup (mapCons x dℓ Δ) with
  | Some Δ' => Some Δ'
  | None => None
  end
.
Lemma spush_ok (x : vart) (dℓ : dynloc) (Δ Δ' : store) :
  spush x dℓ Δ = Some Δ' -> snodupinv Δ'.
Proof.
  intros H0. unfold spush in H0.
  destruct (option_dec (sundup (mapCons x dℓ Δ))) as [Hx|Hy]; try (rewrite Hy in *; congruence);
  apply not_eq_None_Some in Hx as [Δ__x Hx]; rewrite Hx in H0; inv H0;
  apply snodupinv_equiv_sundup; cbn in Hx.
  destruct dℓ.
  destruct (option_dec (List.find (fun x0 : vart => vareq x x0) (dom Δ))) as [Hx0|Hy0]; try (rewrite Hy0 in *; congruence).
  apply not_eq_None_Some in Hx0 as [Δ__x Hx0]; rewrite Hx0 in Hx; inv Hx.
  rewrite Hy0 in Hx. destruct (option_dec (List.find (fun '(ℓ', _) => loc_eqb ℓ' l) (img Δ))) as [Hx1|Hy1].
  apply not_eq_None_Some in Hx1 as [Δ__x Hx1]; rewrite Hx1 in Hx; inv Hx.
  rewrite Hy1 in Hx. destruct (option_dec (sundup Δ)) as [Hx2|Hy2].
  apply not_eq_None_Some in Hx2 as [Δ__x Hx1]. rewrite Hx1 in Hx.
  inv Hx. cbn. apply sundup_refl in Hx1 as Hx1'. rewrite Hx1' in Hy0.
  rewrite (sundup_refl Δ Hx1) in Hx1. rewrite Hx1' in Hy1. rewrite Hy0, Hy1, Hx1; easy.
  rewrite Hy2 in Hx; congruence.
Qed.
Lemma snodupinv_whocares0 (a : vart) (ℓ : loc) (ρ ρ' : poison) (Δ : store) :
  snodupinv (a ↦ (ℓ,ρ) ◘ Δ) <-> snodupinv (a ↦ (ℓ, ρ') ◘ Δ)
.
Proof. split; intros H; constructor; inv H; eauto. Qed.
Lemma snodupinv_split (Δ Δ' : store) :
  snodupinv (Δ ◘ Δ') ->
  snodupinv Δ /\ snodupinv Δ'
.
Proof.
  remember (Δ ◘ Δ') as Δ__c; revert Δ Δ' HeqΔ__c; induction Δ__c; cbn; intros.
  - now destruct Δ, Δ'; inv HeqΔ__c.
  - destruct Δ, Δ'; inv HeqΔ__c; cbn in *.
    + split; try constructor; easy.
    + split; try constructor; now rewrite append_nil in H.
    + inv H. specialize (IHΔ__c Δ (v0 ↦ d0 ◘ Δ') Logic.eq_refl H5) as [IH__a IH__b].
      split; try easy.
      constructor; try easy.
      * revert H3; clear; intros H0 H1; induction Δ; inv H1.
        apply H0; now left.
        assert (~ In v (dom (Δ ◘ v0 ↦ d0 ◘ Δ'))) as H2 by (intros H2; apply H0; now right); auto.
      * revert H4; clear; intros H0 H1; induction Δ; try inv H1.
        cbn in H1; destruct b, l; inv H1. apply H0; now left.
        assert (~ In ℓ (dom(δ_of_Δ (Δ ◘ v0 ↦ d0 ◘ Δ')))) as H2 by (intros H2; apply H0; now right); auto.
Qed.

Lemma snodupinv_whocares (a : vart) (ℓ : loc) (ρ ρ' : poison) (Δ Δ' : store) :
  snodupinv (Δ ◘ a ↦ (ℓ,ρ) ◘ Δ') <-> snodupinv (Δ ◘ a ↦ (ℓ, ρ') ◘ Δ')
.
Proof.
Admitted.
Lemma spush_msubset (Δ Δ' : store) (x : vart) (v : dynloc) :
  Some Δ' = spush x v Δ ->
  MSubset Δ Δ'.
Proof. Admitted.

Lemma δΔ_msubset_invariant (Δ Δ' : store) :
  MSubset Δ Δ' ->
  MSubset (δ_of_Δ Δ) (δ_of_Δ Δ')
.
Proof. Admitted.

#[local]
Instance nateq__Instance : HasEquality nat := {
  eq := Nat.eqb ;
  eq_refl := Nat.eqb_refl ;
  eqb_eq := Nat.eqb_eq ;
  neqb_neq := Nat.eqb_neq
}.
Definition heap := mapind nateq__Instance nat.
Definition hNil : heap := mapNil nateq__Instance nat.
Fixpoint Hgrow_aux (H : heap) (s len : nat) : option heap :=
  match s with
  | 0 => Some(H)
  | S n' =>
    let* Hi := Hgrow_aux H n' len in
    push (len + n') 0 Hi
  end
.
Definition Hgrow (H : heap) (s : nat) : option heap :=
  Hgrow_aux H s (List.length (dom H))
.
Variant comms : Type :=
| Qctxtocomp : comms
| Qcomptoctx : comms
| Qinternal : comms
.
Definition comms_eq (q1 q2 : comms) :=
  match q1, q2 with
  | Qctxtocomp, Qctxtocomp => true
  | Qcomptoctx, Qcomptoctx => true
  | Qinternal, Qinternal => true
  | _, _ => false
  end
.
Definition string_of_comms (q : comms) :=
  match q with
  | Qctxtocomp => "?"%string
  | Qcomptoctx => "!"%string
  | Qinternal => "∅"%string
  end
.
Definition active_ectx := list (evalctx * vart * comms).
(** Contains names of component-level functions *)

#[local]
Existing Instance varteq__Instance | 0.
Definition state : Type := CSC.Fresh.fresh_state * symbols * commlib * active_ectx * heap * store.
Notation "F ';' Ξ ';' ξ ';' K ';' H ';' Δ" := ((F : CSC.Fresh.fresh_state), (Ξ : symbols),
                                               (ξ : commlib), (K : active_ectx), (H : heap), (Δ : store))
                                               (at level 81, K at next level, ξ at next level, Ξ at next level, H at next level, Δ at next level).
Ltac splitΩ Ω :=
  let F := fresh "F" in
  let Ξ := fresh "Ξ" in
  let ξ := fresh "ξ" in
  let K := fresh "K" in
  let H := fresh "H" in
  let Δ := fresh "Δ" in
  destruct Ω as [[[[[F Ξ] ξ] K] H] Δ].
Definition nodupinv (Ω : state) : Prop :=
  let '(F, Ξ, ξ, K, H, Δ) := Ω in
  nodupinv Ξ /\ nodupinv H /\ snodupinv Δ
.
Lemma nodupinv_empty Ξ ξ :
  Util.nodupinv Ξ ->
  nodupinv(Fresh.empty_fresh ; Ξ ; ξ ; List.nil ; hNil ; sNil).
Proof. intros H; cbn; repeat split; eauto; constructor. Qed.
Lemma nodupinv_H F Ξ ξ K H Δ n H':
  nodupinv (F;Ξ;ξ;K;H;Δ) ->
  Hgrow H n = Some H' ->
  nodupinv (F;Ξ;ξ;K;H';Δ)
.
Proof.
  intros [Ha [Hb Hc]]; repeat split; eauto.
  revert H' H Hb H0; induction n; intros H' H Hb H0.
  - now inv H0.
  - cbn in H0. destruct (option_dec (Hgrow_aux H n (List.length (dom H)))) as [Hx|Hy]; try (rewrite Hy in H0; congruence).
    apply not_eq_None_Some in Hx as [H__x Hx].
    rewrite Hx in H0.
    cbn in H0. now apply push_ok in H0.
Qed.

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
| TΩ : forall F Ξ ξ K H Δ (Γ : Gamma), store_split Ξ Δ Γ -> state_split (F ; Ξ ; ξ ; K ; H ; Δ) Γ
.
Inductive rt_check : state -> expr -> Ty -> Prop :=
| Trtcheck : forall (Ω : state) (e : expr) (τ : Ty) (Γ : Gamma),
    state_split Ω Γ ->
    (check Γ e τ) ->
    rt_check Ω e τ
.
Definition ectx_rt_check (Ω : state) (K : evalctx) (τ τ' : Ty) :=
  forall (e : expr), rt_check Ω e τ' -> rt_check Ω (insert K e) τ
.
Lemma rt_check_recompose (Ω : state) (K : evalctx) (e : expr) (τ : Ty) :
  rt_check Ω (insert K e) τ ->
  exists τ', ectx_rt_check Ω K τ' τ /\ rt_check Ω e τ'
.
Proof.
  intros H.
  remember (insert K e).
  destruct H.
  induction H0.
  - induction K; cbn in *; try congruence; subst.
    exists τ; split; try easy; econstructor; eauto; econstructor; eauto.
  - induction K; cbn in *; try congruence; subst.
    exists Tℕ; split; try easy; econstructor; eauto; econstructor; eauto.
  - induction K; cbn in *; try congruence; subst; exists Tℕ.
    + split; try easy; econstructor; eauto; econstructor; eauto.
    + split; inv Heqe0.
      * econstructor; eauto. econstructor; eauto.
Admitted.
Lemma rt_check_decompose (Ω : state) (K : evalctx) (e : expr) (τ τ' : Ty) :
  ectx_rt_check Ω K τ' τ ->
  rt_check Ω e τ' ->
  rt_check Ω (insert K e) τ
.
Proof. Admitted.

(** Types of events that may occur in a trace. *)
Variant event : Type :=
| Sstart : event
| Send (v : value) : event
| Salloc (ℓ : loc) (n : nat) : event
| Sdealloc (ℓ : loc) : event
| Sget (ℓ : loc) (n : nat) : event
| Sset (ℓ : loc) (n : nat) (v : value) : event
| Scrash : event
| Scall (q : comms) (foo : vart) (arg : fnoerr) : event
| Sret (q : comms) (f : fnoerr) : event
.
Definition eventeq (e1 e2 : event) : bool :=
  match e1, e2 with
  | Sstart, Sstart => true
  | Send(Vnat n1), Send(Vnat n2) => Nat.eqb n1 n2
  | Salloc(addr ℓ0) n0, Salloc(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sdealloc(addr ℓ0), Sdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Sget(addr ℓ0) n0, Sget(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sset(addr ℓ0) n0 (Vnat v0), Sset(addr ℓ1) n1 (Vnat v1) => andb (andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1))
                                                                  (Nat.eqb v0 v1)
  | Scrash, Scrash => true
  | Scall q1 foo (Fval(Vnat v0)), Scall q2 bar (Fval(Vnat v1)) => andb (andb (String.eqb foo bar) (Nat.eqb v0 v1)) (comms_eq q1 q2)
  | Scall q1 foo (Fvar x), Scall q2 bar (Fvar y) => andb(andb (String.eqb foo bar) (String.eqb x y)) (comms_eq q1 q2)
  | Sret q1 (Fval(Vnat v0)), Sret q2 (Fval(Vnat v1)) => andb (Nat.eqb v0 v1) (comms_eq q1 q2)
  | Sret q1 (Fvar x), Sret q2 (Fvar y) => andb (String.eqb x y) (comms_eq q1 q2)
  | _, _ => false
  end
.
#[global]
Instance Event__Instance : TraceEvent event := {}.
(** Pretty-printing function for better debuggability *)
Definition string_of_event (e : event) :=
  match e with
  | (Sstart) => "Start"%string
  | (Send(Vnat n)) => String.append ("End "%string) (string_of_nat n)
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
  | (Scall q foo (Fval(Vnat n))) => String.append (String.append
                                                  (String.append ("Call "%string)
                                                   (String.append (string_of_comms q)
                                                    (String.append " "%string foo))) " "%string)
                                   (string_of_nat n)
  | (Scall q foo (Fvar x)) => String.append (String.append
                                            (String.append ("Call "%string)
                                             (String.append (string_of_comms q)
                                              (String.append " "%string foo))) " "%string)
                             x
  | (Sret q (Fval(Vnat n))) => String.append ("Ret "%string)
                              (String.append (string_of_comms q)
                               (String.append " "%string (string_of_nat n)))
  | (Sret q (Fvar x)) => String.append ("Ret "%string)
                         (String.append (string_of_comms q)
                          (String.append " "%string x))
  end
.

(** A runtime program is a state plus an expression. *)
Definition rtexpr : Type := (option state) * expr.
#[global]
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

Definition substτ (Γ : Gamma) (what fore : vart) :=
  match Γ with
  | mapNil _ _ => mapNil _ _
  | mapCons x t Γ' =>
    if vareq x what then
      mapCons fore t Γ'
    else
      mapCons x t Γ'
  end
.

Lemma substi Γ e x y t :
  check Γ e t ->
  check (substτ Γ x y) (subst x e (Fvar y)) t
.
Proof.
  induction 1; cbn.
  - destruct (eq_dec x x0); subst.
    + rewrite String.eqb_refl. econstructor; eauto.
Admitted.

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
| e_get : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H : heap) (Δ1 Δ2 : store) (x : vart) (ℓ n v : nat) (ρ : poison),
    forall (H0a : ℓ + n < length H -> Some v = mget H (ℓ + n))
      (H0b : ℓ + n >= length H -> v = 1729)
      (H0c : Util.nodupinv (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)),
    (F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xget x n --[ (Sget (addr ℓ) n) ]--> (F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ v
| e_set : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H H' : heap) (Δ1 Δ2 : store) (x : vart) (ℓ n v : nat) (ρ : poison),
    forall (H0a : ℓ + n < length H -> Some H' = mset H (ℓ + n) v)
      (H0b : ℓ + n >= length H -> H' = H)
      (H0c : Util.nodupinv (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)),
    (F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xset x n v --[ (Sset (addr ℓ) n v) ]--> (F ; Ξ ; ξ ; K ; H' ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ v
| e_delete : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H : heap) (Δ1 Δ2 : store) (x : vart) (ℓ : nat) (ρ : poison)
      (H0c : Util.nodupinv (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)),
    (F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2)) ▷ Xdel x --[ (Sdealloc (addr ℓ)) ]--> (F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ☣) ◘ Δ2)) ▷ 0
| e_let : forall (Ω : state) (x : vart) (f : fnoerr) (e e' : expr),
    e' = subst x e f ->
    Ω ▷ Xlet x f e --[]--> Ω ▷ e'
| e_alloc : forall (F F' F'' : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H H' : heap) (Δ Δ' : store) (x z : vart) (ℓ n : nat) (e : expr),
    ℓ = Fresh.fresh F ->  F' = Fresh.advance F ->
    z = Fresh.freshv F' -> F'' = Fresh.advance F' ->
    spush z ((addr ℓ) ⋅ ◻) Δ = Some Δ' ->
    Some H' = Hgrow H n ->
    (F ; Ξ ; ξ ; K ; H ; Δ) ▷ Xnew x n e --[ (Salloc (addr ℓ) n) ]--> (F'' ; Ξ ; ξ ; K ; H' ; Δ') ▷ (subst x e (Fvar z))
.
#[global]
Existing Instance pstep.
#[global]
Hint Constructors pstep : core.

Lemma pstep_is_nodupinv_invariant Ω e Ω' e' a :
  Ω ▷ e --[, a ]--> Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  assert (Some Ω = let (oΩ, e) := Ω ▷ e in oΩ) by easy.
  assert (Some Ω' = let (oΩ', e') := Ω' ▷ e' in oΩ') by easy.
  induction 1; try (inv H; inv H0; easy).
  - (*e_set*) splitΩ Ω; inv H; splitΩ Ω'; inv H0.
    intros [Ha [Hb Hc]]; repeat split; eauto.
    destruct (PeanoNat.Nat.le_decidable (length H1) (ℓ + n)).
    + specialize (H0b H); now subst.
    + apply PeanoNat.Nat.nle_gt in H; specialize (H0a H).
      eapply nodupinv_mset in H0a; eauto.
  - (*e_delete*) splitΩ Ω; inv H; splitΩ Ω'; inv H0.
    intros [Ha [Hb Hc]]; repeat split; eauto. revert Hc; clear; intros H.
    destruct ρ; try easy.
    rewrite snodupinv_whocares in H; exact H.
  - (*e_alloc*) splitΩ Ω; inv H; splitΩ Ω'; inv H0.
    intros [Ha [Hb Hc]]; repeat split; eauto.
    + eapply nodupinv_H; eauto. instantiate (1:=Δ'); instantiate (1:=K); instantiate (1:=ξ); instantiate (1:=Ξ); instantiate (1:=advance F).
      repeat split; eauto using spush_ok.
    + now apply spush_ok in H6.
Qed.

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
      let '(F, Ξ, ξ, K, H, Δ) := Ω in
      let* Δ__x := undup Δ in
      let* (Δ1, x, (L, ρ), Δ2) := splitat Δ__x x in
      let '(addr ℓ) := L in
      let v := match mget H (ℓ + n) with
              | None => 1729
              | Some w => w
              end
      in
        Some(Some(Sget (addr ℓ) n), F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2) ▷ v)
    | _ => None
    end
  | Xset x en ev => (* e-set *)
    match en, ev with
    | Xres(Fres(Fval(Vnat n))), Xres(Fres(Fval(Vnat v))) =>
      let '(F, Ξ, ξ, K, H, Δ) := Ω in
      let* Δ__x := undup Δ in
      let* (Δ1, x, (L, ρ), Δ2) := splitat Δ__x x in
      let '(addr ℓ) := L in
      match mset H (ℓ + n) v with
      | Some H' =>
        Some(Some(Sset (addr ℓ) n v), F ; Ξ ; ξ ; K ; H' ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2) ▷ v)
      | None =>
        Some(Some(Sset (addr ℓ) n v), F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ρ) ◘ Δ2) ▷ v)
      end
    | _, _ => None
    end
  | Xdel x => (* e-delete *)
    let '(F, Ξ, ξ, K, H, Δ) := Ω in
    let* Δ__x := undup Δ in
    let* (Δ1, x, (L, ρ), Δ2) := splitat Δ__x x in
    let '(addr ℓ) := L in
    Some(Some(Sdealloc (addr ℓ)), F ; Ξ ; ξ ; K ; H ; (Δ1 ◘ x ↦ ((addr ℓ) ⋅ ☣) ◘ Δ2) ▷ 0)
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
      let '(F, Ξ, ξ, K, H, Δ) := Ω in
      let* H' := Hgrow H n in
      let ℓ := CSC.Fresh.fresh F in
      let F' := Fresh.advance F in
      let z := CSC.Fresh.freshv F' in
      let* Δ' := spush z ((addr ℓ) ⋅ ◻) Δ in
      let e'' := subst x e' (Fvar z) in
      Some(Some(Salloc (addr ℓ) n), (Fresh.advance F' ; Ξ ; ξ ; K ; H' ; Δ') ▷ e'')
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

Lemma Hget_none (H : heap) (n : nat) :
  n >= length H -> mget H n = None.
Proof. Admitted.
Lemma Hget_some (H : heap) (n : nat) :
  n < length H -> exists v, mget H n = Some v.
Proof. Admitted.
Lemma Hset_none (H : heap) (n : nat) v :
  n >= length H -> mset H n v = None.
Proof. Admitted.
Lemma Hset_some (H : heap) (n : nat) v :
  n < length H -> exists H', mset H n v = Some H'.
Proof. Admitted.

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
    + (* e-get *) cbn; apply nodupinv_equiv_undup in H0c as H0c'; rewrite H0c'.
      destruct (Arith.Compare_dec.lt_dec (ℓ + n) (length H)) as [H1a | H1b]; rewrite splitat_elim; eauto.
      * now specialize (H0a H1a) as H0a'; inv H0a'.
      * apply Arith.Compare_dec.not_lt in H1b; specialize (H0b H1b) as H1b'.
        now rewrite (@Hget_none H (ℓ + n) H1b); subst.
    + (* e-set *) cbn; apply nodupinv_equiv_undup in H0c as H0c'; rewrite H0c'.
      destruct (Arith.Compare_dec.lt_dec (ℓ + n) (length H)) as [H1a | H1b]; rewrite splitat_elim; eauto.
      * now rewrite <- (H0a H1a).
      * apply Arith.Compare_dec.not_lt in H1b; specialize (H0b H1b) as H1b'; subst.
        now rewrite (@Hset_none H (ℓ + n) v H1b).
    + (* e-delete *) cbn; apply nodupinv_equiv_undup in H0c as H0c'; rewrite H0c'; rewrite splitat_elim; eauto.
    + (* e-let *) now subst; cbn.
    + (* e-new *) subst; unfold pstepf.
      now rewrite (get_rid_of_letstar (F, Ξ, ξ, K, H, Δ)), <- H5, (get_rid_of_letstar H'), H4, (get_rid_of_letstar Δ').
  - intros H; destruct r0 as [oΩ e], r1 as [Ω' e']; destruct e; cbn in H; crush_interp; clear H.
    + (* e = e1 ⊕ e2 *)
      now grab_value2 e1 e2; inv H1; eapply e_binop.
    + (* e = x[e] *)
      grab_value e; destruct s as [[[[[F Ξ] ξ] K] H] Δ]; crush_undup Δ; apply nodupinv_equiv_undup in Hx.
      recognize_split; elim_split; destruct v as [[ℓ] ρ].
      inv H1; eapply e_get; try intros H0; eauto.
      * now apply Hget_some in H0 as [v ->].
      * now apply Hget_none in H0 as ->.
    + (* e = x[e1] <- e2 *)
      grab_value2 e1 e2. destruct s as [[[[[F Ξ] ξ] K] H] Δ].
      crush_undup Δ; apply nodupinv_equiv_undup in Hx.
      recognize_split; elim_split; destruct v as [[ℓ] ρ].
      destruct (Arith.Compare_dec.lt_dec (ℓ + e1) (length H)) as [H2|H2].
      * apply (@Hset_some H (ℓ + e1) e2) in H2 as [H__x' H2]. rewrite H2 in H1.
        inv H1. eapply e_set; eauto; intros H0; subst; try easy.
        eapply (@Hset_none H (ℓ + e1) e2) in H0; congruence.
      * apply Arith.Compare_dec.not_lt in H2. apply (@Hset_none H (ℓ + e1) e2) in H2; subst; rewrite H2 in H1.
        inv H1. eapply e_set; eauto; intros H0; try easy. apply (@Hset_some H (ℓ + e1) e2) in H0 as [H__x' H0]; congruence.
    + (* e = let x = e1 in e2 *)
      grab_final e1; inv H1; now eapply e_let.
    + (* e = let x = new e1 in e2 *)
      change (pstepf (s ▷ Xnew x e1 e2) = Some (a, (Ω', e'))) in H1.
      unfold pstepf in H1. rewrite (get_rid_of_letstar s) in H1.
      grab_value e1. splitΩ s. destruct (option_dec (Hgrow H e1)) as [Hx|Hy]; try (rewrite Hy in H1; cbn in H1; congruence).
      apply not_eq_None_Some in Hx as [H' Hx]; rewrite Hx in H1.
      rewrite (get_rid_of_letstar H') in H1.
      destruct (option_dec(spush(freshv(advance F)) (addr (fresh F), ◻) Δ)) as [Hx0|Hy0]; try (rewrite Hy0 in H1; cbn in H1; congruence).
      apply not_eq_None_Some in Hx0 as [Δ' Hx0]; rewrite Hx0 in H1.
      rewrite (get_rid_of_letstar Δ') in H1; inv H1. eapply e_alloc; eauto.
    + (* e = delete x *)
      destruct s as [[[[[F Ξ] ξ] K] H] Δ]; inv H1. crush_undup Δ; apply nodupinv_equiv_undup in Hx.
      recognize_split; elim_split; destruct v as [[ℓ] ρ]; subst.
      inv H2; apply e_delete; eauto.
    + (* e = ifz c e0 e1 *)
      grab_value e1. destruct e1; inv H1; apply e_ifz_true || apply e_ifz_false.
    + (* e = abort *)
      apply e_abort.
Qed.
Lemma pstepf_is_nodupinv_invariant Ω e Ω' e' a :
  pstepf (Ω ▷ e) = Some(a, Ω' ▷ e') ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof. intros H0 H1; apply equiv_pstep in H0; apply pstep_is_nodupinv_invariant in H0; eauto. Qed.

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
#[global]
Hint Resolve pstep_compat_weaken call_pestep_compat return_pestep_compat : core.

(** ** Environment Semantics extended with context switches *)
(** ρ__call judgement takes care of emitting Qinternal or Qctxtocomp/Qcomptoctx, depending on whether
    the current context and the new context is in the list of components ξ or not. *)
Inductive ρ__call : commlib -> vart -> vart -> fnoerr -> option event -> comms -> Prop :=
| comm_call_comptoctx : forall ξ foo bar iv,
    ~(List.In foo ξ) ->
    List.In bar ξ ->
    ρ__call ξ foo bar iv (Some(Scall Qcomptoctx foo iv)) Qctxtocomp
| comm_call_ctxtocomp : forall ξ foo bar iv,
    List.In foo ξ ->
    ~(List.In bar ξ) ->
    ρ__call ξ foo bar iv (Some(Scall Qctxtocomp foo iv)) Qcomptoctx
| comm_call_internal_comp : forall ξ foo bar iv,
    List.In foo ξ ->
    List.In bar ξ ->
    ρ__call ξ foo bar iv None Qinternal
| comm_call_internal_ctx : forall ξ foo bar iv,
    ~(List.In foo ξ) ->
    ~(List.In bar ξ) ->
    ρ__call ξ foo bar iv None Qinternal
.
Definition ρf__call (ξ : commlib) (new cur : vart) (f : fnoerr) : (option event) * comms :=
  match List.find (fun x => vareq x new) ξ, List.find (fun x => vareq x cur) ξ with
  | None, None | Some _, Some _ => (None, Qinternal)
  | None, Some _ => (* we call from component into context, so this is Qcomptoctx *)
    (Some(Scall Qcomptoctx new f), Qctxtocomp)
  | Some _, None => (* we call from context into component, so this is Qctxtocomp *)
    (Some(Scall Qctxtocomp new f), Qcomptoctx)
  end
.
Ltac In_find_resolve_contr_hook Hx Hy := fail.
Ltac In_find_resolve_contr := (
      match goal with
      | [Hx : List.find (fun x : string => vareq _ ?bar) ?ξ = None,
         Hy : In ?bar ?ξ |- _] =>
        apply (List.find_none _ _ Hx) in Hy; apply String.eqb_neq in Hy; contradiction
      | [Hx : List.find (fun x : string => vareq _ ?bar) ?ξ = Some _,
         Hy : ~In ?bar ?ξ |- _] =>
        let Hxf := fresh "Hx'" in
        let Hx1 := fresh "Hx1" in
        let Hx2 := fresh "Hx2" in
        assert (Hx':=Hx); apply List.find_some in Hxf as [Hx1 Hx2];
        apply String.eqb_eq in Hx2; subst; contradiction
      | [Hx : List.find (fun x : string => vareq _ ?foo) _ = None,
         Hy : List.find (fun x : string => vareq _ ?bar) _ = None |- _] =>
        In_find_resolve_contr_hook Hx Hy
      | [Hx : List.find (fun x : string => vareq _ ?foo) _ = Some _,
         Hy : List.find (fun x : string => vareq _ ?bar) _ = Some _ |- _] =>
        In_find_resolve_contr_hook Hx Hy
      end)
.
Lemma dup (A : Prop) : A -> A /\ A.
Proof. now split. Qed.
Ltac option_boilerplate H := (
    let Hx := fresh "Hx" in
    let Hx' := fresh "Hx" in
    let x := fresh "x" in
    destruct (option_dec H) as [Hx | Hx]; try
    (apply not_eq_None_Some in Hx as [x Hx']; apply dup in Hx' as [Hx Hx'])
    )
.
Lemma ρ__call_equiv_ρf__call (ξ : commlib) (new cur : vart) (f : fnoerr) (a : option event) (q : comms) :
  ρ__call ξ new cur f a q <-> ρf__call ξ new cur f = (a, q)
.
Proof.
  split.
  - Ltac In_find_resolve_contr_hook Hx Hy ::= now (unfold ρf__call; rewrite Hx, Hy).
    option_boilerplate (List.find (fun x => vareq x new) ξ); option_boilerplate (List.find (fun x => vareq x cur) ξ);
    destruct 1; try In_find_resolve_contr; try now unfold ρf__call; rewrite Hx, Hx1.
  - option_boilerplate (List.find (fun x => vareq x new) ξ); option_boilerplate (List.find (fun x => vareq x cur) ξ);
    unfold ρf__call; intros H.
    + rewrite Hx, Hx1 in H; inv H. apply List.find_some in Hx as [Hy1 Hy2], Hx1 as [Hy3 Hy4].
      apply String.eqb_eq in Hy2, Hy4; subst.
      now constructor.
    + rewrite Hx, Hx1 in H; inv H. eapply List.find_some in Hx as [Hy1 Hy2].
      eapply String.eqb_eq in Hy2; subst.
      constructor; eauto. intros H.
      apply (List.find_none _ _ Hx1) in H. apply String.eqb_neq in H; contradiction.
    + rewrite Hx, Hx0 in H; inv H. apply List.find_some in Hx0 as [Hy1 Hy2].
      eapply String.eqb_eq in Hy2; subst.
      constructor; eauto; intros H.
      apply (List.find_none _ _ Hx) in H. apply String.eqb_neq in H; contradiction.
    + rewrite Hx, Hx0 in H; inv H.
      constructor 4; intros H.
      apply (List.find_none _ _ Hx) in H; apply String.eqb_neq in H; contradiction.
      apply (List.find_none _ _ Hx0) in H; apply String.eqb_neq in H; contradiction.
Qed.

Inductive ρ__ret : comms -> fnoerr -> option event -> Prop :=
| comm_ret_ctxtocomp : forall f,
    ρ__ret Qctxtocomp f (Some(Sret Qctxtocomp f))
| comm_ret_comptoctx : forall f,
    ρ__ret Qcomptoctx f (Some(Sret Qcomptoctx f))
| comm_ret_internal : forall f,
    ρ__ret Qinternal f None
.
Definition ρf__ret (a : comms) (b : fnoerr) : option event :=
  match a with
  | Qctxtocomp | Qcomptoctx => Some(Sret a b)
  | _ => None
  end
.
Lemma ρ__ret_equiv_ρf__ret (a : comms) (b : fnoerr) (c : option event) :
  ρ__ret a b c <-> ρf__ret a b = c
.
Proof.
  split.
  - now destruct 1.
  - destruct a; cbn; inversion 1; auto using comm_ret_ctxtocomp, comm_ret_comptoctx, comm_ret_internal.
Qed.
Inductive estep : CtxStep :=
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
| E_call_main : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (H : heap) (Δ : store)
                  (e__foo : expr) (x__arg : vart),
    Some (x__arg, (Tectx(Tarrow Tℕ Tℕ)), e__foo) = mget Ξ "main"%string ->
    (F ; Ξ ; ξ ; List.nil ; H ; Δ ▷ insert Khole (Xcall "main"%string 0) ==[ Sstart ]==> F ; Ξ ; ξ ; (Khole, "main"%string, Qctxtocomp) :: List.nil ; H ; Δ ▷ Xreturn (subst x__arg e__foo 0))
| E_call : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H : heap) (Δ : store)
             (E E__K : evalctx) (e__foo : expr) (τ__foo : Ty) f (x__arg foo foo__K : vart) (q q__K : comms) (a : option event),
    Some (x__arg, τ__foo, e__foo) = mget Ξ foo ->
    ρ__call ξ foo foo__K f a q ->
    (F ; Ξ ; ξ ; (E__K, foo__K, q__K) :: K ; H ; Δ ▷ insert E (Xcall foo f) ==[, a ]==> F ; Ξ ; ξ ; (E, foo, q) :: (E__K, foo__K, q__K) :: K ; H ; Δ ▷ Xreturn (subst x__arg e__foo f))
| E_ret : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H : heap) (Δ : store)
            (E E' : evalctx) (foo : vart) (q : comms) f (a : option event),
    ρ__ret q f a ->
    K <> List.nil ->
    (F ; Ξ ; ξ ; (E, foo, q) :: K ; H ; Δ ▷ insert E' (Xreturn f) ==[, a ]==> F ; Ξ ; ξ ; K ; H ; Δ ▷ insert E f)
| E_ret_end : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : active_ectx) (H : heap) (Δ : store) f (E : evalctx),
    (F ; Ξ ; ξ ; (Khole, "main"%string, Qcomptoctx) :: List.nil ; H ; Δ ▷ insert E (Xreturn (Fval f)) ==[ Send f ]==> F ; Ξ ; ξ ; List.nil ; H ; Δ ▷ f)
.
#[global]
Existing Instance estep.
#[global]
Hint Constructors estep : core.

Lemma estep_is_nodupinv_invariant Ω e Ω' e' a :
  Ω ▷ e ==[, a ]==> Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  assert (Some Ω = let (oΩ, e) := Ω ▷ e in oΩ) by easy;
  assert (Some Ω' = let (oΩ', e') := Ω' ▷ e' in oΩ') by easy;
  induction 1; try (inv H; inv H0; easy);
  inv H; inv H0; intros H0; apply pstep_is_nodupinv_invariant in H4; eauto.
Qed.
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
    let '(F, Ξ, ξ, Ks', H, Δ) := Ω in
    match mget Ξ foo with
    | None => None
    | Some (argx, τ__arg, e__foo) =>
      match Ks' with
      | List.nil =>
        if vareq foo "main"%string then
          Some(Some Sstart, (F ; Ξ ; ξ ; (Khole, "main"%string, Qctxtocomp) :: List.nil ; H ; Δ ▷ (Xreturn (subst argx e__foo 0))))
        else
          None
      | (K__bar, bar, q) :: Ks =>
        match ρf__call ξ foo bar f with
        | (a, q') =>
          Some(a, (F ; Ξ ; ξ ; ((K, foo, q') :: (K__bar, bar, q) :: Ks) ; H ; Δ ▷ (Xreturn (subst argx e__foo f))))
        end
      end
    end
  | Xreturn(Xres(Fres f)) =>
    let '(F, Ξ, ξ, Ks', H, Δ) := Ω in
    match Ks' with
    | nil => None
    | (Khole, "main"%string, Qctxtocomp) :: List.nil =>
      match f with
      | Fval(v) => Some(Some(Send v), F ; Ξ ; ξ ; List.nil ; H ; Δ ▷ f)
      | _ => None
      end
    | (K__foo, _foo, q) :: Ks =>
      let a := ρf__ret q f in
      Some(a, F ; Ξ ; ξ ; Ks ; H ; Δ ▷ insert K__foo f)
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
  (* FIXME: This proof is broken *)
  (*
  split.
  - induction 1.
    + (* ret *)
      unfold estepf.
      rewrite (get_rid_of_letstar (F, Ξ, E__foo :: ξ, H, Δ)).
      rewrite elim_ectx_ret.
      now rewrite (get_rid_of_letstar (E, Xreturn f)).
    + (* call *)
      unfold estepf.
      rewrite (get_rid_of_letstar (F, Ξ, ξ, H, Δ)).
      rewrite elim_ectx_call.
      rewrite (get_rid_of_letstar (E, Xcall foo f)).
      change ((fun o => (
        match o with
        | Some (argx0, _, e__foo0) =>
            Some (Some (Scall foo f), (Some (F, Ξ, E :: ξ, H, Δ), Xreturn (subst argx0 e__foo0 f)))
        | None => None
        end = Some (Some (Scall foo f), (Some (F, Ξ, E :: ξ, H, Δ), Xreturn (subst argx e__foo f)))
      )) (mget Ξ foo)).
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
          apply (not_eq_None_Some) in Hx as [[[x__arg τ__int] e__foo] Hx].
           rewrite Hx in H1. inv H1.
           eapply ungrab_ectx in Hx0; try rewrite Hx0; eauto.
           eapply E_call; symmetry; eassumption.
        -- destruct Ω as [[[[F Ξ] ξ] H] Δ].
           destruct (option_dec (mget Ξ foo)) as [Hx|Hy]; try (rewrite Hy in H1; congruence).
           apply (not_eq_None_Some) in Hx as [[[x__arg τ__int] e__foo] Hx].
           rewrite Hx in H1. inv H1.
           eapply ungrab_ectx in Hx0; subst; eauto.
           eapply E_call; symmetry; eassumption.
  *)
Admitted.

Lemma estepf_is_nodupinv_invariant Ω e Ω' e' a :
  estepf (Ω ▷ e) = Some(a, Ω' ▷ e') ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof. intros H0 H1; apply equiv_estep in H0; apply estep_is_nodupinv_invariant in H0; eauto. Qed.

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
  Definition is_stuck := fun (r : rtexpr) => match r with
                                          | (None, _) => True
                                          | _ => False
                                          end.
End ModAux.
Module SMod := CSC.Langs.Util.Mod(ModAux).
Import SMod.

Lemma different_reduction Ω Ω' e v v' As :
  ((Ω ▷ e ==[As]==>* Ω' ▷ v) -> False) ->
  Ω ▷ e ==[As]==>* Ω' ▷ v' ->
  v <> v'
.
Proof.
  intros H0 H1 H2; now subst.
Qed.

Lemma star_step_is_nodupinv_invariant Ω e Ω' e' As :
  Ω ▷ e ==[ As ]==>* Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  assert (Some Ω = let (oΩ, e) := Ω ▷ e in oΩ) by easy;
  assert (Some Ω' = let (oΩ', e') := Ω' ▷ e' in oΩ') by easy.
  intros H__star; dependent induction H__star; try (inv H; inv H0; easy); try easy.
  - destruct r2 as [[Ω2|] e2]; try (cbn in H0; contradiction); intros H__x;
    eapply estep_is_nodupinv_invariant in H; eauto.
  - destruct r2 as [[Ω2|] e2]; try (cbn in H0; contradiction); intros H__x;
    eapply estep_is_nodupinv_invariant in H; eauto.
Qed.

(** Qualification to mark whether we go from context to component or vice versa *)
Variant Qcall : Type :=
| ctx_to_comp : Qcall
| comp_to_ctx : Qcall
.
Definition Qcalleq (q1 q2 : Qcall) : bool :=
  match q1, q2 with
  | ctx_to_comp, ctx_to_comp => true
  | comp_to_ctx, comp_to_ctx => true
  | _, _ => false
  end
.
(** Types of events that may occur in a trace. *)
Variant fevent : Type :=
| Sfalloc (ℓ : loc) (n : nat) : fevent
| Sfdealloc (ℓ : loc) : fevent
| Sfget (ℓ : loc) (n : nat) : fevent
| Sfset (ℓ : loc) (n : nat) (v : value) : fevent
| Sfcrash : fevent
| Sfcall (q : Qcall) (foo : vart) (arg : fnoerr) : fevent
| Sfret (q : Qcall) (f : fnoerr) : fevent
.
Definition feventeq (e1 e2 : fevent) : bool :=
  match e1, e2 with
  | Sfalloc(addr ℓ0) n0, Sfalloc(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sfdealloc(addr ℓ0), Sfdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Sfget(addr ℓ0) n0, Sfget(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sfset(addr ℓ0) n0 (Vnat v0), Sfset(addr ℓ1) n1 (Vnat v1) => andb (andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1))
                                                                  (Nat.eqb v0 v1)
  | Sfcrash, Sfcrash => true
  | Sfcall q1 foo (Fval(Vnat v0)), Sfcall q2 bar (Fval(Vnat v1)) => andb (andb (String.eqb foo bar) (Nat.eqb v0 v1)) (Qcalleq q1 q2)
  | Sfcall q1 foo (Fvar x), Sfcall q2 bar (Fvar y) => andb (andb (String.eqb foo bar) (String.eqb x y)) (Qcalleq q1 q2)
  | Sfret q1 (Fval(Vnat v0)), Sfret q2 (Fval(Vnat v1)) => andb (Nat.eqb v0 v1) (Qcalleq q1 q2)
  | Sfret q1 (Fvar x), Sfret q2 (Fvar y) => andb (String.eqb x y) (Qcalleq q1 q2)
  | _, _ => false
  end
.
#[local]
Instance FEvent__Instance : TraceEvent fevent := {}.
(** Pretty-printing function for better debuggability *)
Definition string_of_fevent (e : fevent) := ""%string.

(** Functional style version of star step from above. We need another parameter "fuel" to sidestep termination. *)
Definition star_stepf (fuel : nat) (r : rtexpr) : option (tracepref * rtexpr) :=
  let fix doo (fuel : nat) (r : rtexpr) :=
    let (oΩ, e) := r in
    let* Ω := oΩ in
    match fuel, e with
    | 0, Xres(Fres _) => (* refl *)
      Some(nil, r)
    | S fuel', _ => (* trans *)
      let* (a, r') := estepf r in
      let* (As, r'') := doo fuel' r' in
      match a with
      | None => Some(As, r'')
      | Some(a') => Some(a' :: As, r'')
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
  star_stepf (S fuel) (Ω ▷ e) = Some(a :: As, r')
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
fix doo (fuel : nat) (r : rtexpr) {struct fuel} : option (list event * rtexpr) :=
            let (oΩ, e) := r in
            let* _ := oΩ
            in match fuel with
               | 0 => match e with
                      | Xres(Fres _) => Some (nil, r)
                      | _ => None
                      end
               | S fuel' =>
                   let* (a, r') := estepf r
                   in let* (As, r'') := doo fuel' r'
                      in match a with
                         | Some a' => Some (a' :: As, r'')
                         | None => Some (As, r'')
                         end
               end
                ) fuel (Ω', e'))) as [Hx0|Hy0]; try rewrite Hy0 in H.
      2: inv H.
      apply not_eq_None_Some in Hx0 as [[As0 r1'] Hx0].
      rewrite Hx0 in H.
      rewrite (get_rid_of_letstar (As0, r1')) in H.
      rewrite <- equiv_estep in Hx;
      destruct a as [a|]; inv H.
      * eapply ES_trans_important; eauto;
        destruct Ω' as [Ω'|]; try now cbn.
        1,3: destruct fuel; inv Hx0.
        apply (fuel_step Hf) in Hx.
        eapply IHfuel; eauto.
      * eapply ES_trans_unimportant; eauto;
        destruct Ω' as [Ω'|]; try now cbn.
        apply (fuel_step Hf) in Hx.
        eapply IHfuel; eauto. 
Qed.

Lemma star_stepf_is_nodupinv_invariant Ω e Ω' e' a fuel :
  Some fuel = get_fuel e ->
  star_stepf fuel (Ω ▷ e) = Some(a, Ω' ▷ e') ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof. intros H__fuel H0 H1; apply equiv_starstep in H0; eauto; apply star_step_is_nodupinv_invariant in H0; eauto. Qed.

(** Evaluation of programs *)
Inductive wstep : prog -> tracepref -> rtexpr -> Prop :=
| e_wprog : forall (symbs : symbols) (ξ : commlib) (As : tracepref) (r : rtexpr),
    prog_check (Cprog symbs ξ) ->
    (Fresh.empty_fresh ; symbs ; ξ ; nil ; hNil ; sNil ▷ Xcall "main"%string 0 ==[ As ]==>* r) ->
    wstep (Cprog symbs ξ) As r
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
Fixpoint get_fuel_fn (e : expr) : option nat :=
  match e with
  | Xres _ => Some 0
  | Xabort | Xdel _ => Some 1
  | Xbinop b e1 e2 =>
    let* f1 := get_fuel_fn e1 in
    let* f2 := get_fuel_fn e2 in
    Some (f1 + f2 + 1)
  | Xget x e' =>
    let* f := get_fuel_fn e' in
    Some (f + 1)
  | Xset x e1 e2 =>
    let* f1 := get_fuel_fn e1 in
    let* f2 := get_fuel_fn e2 in
    Some (f1 + f2 + 1)
  | Xlet x e1 e2 =>
    let* f1 := get_fuel_fn e1 in
    let* f2 := get_fuel_fn e2 in
    Some (f1 + f2 + 1)
  | Xnew x e1 e2 =>
    let* f1 := get_fuel_fn e1 in
    let* f2 := get_fuel_fn e2 in
    Some (f1 + f2 + 1)
  | Xifz e0 e1 e2 =>
    let* f0 := get_fuel_fn e0 in
    let* f1 := get_fuel_fn e1 in
    let* f2 := get_fuel_fn e2 in
    Some (f0 + f1 + f2 + 1)
  | Xreturn e' =>
    let* f := get_fuel_fn e' in
    Some (f + 1)
  | Xcall foo e' =>
    let* f := get_fuel_fn e' in
    Some (f + 1)
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
  | _ => Some(mapNil _ _)
  end
.
(** Compute the total amount of fuel necessary to run a complete program. Each context corresponding to a call
    artificially gets a return in the semantics (estep), so add 1.
    Also, add 1 to the final result, because the top-level performs a call to "main". *)
Definition get_fuel_toplevel (ξ : symbols) (foo : vart) : option nat :=
  let* Kτ := mget ξ foo in
  let '(x__arg,_,e__arg) := Kτ in
  let e := subst x__arg e__arg (Xres 0) in
  let* ge := get_fuel e in
  let* symbs := collect_callsites ξ e in
  let* res := List.fold_left (fun acc Eτ =>
                                let '(_,_,e__arg) := Eτ in
                                let* a := acc in
                                let* b := get_fuel_fn e__arg in
                                Some(1 + a + b)) (img symbs) (Some ge) in
  Some(S res)
.

Definition wstepf (p : prog) : option (tracepref * rtexpr) :=
  let '(Cprog symbs ξ) := p in
  let e := Xcall "main"%string 0 in
  let* fuel := get_fuel_toplevel symbs "main"%string in
  let R := Fresh.empty_fresh ; symbs ; ξ ; nil ; hNil ; sNil ▷ e in
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
Definition smsunsafe_ep : expr :=
  Xnew "z"%string
      (Fvar "y"%string)
      (Xlet "w"%string
            (Xget "z"%string 1337)
            (Xlet "_1"%string
                  (Xdel "z"%string)
                  (Fvar "w"%string))
      )
.
(* let x = 3 in call foo x *)
Definition smsunsafe_ctx : expr :=
  Xreturn (Xlet ("_0"%string)
    (Fvar "arg"%string)
    (Xlet ("x"%string)
          3
          (Xcall ("foo"%string) (Fvar "x"%string))))
.

Definition smsunsafe_prog_aux : symbols :=
  ("foo"%string ↦ ("y"%string, Tectx(Tarrow Tℕ Tℕ), smsunsafe_ep) ◘
  ("main"%string ↦ ("arg"%string, Tectx(Tarrow Tℕ Tℕ), smsunsafe_ctx) ◘ mapNil _ _)).
Definition smsunsafe_prog := Cprog smsunsafe_prog_aux ("foo"%string :: List.nil).

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
  induction Γ1; cbn; intros H1 H2; trivial; destruct H1 as [H1__a H1__b]; auto.
Qed.
Lemma ownedptrcons x y Γ2 : NoOwnedPtr (x ↦ y ◘ [⋅]) -> NoOwnedPtr Γ2 -> NoOwnedPtr (x ↦ y ◘ Γ2).
Proof.
  intros [H1__a H1__b] H2; split; auto.
Qed.

Lemma smsunsafe_prog_checks : prog_check smsunsafe_prog.
Proof.
  (*
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
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a. destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; inv H0. easy.
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
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a; destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1. destruct x; inv H0; easy.
    eapply CTcall. eapply intℕ. eapply intℕ.
    splitΓfor. eapply CTvar; try easy.
    unfold NoOwnedPtr. intros. destruct x; cbn in H; inv H. destruct a.
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a. destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy. easy.
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
    destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0.
    destruct a. destruct b, b0, b1, b2, b3, b4, b5, b6; inv H1; destruct x; inv H0; easy.
    *)
Admitted.

Goal exists As R,
    wstep smsunsafe_prog As R.
Proof.
  (*
  do 2 eexists.
  econstructor; try exact smsunsafe_prog_checks.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  econstructor 3. rewrite equiv_estep; now cbn. now cbn.
  econstructor 3. rewrite equiv_estep; now cbn. now cbn.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  econstructor 3. rewrite equiv_estep; now cbn. now cbn.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  econstructor 3. rewrite equiv_estep; now cbn. now cbn.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  econstructor 3. rewrite equiv_estep; now cbn. now cbn.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  econstructor 2. rewrite equiv_estep; now cbn. now cbn.
  now econstructor. *)
Admitted.

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
  Definition is_value := fun (_ : State) => true.
  Definition is_stuck := fun (_ : State) => False.
End MSModAux.
Module SMSMod := CSC.Langs.Util.Mod(MSModAux).

Definition msev_of_ev (ev : event) : option msevent :=
  match ev with
  | Sstart | Send _ => None
  | Salloc ℓ n => Some(MSalloc ℓ n)
  | Sdealloc ℓ => Some(MSdealloc ℓ)
  | Sget ℓ n => Some(MSuse ℓ n)
  | Sset ℓ n _ => Some(MSuse ℓ n)
  | Scrash => Some(MScrash)
  | Scall _ _ _ => None
  | Sret _ _ => None
  end
.
Fixpoint mstracepref_of_tracepref (tr : tracepref) : SMSMod.tracepref :=
  match tr with
  | nil => nil 
  | a :: tr' =>
    match msev_of_ev a with
    | Some a' => a' :: (mstracepref_of_tracepref tr')
    | None => mstracepref_of_tracepref tr'
    end
  end
.

Module TMMon := CSC.Langs.TMMon.
Module TMMonM := TMMon.TMSMod.

Definition deltamap := mapind loceq__Instance TMMon.loc.

Lemma snodupinv_implies_δnodupinv Δ :
  snodupinv Δ ->
  Util.nodupinv (δ_of_Δ Δ)
.
Proof. induction 1; try constructor; destruct ℓ; constructor; trivial. Qed.

(** Trace agreement between memory specific events and TMS monitor events. *)
Inductive ev_eq (δ : deltamap) : option msevent -> option TMMon.event -> Prop :=
| TMSAuthAlloc : forall ℓ ℓ' n, Util.nodupinv δ -> mget δ ℓ = Some ℓ' -> ev_eq δ (Some(MSalloc ℓ n)) (Some(TMMon.Salloc ℓ'))
| TMSAuthDealloc : forall ℓ ℓ', Util.nodupinv δ -> mget δ ℓ = Some ℓ' -> ev_eq δ (Some(MSdealloc ℓ)) (Some(TMMon.Sdealloc ℓ'))
| TMSAuthUse : forall ℓ ℓ' n, Util.nodupinv δ -> mget δ ℓ = Some ℓ' -> ev_eq δ (Some(MSuse ℓ n)) (Some(TMMon.Suse ℓ'))
| TMSAuthNone : Util.nodupinv δ -> ev_eq δ (None) (None)
.
Inductive mstracepref_eq (δ : deltamap) : SMSMod.tracepref -> TMMonM.tracepref -> Prop :=
| TMSAuthRefl : Util.nodupinv δ -> mstracepref_eq δ nil nil
| TMSAuthTrans : forall a a' As As', ev_eq δ (Some a) (Some a') ->
                                mstracepref_eq δ As As' ->
                                mstracepref_eq δ (a :: As) (a' :: As')
.

Import TMMon.TMMonNotation.
(** Store agreement between our stores and the TMS monitor. *)
Inductive store_agree (δ : deltamap) : TMMon.TMSMonitor -> store -> Prop :=
| EmptyAgree : Util.nodupinv δ -> store_agree δ TMMon.emptytmsmon sNil
| ConsAgree : forall (x : vart) (ℓ : loc) (ℓ' : TMMon.loc) (T__TMS : TMMon.TMSMonitor) (Δ : store),
    Util.nodupinv δ ->
    mget δ ℓ = Some ℓ' ->
    ℓ' ∉ T__TMS ->
    store_agree δ T__TMS Δ ->
    store_agree δ ({ℓ'} ∪ T__TMS) (x ↦ (ℓ ⋅ ◻) ◘ Δ)
| PoisonAgree : forall (x : vart) (ℓ : loc) (ℓ' : TMMon.loc) (T__TMS : TMMon.TMSMonitor) (Δ : store),
    Util.nodupinv δ ->
    mget δ ℓ = Some ℓ' ->
    store_agree δ T__TMS Δ ->
    store_agree δ T__TMS (x ↦ (ℓ ⋅ ☣) ◘ Δ)
.
Inductive state_agree (δ : deltamap) : TMMon.TMSMonitor -> state -> Prop :=
| StateAgree : forall F Ξ ξ K H Δ T__TMS, store_agree δ T__TMS Δ -> state_agree δ T__TMS (F ; Ξ ; ξ ; K ; H ; Δ)
.

Definition TMS (As : tracepref) :=
  forall MAs : SMSMod.tracepref, MAs = mstracepref_of_tracepref As ->
                            exists δ (Bs : TMMonM.tracepref), mstracepref_eq δ MAs Bs /\
                                                         TMMon.TMS Bs
.

Lemma pstep_preservation Ω e τ Ω' e' a :
  rt_check Ω e τ ->
  Ω ▷ e --[, a ]--> Ω' ▷ e' ->
  rt_check Ω' e' τ
.
Proof. Admitted.
Lemma estep_preservation Ω e τ Ω' e' a :
  rt_check Ω e τ ->
  Ω ▷ e ==[, a ]==> Ω' ▷ e' ->
  rt_check Ω' e' τ
.
Proof. Admitted.

Lemma δ_of_Δ_poison_eq (Δ1 Δ2 : store) (x : vart) (ℓ : loc) :
  δ_of_Δ (Δ1 ◘ x ↦ (ℓ, ◻) ◘ Δ2) = δ_of_Δ (Δ1 ◘ x ↦ (ℓ, ☣) ◘ Δ2)
.
Proof.
  induction Δ1; cbn; eauto; destruct b as [[] _]; fold (append Δ1 (x ↦ (ℓ, ◻) ◘ Δ2));
  fold (append Δ1 (x ↦ (ℓ, ☣) ◘ Δ2)); now f_equal.
Qed.

Lemma store_agree_split T__TMS Δ1 x ℓ ρ Δ2 δ :
  store_agree δ T__TMS (Δ1 ◘ x ↦ (addr ℓ, ρ) ◘ Δ2) ->
  exists T__TMS1 T__TMS2 ℓ', store_agree δ T__TMS1 Δ1 /\
                    store_agree δ T__TMS2 Δ2 /\
                    store_agree δ ({ℓ'} ∪ (TMMon.emptytmsmon)) (x ↦ (addr ℓ, ρ) ◘ sNil) /\
                    T__TMS = TMMon.append T__TMS1 (TMMon.append ({ℓ'} ∪ TMMon.emptytmsmon) T__TMS2)
.
Proof.
  induction Δ1; intros H; cbn in *.
  - exists TMMon.emptytmsmon. exists T__TMS. exists (TMMon.addr ℓ).
Admitted.

Lemma store_agree_rsplit T__TMS1 T__TMS2 Δ1 Δ2 δ:
  store_agree δ T__TMS1 Δ1 ->
  store_agree δ T__TMS2 Δ2 ->
  store_agree δ (TMMon.append T__TMS1 T__TMS2) (Δ1 ◘ Δ2)
.
Proof.
Admitted.

Lemma store_split_poisoned Ξ Δ1 x ℓ Δ2 Γ :
  store_split Ξ (Δ1 ◘ x ↦ (addr ℓ, ☣) ◘ Δ2) Γ ->
  store_split Ξ (Δ1 ◘ Δ2) Γ /\ (~ List.In x (dom Γ))
.
Proof. Admitted.
Lemma store_agree_subsets δ δ' T__TMS Δ :
  store_agree δ T__TMS Δ ->
  MSubset δ δ' ->
  store_agree δ' T__TMS Δ
.
Proof.
  induction 1; cbn; intros Ha; eauto. constructor.
Admitted.
Lemma store_agree_notin_propagates ℓ (Δ : store) T__TMS :
  ~ In (addr ℓ) (dom(δ_of_Δ Δ)) ->
  store_agree (δ_of_Δ Δ) T__TMS Δ ->
  TMMon.addr(ℓ) ∉ T__TMS
.
Proof. Admitted.

Lemma base_tms_via_monitor (Ω Ω' : state) (e e' : expr) (τ : Ty) (a : event)
                           (T__TMS : TMMon.TMSMonitor) (δ : deltamap) :
  rt_check Ω e τ ->
  (Ω ▷ e --[ a ]--> Ω' ▷ e') ->
  state_agree δ T__TMS Ω ->
  δ = δ_of_Δ (let '(_,_,_,_,Δ) := Ω in Δ) ->
  exists (b : TMMon.event) (δ' : deltamap) (T__TMS' : TMMon.TMSMonitor),
    MSubset δ δ'
  /\ ev_eq δ' (msev_of_ev a) (Some b)
  /\ (TMMon.step T__TMS (Some b) T__TMS')
  /\ state_agree δ' T__TMS' Ω'
  /\ (δ' = δ_of_Δ (let '(_,_,_,_,Δ) := Ω' in Δ))
.
Proof.
  (*FIXME: proof is broken*)
  (*
  intros Aa Ab Ac Ad. inv Ab.
  - inv Ac. assert (H3':=H3); apply store_agree_split in H3 as [T__TMS1 [T__TMS2 [ℓ__TMS [Ac1 [Ac2 [Ac3 Ac4]]]]]].
    exists (TMMon.Suse ℓ__TMS). exists (δ_of_Δ(Δ1 ◘ x ↦ (addr ℓ, ρ) ◘ Δ2)). exists T__TMS; repeat split; try easy; try now constructor.
    cbn. inv Ac3; eauto.  constructor; eauto. constructor; eauto. inv H7.
    constructor; eauto. inv Ac4; easy.
  - inv Ac. assert (H3':=H3); apply store_agree_split in H3 as [T__TMS1 [T__TMS2 [ℓ__TMS [Ac1 [Ac2 [Ac3 Ac4]]]]]].
    exists (TMMon.Suse ℓ__TMS). exists (δ_of_Δ(Δ1 ◘ x ↦ (addr ℓ, ρ) ◘ Δ2)). exists T__TMS; repeat split; try easy; try now constructor.
    cbn. inv Ac3; eauto.  constructor; eauto. constructor; eauto. inv H7.
    constructor; eauto. inv Ac4; easy.
  - inv Ac; assert (H3':=H3); apply store_agree_split in H3 as [T__TMS1 [T__TMS2 [ℓ__TMS [Ac1 [Ac2 [Ac3 Ac4]]]]]].
    exists (TMMon.Sdealloc ℓ__TMS). exists (δ_of_Δ(Δ1 ◘ x ↦ (addr ℓ, ρ) ◘ Δ2)).
    inv Ac3.
    + (* Rule Cons-Agree *)
      exists (TMMon.append T__TMS1 T__TMS2); repeat split; try easy; try now econstructor.
      constructor; eauto using TMMon.remove_loc_from_union.
      cbn. apply store_agree_rsplit; eauto. econstructor; eauto. cbn.
      apply δ_of_Δ_poison_eq.
    + (* Rule Cons-Agree-Ignore *)
      inv Aa. inv H0. eapply store_split_poisoned in H12 as [H12a H12b].
      inv H1; exfalso; revert H12b; clear; intros H; apply H; clear H.
      induction Γ1; cbn; eauto.
  - remember (TMMon.addr(Fresh.fresh F)) as ℓ__TMS;
    remember (addr(Fresh.fresh F)) as ℓ.
    exists (TMMon.Salloc ℓ__TMS); exists (δ_of_Δ Δ'); exists ({ℓ__TMS} ∪ T__TMS); repeat split.
    + unfold spush in H9.
      change ((fun Δ__y : option store => match Δ__y with
                                     | Some Δ__y' => Some Δ__y'
                                     | None => None
                                     end = Some Δ') (sundup (freshv(advance F) ↦ (ℓ, ◻) ◘ Δ))) in H9.
      destruct (option_dec (sundup ((freshv(advance F)) ↦ (ℓ, ◻) ◘ Δ))) as [Hx|Hy].
      * apply not_eq_None_Some in Hx as [Δ__x Hx]. rewrite Hx in H9. inv H9.
        rewrite <- (sundup_refl (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ) Hx).
        rewrite <- (sundup_refl (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ) Hx) in Hx.
        apply snodupinv_equiv_sundup in Hx as Hx'; assert (Hx'':=Hx'). inv Hx'.
        remember (freshv(advance F)↦(addr(fresh F),◻)◘Δ) as Δ__s'.
        assert (Some Δ__s' = spush (freshv(advance F)) (addr(fresh F),◻) Δ).
        unfold spush. symmetry.
        change ((fun Δ__y : option store => match Δ__y with
                                      | Some Δ__y' => Some Δ__y'
                                      | None => None
                                      end = Some Δ__s') (sundup((freshv(advance F))↦(addr(fresh F), ◻) ◘ Δ))).
        rewrite HeqΔ__s' in Hx; rewrite Hx. now subst.
        eapply spush_msubset in H0. subst. now apply δΔ_msubset_invariant.
      * now rewrite Hy in H9.
    + inv H9. inv Ac. apply spush_ok in H1 as H1'.
      apply snodupinv_implies_δnodupinv in H1'.
      constructor; eauto.
      unfold spush in H1.
      destruct (option_dec (sundup (freshv(advance F) ↦ (addr (fresh F), ◻) ◘ Δ))) as [Hx|Hy].
      * apply not_eq_None_Some in Hx as [Δ__x Hx]. rewrite <- (sundup_refl _ Hx) in Hx.
        change ((fun Δ__y : option store => match Δ__y with
                                | Some Δ'0 => Some Δ'0
                                | None => None
                                end = Some Δ') (sundup (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ))) in H1.
        rewrite Hx in H1.
        inv H1. cbn. now rewrite Nat.eqb_refl.
      * change ((fun Δ__y : option store => match Δ__y with
                                       | Some Δ'0 => Some Δ'0
                                       | None => None
                                       end = Some Δ') (sundup (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ))) in H1.
        rewrite Hy in H1; congruence.
    + constructor; try easy. inv Ac. apply spush_ok in H9 as H9'.
      unfold spush in H9.
      destruct (option_dec (sundup (freshv(advance F) ↦ (addr (fresh F), ◻) ◘ Δ))) as [Hx|Hy].
      * apply not_eq_None_Some in Hx as [Δ__x Hx].
        change ((fun Δ__s : option store => match Δ__s with
                                       | Some Δ__t => Some Δ__t
                                       | None => None
                                       end = Some Δ') (sundup (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ))) in H9.
        rewrite Hx in H9. rewrite <- Hx in H9.
        rewrite <- (sundup_refl (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ)) in H9'; eauto.
        inv H9'. eauto using store_agree_notin_propagates.
      * change ((fun Δ__y : option store => match Δ__y with
                                       | Some Δ'0 => Some Δ'0
                                       | None => None
                                       end = Some Δ') (sundup (freshv(advance F) ↦ (addr(fresh F), ◻) ◘ Δ))) in H9.
        rewrite Hy in H9; congruence.
    + unfold spush in H9.
      change ((fun Δ'0 => match Δ'0 with
                      | Some Δ'1 => Some Δ'1
                      | None => None
                      end = Some Δ') (sundup (freshv (advance F) ↦ (ℓ, ◻) ◘ Δ))) in H9.
      destruct (option_dec (sundup (freshv (advance F) ↦ (ℓ, ◻) ◘ Δ))) as [Hx|Hy]; try (rewrite Hy in H9; cbn in H9; congruence).
      apply not_eq_None_Some in Hx as [Δ__x Hx].
      rewrite <- (sundup_refl (freshv (advance F) ↦ (ℓ, ◻) ◘ Δ) Hx) in Hx.
      rewrite Hx in H9. inv H9.
      econstructor; eauto.
      * apply snodupinv_equiv_sundup in Hx as Hx'; now apply snodupinv_implies_δnodupinv in Hx'.
      * cbn; now rewrite Nat.eqb_refl.
      * inv Ac. apply snodupinv_equiv_sundup in Hx. inv Hx. eauto using store_agree_notin_propagates.
      * inv Ac. cbn. eapply store_agree_subsets; try exact H3.
        eapply cons_msubset; symmetry.
        eapply snodupinv_equiv_sundup in Hx as Hx'; eapply snodupinv_implies_δnodupinv in Hx'.
        eapply push_ko; cbn in Hx'; inv Hx'; auto.
  *)
Admitted.

Lemma ctx_tms_via_monitor (Ω Ω' : state) (e e' : expr) (τ : Ty) (a : event)
                          (T__TMS : TMMon.TMSMonitor) (δ : deltamap) :
  rt_check Ω e τ ->
  (Ω ▷ e ==[ a ]==> Ω' ▷ e') ->
  state_agree δ T__TMS Ω ->
  δ = δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω in Δ) ->
  exists (b : option TMMon.event) (δ' : deltamap) (T__TMS' : TMMon.TMSMonitor),
     MSubset δ δ'
  /\ (ev_eq δ' (msev_of_ev a) b)
  /\ (TMMon.step T__TMS b T__TMS')
  /\ state_agree δ' T__TMS' Ω'
  /\ (δ' = δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω' in Δ))
.
Proof.
  intros Aa Ab Ac Ad.
  inv Ab.
  - eapply rt_check_recompose in Aa as [τ' [Aa0 Aa1]]. destruct Ω as [[[[[]]]]]. rename s0 into Δ.
    eapply base_tms_via_monitor in H7; eauto.
    deex. destruct H7 as [H7a [H7b [H7c [H7d H7e]]]].
    destruct Ω' as [[[[[]]]]]; rename s1 into Δ'.
    do 3 eexists; repeat split; subst; eauto.
    now inv H7d.
  - exists None. exists (δ_of_Δ Δ). exists T__TMS. repeat split; eauto; try easy. cbn. constructor. inv Ac. inv H4; easy. constructor. now inv Ac.
  - inv H6; exists None; exists (δ_of_Δ Δ); exists T__TMS; repeat split; eauto; try easy; cbn; try constructor.
    inv Ac. inv H5; easy. now inv Ac. inv Ac. inv H5; easy. now inv Ac.
  - inv H4; exists None; exists (δ_of_Δ Δ); exists T__TMS; repeat split; eauto; try easy; cbn; try constructor.
    inv Ac. inv H3; easy. now inv Ac. inv Ac. inv H3; easy. now inv Ac.
  - exists None. exists (δ_of_Δ Δ). exists T__TMS. repeat split; eauto; try easy. cbn. constructor. inv Ac. inv H3; easy. constructor. now inv Ac.
Qed.

Lemma ctx_tms_via_monitor_ignore (Ω Ω' : state) (e e' : expr) (τ : Ty)
                                 (T__TMS : TMMon.TMSMonitor) (δ : deltamap) :
  rt_check Ω e τ ->
  (Ω ▷ e ==[]==> Ω' ▷ e') ->
  state_agree δ T__TMS Ω ->
  δ = δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω in Δ) ->
  exists (δ' : deltamap) (T__TMS' : TMMon.TMSMonitor),
     MSubset δ δ'
  /\ (TMMon.step T__TMS None T__TMS')
  /\ state_agree δ' T__TMS' Ω'
  /\ (δ' = δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω' in Δ))
.
Proof.
  intros Aa Ab Ac Ad; destruct Ω as [[[[[]]]]]; rename s0 into Δ.
  exists (δ_of_Δ Δ). exists T__TMS. repeat split; subst; eauto; try easy. constructor.
  all: inv Ab; try inv H7; try easy.
  all: inv Ac; now constructor.
Qed.

Lemma steps_tms_via_monitor (Ω Ω' : state) (e e' : expr) (τ : Ty) (As : tracepref)
                          (T__TMS : TMMon.TMSMonitor) (δ : deltamap) :
  rt_check Ω e τ ->
  (Ω ▷ e ==[ As ]==>* Ω' ▷ e') ->
  state_agree δ T__TMS Ω ->
  δ = δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω in Δ) ->
  exists (Bs : TMMonM.tracepref) (δ' : deltamap) (T__TMS' : TMMon.TMSMonitor),
     MSubset δ δ'
  /\ (mstracepref_eq δ' (mstracepref_of_tracepref As) Bs)
  /\ (TMMonM.star_step T__TMS Bs T__TMS')
  /\ state_agree δ' T__TMS' Ω'
  /\ (δ' = δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω' in Δ))
.
Proof.
  intros Aa Ab; revert δ T__TMS; dependent induction Ab; intros δ T__TMS Ac Ad.
  - (* refl *)
    exists (nil). exists δ. exists T__TMS. repeat split; try easy; constructor; try easy. inv Ac. now inv H1.
  - (* trans *)
    destruct r2 as [[Ω2|] e2]; cbn in H0; try contradiction; clear H0.
    eapply estep_preservation in Aa as Aa'; eauto.
    eapply ctx_tms_via_monitor in Aa as Aa''; eauto; deex; try destruct Aa'' as [Ha [Hb [Hc [Hd He]]]].
    specialize (IHAb Ω2 Ω' e2 e' Aa' JMeq_refl JMeq_refl δ' T__TMS' Hd He).
    deex; rename T__TMS'0 into T__TMS''; rename δ'0 into δ''; destruct IHAb as [IHAb1 [IHAb2 [IHAb3 [IHAb4 IHAb5]]]].
    subst. destruct Ω as [[[[[]]]]]; rename s0 into Δ. destruct Ω' as [[[[[]]]]]; rename s1 into Δ'.
    destruct Ω2 as [[[[[]]]]]; rename s2 into Δ2.
    destruct a; cbn in Hb; inv Hb;
    match goal with
    | [H: TMMon.step ?T__TMS (Some(?ev)) ?T__TMS' |- _] =>
      exists (ev :: Bs); exists (δ_of_Δ Δ'); exists T__TMS''; repeat split; eauto;
     (try (etransitivity; eauto)); (try econstructor); eauto; (try econstructor); try eapply mget_subset; eauto
    | [H: TMMon.step ?T__TMS None ?T__TMS' |- _] =>
      exists Bs; exists (δ_of_Δ Δ'); exists T__TMS''; repeat split; eauto;
      (try econstructor); eauto; (try econstructor); try eapply mget_subset; eauto
    end;
    repeat match goal with
    | [H: state_agree ?δ _ _ |- Util.nodupinv ?δ] => inv H
    | [H: store_agree ?δ _ _ |- Util.nodupinv ?δ] => inv H; eauto
    | [H: store_agree ?δ _ _ |- state_agree ?δ _ _] => inv H; eauto
    end; (repeat now inv IHAb4); etransitivity; eauto.
  - (* unimp *)
    destruct r2 as [[Ω2|] e2]; cbn in H0; try contradiction; clear H0.
    eapply estep_preservation in Aa as Aa'; eauto.
    eapply ctx_tms_via_monitor_ignore in Aa as Aa''; eauto; deex; destruct Aa'' as [Ha [Hb [Hc Hd]]].
    specialize (IHAb Ω2 Ω' e2 e' Aa' JMeq_refl JMeq_refl δ' T__TMS' Hc Hd).
    destruct Ω as [[[[[]]]]]; rename s0 into Δ; destruct Ω2 as [[[[[]]]]]; rename s1 into Δ2.
    deex; rename T__TMS'0 into T__TMS''; rename δ'0 into δ''; destruct IHAb as [IHAb1 [IHAb2 [IHAb3 [IHAb4 IHAb5]]]].
    destruct Ω' as [[[[[]]]]]; rename s2 into Δ'; subst.
    exists Bs. exists (δ_of_Δ Δ'). exists T__TMS''. repeat split; eauto.
    + etransitivity; eauto.
    + econstructor; eauto; econstructor; eapply mget_subset; eauto.
    + now inv IHAb4.
Qed.

Lemma toplevel_check_weakening Ξ Γ foo τ0 τ1 bar τ0' τ1' x e__bar :
  interfaces (bar ↦ (x, Tectx(Tarrow τ0' τ1'), e__bar) ◘ Ξ) = Some Γ ->
  mget Γ foo = Some(Tectx(Tarrow τ0 τ1)) ->
  NoOwnedPtr Γ ->
  foo <> bar ->
  check (bar ↦ (Tectx(Tarrow τ0' τ1')) ◘ Γ) (Fvar foo) (Tarrow τ0 τ1) ->
  check Γ (Fvar foo) (Tarrow τ0 τ1)
.
Proof.
Admitted.

Theorem s_is_tms (Ξ : symbols) (ξ : commlib) As Ω f :
  wstep (Cprog Ξ ξ) As (Ω ▷ (Xres f)) ->
  TMS As.
Proof.
  intros Ha; inv Ha; unfold prog_check in H1.
  destruct (option_dec (interfaces Ξ)) as [Hx|Hx]; try (rewrite Hx in H0; contradiction).
  apply not_eq_None_Some in Hx as [x__x Hx]; rewrite Hx in H1.
  remember (Fresh.empty_fresh ; Ξ ; nil ; nil ; hNil ; sNil) as Ω__init; pose ((mapNil _ _) : deltamap) as δ__init.
  assert (state_agree (mapNil _ _) TMMon.emptytmsmon Ω__init) by (subst; repeat constructor).
  assert (δ__init= δ_of_Δ (let '(_,_,_,_,_,Δ) := Ω__init in Δ)) by (subst; cbn; easy).
  subst. eapply steps_tms_via_monitor in H4; eauto.
  deex; destruct H4 as [F__a [F__b [F__c [F__d F__e]]]].
  intros MAs H__As. exists δ'. exists Bs. split; subst. exact F__b.
  unfold TMMon.TMS. exists T__TMS'; try eexact F__c.
  econstructor. repeat constructor. exact Hx.
  econstructor. instantiate (1:=Tℕ); constructor.
  instantiate (1:=Tℕ); constructor.
  shelve.
  constructor.
  option_boilerplate (mget x__x "main"%string); rewrite Hx0 in H1; try easy.
  destruct x; try easy; destruct e; try easy; destruct t, t0; try easy.
  crush_noownedptrf x__x. now apply noownedptr_equiv_noownedptrf.
  now rewrite Hx2 in H1. constructor; now inv H.
  now rewrite Hx in H1.
  Unshelve.
  option_boilerplate (mget x__x "main"%string); rewrite Hx0 in H1; try easy.
  destruct x; try easy; destruct e; try easy; destruct t, t0; try easy.
  crush_noownedptrf x__x; try now rewrite Hx2 in H1.
  clear H H4 H0 Hx1 δ__init; revert x__x H1 Hx Hx0 Hx2; induction Ξ; intros.
  - inv Hx; inv Hx0.
  - destruct b; destruct p. destruct t; try inv H1. destruct e0. destruct H1 as [H1__a [H1__b [H1__c H1__d]]].
    destruct (eq_dec a "main"%string).
    + subst. cbn in Hx.
      option_boilerplate (interfaces Ξ); rewrite Hx1 in Hx; try easy.
      inv Hx. change (check (mapNil _ _ ◘ "main"%string ↦ Tectx(Tarrow t t0) ◘ x0) (Fvar "main"%string) (Tectx(Tarrow Tℕ Tℕ))).
      cbn in Hx0; inv Hx0. eapply CTvar.
      admit.
      easy. easy. apply noownedptr_equiv_noownedptrf in Hx2.
      change (NoOwnedPtr ("main"%string ↦ Tectx(Tarrow Tℕ Tℕ) ◘ mapNil _ _ ◘ x0)) in Hx2.
      now apply noownedptr_split in Hx2 as [Hx2__a Hx2__b].
    + (*indu is bonkers*) admit.
Admitted.
