Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef Lia.

Require Import CSC.Shared.Sema CSC.Shared.Fresh CSC.Util.Sets CSC.Shared.Fresh CSC.Shared.Props.
Require Import CSC.Util.HasEquality CSC.Util.Convenience CSC.Util.NoDupInv.

From RecordUpdate Require Import RecordSet.

(** These are the locs from the L³ paper by Ahmed, Fluet, and Morrisett *)
Inductive Loc : Type :=
| LConst : loc -> vart -> Loc
| LVar : vart -> Loc
.
Definition Loc_eqb (l1 l2 : Loc) : bool :=
  match l1, l2 with
  | LConst l1 v1, LConst l2 v2 => andb (l1 == l2) (v1 == v2)
  | LVar v1, LVar v2 => (v1 == v2)
  | _, _ => false
  end
.
Lemma Loc_eqb_eq l0 l1 :
  Loc_eqb l0 l1 = true <-> l0 = l1.
Proof.
  split; intros H; destruct l0, l1; cbn in *; try easy;
  try ((change ((l == l0) = true) in H + change ((v == v0) = true) in H);
       apply eqb_eq in H; subst; easy).
  eq_to_defeq vareq; eq_to_defeq loc_eqb.
  inv H; eq_to_defeq loc_eqb. split; eauto. eq_to_defeq vareq.
  inv H; eq_to_defeq vareq.
Qed.
#[export]
Instance Loceq__Instance : HasEquality Loc := {
  eq := Loc_eqb ;
  eqb_eq := Loc_eqb_eq ;
}.
(** Values are numbers, pairs, capabilities, and pointers *)
Inductive value : Type :=
| Vnat : nat -> value
| Vpair : value -> value -> value
| Vcap : value
| Vptr : loc -> vart -> value
| Vpack : Loc -> value -> value
.
Coercion Vnat : nat >-> value.
Fixpoint value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Vnat n1, Vnat n2 => Nat.eqb n1 n2
  | Vpair v0 v1, Vpair v0' v1' => andb (value_eqb v0 v0') (value_eqb v1 v1')
  | Vcap, Vcap => true
  | Vptr l0 x0, Vptr l1 x1 => andb (l0 == l1) (x0 == x1)
  | Vpack l0 v0, Vpack l1 v1 => andb (l0 == l1) (value_eqb v0 v1)
  | _, _ => false
  end
.
Lemma value_eqb_eq v1 v2 :
  value_eqb v1 v2 = true <-> v1 = v2.
Proof.
  revert v2; induction v1; cbn; split; intros.
  - destruct v2; try easy. apply Nat.eqb_eq in H; inv H; reflexivity.
  - destruct v2; inv H; apply Nat.eqb_refl.
  - destruct v2; inv H. eq_to_defeq value_eqb. apply IHv1_1 in H; apply IHv1_2 in H0.
    subst. reflexivity.
  - inv H; cbn. eq_to_defeq value_eqb; split. now apply IHv1_1. now apply IHv1_2.
  - destruct v2; inv H. reflexivity.
  - destruct v2; inv H. reflexivity.
  - destruct v2; inv H; eq_to_defeq loc_eqb. eq_to_defeq vareq.
  - destruct v2; inv H; eq_to_defeq loc_eqb. split; eq_to_defeq vareq.
  - destruct v2; inv H; eq_to_defeq Loc_eqb. apply IHv1 in H0; subst. reflexivity.
  - destruct v2; inv H; eq_to_defeq Loc_eqb; split; try easy. now apply IHv1.
Qed.
#[export]
Instance valueeq__Instance : HasEquality value := {
  eq := value_eqb ;
  eqb_eq := value_eqb_eq ;
}.
#[local]
Existing Instance varteq__Instance.
Inductive expr : Type :=
| Xval (v : value) : expr
| Xvar (x : vart) : expr
| Xbinop (symb : binopsymb) (lhs rhs : expr) : expr
| Xget (e0 e1 e2 : expr) : expr
| Xset (e0 e1 e2 e3 : expr) : expr
| Xlet (x : vart) (e0 e1 : expr) : expr
| Xnew (γ : vart) (e__object e__count : expr) : expr (* the γ here is a hack for preservation *)
| Xdel (e : expr) : expr
| Xunpack (γ x : vart) (e0 e1 : expr) : expr
| Xpack (ℓ e : expr) : expr
| Xpair (e1 e2 : expr) : expr
| Xunpair (x1 x2 : vart) (e1 e2 : expr) : expr
| Xreturn (e : expr) : expr
| Xcall (foo : vart) (e : expr) : expr
| Xifz (c e0 e1 : expr) : expr
| Xabort : expr
.
(** The following is a helper function to easily define functions over the syntax of S, e.g. substitution. *)
Definition exprmap (h : expr -> expr) (e : expr) :=
  match e with
  | Xbinop b lhs rhs => Xbinop b (h lhs) (h rhs)
  | Xget e0 e1 e2 => Xget (h e0) (h e1) (h e2)
  | Xset e0 e1 e2 e3 => Xset (h e0) (h e1) (h e2) (h e3)
  | Xlet x e0 e1 => Xlet x (h e0) (h e1)
  | Xnew γ e1 e2 => Xnew γ (h e1) (h e2)
  | Xdel e => Xdel (h e)
  | Xunpack x ℓ e0 e1 => Xunpack x ℓ (h e0) (h e1)
  | Xpack ℓ e => Xpack ℓ (h e)
  | Xpair e1 e2 => Xpair (h e1) (h e2)
  | Xunpair x1 x2 e1 e2 => Xunpair x1 x2 (h e1) (h e2)
  | Xreturn e => Xreturn (h e)
  | Xcall f e => Xcall f (h e)
  | Xifz c e0 e1 => Xifz (h c) (h e0) (h e1)
  | _ => e
  end
.
(** We proceed to define the dynamic semantics via evaluation contexts/environments. *)
Inductive evalctx : Type :=
| Khole : evalctx
| KbinopL (b : binopsymb) (K : evalctx) (e : expr) : evalctx
| KbinopR (b : binopsymb) (v : value) (K : evalctx) : evalctx
| KgetL (K : evalctx) (e0 e1 : expr) : evalctx
| KgetM (v : value) (K : evalctx) (e1 : expr) : evalctx
| KgetR (v0 v1 : value) (K : evalctx) : evalctx
| KsetL (K : evalctx) (e0 e1 e2 : expr) : evalctx
| KsetM0 (v : value) (K : evalctx) (e0 e1 : expr) : evalctx
| KsetM1 (v0 v1 : value) (K : evalctx) (e : expr) : evalctx
| KsetR (v0 v1 v2 : value) (K : evalctx) : evalctx
| Klet (x : vart) (K : evalctx) (e : expr) : evalctx
| KnewL (γ : vart) (K : evalctx) (e : expr) : evalctx
| KnewR (γ : vart) (v : value) (K : evalctx) : evalctx
| Kdel (K : evalctx) : evalctx
| Kunpack (γ x : vart) (K : evalctx) (e : expr) : evalctx
| KpackL (K : evalctx) (e : expr) : evalctx
| KpackR (ℓ : value) (K : evalctx) : evalctx
| KpairL (K : evalctx) (e : expr) : evalctx
| KpairR (v : value) (K : evalctx) : evalctx
| Kunpair (x1 x2 : vart) (K : evalctx) (e : expr) : evalctx
| Kifz (K : evalctx) (e0 e1 : expr) : evalctx
| Kreturn (K : evalctx) : evalctx
| Kcall (foo : vart) (K : evalctx) : evalctx
.
(** Pre-Types of S *)
Inductive pre_ty : Type :=
| Tnat : pre_ty
| Tptr : Loc -> pre_ty
| Tcap : Loc -> pre_ty -> pre_ty
| Tpair : pre_ty -> pre_ty -> pre_ty
| Texists : vart -> pre_ty -> pre_ty
.
#[global]
Notation "'Tℕ'" := (Tnat).
Fixpoint pre_ty_eqb (t1 t2 : pre_ty) : bool :=
  match t1, t2 with
  | Tnat, Tnat => true
  | Tptr l1, Tptr l2 => (l1 == l2)
  | Tcap l1 t1, Tcap l2 t2 => andb (l1 == l2) (pre_ty_eqb t1 t2)
  | Tpair t1 t2, Tpair t1' t2' => andb (pre_ty_eqb t1 t1') (pre_ty_eqb t2 t2')
  | Texists x t1, Texists y t2 => andb (x == y) (pre_ty_eqb t1 t2)
  | _, _ => false
  end
.
Lemma pre_ty_eqb_eq t0 t1 :
  pre_ty_eqb t0 t1 = true <-> t0 = t1.
Proof.
  split; revert t1; induction t0; intros.
  - destruct t1; now cbn.
  - destruct t1; cbn in H; try easy. eq_to_defeq Loc_eqb.
  - destruct t1; cbn in H; try easy. eq_to_defeq Loc_eqb.
    specialize (IHt0 t1 H0); subst; reflexivity.
  - destruct t1; cbn in H; try easy. eq_to_defeq pre_ty_eqb.
    specialize (IHt0_1 t1_1 H); specialize (IHt0_2 t1_2 H0); subst.
    reflexivity.
  - destruct t1; cbn in H; try easy. eq_to_defeq vareq.
    specialize (IHt0 t1 H0); subst; reflexivity.
  - now destruct t1.
  - destruct t1; try easy; inv H; cbn; eq_to_defeq Loc_eqb.
  - destruct t1; try easy; inv H; cbn; eq_to_defeq Loc_eqb.
    split; eq_to_defeq Loc_eqb. eapply IHt0; eauto.
  - destruct t1; inv H. cbn; eq_to_defeq eq. split; eauto.
  - destruct t1; try easy; inv H; cbn; eq_to_defeq vareq; split;
    eq_to_defeq vareq; eapply IHt0; eauto.
Qed.
#[export]
Instance pre_tyeq__Instance : HasEquality pre_ty := {
  eq := pre_ty_eqb ;
  eqb_eq := pre_ty_eqb_eq ;
}.
#[local]
Existing Instance varteq__Instance.

(** Types of S *)
Inductive ty : Type :=
| Tpre : pre_ty -> ty
| Tret : pre_ty -> ty
| Tfun : pre_ty -> pre_ty -> ty
.
Coercion Tpre : pre_ty >-> ty.
Definition ty_eqb (t1 t2 : ty) : bool :=
  match t1, t2 with
  | Tpre t1, Tpre t2 => (t1 == t2)
  | Tret t1, Tret t2 => (t1 == t2)
  | Tfun t1 t2, Tfun t1' t2' => andb (t1 == t1') (t2 == t2')
  | _, _ => false
  end
.
Lemma ty_eqb_eq t0 t1 :
  ty_eqb t0 t1 = true <-> t0 = t1.
Proof.
  destruct t0, t1; split; intros H; try easy; cbn in H;
  eq_to_defeq pre_ty_eqb; inv H; cbn; eq_to_defeq pre_ty_eqb.
Qed.
#[export]
Instance tyeq__Instance : HasEquality ty := {
  eq := ty_eqb ;
  eqb_eq := ty_eqb_eq ;
}.
#[local]
Existing Instance varteq__Instance.

(** Symbols look like `fn foo x : τ := e` *)
Definition symbol : Type := vart * pre_ty * pre_ty * expr.
Definition symbols := mapind varteq__Instance symbol.

Definition vart_of_symbol (s : symbol) := let '(v, t0, t1, e) := s in v.
Definition expr_of_symbol (s : symbol) := let '(v, t0, t1, e) := s in e.
Definition ty_of_symbol (s : symbol) := let '(v, t0, t1, e) := s in Tfun t0 t1.
