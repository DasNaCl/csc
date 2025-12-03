Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Lists.List Program.Equality Recdef Lia.

Require Import CSC.Shared.Sema CSC.Shared.Fresh CSC.Util.Sets CSC.Shared.Fresh CSC.Shared.Props.
Require Import CSC.Util.HasEquality CSC.Util.Convenience CSC.Util.NoDupInv.

From RecordUpdate Require Import RecordSet.

(** Values are numbers, pairs, capabilities, and pointers *)
Inductive value : Type :=
| Vnat : nat -> value
| Vpair : value -> value -> value
.
Coercion Vnat : nat >-> value.
Fixpoint value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Vnat n1, Vnat n2 => Nat.eqb n1 n2
  | Vpair v0 v1, Vpair v0' v1' => andb (value_eqb v0 v0') (value_eqb v1 v1')
  | _, _ => false
  end
.
Lemma value_eqb_eq v1 v2 :
  value_eqb v1 v2 = true <-> v1 = v2.
Proof.
  revert v2; induction v1; cbn; split; intros.
  - destruct v2; try easy. apply PeanoNat.Nat.eqb_eq in H; inv H; reflexivity.
  - destruct v2; inv H; apply PeanoNat.Nat.eqb_refl.
  - inv H; cbn. destruct v2; inv H1. eq_to_defeq value_eqb.
    eapply IHv1_1 in H. eapply IHv1_2 in H0. now subst.
  - destruct v2; inv H. eq_to_defeq value_eqb; split. now eapply IHv1_1.
    now eapply IHv1_2.
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
| Xget (x : vart) (e : expr) : expr
| Xset (x : vart) (e0 e1 : expr) : expr
| Xlet (x : vart) (e0 e1 : expr) : expr
| Xnew (x : vart) (e__object e__count e : expr) : expr
| Xdel (x : vart) : expr
| Xpair (e1 e2 : expr) : expr
| Xunpair (x1 x2 : vart) (e1 e2 : expr) : expr
| Xreturn (e : expr) : expr
| Xcall (foo : vart) (e : expr) : expr
| Xifz (c e0 e1 : expr) : expr
| Xabort : expr
.
Fixpoint string_of_value v := 
  match v with
  | Vnat n => string_of_nat n
  | Vpair v1 v2 => "<" ++ (string_of_value v1) ++ ", " ++ (string_of_value v2) ++ ">"
  end%string
.
Fixpoint string_of_expr e := 
  match e with
  | Xval v => string_of_value v
  | Xvar x => x
  | Xbinop symb e1 e2 => "(" ++ (string_of_expr e1)
      ++ " " ++ (string_of_symb symb) ++ " "
      ++ (string_of_expr e2) ++ ")"
  | Xget x e => x ++ "[" ++ (string_of_expr e) ++ "]"
  | Xset x e1 e2 => x ++ "[" ++ (string_of_expr e1) ++ "] <- " ++ (string_of_expr e2)
  | Xlet x e1 e2 => "let " ++ x ++ " = " ++ (string_of_expr e1) ++ " in " ++ (string_of_expr e2)
  | Xnew x e1 e2 e3 => "let " ++ x ++ " = new " ++ (string_of_expr e1) ++ "[" ++ (string_of_expr e2) ++ "] in " ++ (string_of_expr e3)
  | Xdel x => "delete " ++ x
  | Xpair e1 e2 => "<" ++ (string_of_expr e1) ++ ", " ++ (string_of_expr e2) ++ ">"
  | Xunpair x1 x2 e1 e2 => "let <" ++ x1 ++ ", " ++ x2 ++ "> = " ++ (string_of_expr e1) ++ " in " ++ (string_of_expr e2)
  | Xreturn e => "return " ++ (string_of_expr e)
  | Xcall foo e => "call " ++ foo ++ " " ++ (string_of_expr e)
  | Xifz e1 e2 e3 => "ifz " ++ (string_of_expr e1) ++ " then " ++ (string_of_expr e2) ++ " else " ++ (string_of_expr e3)
  | Xabort => "abort"
  end%string
.
(** The following is a helper function to easily define functions over the syntax of S, e.g. substitution. *)
Definition exprmap (h : expr -> expr) (e : expr) :=
  match e with
  | Xbinop b lhs rhs => Xbinop b (h lhs) (h rhs)
  | Xget x e1 => Xget x (h e1)
  | Xset x e1 e2 => Xset x (h e1) (h e2)
  | Xlet x e0 e1 => Xlet x (h e0) (h e1)
  | Xnew x e1 e2 e3 => Xnew x (h e1) (h e2) (h e3)
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
| Kget (x : vart) (K : evalctx) : evalctx
| KsetL (x : vart) (K : evalctx) (e : expr) : evalctx
| KsetR (x : vart) (v : value) (K : evalctx) : evalctx
| Klet (x : vart) (K : evalctx) (e : expr) : evalctx
| KnewL (x : vart) (K : evalctx) (e0 e1 : expr) : evalctx
| KnewR (x : vart) (v : value) (K : evalctx) (e : expr) : evalctx
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
| Tpair : pre_ty -> pre_ty -> pre_ty
.
#[global]
Notation "'Tℕ'" := (Tnat).
Fixpoint pre_ty_eqb (t1 t2 : pre_ty) : bool :=
  match t1, t2 with
  | Tnat, Tnat => true
  | Tpair t1 t2, Tpair t1' t2' => andb (pre_ty_eqb t1 t1') (pre_ty_eqb t2 t2')
  | _, _ => false
  end
.
Lemma pre_ty_eqb_eq t0 t1 :
  pre_ty_eqb t0 t1 = true <-> t0 = t1.
Proof.
  split; revert t1; induction t0; intros.
  - destruct t1; now cbn.
  - destruct t1; cbn in H; try easy. eq_to_defeq pre_ty_eqb.
    specialize (IHt0_1 t1_1 H); specialize (IHt0_2 t1_2 H0); subst.
    reflexivity.
  - now destruct t1.
  - destruct t1; try easy; inv H; cbn; eq_to_defeq Loc_eqb.
    split; eq_to_defeq Loc_eqb. eapply IHt0_1; eauto.
    eapply IHt0_2; eauto.
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
