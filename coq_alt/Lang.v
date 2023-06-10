Set Implicit Arguments.

From RecordUpdate Require Import RecordSet.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Coq.Program.Equality.
Require Import CSC.Sets CSC.Util CSC.Fresh.

(* This file defines the overlapping mechanics of our programming languages *)

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

Inductive value : Type :=
| Vnat : nat -> value
.
Coercion Vnat : nat >-> value.

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

#[global]
Hint Resolve loc_eqb_refl String.eqb_refl : core.

(** * Actual Syntax *)

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

Definition is_stuck : expr -> Prop := fun _ => False. (* TODO: actually do the check *)
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

Variable symbol : Type.
Variable argname_of_symbol : symbol -> vart.
Variable expr_of_symbol : symbol -> expr.
(** printing  *symbols* $\Xi$ *)
Definition symbols := mapind varteq__Instance symbol.
Definition commlib := list vart.
Inductive prog : Type := Cprog : symbols -> commlib -> prog.

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
Global Notation "'◻'" := (poisonless).
Global Notation "'☣'" := (poisoned).

Variant sandboxtag := SCtx | SComp.
Definition sandboxtag_eqb t1 t2 :=
  match t1, t2 with
  | SCtx, SCtx => true
  | SComp, SComp => true
  | _, _ => false
  end
.
Definition string_of_sandboxtag t :=
  match t with
  | SCtx => "CTX"%string
  | SComp => "COMP"%string
  end
.
Lemma sandboxtag_eqb_refl t :
  sandboxtag_eqb t t = true.
Proof. now destruct t. Qed.
Lemma sandboxtag_eqb_eq t1 t2 :
  sandboxtag_eqb t1 t2 = true <-> t1 = t2.
Proof. now destruct t1, t2. Qed.
Lemma sandboxtag_eqb_neq t1 t2 :
  sandboxtag_eqb t1 t2 = false <-> t1 <> t2.
Proof. now destruct t1, t2. Qed.
#[global] Hint Resolve sandboxtag_eqb_refl Nat.eqb_refl : core.

(* A "dynamic" location contains the location and its poison *)
Definition dynloc : Type := loc * sandboxtag * poison * nat.
Definition dynloc_eqb :=
  fun (dℓ1 dℓ2 : dynloc) =>
    match dℓ1, dℓ2 with
    | (ℓ1, t1, ☣, n1), (ℓ2, t2, ☣, n2) => andb (andb (sandboxtag_eqb t1 t2) (Nat.eqb n1 n2)) (loc_eqb ℓ1 ℓ2)
    | (ℓ1, t1, ◻, n1), (ℓ2, t2, ◻, n2) => andb (andb (sandboxtag_eqb t1 t2) (Nat.eqb n1 n2)) (loc_eqb ℓ1 ℓ2)
    | (ℓ1, t1, ☣, n1), (ℓ2, t2, ◻, n2) => false
    | (ℓ1, t1, ◻, n1), (ℓ2, t2, ☣, n2) => false
    end
.
Lemma dynloc_eqb_refl (dℓ1 : dynloc) :
  dynloc_eqb dℓ1 dℓ1 = true.
Proof. destruct dℓ1; repeat destruct p; destruct p0; cbn; repeat rewrite bool_and_equiv_prop; auto. Qed.
Lemma dynloc_eqb_eq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = true <-> dℓ0 = dℓ1.
Proof.
  destruct dℓ0 as [[[ℓ0 t0] ρ0] n0], dℓ1 as [[[ℓ1 t1] ρ1] n1]; destruct ρ0, ρ1; split; cbn; intros H; try apply loc_eqb_eq in H; subst; eauto;
  inv H; auto.

  1,3:
    repeat rewrite bool_and_equiv_prop in H1; destruct H1 as [[H1a H1b] H1c];
    now apply loc_eqb_eq in H1c; apply Nat.eqb_eq in H1b; apply sandboxtag_eqb_eq in H1a; subst.

  all:
    repeat rewrite bool_and_equiv_prop; split; auto.
Qed.
Lemma dynloc_eqb_neq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = false <-> dℓ0 <> dℓ1.
Proof.
  destruct dℓ0 as [[[ℓ0 t0] ρ0] n0], dℓ1 as [[[ℓ1 t1] ρ1] n1]; destruct ρ0, ρ1; split; cbn; intros H; try easy.

  1, 3:
  repeat rewrite nbool_and_equiv_nprop in H; destruct H as [[H | H] | H];
  try (apply sandboxtag_eqb_neq in H + apply Nat.eqb_neq in H + apply loc_eqb_neq in H); congruence.

  all:
    repeat rewrite nbool_and_equiv_nprop.
  destruct (Nat.eq_dec n0 n1) as [H0|H0]; subst.
  destruct t0, t1; cbn in *; auto.
  destruct ℓ0, ℓ1; cbn in *; auto. right. apply Nat.eqb_neq. intros H'; subst; auto.
  right. apply loc_eqb_neq. intros H'; subst; auto.
  apply Nat.eqb_neq in H0; auto.

  destruct (Nat.eq_dec n0 n1) as [H0|H0]; subst.
  destruct t0, t1; cbn in *; auto.
  destruct ℓ0, ℓ1; cbn in *; auto. right. apply Nat.eqb_neq. intros H'; subst; auto.
  right. apply loc_eqb_neq. intros H'; subst; auto.
  apply Nat.eqb_neq in H0; auto.
Qed.
#[local]
Instance dynloceq__Instance : HasEquality dynloc := {
  eq := dynloc_eqb ;
  eq_refl := dynloc_eqb_refl ;
  eqb_eq := dynloc_eqb_eq ;
  neqb_neq := dynloc_eqb_neq
}.

(** Stores map variables to potentially poisoned locations. *)
Definition store := mapind varteq__Instance dynloc.
Definition sNil : store := mapNil varteq__Instance dynloc.

Variable abstract_loc : Type.
Variable addr_conv : nat -> abstract_loc.
Fixpoint δ_of_Δ (Δ : store) :=
  match Δ with
  | mapNil _ _ => mapNil _ _
  | mapCons _ ((addr ℓ), _, _, _) Δ' => mapCons (addr ℓ) (addr_conv ℓ) (δ_of_Δ Δ')
  end
.
Lemma δ_of_Δ_in_dom (Δ : store) ℓ :
  In ℓ (dom (δ_of_Δ Δ)) ->
  exists t ρ n, In (ℓ, t, ρ, n) (img Δ)
.
Proof.
  revert ℓ; induction Δ; cbn; intros; try easy.
  destruct b as [[[l t] ρ] n], l; destruct H as [H|H].
  - inv H; eauto.
  - specialize (IHΔ ℓ H); deex; eauto.
Qed.
Lemma δ_of_Δ_in_img (Δ : store) ℓ t ρ n :
  In (ℓ, t, ρ, n) (img Δ) ->
  In ℓ (dom (δ_of_Δ Δ))
.
Proof.
  induction Δ; cbn; intros H; try easy.
  destruct H as [H|H]; destruct b as [[[l t'] ρ'] n'], l.
  - inv H; now left.
  - specialize (IHΔ H); now right.
Qed.

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
Definition active_ectx := list (evalctx * vart).
(** Contains names of component-level functions *)

#[local]
Existing Instance varteq__Instance | 0.

Record cfstate : Type := mkcfstate {
  Ξ : symbols ;
  ξ : commlib ;
  Ks : active_ectx
}.
#[export]
Instance: Settable cfstate := settable! mkcfstate <Ξ; ξ; Ks>.
Record memstate : Type := mkmemstate {
  H__ctx : heap ;
  H__comp : heap ;
  Δ : store
}.
#[export]
Instance: Settable memstate := settable! mkmemstate <H__ctx; H__comp; Δ>.
Record state : Type := mkstate {
  F : CSC.Fresh.fresh_state ;
  Ψ : cfstate ;
  Ωt : sandboxtag ;
  doit : nat ;
  Φ : memstate
}.
#[export]
Instance: Settable state := settable! mkstate <F; Ψ; Ωt; doit; Φ>.

#[global]
Notation "'s(' F ';' Φ ';' t ';' n ';' Ψ ')'" := (mkstate F Φ t n Ψ : state) (at level 81,
                                                  Φ at next level,
                                                  t at next level,
                                                  n at next level,
                                                  Ψ at next level).
#[global]
Notation  "'cf(' Ξ ';' ξ ';' K ')'" := (mkcfstate Ξ ξ K : cfstate) (at level 81,
                                        ξ at next level,
                                        K at next level).
#[global]
Notation "'m(' H__ctx ';' H__comp ';' Δ ')'" := (mkmemstate H__ctx H__comp Δ : memstate) (at level 81,
                                                  H__comp at next level,
                                                  Δ at next level).
(*
Ltac splitΦ Φ :=
  let Ξ := fresh "Ξ" in
  let ξ := fresh "ξ" in
  let K := fresh "K" in
  destruct Φ as [[Ξ ξ] K]
.
Ltac splitΨ Ψ :=
  let H__ctx := fresh "H__ctx" in
  let H__comp := fresh "H__comp" in
  let Δ := fresh "Δ" in
  destruct Ψ as [[H__ctx H__comp] Δ]
.
Ltac splitΩ Ω :=
  let F := fresh "F" in
  let Φ := fresh "Φ" in
  let t := fresh "t" in
  let n := fresh "n" in
  let Ψ := fresh "Ψ" in
  destruct Ω as [[[[F Φ] t] n] Ψ];
  splitΦ Φ; splitΨ Ψ
.
 *)
Definition nodupinv (Ω : state) : Prop :=
  let Φ := Ω.(Φ) in
  let Ψ := Ω.(Ψ) in
  nodupinv Ψ.(Ξ) /\ nodupinv Φ.(H__ctx) /\ nodupinv Φ.(H__comp) /\ nodupinv Φ.(Δ)
.
Lemma nodupinv_empty Ξ ξ n t :
  Util.nodupinv Ξ ->
  nodupinv(s(Fresh.empty_fresh ; cf(Ξ ; ξ ; List.nil) ; t ; n ; m(hNil ; hNil ; sNil))).
Proof. intros H; cbn; repeat split; eauto; constructor. Qed.
Lemma nodupinv_H H H' n :
  Util.nodupinv H ->
  Hgrow H n = Some H' ->
  Util.nodupinv H'
.
Proof.
  repeat split; eauto.
  revert H' H; induction n; intros H' H Hb H0.
  - now inv H0.
  - cbn in H0. destruct (option_dec (Hgrow_aux H n (List.length (dom H)))) as [Hx|Hy]; try (rewrite Hy in H0; congruence).
    apply not_eq_None_Some in Hx as [H__x Hx].
    rewrite Hx in H0.
    cbn in H0. now apply push_ok in H0.
Qed.

(** Types of events that may occur in a trace. *)
Variant eventb : Type :=
| Sstart : eventb
| Send (v : value) : eventb
| Salloc (ℓ : loc) (n : nat) : eventb
| Sdealloc (ℓ : loc) : eventb
| Sget (ℓ : loc) (n : nat) : eventb
| Sset (ℓ : loc) (n : nat) (v : value) : eventb
| Scall (q : comms) (foo : vart) (arg : fnoerr) : eventb
| Sret (q : comms) (f : fnoerr) : eventb
.
Definition eventbeq (e1 e2 : eventb) : bool :=
  match e1, e2 with
  | Sstart, Sstart => true
  | Send(Vnat n1), Send(Vnat n2) => Nat.eqb n1 n2
  | Salloc(addr ℓ0) n0, Salloc(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sdealloc(addr ℓ0), Sdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Sget(addr ℓ0) n0, Sget(addr ℓ1) n1 => andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1)
  | Sset(addr ℓ0) n0 (Vnat v0), Sset(addr ℓ1) n1 (Vnat v1) => andb (andb (Nat.eqb ℓ0 ℓ1) (Nat.eqb n0 n1))
                                                                  (Nat.eqb v0 v1)
  | Scall q1 foo (Fval(Vnat v0)), Scall q2 bar (Fval(Vnat v1)) => andb (andb (String.eqb foo bar) (Nat.eqb v0 v1)) (comms_eq q1 q2)
  | Scall q1 foo (Fvar x), Scall q2 bar (Fvar y) => andb(andb (String.eqb foo bar) (String.eqb x y)) (comms_eq q1 q2)
  | Sret q1 (Fval(Vnat v0)), Sret q2 (Fval(Vnat v1)) => andb (Nat.eqb v0 v1) (comms_eq q1 q2)
  | Sret q1 (Fvar x), Sret q2 (Fvar y) => andb (String.eqb x y) (comms_eq q1 q2)
  | _, _ => false
  end
.
Variant securitytag := Lock | Unlock.
Definition securitytageq (σ1 σ2 : securitytag) : bool :=
  match σ1, σ2 with
  | Lock, Lock | Unlock, Unlock => true
  | _, _ => false
  end
.
Definition string_of_securitytag (σ : securitytag) : string :=
  match σ with
  | Lock => "HIGH"
  | Unlock => "LOW"
  end
.

Record eventr : Type := mkevent {
  ee : eventb ;
  et : sandboxtag ;
  eσ : securitytag ;
}.
#[export]
Instance: Settable eventr := settable! mkevent <ee; et; eσ>.
Variant event : Type :=
| Sevent : eventr -> event
| Scrash : event
.
Notation "'e[' e ';' t ';' σ ']'" := (Sevent (mkevent e t σ)) (at level 81, t at next level).
#[global]
Instance Event__Instance : TraceEvent event := {}.
Definition string_of_event (e : event) :=
  match e with
  | Scrash => "↯"%string
  | Sevent e =>
    let pref := match e.(ee) with
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
    end in
    String.append pref (String.append ";"%string
                        (String.append (string_of_sandboxtag e.(et))
                        (String.append ";"%string (string_of_securitytag e.(eσ)))))
  end
.
Definition tracepref := list event.
(** A runtime program is a state plus an expression. *)
Definition rtexpr : Type := (option state) * expr.
#[global]
Instance rtexpr__Instance : RuntimeExprClass rtexpr := {}.
Global Notation "Ω '▷' e" := ((((Some (Ω)) : option state), (e : expr)) : rtexpr) (at level 81).
Global Notation "↯ '▷' 'stuck'" := (((None : option state), (Fabrt : expr)) : rtexpr).

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

Variable pstep : PrimStep.
#[global]
Existing Instance pstep.

Variable pstep_fnostep : forall Ω (f : ferr) Ω' e' a,
    Ω ▷ f --[, a ]--> Ω' ▷ e' ->
    False
.
#[local]
Hint Resolve pstep_fnostep : core.

Variable pstep_is_nodupinv_invariant : forall Ω e Ω' e' a,
  Ω ▷ e --[, a ]--> Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Variable pstepf : forall (r : rtexpr), option (option event * rtexpr).

#[global]
Ltac grab_value e :=
  (destruct e as [[[[e]|]|]| | | | | | | | | |]; try congruence)
.
#[global]
Ltac grab_value2 e1 e2 := (grab_value e1; grab_value e2).
#[global]
Ltac grab_final e :=
  (destruct e as [[e|]| | | | | | | | | | ]; try congruence)
.
Variable equiv_pstep : forall (r0 : rtexpr) (a : option event) (r1 : rtexpr), r0 --[, a ]--> r1 <-> pstepf r0 = Some(a, r1).
Variable pstepf_is_nodupinv_invariant : forall Ω e Ω' e' a, pstepf (Ω ▷ e) = Some(a, Ω' ▷ e') -> nodupinv Ω -> nodupinv Ω'.
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
Definition ρ__call (t : sandboxtag) : comms :=
  match t with
  | SCtx => Qctxtocomp
  | SComp => Qcomptoctx
  end
.
(* $foo \in_\sandboxtag \commlib$ *)
(** If the sandboxtag `t` is "Comp", then foo must be part of commlib.
    This basically means that we want to perform a call into a component
    and, thus, `foo` must be a valid, registered component. *)
Definition footincommlib (foo : vart) (ξ : commlib) (t : sandboxtag) :=
  match t with
  | SCtx => ~ List.In foo ξ
  | SComp => List.In foo ξ
  end
.
Definition negt (t : sandboxtag) : sandboxtag :=
  match t with
  | SCtx => SComp
  | SComp => SCtx
  end
.
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
| E_ctx_call_main : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib)
                      (Φ : memstate) (s : symbol) (x__arg : vart) (e : expr),
    Some s = mget Ξ "main"%string ->
    argname_of_symbol s = x__arg ->
    expr_of_symbol s = e ->
    s(F ; cf(Ξ ; ξ ; List.nil) ; SComp ; 0 ; Φ) ▷ (insert Khole (Xcall "main"%string 0)) ==[ e[Sstart ; SComp ; Unlock] ]==> s(F ; cf(Ξ ; ξ ; (Khole, "main"%string) :: List.nil) ; SCtx ; 0 ; Φ) ▷ Xreturn (subst x__arg e 0)
| E_ctx_call_notsame : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K : evalctx) (Ks : active_ectx)
                         (doit : nat) (Φ : memstate) (s : symbol) (foo : vart) (x__arg : vart) (e : expr) (v : value)
                         (c : comms),
    footincommlib foo ξ (negt t) ->
    ρ__call (negt t) = c ->
    Some s = mget Ξ foo ->
    argname_of_symbol s = x__arg ->
    expr_of_symbol s = e ->
    s(F ; cf(Ξ ; ξ ; Ks) ; t ; doit ; Φ) ▷ (insert K (Xcall foo (Xres v))) ==[ e[Scall c foo v; t; Unlock] ]==> s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; (negt t) ; doit ; Φ) ▷ Xreturn (subst x__arg e v)
| E_ctx_call_same : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K : evalctx) (Ks : active_ectx)
                      (doit : nat) (Φ : memstate) (s : symbol) (foo : vart) (x__arg : vart) (e : expr) (v : value)
                      (c : comms),
    footincommlib foo ξ t ->
    Some s = mget Ξ foo ->
    argname_of_symbol s = x__arg ->
    expr_of_symbol s = e ->
    s(F ; cf(Ξ ; ξ ; Ks) ; t ; doit ; Φ) ▷ (insert K (Xcall foo (Xres v))) ==[ e[Scall Qinternal foo v; t; Unlock] ]==> s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; t ; doit ; Φ) ▷ Xreturn (subst x__arg e v)
| E_ctx_ret_notsame : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K K' : evalctx) (Ks : active_ectx)
                        (doit : nat) (Φ : memstate) (foo : vart) (s : symbol) (v : value) (c : comms),
    footincommlib foo ξ (negt t) ->
    ρ__call (negt t) = c ->
    Some s = mget Ξ foo ->
    s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; t ; doit ; Φ) ▷ (insert K' (Xreturn v)) ==[ e[Sret c v; t; Unlock] ]==> s(F ; cf(Ξ ; ξ ; Ks) ; (negt t) ; doit ; Φ) ▷ (insert K v)
| E_ctx_ret_same : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K K' : evalctx) (Ks : active_ectx)
                     (doit : nat) (Φ : memstate) (foo : vart) (s : symbol) (v : value) (c : comms),
    footincommlib foo ξ t ->
    Some s = mget Ξ foo ->
    s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; t ; doit ; Φ) ▷ (insert K' (Xreturn v)) ==[ e[Sret Qinternal v; t; Unlock] ]==> s(F ; cf(Ξ ; ξ ; Ks) ; t ; doit ; Φ) ▷ (insert K v)
| E_ctx_ret_main : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : evalctx)
                     (doit : nat) (Φ : memstate) (s : symbol) (v : value),
    Some s = mget Ξ "main"%string ->
    s(F ; cf(Ξ ; ξ ; (Khole, "main"%string) :: List.nil) ; SCtx ; doit ; Φ) ▷ (insert K (Xreturn v)) ==[ e[Send v; SCtx; Unlock] ]==> s(F ; cf(Ξ ; ξ ; List.nil) ; SComp ; doit ; Φ) ▷ v
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
  None
  (*
  let '(oΩ, e) := r in
  let* Ω := oΩ in
  let* (K, e0) := evalctx_of_expr e in
  match e0 with
  | Xcall foo (Xres(Fres f)) =>
    let '(F, (Ξ, ξ, Ks'), q, doit, (H__ctx, H__comp, Δ)) := Ω in
    match mget Ξ foo with
    | None => None
    | Some (argx, τ__arg, e__foo) =>
      match Ks' with
      | List.nil =>
        if vareq foo "main"%string then
          Some(Some Sstart, s(F ; cf(Ξ ; ξ ; (Khole, "main"%string, Qctxtocomp) :: List.nil) ; q ; doit ; m(H__ctx ; H__comp ; Δ)) ▷ (Xreturn (subst argx e__foo 0)))
        else
          None
      | (K__bar, bar) :: Ks =>
        match ρ__call ξ foo bar f with
        | (a, q') =>
          Some(a, s(F ; cf(Ξ ; ξ ; ((K, foo, q') :: (K__bar, bar, q) :: Ks)) ; q ; doit ; m(H__ctx ; H__comp ; Δ)) ▷ (Xreturn (subst argx e__foo f)))
        end
      end
    end
  | Xreturn(Xres(Fres f)) =>
    let '(F, (Ξ, ξ, Ks'), q, doit, (H__ctx, H__comp, Δ)) := Ω in
    match Ks' with
    | nil => None
    | (Khole, "main"%string, Qctxtocomp) :: List.nil =>
      match f with
      | Fval(v) => Some(Some(Send v), s(F ; cf(Ξ ; ξ ; List.nil) ; q ; doit ; m(H__ctx ; H__comp ; Δ)) ▷ f)
      | _ => None
      end
    | (K__foo, _foo) :: Ks =>
      let a := ρ__ret q f in
      Some(a, s(F ; cf(Ξ ; ξ ; Ks) ; q ; doit ; m(H__ctx ; H__comp ; Δ)) ▷ insert K__foo f)
    end
  | _ =>
    let* _ := pstep_compatible e0 in
    let* (a, (oΩ, e0')) := pstepf (Ω ▷ e0) in
    match oΩ with
    | None => Some(Some(Scrash), ↯ ▷ stuck)
    | Some Ω' => Some(a, Ω' ▷ insert K e0')
    end
  end*)
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

Lemma different_reduction Ω Ω' e v v' As :
  ((estep (Ω ▷ e) As (Ω' ▷ v)) -> False) ->
  (estep (Ω ▷ e) As (Ω' ▷ v')) ->
  v <> v'
.
Proof.
  intros H0 H1 H2; now subst.
Qed.

Reserved Notation "e0 '==[' a ']==>*' e1" (at level 82, e1 at next level).
Inductive star_step : rtexpr -> tracepref -> rtexpr -> Prop :=
| ES_refl : forall (r1 : rtexpr),
    is_val (let '(_, e) := r1 in e) ->
    r1 ==[ nil ]==>* r1
| ES_trans_important : forall (r1 r2 r3 : rtexpr) (a : event) (As : tracepref),
    r1 ==[ a ]==> r2 ->
    r2 ==[ As ]==>* r3 ->
    r1 ==[ a :: As ]==>* r3
| ES_trans_unimportant : forall (r1 r2 r3 : rtexpr) (As : tracepref),
    r1 ==[]==> r2 ->
    r2 ==[ As ]==>* r3 ->
    r1 ==[ As ]==>* r3
where "e0 '==[' a ']==>*' e1" := (star_step e0 a e1).
#[export]
Hint Constructors star_step : core.
Notation "e0 '==[]==>*' e1" := (star_step e0 (nil) e1) (at level 82, e1 at next level).

Lemma star_step_is_nodupinv_invariant Ω e Ω' e' As :
  Ω ▷ e ==[ As ]==>* Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  assert (Some Ω = let (oΩ, e) := Ω ▷ e in oΩ) by easy;
  assert (Some Ω' = let (oΩ', e') := Ω' ▷ e' in oΩ') by easy.
  intros H__star; dependent induction H__star; try (inv H; inv H0; easy); try easy.
  - destruct r2 as [[Ω2|] e2]; try (cbn in H0; contradiction); intros H__x.
    eapply estep_is_nodupinv_invariant in H; eauto.
    admit.
  - destruct r2 as [[Ω2|] e2]; try (cbn in H0; contradiction); intros H__x.
    eapply estep_is_nodupinv_invariant in H; eauto.
    admit.
Admitted.
(** Functional style version of star step from above. We need another parameter "fuel" to sidestep termination. *)
Definition star_stepf (fuel : nat) (r : rtexpr) : option (tracepref * rtexpr) :=
  let fix doo (fuel : nat) (r : rtexpr) :=
    let (oΩ, e) := r in
    let* Ω := oΩ in
    match fuel, e with
    | 0, Xres(_) => (* refl *)
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
  - crush_fuel; crush_estep; easy.
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
Admitted.

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
    s(Fresh.empty_fresh ; cf(symbs ; ξ ; nil) ; SComp ; 0 ; m(hNil ; hNil ; sNil)) ▷ Xcall "main"%string 0 ==[ As ]==>* r ->
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
  let x__arg := argname_of_symbol Kτ in
  let e__arg := expr_of_symbol Kτ in
  let e := subst x__arg e__arg (Xres 0) in
  let* ge := get_fuel e in
  let* symbs := collect_callsites ξ e in
  let* res := List.fold_left (fun acc Eτ =>
                                let e__arg := expr_of_symbol Eτ in
                                let* a := acc in
                                let* b := get_fuel_fn e__arg in
                                Some(1 + a + b)) (img symbs) (Some ge) in
  Some(S res)
.

Definition wstepf (p : prog) : option (tracepref * rtexpr) :=
  let '(Cprog symbs ξ) := p in
  let e := Xcall "main"%string 0 in
  let* fuel := get_fuel_toplevel symbs "main"%string in
  let R := s(Fresh.empty_fresh ; cf(symbs ; ξ ; nil) ; SComp ; 0 ; m(hNil ; hNil ; sNil)) ▷ e in
  star_stepf fuel R
.
Fixpoint string_of_tracepref_aux (t : tracepref) (acc : string) : string :=
  match t with
  | nil => acc
  | a :: nil => String.append acc (string_of_event a)
  | a :: As =>
      let acc' := String.append acc (String.append (string_of_event a) (" · "%string))
      in string_of_tracepref_aux As acc'
  end
.
Definition string_of_tracepref (t : tracepref) : string := string_of_tracepref_aux t (""%string).

Definition debug_eval (p : prog) :=
  let* (As, _) := wstepf p in
  Some(string_of_tracepref As)
.

Lemma δ_of_Δ_poison_eq (Δ1 Δ2 : store) (x : vart) (ℓ : loc) (t : sandboxtag) (n : nat) :
  δ_of_Δ (Δ1 ◘ x ↦ (ℓ, t, ◻, n) ◘ Δ2) = δ_of_Δ (Δ1 ◘ x ↦ (ℓ, t, ☣, n) ◘ Δ2)
.
Proof.
  induction Δ1; cbn; eauto; destruct b as [[] _]; fold (append Δ1 (x ↦ (ℓ, t, ◻, n) ◘ Δ2));
  fold (append Δ1 (x ↦ (ℓ, t, ☣, n) ◘ Δ2)).
  destruct p, l.  now f_equal.
Qed.

Reserved Notation "e0 '=(' n ')=[' a ']==>' e1" (at level 82, e1 at next level).
Inductive n_step : rtexpr -> nat -> tracepref -> rtexpr -> Prop :=
| ENS_refl : forall (r1 : rtexpr),
    is_val (let '(_, e) := r1 in e) ->
    r1 =( 0 )=[ nil ]==> r1
| ENS_trans_important : forall (r1 r2 r3 : rtexpr) (a : event) (As : tracepref) (n : nat),
    r1 ==[ a ]==> r2 ->
    r2 =( n )=[ As ]==> r3 ->
    r1 =( S n )=[ a :: As ]==> r3
| ENS_trans_unimportant : forall (r1 r2 r3 : rtexpr) (As : tracepref) (n : nat),
    r1 ==[]==> r2 ->
    r2 =( n )=[ As ]==> r3 ->
    r1 =( S n )=[ As ]==> r3
where "e0 '=(' n ')=[' a ']==>' e1" := (n_step e0 n a e1).
#[export]
Hint Constructors star_step : core.
Notation "e0 '=(0)=[]==>' e1" := (n_step e0 0 nil e1) (at level 82, e1 at next level).

