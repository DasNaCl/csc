Set Implicit Arguments.

Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List.
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

Definition cfstate : Type := symbols * commlib * active_ectx.
Definition memstate : Type := heap * heap * store.
Definition state : Type := CSC.Fresh.fresh_state * cfstate * sandboxtag * nat * memstate.

#[global]
Notation "'s(' F ';' Φ ';' t ';' n ';' Ψ ')'" := ((F, Φ, t, n, Ψ) : state) (at level 81,
                                                  Φ at next level,
                                                  t at next level,
                                                  n at next level,
                                                  Ψ at next level).
#[global]
Notation  "'cf(' Ξ ';' ξ ';' K ')'" := ((Ξ, ξ, K) : cfstate) (at level 81,
                                        ξ at next level,
                                        K at next level).
#[global]
Notation "'m(' H__ctx ';' H__comp ';' Δ ')'" := ((H__ctx, H__comp, Δ) : memstate) (at level 81,
                                                  H__comp at next level,
                                                  Δ at next level).
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
Definition nodupinv (Ω : state) : Prop :=
  let '(F, (Ξ, ξ, K), t, n, (H__ctx, H__comp, Δ)) := Ω in
  nodupinv Ξ /\ nodupinv H__ctx /\ nodupinv H__comp /\ nodupinv Δ
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
    s(F ; cf(Ξ ; ξ ; List.nil) ; SComp ; 0 ; Φ) ▷ (insert Khole (Xcall "main"%string 0)) ==[ Sstart ]==> s(F ; cf(Ξ ; ξ ; (Khole, "main"%string) :: List.nil) ; SCtx ; 0 ; Φ) ▷ Xreturn (subst x__arg e 0)
| E_ctx_call_notsame : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K : evalctx) (Ks : active_ectx)
                         (doit : nat) (Φ : memstate) (s : symbol) (foo : vart) (x__arg : vart) (e : expr) (v : value)
                         (c : comms),
    footincommlib foo ξ (negt t) ->
    ρ__call (negt t) = c ->
    Some s = mget Ξ foo ->
    argname_of_symbol s = x__arg ->
    expr_of_symbol s = e ->
    s(F ; cf(Ξ ; ξ ; Ks) ; t ; doit ; Φ) ▷ (insert K (Xcall foo (Xres v))) ==[ Scall c foo v ]==> s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; (negt t) ; doit ; Φ) ▷ Xreturn (subst x__arg e v)
| E_ctx_call_same : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K : evalctx) (Ks : active_ectx)
                      (doit : nat) (Φ : memstate) (s : symbol) (foo : vart) (x__arg : vart) (e : expr) (v : value)
                      (c : comms),
    footincommlib foo ξ t ->
    Some s = mget Ξ foo ->
    argname_of_symbol s = x__arg ->
    expr_of_symbol s = e ->
    s(F ; cf(Ξ ; ξ ; Ks) ; t ; doit ; Φ) ▷ (insert K (Xcall foo (Xres v))) ==[ Scall Qinternal foo v ]==> s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; t ; doit ; Φ) ▷ Xreturn (subst x__arg e v)
| E_ctx_ret_notsame : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K K' : evalctx) (Ks : active_ectx)
                        (doit : nat) (Φ : memstate) (foo : vart) (s : symbol) (v : value) (c : comms),
    footincommlib foo ξ (negt t) ->
    ρ__call (negt t) = c ->
    Some s = mget Ξ foo ->
    s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; t ; doit ; Φ) ▷ (insert K' (Xreturn v)) ==[ Sret c v ]==> s(F ; cf(Ξ ; ξ ; Ks) ; (negt t) ; doit ; Φ) ▷ (insert K v)
| E_ctx_ret_same : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (t : sandboxtag) (K K' : evalctx) (Ks : active_ectx)
                     (doit : nat) (Φ : memstate) (foo : vart) (s : symbol) (v : value) (c : comms),
    footincommlib foo ξ t ->
    Some s = mget Ξ foo ->
    s(F ; cf(Ξ ; ξ ; (K, foo) :: Ks) ; t ; doit ; Φ) ▷ (insert K' (Xreturn v)) ==[ Sret Qinternal v ]==> s(F ; cf(Ξ ; ξ ; Ks) ; t ; doit ; Φ) ▷ (insert K v)
| E_ctx_ret_main : forall (F : CSC.Fresh.fresh_state) (Ξ : symbols) (ξ : commlib) (K : evalctx)
                     (doit : nat) (Φ : memstate) (s : symbol) (v : value),
    Some s = mget Ξ "main"%string ->
    s(F ; cf(Ξ ; ξ ; (Khole, "main"%string) :: List.nil) ; SCtx ; doit ; Φ) ▷ (insert K (Xreturn v)) ==[ Send v ]==> s(F ; cf(Ξ ; ξ ; List.nil) ; SComp ; doit ; Φ) ▷ v
.
#[global]
Existing Instance estep.
#[global]
Hint Constructors estep : core.
