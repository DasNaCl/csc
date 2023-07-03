Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef Lia.
Require Import CSC.Sets CSC.Util CSC.Fresh CSC.Props.

From RecordUpdate Require Import RecordSet.

(** * Syntax *)

(** These are the locs from the L³ paper by Ahmed, Fluet, and Morrisett *)
Inductive Loc : Type :=
| LConst : loc -> Loc
| LVar : vart -> Loc
.
Definition Loc_eqb (l1 l2 : Loc) : bool :=
  match l1, l2 with
  | LConst l1, LConst l2 => (l1 == l2)
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
  inv H; change ((l0 == l0) = true); apply eq_refl.
  inv H; change ((v0 == v0) = true); apply eq_refl.
Qed.
#[local]
Instance Loceq__Instance : HasEquality Loc := {
  eq := Loc_eqb ;
  eqb_eq := Loc_eqb_eq ;
}.
(** Values are numbers, pairs, capabilities, and pointers *)
Inductive value : Type :=
| Vnat : nat -> value
| Vpair : value -> value -> value
| Vcap : value
| Vptr : loc -> value
| Vpack : Loc -> value -> value
.
Coercion Vnat : nat >-> value.
Fixpoint value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | Vnat n1, Vnat n2 => Nat.eqb n1 n2
  | Vpair v0 v1, Vpair v0' v1' => andb (value_eqb v0 v0') (value_eqb v1 v1')
  | Vcap, Vcap => true
  | Vptr l0, Vptr l1 => l0 == l1
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
  - destruct v2; inv H; eq_to_defeq loc_eqb.
  - destruct v2; inv H; eq_to_defeq loc_eqb.
  - destruct v2; inv H; eq_to_defeq Loc_eqb. apply IHv1 in H0; subst. reflexivity.
  - destruct v2; inv H; eq_to_defeq Loc_eqb; split; try easy. now apply IHv1.
Qed.
#[local]
Instance valueeq__Instance : HasEquality value := {
  eq := value_eqb ;
  eqb_eq := value_eqb_eq ;
}.
#[local]
Existing Instance varteq__Instance.
(** Possible binary operations. *)
Variant binopsymb : Type :=
| Badd : binopsymb
| Bsub : binopsymb
| Bmul : binopsymb
| Bdiv : binopsymb
| Bless : binopsymb
.
#[local]
Existing Instance varteq__Instance.
Inductive expr : Type :=
| Xval (v : value) : expr
| Xvar (x : vart) : expr
| Xbinop (symb : binopsymb) (lhs rhs : expr) : expr
| Xget (e0 e1 e2 : expr) : expr
| Xset (e0 e1 e2 e3 : expr) : expr
| Xlet (x : vart) (e0 e1 : expr) : expr
| Xnew (e__object e__count : expr) : expr
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
  | Xnew e1 e2 => Xnew (h e1) (h e2)
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
| KnewL (K : evalctx) (e : expr) : evalctx
| KnewR (v : value) (K : evalctx) : evalctx
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
#[local]
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
#[local]
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

(** Type for list of relevant functions, i.e. those that are part of the component. *)
Definition commlib := list vart.
(** Fill hole in evaluation context. *)
Fixpoint insert (K : evalctx) (withh : expr) : expr :=
  let R := fun k => insert k withh in
  match K with
  | Khole => withh
  | KbinopL b K' e => Xbinop b (R K') e
  | KbinopR b v K' => Xbinop b (Xval v) (R K')
  | KgetL K' e0 e1 => Xget (R K') e0 e1
  | KgetM v K' e => Xget (Xval v) (R K') e
  | KgetR v0 v1 K' => Xget (Xval v0) (Xval v1) (R K')
  | KsetL K' e0 e1 e2 => Xset (R K') e0 e1 e2
  | KsetM0 v K' e0 e1 => Xset (Xval v) (R K') e0 e1
  | KsetM1 v0 v1 K' e => Xset (Xval v0) (Xval v1) (R K') e
  | KsetR v0 v1 v2 K' => Xset (Xval v0) (Xval v1) (Xval v2) (R K')
  | Klet x K' e => Xlet x (R K') e
  | KnewL K' e => Xnew (R K') e
  | KnewR v K' => Xnew (Xval v) (R K')
  | Kdel K' => Xdel (R K')
  | Kunpack γ x K' e => Xunpack γ x (R K') e
  | KpackL K' e => Xpack (R K') e
  | KpackR ℓ K' => Xpack (Xval ℓ) (R K')
  | KpairL K' e => Xpair (R K') e
  | KpairR v K' => Xpair (Xval v) (R K')
  | Kunpair x1 x2 K' e => Xunpair x1 x2 (R K') e
  | Kifz K' e0 e1 => Xifz (R K') e0 e1
  | Kreturn K' => Xreturn (R K')
  | Kcall foo K' => Xcall foo (R K')
  end
.
(** * Dynamics *)

(** Evaluation of binary expressions. Note that 0 means `true` in S, so `5 < 42` evals to `0`. *)
Definition eval_binop (b : binopsymb) (v0 v1 : value) : option value :=
  let* n0 := match v0 with | Vnat n => Some n | _ => None end in
  let* n1 := match v1 with | Vnat n => Some n | _ => None end in
  Some(Vnat(match b with
       | Bless => (if Nat.ltb n0 n1 then 0 else 1)
       | Badd => (n0 + n1)
       | Bdiv => (n0 / n1)
       | Bsub => (n0 - n1)
       | Bmul => (n0 * n1)
       end))
.
(** Poison used to mark locations in our operational state. *)
Inductive poison : Type :=
| poisonless : poison
| poisoned : poison
.
Notation "'◻'" := (poisonless).
Notation "'☣'" := (poisoned).
Definition poison_eqb :=
  fun (ρ1 ρ2 : poison) =>
    match ρ1, ρ2 with
    | ◻, ◻ | ☣, ☣ => true
    | _, _ => false
    end
.
Lemma poison_eqb_eq ρ1 ρ2 :
  poison_eqb ρ1 ρ2 = true <-> ρ1 = ρ2.
Proof. destruct ρ1, ρ2; now cbn. Qed.
#[local]
Instance poisoneq__Instance : HasEquality poison := {
  eq := poison_eqb ;
  eqb_eq := poison_eqb_eq ;
}.

(* A "dynamic" location contains the location and its poison *)
Record dynloc : Type := mkdL {
  dρ : poison ;     (* wether the location is already deallocated *)
  dn : nat ;          (* allocation size *)
}.
#[local]
Instance etaDynloc : Settable _ := settable! mkdL < dρ; dn>.
Definition dynloc_eqb :=
  fun (dℓ1 dℓ2 : dynloc) =>
    (andb (dℓ1.(dρ) == dℓ2.(dρ))
          (Nat.eqb dℓ1.(dn) dℓ2.(dn)))
.
Lemma dynloc_eqb_eq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = true <-> dℓ0 = dℓ1.
Proof.
  unfold dynloc_eqb; split; intros.
  eq_to_defeq Nat.eqb. cbv in *; destruct dℓ0, dℓ1; inv H. inv H1. apply Nat.eqb_eq in H0. inv H0. reflexivity.
  inv H; eq_to_defeq Nat.eqb; try apply Nat.eqb_eq. repeat split; try apply eq_refl. apply Nat.eqb_refl.
Qed.
#[local]
Instance dynloceq__Instance : HasEquality dynloc := {
  eq := dynloc_eqb ;
  eqb_eq := dynloc_eqb_eq ;
}.
Notation "'dL(' bρ ';' bn ')'" := (({| dρ := bρ ;
                                       dn := bn |}) : dynloc) (at level 80).

Record ptr_key : Type := mkdPtr {
  dL : loc ;         (* the concrete location *)
  dt : ControlTag ;  (* wether the location is on the heap of the component or context *)
}.
#[local]
Instance etaPtrkey : Settable _ := settable! mkdPtr < dL; dt>.
Definition ptr_key_eqb :=
  fun (kℓ0 kℓ1 : ptr_key) =>
    (andb (kℓ0.(dL) == kℓ1.(dL))
          (kℓ0.(dt) == kℓ1.(dt)))
.
Lemma ptr_key_eqb_eq kℓ0 kℓ1 :
  ptr_key_eqb kℓ0 kℓ1 = true <-> kℓ0 = kℓ1.
Proof.
  unfold ptr_key_eqb; split; intros.
  eq_to_defeq x. cbv in *; destruct kℓ0, kℓ1; inv H. easy.
  eq_to_defeq x; inv H; split; apply eq_refl.
Qed.
#[local]
Instance ptrkeyeq__Instance : HasEquality ptr_key := {
  eq := ptr_key_eqb ;
  eqb_eq := ptr_key_eqb_eq ;
}.
Notation "'dK(' bl ';' bt ')'" := (({| dL := bl ; dt := bt |}) : ptr_key) (at level 80).

(** Stores pointers and their respective metadata. *)
Definition ptrstore := mapind ptrkeyeq__Instance dynloc.
Definition snil : ptrstore := mapNil ptrkeyeq__Instance dynloc.

#[local]
Instance nateq__Instance : HasEquality nat := {
  eq := Nat.eqb ;
  eqb_eq := Nat.eqb_eq ;
}.
Definition heap := list (value).
Definition hNil : heap := nil.
Fixpoint Hgrow_aux (H : heap) (s : nat) (default : value) : heap :=
  match s with
  | 0 => H
  | S n' => default :: Hgrow_aux H n' default
  end
.
Definition Hgrow (H : heap) (s : nat) (default : value) : heap :=
  Hgrow_aux H s default
.
(* Context switch indicators. The paper calls these Transfer Tags *)
Variant comms : Type :=
| Qctxtocomp : comms
| Qcomptoctx : comms
| Qinternal : comms
.
Definition comms_eqb (q1 q2 : comms) :=
  match q1, q2 with
  | Qctxtocomp, Qctxtocomp => true
  | Qcomptoctx, Qcomptoctx => true
  | Qinternal, Qinternal => true
  | _, _ => false
  end
.
Lemma comms_eqb_eq (q1 q2 : comms) :
  comms_eqb q1 q2 = true <-> q1 = q2.
Proof. destruct q1, q2; now cbn. Qed.
#[local]
Instance commseq__Instance : HasEquality comms := {
  eq := comms_eqb ;
  eqb_eq := comms_eqb_eq ;
}.
Definition string_of_comms (q : comms) :=
  match q with
  | Qctxtocomp => "?"%string
  | Qcomptoctx => "!"%string
  | Qinternal => "∅"%string
  end
.
(* Continuation Stacks *)
Definition active_ectx := list (evalctx * vart).

#[local]
Existing Instance varteq__Instance | 0.
Record CfState : Type := mkΨ {
  CΞ : symbols ;
  Cξ : commlib ;
  CKs : active_ectx ;
}.
#[local]
Instance etaCfState : Settable _ := settable! mkΨ <CΞ; Cξ; CKs>.
Record MemState : Type := mkΦ {
  MH__ctx : heap ;
  MH__comp : heap ;
  MΔ : ptrstore ;
}.
#[local]
Instance etaMemState : Settable _ := settable! mkΦ <MH__ctx; MH__comp; MΔ>.
Definition EmptyΦ : MemState := mkΦ hNil hNil snil.
Record state : Type := mkΩ {
  SF : CSC.Fresh.fresh_state ;
  SΨ : CfState ;
  St : ControlTag ;
  SΦ : MemState ;
}.
#[local]
Instance etaState : Settable _ := settable! mkΩ <SF; SΨ; St; SΦ>.

Import RecordSetNotations.

Definition Htgrow (Φ : MemState) (s : nat) (t : ControlTag) (default : value) : MemState :=
  match t with
  | CCtx => let H := Hgrow Φ.(MH__ctx) s default in (Φ <| MH__ctx := H |>)
  | CComp => let H := Hgrow Φ.(MH__comp) s default in (Φ <| MH__comp := H |>)
  end
.
Definition getH (Φ : MemState) (t : ControlTag) : heap :=
  match t with
  | CCtx => Φ.(MH__ctx)
  | CComp => Φ.(MH__comp)
  end
.
Definition setH (Φ : MemState) (t : ControlTag) (H : heap) : MemState :=
  match t with
  | CCtx => Φ <| MH__ctx := H |>
  | CComp => Φ <| MH__comp := H |>
  end
.

Notation "'Ψ(' Ξ ';' ξ ';' Ks ')'" := ({| CΞ := Ξ ; Cξ := ξ ; CKs := Ks |}) (at level 81, ξ at next level, Ks at next level).
Notation "'Φ(' H__ctx ';' H__comp ';' Δ ')'" := ({| MH__ctx := H__ctx ; MH__comp := H__comp ; MΔ := Δ |}) (at level 81, H__comp at next level, Δ at next level).
Notation "'Ωa(' F ';' Ψ ';' t ';' Φ ')'" := ({| SF := F ; SΨ := Ψ ; St := t ; SΦ := Φ |}) (at level 81, Ψ at next level, t at next level, Φ at next level).
Notation "'Ω(' F ';' Ξ ';' ξ ';' Ks ';' t ';' H__ctx ';' H__comp ';' Δ ')'" :=
  (Ωa(F ; (Ψ(Ξ ; ξ ; Ks) : CfState) ; t ; (Φ(H__ctx ; H__comp ; Δ) : MemState))) (at level 81, Δ at next level).
Definition nodupinv (Ω : state) : Prop :=
  nodupinv (Ω.(SΨ).(CΞ)) /\ nodupinv (Ω.(SΦ).(MΔ))
.
Lemma nodupinv_empty (Ξ : symbols) (ξ : commlib) :
  Util.nodupinv Ξ ->
  nodupinv (Ω(Fresh.empty_fresh; Ξ; ξ; List.nil; CComp; hNil; hNil; snil)).
Proof. intros H; cbn; repeat split; eauto; constructor. Qed.

(** Types of events that may occur in a trace. *)
Variant preevent : Type :=
| Sstart : preevent
| Send (v : value) : preevent
| Salloc (ℓ : loc) (n : nat) : preevent
| Sdealloc (ℓ : loc) : preevent
| Sget (ℓ : loc) (n : nat) : preevent
| Sset (ℓ : loc) (n : nat) (v : value) : preevent
| Scall (q : comms) (foo : vart) (arg : value) : preevent
| Sret (q : comms) (v : value) : preevent
.
Definition preevent_eqb (e1 e2 : preevent) : bool :=
  match e1, e2 with
  | Sstart, Sstart => true
  | Send n1, Send n2 => n1 == n2
  | Salloc ℓ0 n0, Salloc ℓ1 n1 => andb (ℓ0 == ℓ1) (Nat.eqb n0 n1)
  | Sdealloc ℓ0, Sdealloc ℓ1 => ℓ0 == ℓ1
  | Sget ℓ0 n0, Sget ℓ1 n1 => andb (ℓ0 == ℓ1) (Nat.eqb n0 n1)
  | Sset ℓ0 n0 v0, Sset ℓ1 n1 v1 => andb (andb (ℓ0 == ℓ1) (n0 == n1))
                                              (v0 == v1)
  | Scall q1 foo v0, Scall q2 bar v1 => andb (andb (String.eqb foo bar) (v0 == v1)) (q1 == q2)
  | Sret q1 v0, Sret q2 v1 => andb (v0 == v1) (q1 == q2)
  | _, _ => false
  end
.
Lemma preevent_eqb_eq e1 e2 :
  preevent_eqb e1 e2 = true <-> e1 = e2.
Proof.
  destruct e1, e2; cbn; split; intros; try easy; eq_to_defeq value_eqb; eq_to_defeq loc_eqb; eq_to_defeq comms_eqb.
  - now inv H.
  - apply Nat.eqb_eq in H0; inv H0. reflexivity.
  - inv H; split; try easy. apply Nat.eqb_refl.
  - now inv H.
  - apply Nat.eqb_eq in H0; inv H0; reflexivity.
  - inv H; split; try easy. apply Nat.eqb_refl.
  - apply Nat.eqb_eq in H0; inv H0; reflexivity.
  - inv H; repeat split; try easy. apply Nat.eqb_refl.
  - apply String.eqb_eq in H; inv H; reflexivity.
  - inv H; repeat split; easy.
  - inv H; split; easy.
Qed.
#[local]
Instance preeventeq__Instance : HasEquality preevent := {
  eq := preevent_eqb ;
  eqb_eq := preevent_eqb_eq ;
}.
Variant event : Type :=
| SCrash : event
| Sev (e__b : preevent) (t : ControlTag) : event
.
Definition event_eqb (e1 e2 : event) : bool :=
  match e1, e2 with
  | SCrash, SCrash => true
  | Sev e1 t1, Sev e2 t2 => andb (e1 == e2) (t1 == t2)
  | _, _ => false
  end
.
Lemma event_eqb_eq (e1 e2 : event) :
  event_eqb e1 e2 = true <-> e1 = e2.
Proof.
  destruct e1, e2; cbn; split; intros; try easy; eq_to_defeq event_eqb.
  eq_to_defeq preevent_eqb; eq_to_defeq control_tag_eq.
  inv H; eq_to_defeq preevent_eqb; eq_to_defeq control_tag_eq.
Qed.
#[local]
Instance eventeq__Instance : HasEquality event := {
  eq := event_eqb ;
  eqb_eq := event_eqb_eq ;
}.
Notation "'ev(' e ';' t ')'" := (Sev e t) (at level 81, t at next level).
(** Pretty-printing function for better debuggability *)
Definition string_of_preevent (e : preevent) :=
  match e with
  | (Sstart) => "Start"%string
  | (Send v) => String.append ("End "%string) ("v"%string)
  | (Salloc (addr ℓ) n) => String.append
                      (String.append ("Alloc ℓ"%string) (string_of_nat ℓ))
                      (String.append (" "%string) (string_of_nat n))
  | (Sdealloc (addr ℓ)) => String.append ("Dealloc ℓ"%string) (string_of_nat ℓ)
  | (Sget (addr ℓ) n) => String.append
                    (String.append ("Get ℓ"%string) (string_of_nat ℓ))
                    (String.append (" "%string) (string_of_nat n))
  | (Sset (addr ℓ) n m) => String.append
                             (String.append
                               (String.append ("Set ℓ"%string) (string_of_nat ℓ))
                               (String.append (" "%string) ("n"%string)))
                             (String.append (" "%string) ("m"%string))
  | (Scall q foo v) => String.append (String.append
                                     (String.append ("Call "%string)
                                      (String.append (string_of_comms q)
                                       (String.append " "%string foo))) " "%string)
                      ("v"%string)
  | (Sret q v) => String.append ("Ret "%string)
                 (String.append (string_of_comms q)
                  (String.append " "%string "v"%string))
  end
.
Definition string_of_event (e : event) :=
  match e with
  | SCrash => "↯"%string
  | Sev e__b t => String.append (string_of_preevent e__b) (string_of_controltag t)
  end
.

(** A runtime program is a state plus an expression. *)
Inductive rtexpr : Type :=
| RTerm (Ω : state) (e : expr)
| RCrash
.
(* '▷' is `\triangleright and '↯' is `\lightning`` *)
Notation "Ω '▷' e" := ((RTerm Ω e) : rtexpr) (at level 81, e at next level).
Notation "'↯' '▷' 'stuck'" := (RCrash).

(** Substitution, which assumes that the given expression is closed. *)
Definition subst (what : vart) (inn forr : expr) : expr :=
  let fix R e :=
    match e with
    | Xval _ => e
    | Xabort => Xabort
    | Xlet x e0 e1 => if vareq what x then Xlet x (R e0) e1 else Xlet x (R e0) (R e1)
    | Xnew e0 e1 => Xnew (R e0) (R e1)
    | Xdel e => Xdel (R e)
    | Xget e0 e1 e2 => Xget (R e0) (R e1) (R e2)
    | Xset e0 e1 e2 e3 => Xset (R e0) (R e1) (R e2) (R e3)
    | Xvar x => if vareq what x then forr else e
    | Xbinop b e1 e2 => Xbinop b (R e1) (R e2)
    | Xifz c e1 e2 => Xifz (R c) (R e1) (R e2)
    | Xreturn e => Xreturn (R e)
    | Xcall foo e => Xcall foo (R e)
    | Xunpack γ x e0 e1 => if vareq what x then Xunpack γ x (R e0) e1 else Xunpack γ x (R e0) (R e1)
    | Xpack ℓ e => Xpack (R ℓ) (R e)
    | Xpair e0 e1 => Xpair (R e0) (R e1)
    | Xunpair x1 x2 e0 e1 => if orb (vareq what x1) (vareq what x2) then
                              Xunpair x1 x2 (R e0) e1
                            else
                              Xunpair x1 x2 (R e0) (R e1)
    end
  in
  R inn
.
Inductive pstep : PrimStep rtexpr event :=
| e_binop : forall (Ω : state) (n1 n2 n3 : nat) (b : binopsymb),
    Some(Vnat n3) = eval_binop b n1 n2 ->
    Ω ▷ Xbinop b (Xval n1) (Xval n2) --[]--> Ω ▷ (Xval n3)
| e_ifz_true : forall (Ω : state) (e1 e2 : expr),
    Ω ▷ Xifz (Xval 0) e1 e2 --[]--> Ω ▷ e1
| e_ifz_false : forall (Ω : state) (e1 e2 : expr) (n : nat),
    n <> 0 ->
    Ω ▷ Xifz (Xval n) e1 e2 --[]--> Ω ▷ e2
| e_pair : forall (Ω : state) (v1 v2 : value),
    Ω ▷ Xpair (Xval v1) (Xval v2) --[]--> Ω ▷ Xval(Vpair v1 v2)
| e_abort : forall (Ω : state),
    Ω ▷ Xabort --[ (SCrash) ]--> ↯ ▷ stuck
| e_let : forall (Ω : state) (x : vart) (v : value) (e e' : expr),
    e' = subst x e (Xval v) ->
    Ω ▷ Xlet x (Xval v) e --[]--> Ω ▷ e'
| e_unpair : forall (Ω : state) (v1 v2 : value) (x1 x2 : vart) (e e' : expr),
    e' = subst x1 (subst x2 e (Xval v2)) (Xval v1) ->
    Ω ▷ Xunpair x1 x2 (Xval(Vpair v1 v2)) e --[]--> Ω ▷ e'
| e_alloc : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
              (Φ Φ' : MemState) (v : value) (n : nat) (ℓ : loc) (Δ' : ptrstore),
    ℓ = addr(List.length (getH Φ t)) ->
    Util.nodupinv Φ.(MΔ) ->
    push (dK(ℓ ; t)) (dL(◻ ; n)) Φ.(MΔ) = Some Δ' ->
    Φ' = Htgrow (Φ <| MΔ := Δ' |>) n t v ->
    (Ωa(F ; Ψ ; t ; Φ)) ▷ Xnew (Xval v) (Xval n) --[ ev( Salloc ℓ n ; t ) ]--> (Ωa(F ; Ψ ; t ; Φ')) ▷ Xval (Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ)))
| e_delete : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
               (Φ Φ' : MemState) (n : nat) (ℓ : loc) (ρ : poison) (Δ1 Δ2 : ptrstore),
    Util.nodupinv (Δ1 ◘ (dK(ℓ ; t)) ↦ (dL(ρ ; n)) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK(ℓ ; t)) ↦ dL(ρ ; n) ◘ Δ2) ->
    Φ' = Φ <| MΔ := Δ1 ◘ (dK(ℓ ; t)) ↦ (dL(☣ ; n)) ◘ Δ2 |> ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xdel (Xval (Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ)))) --[ ev( Sdealloc ℓ ; t ) ]--> Ωa(F ; Ψ ; t ; Φ') ▷ Xval 0
| e_get : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
            (Φ : MemState) (n m ℓ : nat) (v : value)  (ρ : poison) (Δ1 Δ2 : ptrstore),
    Util.nodupinv (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(ρ ; m) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(ρ ; m) ◘ Δ2) ->
    (List.nth_error (getH Φ t) (ℓ + n) = (Some v) \/ (v = Vnat 1729 /\ List.nth_error (getH Φ t) (ℓ + n) = None)) ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xget (Xval Vcap) (Xval(Vptr (addr ℓ))) (Xval n) --[ ev( Sget (addr ℓ) n ; t ) ]--> Ωa(F ; Ψ ; t ; Φ) ▷ Xval (Vpair Vcap v)
| e_set : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag) (H' : heap)
            (Φ Φ' : MemState) (n m ℓ : nat) (w : value) (ρ : poison) (Δ1 Δ2 : ptrstore),
    Util.nodupinv (Δ1 ◘ (dK((addr ℓ); t)) ↦ dL(ρ ; m) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK((addr ℓ); t)) ↦ dL(ρ ; m) ◘ Δ2) ->
    (NoDupList.swap_nth_aux (getH Φ t) (ℓ + n) (w) = Some H' \/ (H' = getH Φ t /\ NoDupList.swap_nth_aux (getH Φ t) (ℓ + n) (w) = None)) ->
    Φ' = setH Φ t H' ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xset (Xval Vcap) (Xval(Vptr (addr ℓ))) (Xval n) (Xval w) --[ ev( Sset (addr ℓ) n w ; t ) ]--> Ωa(F ; Ψ ; t ; Φ') ▷ Xval (Vpair Vcap w)
| e_unpack : forall (Ω : state) (γ x : vart) (ℓ : loc) (v : value) (e e' : expr),
    e' = subst γ (subst x e (Xval v)) (Xval (Vptr ℓ)) ->
    Ω ▷ Xunpack γ x (Xval (Vpack (LConst ℓ) v)) e --[]--> Ω ▷ e'
| e_pack : forall (Ω : state) (ℓ : loc) (v : value),
    Ω ▷ Xpack (Xval (Vptr ℓ)) (Xval v) --[]--> Ω ▷ Xval(Vpack (LConst ℓ) v)
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
  intros H; cbv in H; dependent induction H; try easy.
  - (* e_alloc *) admit.
  - (* e_del *) inv H1. inv H2. intros H1. inv H1; constructor; cbn in *; auto.
    admit.
  - (* e_set *) admit.
Admitted.

(** functional version of the above *)
Definition pstepf (r : rtexpr) : option (option event * rtexpr) :=
  match r with
  | RCrash => None
  | RTerm Ω e =>
    match e with
    | Xbinop b (Xval v1) (Xval v2) =>
      let* v3 := eval_binop b v1 v2 in
      Some(None, Ω ▷ Xval v3)
    | Xifz (Xval(Vnat n)) e1 e2 =>
      match n with
      | 0 => Some(None, Ω ▷ e1)
      | _ => Some(None, Ω ▷ e2)
      end
    | Xpair (Xval v1) (Xval v2) =>
      Some(None, Ω ▷ Xval(Vpair v1 v2))
    | Xabort => Some(Some SCrash, ↯ ▷ stuck)
    | Xlet x (Xval v) e =>
      Some(None, Ω ▷ subst x e (Xval v))
    | Xunpair x1 x2 (Xval(Vpair v1 v2)) e =>
      Some(None, Ω ▷ subst x1 (subst x2 e (Xval v2)) (Xval v1))
    | Xnew (Xval v) (Xval(Vnat n)) =>
      let ℓ := addr(List.length (getH Ω.(SΦ) Ω.(St))) in
      let* _ := undup Ω.(SΦ).(MΔ) in
      let* Δ' := push (dK(ℓ ; Ω.(St))) (dL(◻ ; n)) Ω.(SΦ).(MΔ) in
      let Φ' := Htgrow (Ω.(SΦ) <| MΔ := Δ' |>) n Ω.(St) v in
      let Ω' := Ω <| SΦ := Φ' |> in
      Some(Some(ev(Salloc ℓ n ; Ω.(St))), Ω' ▷ Xval(Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ))))
    | Xdel (Xval(Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ')))) =>
      if ℓ == ℓ' then
        let* Δ := undup Ω.(SΦ).(MΔ) in
        let* (Δ1, dK, dl, Δ2) := splitat Δ (dK(ℓ ; Ω.(St))) in
        if ℓ == dK.(dL) then
          let dl' := dl <| dρ := ☣ |> in
          let Φ' := Ω.(SΦ) <| MΔ := Δ1 ◘ dK ↦ dl' ◘ Δ2 |> in
          let Ω' := Ω <| SΦ := Φ' |> in
          if Ω.(St) == dK.(dt) then
            Some(Some(ev(Sdealloc ℓ ; Ω.(St))), Ω' ▷ Xval 0)
          else
            None
        else
          None
      else
        None
    | Xget (Xval Vcap) (Xval(Vptr(addr ℓ))) (Xval(Vnat n)) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, dk, dl, Δ2) := splitat Δ (dK((addr ℓ) ; Ω.(St))) in
      let '(addr ln) := dk.(dL) in
      if ℓ == ln then
        let v := match List.nth_error (getH Ω.(SΦ) Ω.(St)) (ℓ+n) with
                 | Some(v) => v
                 | _ => Vnat 1729
                 end
        in
        if Ω.(St) == dk.(dt) then
          Some(Some(ev(Sget (addr ℓ) n ; Ω.(St))), Ω ▷ Xval(Vpair Vcap v))
        else
          None
      else
        None
    | Xset (Xval Vcap) (Xval(Vptr(addr ℓ))) (Xval(Vnat n)) (Xval w) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, dk, dl, Δ2) := splitat Δ (dK((addr ℓ) ; Ω.(St))) in
      let '(addr ln) := dk.(dL) in
      if ℓ == ln then
        let H' := match NoDupList.swap_nth_aux (getH Ω.(SΦ) Ω.(St)) (ℓ+n) (w) with
                  | Some(H') => H'
                  | _ => getH Ω.(SΦ) Ω.(St)
                  end
        in
        let Φ' := setH Ω.(SΦ) Ω.(St) H' in
        let Ω' := Ω <| SΦ := Φ' |> in
        if Ω.(St) == dk.(dt) then
          Some(Some(ev(Sset (addr ℓ) n w ; Ω.(St))), Ω' ▷ Xval(Vpair Vcap w))
        else
          None
      else
        None
    | Xunpack γ x (Xval(Vpack (LConst ℓ) v)) e =>
      let e' := subst γ (subst x e (Xval v)) (Xval(Vptr ℓ)) in
      Some(None, Ω ▷ e')
    | Xpack (Xval(Vptr ℓ)) (Xval v) =>
      Some(None, Ω ▷ Xval(Vpack (LConst ℓ) v))
    | _ => None
    end
  end
.
Ltac grab_value e :=
  let n := fresh "n" in
  let v0 := fresh "v0" in
  let v1 := fresh "v1" in
  let l := fresh "ℓ" in
  let v := fresh "v" in
  (destruct e as [[n | v0 v1 | (* Vcap *) | l | l v]| | | | | | | | | | | | | | |]; try congruence)
.
Ltac grab_value2 e1 e2 := (grab_value e1; grab_value e2).
Ltac grab_value3 e1 e2 e3 := (grab_value e1; grab_value e2; grab_value e3).
Ltac grab_value4 e1 e2 e3 e4 := (grab_value e1; grab_value e2; grab_value e3; grab_value e4).

Lemma Hget_none (H : heap) (n : nat) :
  n >= List.length H -> List.nth_error H n = None.
Proof.
  revert n; induction H; cbn; intros.
  - destruct n; easy.
  - destruct n; cbn; try easy. assert (n >= List.length H) by lia.
    now specialize (IHlist n H1).
Qed.
Lemma Hget_some (H : heap) (n : nat) :
  n < List.length H -> exists v, List.nth_error H n = Some v.
Proof.
  revert n; induction H; cbn; intros.
  - destruct n; easy.
  - destruct n; cbn; try easy. exists a; easy.
    assert (n < List.length H) by lia.
    now specialize (IHlist n H1).
Qed.
Lemma Hset_none (H : heap) (n : nat) v :
  n >= List.length H -> NoDupList.swap_nth_aux H n v = None.
Proof.
  revert n; induction H; cbn; intros.
  - now inv H.
  - destruct n; try easy. assert (n >= List.length H) by lia.
    specialize (IHlist n H1); now rewrite IHlist.
Qed.
Lemma Hset_some (H : heap) (n : nat) v :
  n < List.length H -> exists H', NoDupList.swap_nth_aux H n v = Some H'.
Proof.
  revert n; induction H; cbn; intros.
  - destruct n; easy.
  - destruct n; cbn; try easy. exists (v :: H); easy.
    assert (n < List.length H) by lia.
    specialize (IHlist n H1); deex. exists (a :: H'); now rewrite IHlist.
Qed.

(** We use an alternative notation of pstep here that does not constrain a to be *either* Some/None *)
Lemma equiv_pstep (r0 : rtexpr) (a : option event) (r1 : rtexpr) :
  r0 --[, a ]--> r1 <-> pstepf r0 = Some(a, r1).
Proof.
  split.
  - intros H; cbv in H; dependent induction H; cbn.
    + (* binop *) destruct b; inv H; easy.
    + (* ifz-true *) easy.
    + (* ifz-false *) destruct n; easy.
    + (* pair *) easy.
    + (* crash *) easy.
    + (* let *) now inv H.
    + (* unpair *) now inv H.
    + (* alloc *) crush_undup (MΔ Φ); inv H; rewrite H1; easy.
    + (* del *) eq_to_defeq loc_eqb; rewrite eq_refl; apply nodupinv_equiv_undup in H as H'. inv H0. rewrite H3, H'.
      apply splitat_elim in H as ->. eq_to_defeq loc_eqb; rewrite eq_refl. eq_to_defeq control_tag_eq; rewrite eq_refl. easy.
    + (* get *) apply nodupinv_equiv_undup in H as H'. inv H0. rewrite H3, H'.
      apply splitat_elim in H as ->. cbn. rewrite Nat.eqb_refl. cbn; eq_to_defeq control_tag_eq; rewrite eq_refl. destruct H1 as [-> | [-> ->]]; easy.
    + (* set *) apply nodupinv_equiv_undup in H as H'0. rewrite H0, H'0.
      apply splitat_elim in H as ->. cbn. rewrite Nat.eqb_refl. inv H2. eq_to_defeq control_tag_eq; rewrite eq_refl. destruct H1 as [-> | [-> ->]]; try easy.
    + (* unpack *) now inv H.
    + (* pack *) easy.
  - destruct r0 as [Ω e|]; try now cbn.
    revert Ω a r1; induction e; intros; cbn in H.
    + (* value *) inv H.
    + (* variable *) inv H.
    + (* binop *) grab_value2 e1 e2; destruct symb; inv H; now constructor.
    + (* get *) grab_value3 e1 e2 e3; destruct ℓ; try now inv H. crush_undup (MΔ (SΦ Ω)).
      apply nodupinv_equiv_undup in Hx as Hy; recognize_split; elim_split. cbn in H.
      rewrite Nat.eqb_refl in H. destruct v; cbn in H; eq_to_defeq control_tag_eq. rewrite eq_refl in H.
      crush_option (List.nth_error (getH (SΦ Ω) (St Ω)) (n0 + n)).
      * inv H. cbn in *. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; econstructor; try eassumption. now left.
      * rewrite Hx0 in H. inv H. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; econstructor; try eassumption. right; now split.
    + (* set *) grab_value3 e1 e2 e3; destruct ℓ; try now inv H. destruct e4; try now inv H. crush_undup (MΔ (SΦ Ω)).
      apply nodupinv_equiv_undup in Hx as Hy; recognize_split; elim_split. destruct v0. cbn in H.
      rewrite Nat.eqb_refl in H.
      cbn in H; eq_to_defeq control_tag_eq. rewrite eq_refl in H.
      crush_option (NoDupList.swap_nth_aux (getH (SΦ Ω) (St Ω)) (n0 + n) v).
      * inv H. cbn in *. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; cbn in *; econstructor; cbn; try eassumption. left; eassumption. reflexivity.
      * rewrite Hx0 in H. inv H. cbn in *. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; cbn in *; econstructor; cbn; try eassumption. now right. reflexivity.
    + (* let *) grab_value e1; inv H; now constructor.
    + (* new *) destruct e1; try now inv H. grab_value e2.
      crush_undup (MΔ (SΦ Ω)).
      crush_option (push (dK(addr (List.length (getH (SΦ Ω) (St Ω))) ; Ω.(St))) {| dρ := ◻; dn := n |} (MΔ (SΦ Ω))).
      inv H. destruct Ω; econstructor; try eassumption. now cbn. now apply nodupinv_equiv_undup in Hx. now symmetry.
    + (* del *) grab_value e. destruct ℓ; try now inv H. destruct v; try now inv H. destruct v1, v2; try now inv H.
      eq_to_defeq loc_eqb. destruct (eq_dec l l0); try (apply neqb_neq in H0; now rewrite H0 in H).
      rewrite H0 in H; rewrite eq_refl in H. crush_undup (MΔ (SΦ Ω)). apply nodupinv_equiv_undup in Hx as Hy; recognize_split; elim_split.
      subst. eq_to_defeq loc_eqb; rewrite eq_refl in H. inv H.
      destruct v; cbn in *; rewrite H1 in Hy. eq_to_defeq control_tag_eq. rewrite eq_refl in H2.
      inv H2. destruct Ω; cbn in *; econstructor; cbn; try eassumption. easy.
    + (* unpack *) grab_value e1; inv H; destruct ℓ; try now inv H1; destruct Ω; cbn in *; econstructor.
    + (* pack *) grab_value2 e1 e2; inv H; constructor.
    + (* pair *) grab_value2 e1 e2; inv H; constructor.
    + (* unpair *) grab_value e1; inv H; constructor; reflexivity.
    + (* return *) inv H.
    + (* call *) inv H.
    + (* ifz *) grab_value e1; destruct n; inv H; constructor; easy.
    + (* crash *) inv H; constructor.
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
  | Xval _ => None
  | Xvar _ => None
  | Xabort => Some(Khole, Xabort)
  | Xbinop b e1 e2 =>
    match e1, e2 with
    | Xval(Vnat n1), Xval(Vnat n2) =>
      Some(Khole, Xbinop b (Xval n1) (Xval n2))
    | Xval(Vnat n1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KbinopR b n1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KbinopL b K e2, e1')
    end
  | Xget e0 e1 e2 =>
    match e0, e1, e2 with
    | Xval(v0), Xval(v1), Xval(v2) =>
      Some(Khole, Xget (Xval v0) (Xval v1) (Xval v2))
    | Xval(v0), Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KgetR v0 v1 K, e2')
    | Xval(v), en1, e2 =>
      let* (K, e1') := evalctx_of_expr en1 in
      Some(KgetM v K e2, e1')
    | _, _, _ =>
      let* (K, e0') := evalctx_of_expr e0 in
      Some(KgetL K e1 e2, e0')
    end
  | Xset e0 e1 e2 e3 =>
    match e0, e1, e2, e3 with
    | Xval(v0), Xval(v1), Xval(v2), Xval(v3) =>
      Some (Khole, Xset (Xval v0) (Xval v1) (Xval v2) (Xval v3))
    | Xval(v0), Xval(v1), Xval(v2), en3 =>
      let* (K, e3') := evalctx_of_expr en3 in
      Some (KsetR v0 v1 v2 K, e3')
    | Xval(v0), Xval(v1), en2, en3 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some (KsetM1 v0 v1 K en3, e2')
    | Xval(v0), en1, en2, en3 =>
      let* (K, e1') := evalctx_of_expr en1 in
      Some (KsetM0 v0 K en2 en3, e1')
    | _, _, _, _ =>
      let* (K, e0') := evalctx_of_expr e0 in
      Some (KsetL K e1 e2 e3, e0')
    end
  | Xlet x e1 e2 =>
    match e1 with
    | Xval(v) =>
      Some(Khole, Xlet x (Xval v) e2)
    | _ => let* (K, e1') := evalctx_of_expr e1 in
          Some(Klet x K e2, e1')
    end
  | Xunpair x1 x2 e1 e2 =>
    match e1 with
    | Xval(v) =>
      Some(Khole, Xunpair x1 x2 (Xval v) e2)
    | _ => let* (K, e1') := evalctx_of_expr e1 in
          Some(Kunpair x1 x2 K e2, e1')
    end
  | Xnew e1 e2 =>
    match e1, e2 with
    | Xval(v1), Xval(v2) =>
      Some(Khole, Xnew (Xval v1) (Xval v2))
    | Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KnewR v1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KnewL K e2, e1')
    end
  | Xdel e =>
    match e  with
    | Xval(v) =>
      Some(Khole, Xdel (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kdel K, e')
    end
  | Xunpack γ x e0 e1 =>
    match e0 with
    | Xval(v0) =>
      Some(Khole, Xunpack γ x (Xval v0) e1)
    | en0 =>
      let* (K, e0') := evalctx_of_expr en0 in
      Some(Kunpack γ x K e1, e0')
    end
  | Xpack e1 e2 =>
    match e1, e2 with
    | Xval(v1), Xval(v2) =>
      Some(Khole, Xpack (Xval v1) (Xval v2))
    | Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KpackR v1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KpackL K e2, e1')
    end
  | Xpair e1 e2 =>
    match e1, e2 with
    | Xval(v1), Xval(v2) =>
      Some(Khole, Xpair (Xval v1) (Xval v2))
    | Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KpairR v1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KpairL K e2, e1')
    end
  | Xreturn e =>
    match e with
    | Xval v =>
      Some(Khole, Xreturn (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kreturn K, e')
    end
  | Xcall foo e =>
    match e with
    | Xval v =>
      Some(Khole, Xcall foo (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kcall foo K, e')
    end
  | Xifz c e0 e1 =>
    match c with
    | Xval(v) =>
      Some(Khole, Xifz (Xval v) e0 e1)
    | _ => let* (K, c') := evalctx_of_expr c in
          Some(Kifz K e0 e1, c')
    end
  end
.
(** Checks wether the thing that is filled into the hole is somehow structurually compatible with pstep *)
(** This check does not apply to contextual steps *)
Definition pstep_compatible (e : expr) : option expr :=
  match e with
  | Xifz (Xval v) e0 e1 => Some (Xifz (Xval v) e0 e1)
  | Xabort => Some (Xabort)
  | Xbinop b (Xval v1) (Xval v2) => Some(Xbinop b (Xval v1) (Xval v2))
  | Xlet x (Xval v) e => Some(Xlet x (Xval v) e)
  | Xpair (Xval v1) (Xval v2) => Some(Xpair (Xval v1) (Xval v2))
  | Xunpair x1 x2 (Xval v) e => Some(Xunpair x1 x2 (Xval v) e)
  | Xnew (Xval v1) (Xval v2) => Some(Xnew (Xval v1) (Xval v2))
  | Xdel (Xval v) => Some(Xdel (Xval v))
  | Xget (Xval v0) (Xval v1) (Xval v2) => Some(Xget (Xval v0) (Xval v1) (Xval v2))
  | Xset (Xval v0) (Xval v1) (Xval v2) (Xval v3) => Some(Xset (Xval v0) (Xval v1) (Xval v2) (Xval v3))
  | Xpack (Xval v1) (Xval v2) => Some(Xpack (Xval v1) (Xval v2))
  | Xunpack γ x (Xval v) e => Some(Xunpack γ x (Xval v) e)
  | _ => None
  end
.
(** This function subsumes `pstep_compatible`, but it also includes the contextual steps. *)
Definition pestep_compatible (e : expr) : option expr :=
  match e with
  | Xifz (Xval v) e0 e1 => Some (Xifz (Xval v) e0 e1)
  | Xabort => Some (Xabort)
  | Xbinop b (Xval v1) (Xval v2) => Some(Xbinop b (Xval v1) (Xval v2))
  | Xlet x (Xval v) e => Some(Xlet x (Xval v) e)
  | Xpair (Xval v1) (Xval v2) => Some(Xpair (Xval v1) (Xval v2))
  | Xunpair x1 x2 (Xval v) e => Some(Xunpair x1 x2 (Xval v) e)
  | Xnew (Xval v1) (Xval v2) => Some(Xnew (Xval v1) (Xval v2))
  | Xdel (Xval v) => Some(Xdel (Xval v))
  | Xget (Xval v0) (Xval v1) (Xval v2) => Some(Xget (Xval v0) (Xval v1) (Xval v2))
  | Xset (Xval v0) (Xval v1) (Xval v2) (Xval v3) => Some(Xset (Xval v0) (Xval v1) (Xval v2) (Xval v3))
  | Xpack (Xval v1) (Xval v2) => Some(Xpack (Xval v1) (Xval v2))
  | Xunpack γ x (Xval v) e => Some(Xunpack γ x (Xval v) e)
  | Xcall foo (Xval v) => Some(Xcall foo (Xval v))
  | Xreturn (Xval v) => Some(Xreturn (Xval v))
  | _ => None
  end
.
Lemma return_pestep_compat (v : value) :
  Some(Xreturn (Xval v)) = pestep_compatible (Xreturn (Xval v)).
Proof. now cbn. Qed.
Lemma call_pestep_compat foo (v : value) :
  Some(Xcall foo (Xval v)) = pestep_compatible (Xcall foo (Xval v)).
Proof. now cbn. Qed.
Lemma pstep_compat_weaken e :
  Some e = pstep_compatible e ->
  Some e = pestep_compatible e.
Proof. induction e; now cbn. Qed.
#[global]
Hint Resolve pstep_compat_weaken call_pestep_compat return_pestep_compat : core.

(** ** Environment Semantics  *)
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
Definition comm (t : ControlTag) : comms :=
  match t with
  | CCtx => Qctxtocomp
  | CComp => Qcomptoctx
  end
.
Inductive context_switched : commlib -> vart -> ControlTag -> comms -> ControlTag -> Prop :=
| SwitchCtxToComp : forall (ξ : commlib) (foo : vart),
    (* foo is called, foo is part of component, so for switch the call must've been CCtx *)
    List.In foo ξ ->
    context_switched ξ foo CCtx Qctxtocomp CComp
| SwitchCompToCtx : forall (ξ : commlib) (foo : vart),
    (* foo is called, foo is not part of component, so for switch the call must've been CComp *)
    ~(List.In foo ξ) ->
    context_switched ξ foo CComp Qcomptoctx CCtx
| NoSwitchComp : forall (ξ : commlib) (foo : vart),
    (* component calling foo, which is in component, is an internal fn call *)
    List.In foo ξ ->
    context_switched ξ foo CComp Qinternal CComp
| NoSwitchCtx : forall (ξ : commlib) (foo : vart),
    (* context calling foo, which is in context, is an internal fn call *)
    ~(List.In foo ξ) ->
    context_switched ξ foo CCtx Qinternal CCtx
.
Definition context_switchedf (ξ : commlib) (foo : vart) (t : ControlTag) : (comms * ControlTag) :=
  match List.find (fun x => foo == x) ξ with
  | Some _ =>
    match t with
    | CCtx => (* SwitchCtxToComp *)
      (Qctxtocomp, CComp)
    | CComp => (* NoSwitchComp *)
      (Qinternal, CComp)
    end
  | None =>
    match t with
    | CCtx => (* NoSwitchCtx *)
      (Qinternal, CCtx)
    | CComp => (* SwitchCompToCtx *)
      (Qcomptoctx, CCtx)
    end
  end
.
Lemma context_switched_equiv (ξ : commlib) (foo : vart) (t t' : ControlTag) (q : comms) :
  context_switched ξ foo t q t' <-> context_switchedf ξ foo t = (q, t').
Proof.
  split; intros H.
  - inv H; unfold context_switchedf.
    + crush_option (List.find (fun x => foo == x) ξ). easy. eapply List.find_none in H0; eauto.
      cbn in H0; eq_to_defeq vareq; apply neqb_neq in H0. contradiction.
    + crush_option (List.find (fun x => foo == x) ξ).
      apply List.find_some in Hx as [Hx Hy]. apply eqb_eq in Hy; subst. contradiction.
    + crush_option (List.find (fun x => foo == x) ξ). easy. eapply List.find_none in Hx; eauto.
      apply neqb_neq in Hx. contradiction.
    + crush_option (List.find (fun x => foo == x) ξ). eapply List.find_some in Hx as [Hx Hy]; eauto.
      apply eqb_eq in Hy; subst; contradiction.
  - unfold context_switchedf in H.
    crush_option (List.find (fun x => foo == x) ξ); destruct t; inv H.
    + constructor. apply List.find_some in Hx as [Hx Hy].
      apply eqb_eq in Hy; subst; assumption.
    + constructor. apply List.find_some in Hx as [Hx Hy].
      apply eqb_eq in Hy; subst; assumption.
    + cbn in Hx. rewrite Hx in H1. inv H1. constructor. intros H. eapply List.find_none in Hx; eauto.
      eq_to_defeq vareq. apply neqb_neq in Hx; contradiction.
    + cbn in Hx. rewrite Hx in H1. inv H1. constructor. intros H. eapply List.find_none in Hx; eauto.
      eq_to_defeq vareq. apply neqb_neq in Hx; contradiction.
Qed.

Inductive estep : EctxStep rtexpr event :=
| E_ectx : forall (Ω Ω' : state) (e e' e0 e0' : expr) (o : option event) (K : evalctx),
    (*Some(K,e) = evalctx_of_expr e0 ->*)
    Some e = pstep_compatible e ->
    e0 = insert K e ->
    e0' = insert K e' ->
    Ω ▷ e --[, o ]--> Ω' ▷ e' ->
    Ω ▷ e0 ==[, o ]==> Ω' ▷ e0'
| E_stuck : forall (Ω : state) (e e0 : expr) (K : evalctx),
    (*Some(K,e) = evalctx_of_expr e0 ->*)
    Some e = pstep_compatible e ->
    e0 = insert K e ->
    Ω ▷ e --[ SCrash ]--> ↯ ▷ stuck ->
    Ω ▷ e0 ==[ SCrash ]==> ↯ ▷ stuck
| E_start : forall (Ω Ω' : state) (Ξ1 Ξ2 : symbols) (main : symbol) (Ψ' : CfState) (e : expr),
    Ω.(SΨ).(CKs) = nil ->
    Ω.(St) = CComp ->
    Ω.(SΦ) = EmptyΦ ->
    ((Ω.(SΨ).(CΞ)) = (Ξ1 ◘ "main"%string ↦ main ◘ Ξ2)) ->
    e = subst (vart_of_symbol main) (expr_of_symbol main) (Xval 0) ->
    Ψ' = Ω.(SΨ) <| CKs := ((Khole, "main"%string) :: nil)%list |> ->
    Ω' = Ω <| St := CCtx |> <| SΨ := Ψ' |> ->
    Ω ▷ Xcall "main"%string (Xval 0) ==[ ev(Sstart ; CComp) ]==> Ω' ▷ e
| E_call : forall (Ω Ω' : state) (Ξ1 Ξ2 : symbols) (foov : vart) (foo : symbol) (Ψ' : CfState)
             (x : vart) (v : value) (K : evalctx) (e0 e0' : expr) (q : comms) (t' : ControlTag),
    Ω.(SΨ).(CΞ) = (Ξ1 ◘ foov ↦ foo ◘ Ξ2) ->
    context_switched Ω.(SΨ).(Cξ) foov Ω.(St) q t' ->
    e0' = subst (vart_of_symbol foo) (expr_of_symbol foo) (Xval v) ->
    Ψ' = Ω.(SΨ) <| CKs := ((K, foov) :: Ω.(SΨ).(CKs)) |> ->
    Ω' = Ω <| St := t' |> <| SΨ := Ψ' |> ->
    e0 = insert K (Xcall foov (Xval v)) ->
    Ω ▷ e0 ==[ ev(Scall q foov v ; Ω.(St)) ]==> Ω' ▷ e0'
| E_ret : forall (Ω Ω' : state) (foov : vart) (K K__foo : evalctx) (Ψ' : CfState)
            (e0 e0' : expr) (v : value) (q : comms) (Ks : active_ectx) (t' : ControlTag),
    context_switched Ω.(SΨ).(Cξ) foov Ω.(St) q t' ->
    Ω.(SΨ).(CKs) = ((K__foo, foov) :: Ks)%list ->
    Ks <> nil -> (* <- prevent E_end from firing *)
    Ψ' = Ω.(SΨ) <| CKs := Ks |> ->
    Ω' = Ω <| St := t' |> <| SΨ := Ψ' |> ->
    e0 = insert K (Xreturn (Xval v)) ->
    e0' = insert K__foo (Xval v) ->
    Ω ▷ e0 ==[ ev(Sret q v ; Ω.(St)) ]==> Ω' ▷ e0'
| E_end : forall (Ω Ω' : state) (K : evalctx) (Ψ' : CfState)
            (e0 : expr) (v : value),
    Ω.(SΨ).(CKs) = ((Khole, "main"%string) :: nil)%list ->
    Ψ' = Ω.(SΨ) <| CKs := nil |> ->
    Ω' = Ω <| St := CComp |> <| SΨ := Ψ' |> ->
    e0 = insert K (Xreturn (Xval v)) ->
    Ω ▷ e0 ==[ ev(Send v ; CCtx) ]==> Ω' ▷ (Xval v)
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
  remember (Ω ▷ e) as r0; remember (Ω' ▷ e') as r1.
  induction 1; inv Heqr0; inv Heqr1; try easy.
  intros H0; apply pstep_is_nodupinv_invariant in H2; eauto.
Qed.
Local Set Warnings "-cast-in-pattern".

Definition estepf (r : rtexpr) : option (option event * rtexpr) :=
  match r with
  | RCrash => None
  | RTerm Ω e =>
    let* (K, e0) := evalctx_of_expr e in
    match e0 with
    | Xcall foo (Xval v) =>
      let* (Ξ1, foof, foo, Ξ2) := splitat Ω.(SΨ).(CΞ) (foo) in
      let e := subst (vart_of_symbol foo) (expr_of_symbol foo) (Xval v) in
      let Ψ' := Ω.(SΨ) <| CKs := ((K, foof) :: Ω.(SΨ).(CKs))%list |> in
      let (q, t') := context_switchedf Ω.(SΨ).(Cξ) foof Ω.(St) in
      let Ω' := Ω <| St := t' |> <| SΨ := Ψ' |> in
      if String.eqb foof "main"%string then
        if andb (Nat.eqb (List.length Ω.(SΨ).(CKs)) 0)
           (andb (Ω.(St) == CComp)
           (andb (Nat.eqb (List.length Ω.(SΦ).(MH__ctx)) 0)
           (andb (Nat.eqb (List.length Ω.(SΦ).(MH__comp)) 0)
                 (Nat.eqb (Util.length Ω.(SΦ).(MΔ)) 0)))) then
          match v, K, Ω.(SΨ).(CKs), Ω.(St) with
          | Vnat 0, Khole, nil, CComp =>
            Some(Some(ev(Sstart ; CComp)), Ω' ▷ e)
          | _, _, _, _ => None
          end
        else
          (* just a recursive function call to "main", not the initial call, though *)
          Some(Some(ev(Scall q foof v ; Ω.(St))), Ω' ▷ e)
      else
        Some(Some(ev(Scall q foof v ; Ω.(St))), Ω' ▷ e)
    | Xreturn(Xval v) =>
      match Ω.(SΨ).(CKs) with
      | nil => None
      | ((Khole, main)::nil)%list =>
        if String.eqb main "main"%string then
          let Ψ' := Ω.(SΨ) <| CKs := nil |> in
          let Ω' := Ω <| St := CComp |> <| SΨ := Ψ' |> in
          Some(Some(ev(Send v ; CCtx)), Ω' ▷ Xval v)
        else
          None
      | ((K__foo, foo)::Ks)%list =>
        let (q, t') := context_switchedf Ω.(SΨ).(Cξ) foo Ω.(St) in
        let Ψ' := Ω.(SΨ) <| CKs := Ks |> in
        let Ω' := Ω <| St := t' |> <| SΨ := Ψ' |> in
        let e0' := insert K__foo (Xval v) in
        Some(Some(ev(Sret q v ; Ω.(St))), Ω' ▷ e0')
      end
    | _ =>
      let* _ := pstep_compatible e0 in
      let* (a, r') := pstepf (Ω ▷ e0) in
      match r' with
      | RCrash => Some(Some SCrash, ↯ ▷ stuck)
      | RTerm Ω' e0' =>
        let e' := insert K e0' in
        Some(a, Ω' ▷ e')
      end
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
| Cval : forall (e : expr) (v : value), e = Xval v -> is_val e
.
(** A runtime expression is classified as value if the associated state is also freed completely. *)
Inductive rtexpr_is_val : rtexpr -> Prop :=
| CRTval : forall (Ω : state) (e : expr) (v : value),
    (forall l t dl, mget Ω.(SΦ).(MΔ) (dK(l ; t)) = Some dl -> dl.(dρ) = ☣) ->
    nodupinv Ω ->
    e = Xval v ->
    rtexpr_is_val (Ω ▷ e)
| CRTfail : rtexpr_is_val (↯ ▷ stuck) (* this will let star_step terminate with a crash *)
.
Lemma expr_val_dec e :
  { is_val e } + { ~is_val e }.
Proof.
  induction e.
  1: destruct v; left; eauto using Cval.
  all: right; intros H; inv H; inv H0.
Qed.
Lemma grab_ectx e K e0 :
  Some e0 = pestep_compatible e0 ->
  e = insert K e0 ->
  evalctx_of_expr e = Some(K, e0)
.
Proof.
Admitted.

Lemma easy_ectx e0 :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e0 = Some(Khole, e0).
Proof. Admitted.

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
  - (* get *) grab_value3 e1 e2 e3.
  - (* set *) grab_value4 e1 e2 e3 e4.
  - (* let *) grab_value e1.
  - (* new *) grab_value2 e1 e2.
  - (* del *) grab_value e.
  - (* unpack *) grab_value e1.
  - (* pack *) grab_value2 e1 e2.
  - (* pair *) grab_value2 e1 e2.
  - (* unpair *) grab_value e1.
  - (* ifz *) grab_value e1.
Qed.

Lemma pestep_compatible_some e e' :
  pestep_compatible e = Some e' -> e = e'.
Proof.
  revert e'; induction e; intros; cbn in H; try congruence.
  - (* binop *) grab_value2 e1 e2.
  - (* get *) grab_value3 e1 e2 e3.
  - (* set *) grab_value4 e1 e2 e3 e4.
  - (* let *) grab_value e1.
  - (* new *) grab_value2 e1 e2.
  - (* del *) grab_value e.
  - (* unpack *) grab_value e1.
  - (* pack *) grab_value2 e1 e2.
  - (* pair *) grab_value2 e1 e2.
  - (* unpair *) grab_value e1.
  - (* return *) grab_value e.
  - (* call *) grab_value e.
  - (* ifz *) grab_value e1.
Qed.
Lemma elim_ectx_ret K (v : value) :
  evalctx_of_expr (insert K (Xreturn (Xval v))) = Some(K, Xreturn (Xval v)).
Proof. remember (insert K (Xreturn (Xval v))); eapply grab_ectx in Heqe; eauto. Qed.
Lemma elim_ectx_call K foo (v : value) :
  evalctx_of_expr (insert K (Xcall foo (Xval v))) = Some(K, Xcall foo (Xval v)).
Proof. remember (insert K (Xcall foo (Xval v))); eapply grab_ectx in Heqe; eauto. Qed.

Lemma equiv_estep r0 a r1 :
  r0 ==[, a ]==> r1 <-> estepf r0 = Some(a, r1).
Proof.
Admitted.

Lemma estepf_is_nodupinv_invariant Ω e Ω' e' a :
  estepf (Ω ▷ e) = Some(a, Ω' ▷ e') ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof. intros H0 H1; apply equiv_estep in H0; apply estep_is_nodupinv_invariant in H0; eauto. Qed.

#[local]
Instance TMS__TraceParams : TraceParams := {
  Ev := event ;
  string_of_event := string_of_event;
}.
#[local]
Instance TMS__LangParams : LangParams := {
  State := rtexpr ;
  Trace__Instance := TMS__TraceParams ;
  step := estep ;
  is_value := rtexpr_is_val ;
}.
Definition tracepref : Type := @Util.tracepref TMS__TraceParams.
Import LangNotations.
Open Scope LangNotationsScope.

(** Functional style version of star step from above. We need another parameter "fuel" to sidestep termination. *)
Definition star_stepf (fuel : nat) (r : rtexpr) : option(tracepref * rtexpr) :=
  let fix doo (fuel : nat) (r : rtexpr) :=
    match r with
    | RCrash => Some((SCrash :: nil)%list, (↯ ▷ stuck))
    | RTerm Ω e =>
      match fuel, e with
      | _, Xval _ => (* refl *)
        Some(nil, (Ω ▷ e))
      | S fuel', _ => (* trans variants *)
        let* (o, r') := estepf (Ω ▷ e) in
        let* (As, r'') := doo fuel' r' in
        match o with
        | None => (* trans-unimportant *) Some(As, r'')
        | Some a => (* trans-important *) Some(a :: As, r'')
        end
      | _, _ => (* garbage *)
        Some(nil, Ω ▷ e)
      end
    end
  in doo fuel r
.

Lemma different_reduction Ω Ω' e v v' As :
  ((Ω ▷ e ==[As]==>* Ω' ▷ v) -> False) ->
  Ω ▷ e ==[As]==>* Ω' ▷ v' ->
  v <> v'
.
Proof. intros H0 H1 H2; now subst. Qed.

Lemma star_step_is_nodupinv_invariant Ω e Ω' e' As :
  Ω ▷ e ==[ As ]==>* Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
Admitted.

(** Inductive relation modelling linking *)
Inductive link : symbols -> symbols -> symbols -> Prop :=
| linkEmptyL : forall (Ξ__ctx : symbols), link (mapNil _ _) Ξ__ctx Ξ__ctx
| linkConsL : forall (name : vart) (s : symbol) (Ξ__ctx Ξ__comp Ξ : symbols),
    ~(In name (dom Ξ)) ->
    ~(In name (dom Ξ__ctx)) ->
    ~(In name (dom Ξ__comp)) ->
    link Ξ__ctx Ξ__comp Ξ ->
    link (name ↦ s ◘ Ξ__ctx) Ξ__comp (name ↦ s ◘ Ξ)
.
#[local] Hint Constructors link : core.
Fixpoint linkf (Ξ__ctx Ξ__comp : symbols) : option symbols :=
  match Ξ__ctx with
  | mapNil _ _ => Some(Ξ__comp)
  | (name ↦ s ◘ Ξ__ctx) =>
    let* Ξ := linkf Ξ__ctx Ξ__comp in
    match List.find (fun x => x == name) (dom Ξ),
          List.find (fun x => x == name) (dom Ξ__ctx),
          List.find (fun x => x == name) (dom Ξ__comp) with
    | None, None, None => Some(name ↦ s ◘ Ξ)
    | _, _, _ => None
    end
  end
.
Lemma linkf_equiv_link (Ξ__ctx Ξ__comp Ξ : symbols) :
  linkf Ξ__ctx Ξ__comp = Some Ξ <-> link Ξ__ctx Ξ__comp Ξ
.
Proof.
  split; intros.
  - revert Ξ__comp Ξ H; induction Ξ__ctx; intros; cbn in H.
    + inv H; constructor.
    + crush_option (linkf Ξ__ctx Ξ__comp).
      crush_option (List.find (fun x : vart => vareq x a) (dom x)).
      inv H.
      crush_option (List.find (fun x : vart => vareq x a) (dom Ξ__ctx)).
      rewrite Hx0 in H. inv H.
      crush_option (List.find (fun x : vart => vareq x a) (dom (Ξ__comp))).
      rewrite Hx0, Hx1 in H. inv H.
      rewrite Hx0, Hx1, Hx2 in H. inv H.
      constructor. intros Hy; eapply List.find_none in Hx0; eauto. eq_to_defeq vareq.
      apply neqb_neq in Hx0; contradiction.
      intros Hy; eapply List.find_none in Hx1; eauto. eq_to_defeq vareq.
      apply neqb_neq in Hx1; contradiction.
      intros Hy; eapply List.find_none in Hx2; eauto. eq_to_defeq vareq.
      apply neqb_neq in Hx2; contradiction.
      eauto.
  - induction H; cbn; try easy.
    rewrite IHlink.
    crush_option (List.find (fun x : vart => vareq x name) (dom Ξ)).
    apply List.find_some in Hx as [Hx1 Hx2]; eq_to_defeq vareq.
    rewrite Hx.
    crush_option (List.find (fun x : vart => vareq x name) (dom Ξ__ctx)).
    apply List.find_some in Hx0 as [Hx1 Hx2]; eq_to_defeq vareq.
    rewrite Hx0.
    crush_option (List.find (fun x : vart => vareq x name) (dom (Ξ__comp))).
    apply List.find_some in Hx1 as [Hx2 Hx3]; eq_to_defeq vareq.
    rewrite Hx1.
    easy.
Qed.

(** Static Environments. Value Contexts and Location Contexts *)
Definition Gamma : Type := mapind varteq__Instance ty.
Definition Delta : Type := list vart.

(** Interface types. These are the only things allowed to be passed
    across the boundary, i.e., context to comp (!) or vice versa (?). *)
Inductive int : ty -> Prop :=
| intℕ : int (Tpre Tℕ)
.
Definition intf (τ : ty) : option ty :=
  match τ with
  | Tpre Tℕ => Some(Tpre Tℕ)
  | _ => None
  end
.
Lemma intf_refl τ τ' :
  intf τ = Some τ' -> τ = τ'.
Proof. induction τ; cbn; intros; inv H; try easy. destruct p; try easy. now inv H1. Qed.
Lemma int_equiv_intf τ :
  int τ <-> intf τ = Some τ
.
Proof.
  destruct τ; cbn; try easy.
  now induction p; cbn.
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

Notation "[⋅]" := (mapNil _ _).

Reserved Notation "Γ '≡' Γ1 '∘' Γ2" (at level 81, Γ1 at next level, Γ2 at next level).
Inductive splitting : Gamma -> Gamma -> Gamma -> Prop :=
| splitEmpty : [⋅] ≡ [⋅] ∘ [⋅]
| splitSymb : forall (foo : vart) (τ1 τ2 : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (foo ↦ Tfun τ1 τ2 ◘ Γ) ≡ (foo ↦ Tfun τ1 τ2 ◘ Γ1) ∘ (foo ↦ Tfun τ1 τ2 ◘ Γ2)
| splitNat : forall (x : vart) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre Tℕ ◘ Γ) ≡ (x ↦ Tpre Tℕ ◘ Γ1) ∘ (x ↦ Tpre Tℕ ◘ Γ2)
| splitPtr : forall (x : vart) (ℓ : Loc) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Tptr ℓ) ◘ Γ) ≡ (x ↦ Tpre(Tptr ℓ) ◘ Γ1) ∘ (x ↦ Tpre(Tptr ℓ) ◘ Γ2)
| splitCapL : forall (x : vart) (ℓ : Loc) (τ : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Tcap ℓ τ) ◘ Γ) ≡ (x ↦ Tpre(Tcap ℓ τ) ◘ Γ1) ∘ Γ2
| splitCapR : forall (x : vart) (ℓ : Loc) (τ : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Tcap ℓ τ) ◘ Γ) ≡ Γ1 ∘ (x ↦ Tpre(Tcap ℓ τ) ◘ Γ2)
| splitPairL : forall (x : vart) (τ1 τ2 : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Tpair τ1 τ2) ◘ Γ) ≡ (x ↦ Tpre(Tpair τ1 τ2) ◘ Γ1) ∘ Γ2
| splitPairR : forall (x : vart) (τ1 τ2 : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Tpair τ1 τ2) ◘ Γ) ≡ Γ1 ∘ (x ↦ Tpre(Tpair τ1 τ2) ◘ Γ2)
| splitExistsL : forall (γ x : vart) (τ : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Texists γ τ) ◘ Γ) ≡ (x ↦ Tpre(Texists γ τ) ◘ Γ1) ∘ Γ2
| splitExistsR : forall (γ x : vart) (τ : pre_ty) (Γ Γ1 Γ2 : Gamma),
    Γ ≡ Γ1 ∘ Γ2 ->
    (x ↦ Tpre(Texists γ τ) ◘ Γ) ≡ Γ1 ∘ (x ↦ Tpre(Texists γ τ) ◘ Γ1)
where "Γ '≡' Γ1 '∘' Γ2" := (splitting Γ Γ1 Γ2)
.

(* There must not be any capability in Γ whatsoever, i.e., nothing is owned *)
Fixpoint NoOwnedPtrpreτ (τ : pre_ty) :=
  match τ with
  | Tcap _ _ => False
  | Tpair τ1 τ2 => NoOwnedPtrpreτ τ1 /\ NoOwnedPtrpreτ τ2
  | Texists γ τ => NoOwnedPtrpreτ τ
  | _ => True
  end
.
Definition NoOwnedPtrτ (τ : ty) :=
  match τ with
  | Tpre τ => NoOwnedPtrpreτ τ
  | Tret τ => NoOwnedPtrpreτ τ
  | Tfun _ _ => True (* functions are allowed to "eat" pointers *)
  end
.
Fixpoint NoOwnedPtr (Γ : Gamma) :=
  match Γ with
  | [⋅] => True
  | x ↦ τ ◘ Γ => NoOwnedPtrτ τ /\ NoOwnedPtr Γ
  end
.

Lemma noownedptr_split (Γ1 Γ2 : Gamma) :
  NoOwnedPtr (Γ1 ◘ Γ2) <->
  NoOwnedPtr Γ1 /\ NoOwnedPtr Γ2
.
Proof.
  remember (Γ1 ◘ Γ2) as Γ. revert Γ1 Γ2 HeqΓ; induction Γ; split; intros.
  destruct Γ1, Γ2; inv HeqΓ. now split. easy.
  destruct Γ1. inv HeqΓ. cbn in H0. inv H0. now split.
  inv HeqΓ. cbn in H. destruct H as [H0 H1]. assert ((Γ1 ◘ Γ2) = (Γ1 ◘ Γ2)) by reflexivity.
  specialize (IHΓ Γ1 Γ2 H). apply IHΓ in H1. destruct H1 as [H1 H2]. cbn; repeat split; easy.
  destruct Γ1; cbn in HeqΓ; inv HeqΓ. easy. cbn in *. fold (append Γ1 Γ2) in *.
  destruct H as [[H H1] H2]. split; eauto. eapply IHΓ; eauto.
Qed.

Fixpoint substτ (what : vart) (inn : pre_ty) (forr : vart) :=
  match inn with
  | Tptr(LVar x) => if x == what then Tptr(LVar forr) else Tptr(LVar x)
  | Tcap(LVar x) τ => if x == what then Tcap (LVar forr) (substτ what τ forr) else Tcap(LVar x) (substτ what τ forr)
  | Tpair τ1 τ2 => Tpair (substτ what τ1 forr) (substτ what τ2 forr)
  | Texists γ τ => if γ == what then Texists γ τ else Texists γ (substτ what τ forr)
  | _ => inn
  end
.
Fixpoint flv (τ : pre_ty) : list vart :=
  (match τ with
  | Tptr(LVar x) => x :: nil
  | Tcap(LVar x) τ => x :: flv τ
  | Tpair τ1 τ2 => flv τ1 ++ flv τ2
  | Texists γ τ => List.filter (fun x => negb(x == γ)) (flv τ)
  | _ => nil
  end)%list
.
Definition flvt (τ : ty) : list vart :=
  (match τ with
  | Tpre τ => flv τ
  | Tret τ => flv τ
  | Tfun τ1 τ2 => flv τ1 ++ flv τ2
  end)%list
.

(** Type system spec *)
Reserved Notation "'[' b ';' Δ ';' Γ '|-' e ':' τ  ']'" (at level 81, Γ at next level, e at next level, τ at next level).
Inductive check : bool -> Delta -> Gamma -> expr -> ty -> Prop :=
| T_var : forall (dontuse : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (x : vart) (τ : pre_ty),
    (forall x, List.In x (flv τ) -> List.In x Δ) ->
    Γ = (Γ1 ◘ x ↦ (Tpre τ) ◘ Γ2) ->
    NoOwnedPtr (if dontuse then Γ1 ◘ x ↦ (Tpre τ) ◘ Γ2 else Γ1 ◘ Γ2) ->
    [ dontuse ; Δ ; Γ |- Xvar x : τ ]
| T_foo : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (foo : vart) (τ1 τ2 : pre_ty),
    (forall x, List.In x (flv τ1) -> List.In x Δ) ->
    (forall x, List.In x (flv τ2) -> List.In x Δ) ->
    Γ = (Γ1 ◘ foo ↦ (Tfun τ1 τ2) ◘ Γ2) ->
    NoOwnedPtr (Γ1 ◘ Γ2) ->
    [ b ; Δ ; Γ |- Xvar foo : Tfun τ1 τ2 ]
| T_abort : forall (b : bool) (Δ : Delta) (Γ : Gamma) (τ : ty),
    NoOwnedPtr Γ ->
    [ b ; Δ ; Γ |- Xabort : τ ]
| T_vnat : forall (b : bool) (Δ : Delta) (Γ : Gamma) (n : nat),
    NoOwnedPtr Γ ->
    [ b ; Δ ; Γ |- Xval(Vnat n) : Tpre Tℕ ]
| T_vpair : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (v1 v2 : value) (τ1 τ2 : pre_ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [b ; Δ ; Γ1 |- Xval v1 : τ1] ->
    [b ; Δ ; Γ2 |- Xval v2 : τ2] ->
    [b ; Δ ; Γ |- Xval(Vpair v1 v2) : Tpair τ1 τ2]
| T_vpack : forall (b : bool) (Δ : Delta) (Γ : Gamma) (γ γ' : vart) (v : value) (τ : pre_ty),
    List.In γ' Δ ->
    [b ; Δ ; Γ |- Xval v: substτ γ τ γ'] ->
    [b ; Δ ; Γ |- Xval(Vpack (LVar γ) v) : Texists γ τ]
| T_pair : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (e1 e2 : expr) (τ1 τ2 : pre_ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [b ; Δ ; Γ1 |- e1 : τ1] ->
    [b ; Δ ; Γ2 |- e2 : τ2] ->
    [b ; Δ ; Γ |- Xpair e1 e2 : Tpair τ1 τ2]
| T_unpair : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (x1 x2 : vart) (e0 e1 : expr) (τ1 τ2 : pre_ty) (τ3 : ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [false ; Δ ; Γ1 |- e0 : Tpair τ1 τ2] ->
    [false ; Δ ; x1 ↦ (Tpre τ1) ◘ (x2 ↦ (Tpre τ2) ◘ Γ2) |- e1 : τ3]%list ->
    [b ; Δ ; Γ |- Xunpair x1 x2 e0 e1 : τ3]
| T_binop : forall (bb : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (b : binopsymb) (e1 e2 : expr),
    Γ ≡ Γ1 ∘ Γ2 ->
    [bb ; Δ ; Γ1 |- e1 : Tℕ] ->
    [bb ; Δ ; Γ2 |- e2 : Tℕ] ->
    [bb ; Δ ; Γ |- Xbinop b e1 e2 : Tℕ]
| T_pack : forall (Δ : Delta) (Γ : Gamma) (γ γ' : vart) (e : expr) (τ : pre_ty),
    List.In γ' Δ ->
    [false ; Δ ; Γ |- e : substτ γ τ γ'] ->
    [false ; Δ ; Γ |- Xpack (Xvar γ) e : Texists γ τ ]
| T_unpack : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (γ x : vart) (e1 e2 : expr) (τ1 : pre_ty) (τ2 : ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [false; Δ ; Γ1 |- e1 : Texists γ τ1] ->
    (forall x, List.In x (flvt τ2) -> List.In x Δ) ->
    [true ; γ :: Δ ; x ↦ (Tpre τ1) ◘ Γ2 |- e2 : τ2]%list ->
    [b ; Δ ; Γ |- Xunpack γ x e1 e2 : τ2]
| T_new : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (γ : vart) (e0 e1 : expr) (τ : pre_ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [true ; Δ ; Γ1 |- e0 : τ] ->
    [true ; Δ ; Γ2 |- e1 : Tnat] ->
    [b ; Δ ; Γ |- Xnew e0 e1 : Texists γ (Tpair (Tcap (LVar γ) τ) (Tptr (LVar γ)))]
| T_del : forall (b : bool) (Δ : Delta) (Γ : Gamma) (γ : vart) (e : expr) (τ : pre_ty),
    [false ; Δ ; Γ |- e : Texists γ (Tpair (Tcap (LVar γ) τ) (Tptr (LVar γ)))] ->
    [b ; Δ ; Γ |- Xdel e : Tℕ]
| T_get : forall (b : bool) (Δ : Delta) (Γ Γ' Γ1 Γ2 Γ3 : Gamma) (γ : vart) (e0 e1 e2 : expr) (τ : pre_ty),
    Γ' ≡ Γ1 ∘ Γ2 ->
    Γ ≡ Γ' ∘ Γ3 ->
    [false ; Δ ; Γ1 |- e0 : Tcap (LVar γ) τ] ->
    [false ; Δ ; Γ2 |- e1 : Tptr (LVar γ)] ->
    [true ; Δ ; Γ3 |- e2 : Tℕ] ->
    [b ; Δ ; Γ |- Xget e0 e1 e2 : Tpair (Tcap (LVar γ) τ) τ]
| T_set : forall (b : bool) (Δ : Delta) (Γ Γ' Γ'' Γ1 Γ2 Γ3 Γ4 : Gamma) (γ : vart) (e0 e1 e2 e3 : expr) (τ : pre_ty),
    Γ' ≡ Γ1 ∘ Γ2 ->
    Γ'' ≡ Γ' ∘ Γ3 ->
    Γ ≡ Γ'' ∘ Γ4 ->
    [false ; Δ ; Γ1 |- e0 : Tcap (LVar γ) τ] ->
    [false ; Δ ; Γ2 |- e1 : Tptr (LVar γ)] ->
    [true ; Δ ; Γ3 |- e2 : Tℕ] ->
    [true ; Δ ; Γ4 |- e3 : τ] ->
    [b ; Δ ; Γ |- Xset e0 e1 e2 e3 : Tpair (Tcap (LVar γ) τ) τ]
| T_let : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (x : vart) (e0 e1 : expr) (τ1 : pre_ty) (τ2 : ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [b ; Δ ; Γ1 |- e0 : τ1] ->
    [true ; Δ ; x ↦ (Tpre τ1) ◘ Γ2 |- e1 : τ2]%list ->
    [b ; Δ ; Γ |- Xlet x e0 e1 : τ2]
| T_ifz : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (e0 e1 e2 : expr) (τ : ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [b ; Δ ; Γ1 |- e0 : Tℕ] ->
    [b ; Δ ; Γ2 |- e1 : τ] ->
    [b ; Δ ; Γ2 |- e2 : τ] ->
    [b ; Δ ; Γ |- Xifz e0 e1 e2 : τ]
| T_return : forall (b : bool) (Δ : Delta) (Γ : Gamma) (e : expr) (τ : pre_ty),
    [false ; Δ ; Γ |- e : τ] ->
    [b ; Δ ; Γ |- Xreturn e : Tret τ]
| T_call : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (foo : vart) (e : expr) (τ1 τ2 : pre_ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [b ; Δ ; Γ1 |- Xvar foo : Tfun τ1 τ2] ->
    [false ; Δ ; Γ2 |- e : τ1] ->
    [b ; Δ ; Γ |- Xcall foo e : τ2]
where "'[' b ';' Δ ';' Γ '|-' e ':' τ ']'" := (check b Δ Γ e τ)
.
(** Collect symbol names and their types into static type env. *)
Fixpoint gamma_from_symbols (Ξ : symbols) : Gamma :=
  match Ξ with
  | [⋅] => [⋅]
  | foo ↦ s ◘ Ξ =>
    let Γ := gamma_from_symbols Ξ in
    (foo ↦ ty_of_symbol s ◘ Γ)
  end
.
(** Check all symbols *)
Definition check_symbols (Γ : Gamma) (Ξ : symbols) : Prop :=
  match undup Ξ with
  | Some Ξ =>
    match mget Ξ "main"%string with
    | Some s__main =>
      match ty_of_symbol s__main with
      | Tfun Tℕ Tℕ =>
        let fix doo (Γ : Gamma) (Ξ : symbols) {struct Ξ} : Prop :=
          match Ξ with
          | [⋅] => True
          | foo ↦ s ◘ Ξ =>
            let x := vart_of_symbol s in
            let τ := ty_of_symbol s in
            let e := expr_of_symbol s in
            match τ with
            | Tfun τ1 τ2 => [ false ; nil ; x ↦ (Tpre τ1) ◘ Γ |- e : Tret τ2 ]
                          /\ (doo Γ Ξ)
            | _ => False
            end
          end
        in doo Γ Ξ
      | _ => False (* main has wrong type *)
      end
    | _ => False (* no main function *)
    end
  | _ => False (* multiple declared symbols *)
  end
.
(** Top-level programs *)
Inductive prog : Type := Cprog (Ξ__ctx Ξ__comp : symbols) : prog.

Definition prog_check (p : prog) : Prop :=
  let '(Cprog Ξ__ctx Ξ__comp) := p in
  ~(List.In "main"%string (dom Ξ__comp)) /\
  List.In "main"%string (dom Ξ__ctx) /\
  exists Ξ, link Ξ__ctx Ξ__comp Ξ /\
      let Γ0 := gamma_from_symbols Ξ in
      check_symbols Γ0 Ξ
.
Inductive wstep : prog -> tracepref -> rtexpr -> Prop :=
| e_wprog : forall (Ξ Ξ__ctx Ξ__comp : symbols) (ξ : commlib) (As : tracepref) (r : rtexpr),
    link Ξ__ctx Ξ__comp Ξ ->
    ξ = dom Ξ__comp ->
    (Ω(Fresh.empty_fresh; Ξ ; ξ ; nil ; CComp ; hNil ; hNil ; snil) ▷ Xcall "main"%string (Xval 0) ==[ As ]==>* r) ->
    prog_check (Cprog Ξ__ctx Ξ__comp) ->
    wstep (Cprog Ξ__ctx Ξ__comp) As r
.

Definition initΩ (Ξ__ctx Ξ__comp : symbols) : option state :=
  let* Ξ := linkf Ξ__ctx Ξ__comp in
  let ξ := dom Ξ__comp in
  Some(Ω(Fresh.empty_fresh; Ξ ; ξ ; nil ; CComp ; hNil ; hNil ; snil))
.

(** * Example: strncpy *)
(** Copy one string into another *)
(** packs up a pointer's location and its capability + ptr constant *)
Definition L_packptr xloc xcap xptr : expr :=
  Xpack xloc (Xpair xcap xptr)
.
(** Unpacks "what" into xloc, xcap, xptr. Expects another expression as a continuation,
    which may now use xloc, xcap, xptr. They are not bound outside due to the existential! *)
Definition L_unpackptr xloc xcap xptr what : expr -> expr :=
  fun e =>
  Xunpack xloc
          (String.append xcap xptr)
          what (Xunpair xcap xptr (Xvar (String.append xcap xptr)) e)
.
Definition strncpy_get_params from i n x y : expr -> expr := (
  fun e =>
    let pxy := String.append "p" (String.append x y) in
    let px := String.append "p" x in
    let py := String.append "p" y in
    let xℓ := String.append x "ℓ" in
    let xcap := String.append x "cap" in
    let xptr := String.append x "ptr" in
    let yℓ := String.append y "ℓ" in
    let ycap := String.append y "cap" in
    let yptr := String.append y "ptr" in
  Xunpair i "p0" from
 (Xunpair n pxy (Xvar "p0")
 (Xunpair px py (Xvar pxy)
 (L_unpackptr xℓ xcap xptr (Xvar px)
 (L_unpackptr yℓ ycap yptr (Xvar py)
          e))))
)%string.

(* parameters are < i, <n, < ∃ xℓ. <xcap, xptr ℓ>,  ∃ yℓ. <ycap, y ℓ> > > > *)
Definition strncpy_pack_params (i n : expr) x y : expr := (
    Xpair i (
      Xpair n (
        Xpair (L_packptr (Xvar (String.append x "ℓ"))
                         (Xvar (String.append x "cap"))
                         (Xvar (String.append x "ptr"))
              )
              (L_packptr (Xvar (String.append y "ℓ"))
                         (Xvar (String.append y "cap"))
                         (Xvar (String.append y "ptr"))
              )
        )
    )
)%string.

Definition seq (e0 e1 : expr) : expr := Xlet dontcare e0 e1.

(* strncpy(p) with p=<i; n; x; y>, where x and y are pointers and i index and n size of buffers x, y *)
(* this is supposed to be an unsafe version of strncpy *)
Example strncpy := (
  strncpy_get_params (Xvar "p") "i" "n" "x" "y" (
    (* function body after unpacking parameters *)
    Xunpair "xcap" "x[i]" (Xget (Xvar "xcap") (Xvar "xptr") (Xvar "i"))
    (* ifz x[i] = 0 then *)
    (Xifz (Xvar "x[i]")
      (Xreturn (strncpy_pack_params (Xvar "i") (Xvar "n") "x" "y"))
    (* else if i < n then *)
      (Xifz (Xbinop Bless (Xvar "i") (Xvar "n"))
        (Xunpair "ycap" dontcare
          (* y[i] = x[i] *)
          (Xset (Xvar "ycap") (Xvar "yptr") (Xvar "i") (Xvar "x[i]"))
          (* recursive call to simulate the loop *)
          (Xreturn (Xcall "strncpy" (strncpy_pack_params (Xbinop Badd (Xvar "i") (Xval 1)) (Xvar "n") "x" "y")))
        )
        (Xreturn (strncpy_pack_params (Xvar "i") (Xvar "n") "x" "y"))
      )
    )
  )
)%string.

(* Simple, correct context that calls strncpy *)
Example main' := (
  L_unpackptr "xℓ" "xcap" "xptr" (Xnew (Xval 0) (Xval 3)) (
    L_unpackptr "yℓ" "ycap" "yptr" (Xnew (Xval 0) (Xval 3)) (
      Xunpair "xcap" dontcare (Xset (Xvar "xcap") (Xvar "xptr") (Xval 0) (Xval 1))
     (Xunpair "xcap" dontcare (Xset (Xvar "xcap") (Xvar "xptr") (Xval 1) (Xval 2))
       (Xunpair "xcap" dontcare (Xset (Xvar "xcap") (Xvar "xptr") (Xval 2) (Xval 3))
         (seq
             (Xlet "r"
                (Xcall "strncpy" (strncpy_pack_params (Xval 0) (Xval 3) "x" "y"))
                (strncpy_get_params (Xvar "r") "i" "n" "x" "y" (
                    seq (Xdel (L_packptr (Xvar "xℓ") (Xvar "xcap") (Xvar "xptr")))
                        (Xdel (L_packptr (Xvar "yℓ") (Xvar "ycap") (Xvar "yptr")))
                  )
                )
             ) (Xreturn (Xval 69))
         )
       )
     )
    )
  )
)%string.

Example main := (Xreturn (Xcall "main'"%string (Xval 0))).

Definition strncpyparams__ty := (
  Tpair Tℕ (Tpair Tℕ (Tpair (Texists "xℓ" (Tpair (Tcap (LVar "xℓ") Tℕ) (Tptr (LVar "xℓ"))))
                            (Texists "yℓ" (Tpair (Tcap (LVar "yℓ") Tℕ) (Tptr (LVar "yℓ"))))))
)%string.
Definition strncpy__ty := Tfun strncpyparams__ty strncpyparams__ty.

Example Ξ__ctx : symbols := ("main"%string ↦ (dontcare, Tℕ, Tℕ, main) ◘ (mapNil _ _)).
Example Ξ__comp : symbols := ("main'"%string ↦ (dontcare, Tℕ, Tℕ, main') ◘
                            ("strncpy"%string ↦ ("p"%string, strncpyparams__ty, strncpyparams__ty, strncpy) ◘
                             (mapNil _ _))).

Local Set Warnings "-abstract-large-number".
Compute ((fun n => (let* iΩ := initΩ Ξ__ctx Ξ__comp in
         let* (As, r) := star_stepf n (iΩ ▷ (Xcall "main"%string (Xval 0))) in
         match r with
         | RCrash => None
         | RTerm Ω e => Some(As, Ω.(SΦ), e)
         end
        ))
133).

Example strncpy_prog := Cprog Ξ__ctx Ξ__comp.

Goal exists τ, [false ; nil ; [⋅] |- Xlet "x"%string (Xnew (Xval 5) (Xval 5)) ((Xvar "x"%string)) : τ].
Proof.
  eexists.
  econstructor. eapply splitEmpty.
  econstructor. eapply splitEmpty. econstructor. easy. econstructor. easy.
  econstructor. 2: now instantiate (3:=[⋅]). instantiate (1:="x"%string).
  cbn. easy. cbn.
Abort.

Goal prog_check strncpy_prog.
Proof.
  unfold strncpy_prog; repeat split; try (eexists; split).
  - (* main not component *) unfold Ξ__comp; cbn; intros [H | [H | H]]; congruence.
  - (* main in context *) unfold Ξ__ctx; cbn; now left.
  - (* link Ξ__ctx Ξ__comp *) unfold Ξ__ctx; unfold Ξ__comp;
    apply linkf_equiv_link; cbn; reflexivity.
  - (* actual typechecking *)
    assert (NoOwnedPtr
   (dontcare ↦ Tpre Tℕ
    ◘ ("main"%string ↦ Tfun Tℕ Tℕ
       ◘ ("main'"%string ↦ Tfun Tℕ Tℕ ◘ ("strncpy"%string ↦ strncpy__ty ◘ [⋅]))))) as H__NoOwnedPtrInit by easy.
    cbn; repeat split.
    + (* typechecking main *)
      constructor. econstructor; try easy. eauto using splitEmpty, splitSymb, splitNat.
      instantiate (1:= Tℕ). 2: now constructor.
      econstructor; try easy.
      instantiate (2:=dontcare ↦ Tpre Tℕ ◘ ("main"%string ↦ Tfun Tℕ Tℕ ◘ [⋅]));
      reflexivity.
      easy.
    + (* typechecking main' *)
      econstructor; try easy.

      eapply splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      2: instantiate (1:=Tpair (Tcap (LVar "xℓ"%string) Tℕ) (Tptr (LVar "xℓ"%string)));
      econstructor. econstructor.
      eapply splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      1,2: constructor; try easy.
      eapply splitPairL, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      eapply T_var. 2: instantiate (4:=[⋅]); try reflexivity.
      intros x [H | [H | H]]; (now left + now right).
      cbn. easy.

      econstructor; try easy.
      eapply splitCapR, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      instantiate (1:=Tpair (Tcap (LVar "yℓ"%string) Tℕ) (Tptr (LVar "yℓ"%string)));
      econstructor.
      eapply splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      1,2: now constructor.

      econstructor; try easy.
      eapply splitPairL, splitCapR, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      2: instantiate (4:=[⋅]); reflexivity.
      intros x [H | [H | H]]; (now left + now right).
      easy.

      econstructor; try easy.
      eapply splitCapR, splitPtr, splitCapL, splitPtr,
             splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (1:=Tℕ); instantiate (1:=Tcap (LVar "xℓ"%string) Tℕ).
      econstructor.
      1,2,3: eapply splitPtr, splitCapL, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      all: try now econstructor.
      econstructor. intros x [H | H]; (now left + right; subst; now left).
      now instantiate (2:="yptr"%string ↦ Tpre(Tptr(LVar "yℓ"%string)) ◘ [⋅]).
      easy.
      econstructor. intros x [H | H]; (now left + right; subst; now left).
      now instantiate (2:="yptr"%string ↦ Tpre(Tptr(LVar "yℓ"%string)) ◘ [⋅]).
      easy.

      econstructor; try easy.
      eapply splitCapL, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (1:=Tℕ); instantiate (1:=Tcap (LVar "xℓ"%string) Tℕ).
      econstructor.
      1,2,3: eapply splitCapL, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      all: try now econstructor.
      econstructor. intros x [H | H]; (now left + right; subst; now left).
      now instantiate (2:=[⋅]).
      easy.
      econstructor. intros x [H | H]; (now left + right; subst; now left).
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ ("yptr"%string ↦ Tpre(Tptr(LVar "yℓ"%string)) ◘ [⋅])).
      easy.

      econstructor; try easy.
      eapply splitCapL, splitNat, splitNat, splitCapR, splitPtr, splitPtr,
             splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (1:=Tℕ); instantiate (1:=Tcap (LVar "xℓ"%string) Tℕ).
      econstructor.
      1,2,3: eapply splitCapL, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      all: try now econstructor.
      econstructor. intros x [H | H]; (now left + right; subst; now left).
      now instantiate (2:=[⋅]).
      easy.
      econstructor. intros x [H | H]; (now left + right; subst; now left).
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘ ("yptr"%string ↦ Tpre(Tptr(LVar "yℓ"%string)) ◘ [⋅]))).
      easy.

      econstructor.
      eapply splitCapL, splitNat, splitNat, splitNat, splitCapL, splitPtr, splitPtr,
             splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      2: repeat econstructor; instantiate (1:=Tℕ); easy.

      econstructor.
      eapply splitCapL, splitNat, splitNat, splitNat, splitCapL, splitPtr, splitPtr,
             splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (1:=strncpyparams__ty).

      econstructor; try instantiate (1:=strncpyparams__ty).
      eapply splitCapR, splitNat, splitNat, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor; try easy.
      now instantiate (2:=(dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘
        ("yptr"%string ↦ Tpre(Tptr (LVar "yℓ"%string))
         ◘ ("xptr"%string ↦ Tpre(Tptr (LVar "xℓ"%string))
          ◘ (dontcare ↦ Tpre Tℕ
            ◘ ("main"%string ↦ Tfun Tℕ Tℕ
               ◘ ("main'"%string ↦ Tfun Tℕ Tℕ ◘ [⋅]))))))))).
      easy.
      econstructor.
      eapply splitCapR, splitNat, splitNat, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      now econstructor.
      econstructor.
      eapply splitCapR, splitNat, splitNat, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      now econstructor.
      econstructor.
      eapply splitCapL, splitNat, splitNat, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      econstructor. instantiate (1:="xℓ"%string); right; now left.
      econstructor.
      eapply splitCapL, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. econstructor.
      intros x [H | H]; (now left + right; now left).
      now instantiate (2:=[⋅]).
      easy.
      rewrite eq_refl.
      econstructor. intros x [H | H]; (now left + right; now left).
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ (
                          dontcare ↦ Tpre Tℕ ◘ (
                          dontcare ↦ Tpre Tℕ ◘ ("yptr"%string ↦ Tpre(Tptr (LVar "yℓ"%string)) ◘ [⋅])))).
      easy.

      econstructor. instantiate (1:="yℓ"%string); now left.
      econstructor.
      eapply splitNat, splitNat, splitNat, splitCapL, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. econstructor.
      intros x [H | H]; (now left).
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘ [⋅]))).
      easy.
      rewrite eq_refl.
      econstructor. intros x [H | H]; (now left).
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘ (dontcare ↦ Tpre Tℕ ◘ [⋅]))).
      easy.

      econstructor; cbn.
      eapply splitPairL, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (1:=
          (Tpair Tℕ (Tpair
             (Texists "xℓ"%string
                (Tpair (Tcap (LVar "xℓ"%string) Tℕ) (Tptr (LVar "xℓ"%string))))
             (Texists "yℓ"%string
                (Tpair (Tcap (LVar "yℓ"%string) Tℕ) (Tptr (LVar "yℓ"%string))))))).
      instantiate (1:=Tℕ).
      econstructor; cbn.
      intros x [].
      now instantiate (2:= [⋅]).
      easy.

      econstructor.
      eapply splitNat, splitPairL, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (2:=Tℕ).
      instantiate (1:=
          Tpair
             (Texists "xℓ"%string
                (Tpair (Tcap (LVar "xℓ"%string) Tℕ) (Tptr (LVar "xℓ"%string))))
             (Texists "yℓ"%string
                (Tpair (Tcap (LVar "yℓ"%string) Tℕ) (Tptr (LVar "yℓ"%string))))).
      econstructor; cbn.
      intros x [].
      now instantiate (2:="i"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.

      econstructor.
      eapply splitNat, splitPairL, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (2:=
             (Texists "xℓ"%string
                (Tpair (Tcap (LVar "xℓ"%string) Tℕ) (Tptr (LVar "xℓ"%string))))).

      instantiate (1:=
             (Texists "yℓ"%string
                (Tpair (Tcap (LVar "yℓ"%string) Tℕ) (Tptr (LVar "yℓ"%string))))).
      econstructor; cbn.
      intros x [].
      now instantiate (2:="n"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.

      econstructor; cbn.
      eapply splitExistsL, splitExistsR, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      2: intros x [].
      instantiate (1:=
             (
                (Tpair (Tcap (LVar "xℓ"%string) Tℕ) (Tptr (LVar "xℓ"%string))))).
      econstructor; cbn.
      intros x [].
      now instantiate (2:=[⋅]).
      easy.

      econstructor; cbn.
      eapply splitPairL, splitExistsR, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (2:=Tcap(LVar "xℓ"%string) Tℕ).
      instantiate (1:=Tptr(LVar "xℓ"%string)).
      econstructor; cbn.
      intros x [H | [H | H]]; ((now left) + (right; now left)).
      now instantiate (2:=[⋅]).
      easy.

      econstructor; cbn.
      eapply splitCapR, splitPtr, splitExistsL, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (1:=Tpair (Tcap (LVar "yℓ"%string) Tℕ) (Tptr (LVar "yℓ"%string))).
      econstructor; cbn.
      intros x [].
      now instantiate (2:="xptr"%string ↦ Tpre(Tptr(LVar "xℓ"%string)) ◘ [⋅]).
      easy.
      intros x [].

      econstructor; cbn.
      eapply splitPairL, splitCapR, splitPtr, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (2:=Tcap(LVar "yℓ"%string) Tℕ).
      instantiate (1:=Tptr(LVar "yℓ"%string)).
      econstructor; cbn.
      intros x [H | [H | H]]; ((now left) + (right; now left)).
      now instantiate (2:=[⋅]).
      easy.

      econstructor; cbn.
      eapply splitCapR, splitPtr, splitCapL, splitPtr, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      econstructor. econstructor.
      instantiate (1:="xℓ"%string).
      right; now left.

      econstructor.
      eapply splitPtr, splitCapL, splitPtr, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. instantiate (1:=Tℕ); cbn. econstructor; cbn.
      intros x [H | H]; right; now left.
      now instantiate (2:="yptr"%string ↦ Tpre(Tptr (LVar "yℓ"%string)) ◘ [⋅]).
      easy.
      rewrite eq_refl. econstructor; cbn.
      intros x [H | H]; right; now left.
      now instantiate (2:="yptr"%string ↦ Tpre(Tptr (LVar "yℓ"%string)) ◘ [⋅]).
      easy.

      econstructor. econstructor.
      instantiate (1:="yℓ"%string).
      now left.

      econstructor.
      eapply splitNat, splitCapL, splitPtr, splitPtr, splitNat, splitNat, splitNat, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. instantiate (1:=Tℕ); cbn. econstructor; cbn.
      intros x [H | H]; now left.
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ [⋅]).
      easy.
      rewrite eq_refl. econstructor; cbn.
      intros x [H | H]; now left.
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ [⋅]).
      easy.
    + (* typechecking strncpy *)
      econstructor.
      eapply splitPairL, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (4:=[⋅]).
      intros x []. easy.

      econstructor. eapply splitNat, splitPairL, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (4:="i"%string ↦ Tpre Tℕ ◘ ([⋅])).
      easy. easy.

      econstructor. eapply splitNat, splitPairL, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (4:="n"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy. easy.

      econstructor. eapply splitExistsL, splitExistsR, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (3:=[⋅]).
      easy. easy.
      easy.

      econstructor. eapply splitPairL, splitExistsR, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (4:=[⋅]).
      intros x [H|[H|H]]; now left.
      easy.

      econstructor. eapply splitCapR, splitPtr, splitExistsL, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (3:="xptr"%string ↦ Tpre(Tptr(LVar "xℓ"%string)) ◘ [⋅]).
      easy. easy. easy.

      econstructor. eapply splitPairL, splitCapR, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. 2: now instantiate (4:=[⋅]).
      intros x [H|[H|H]]; now left.
      easy.

      econstructor. eapply splitCapR, splitPtr, splitCapL, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      2,1: eapply splitPtr, splitCapL, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      2: now instantiate (4:="yptr"%string ↦ Tpre(Tptr(LVar "yℓ"%string)) ◘ [⋅]).
      intros x [H|H]; now right; left. easy.
      econstructor.
      intros x [H|H]; now right; left.
      now instantiate (2:="yptr"%string ↦ Tpre(Tptr(LVar "yℓ"%string)) ◘ [⋅]).
      easy.
      econstructor. easy.
      now instantiate (2:=
  (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
   ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
      ◘ ("n"%string ↦ Tpre Tℕ ◘ [⋅])))).
      easy.

      econstructor. eapply splitCapR, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=[⋅]).
      easy.

      econstructor. econstructor.
      eapply splitCapR, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
         ◘ ("n"%string ↦ Tpre Tℕ ◘ [⋅]))))).
      easy. econstructor.
      eapply splitCapR, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string)) ◘ [⋅])))).
      easy.
      econstructor.
      eapply splitCapL, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      econstructor. instantiate (1:="xℓ"%string); right; now left.
      econstructor.
      eapply splitCapL, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. econstructor.
      intros x [H|H]; right; now left.
      now instantiate (2:=[⋅]).
      easy.
      rewrite eq_refl. econstructor. intros x [H|H]; right; now left.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string)) ◘ [⋅]
                  ))).
      easy.

      econstructor. instantiate (1:="yℓ"%string); now left.
      econstructor.
      eapply splitNat, splitCapL, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. econstructor.
      intros x [H|H]; now left.
      now instantiate (2:="x[i]"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.
      rewrite eq_refl. econstructor.
      intros x [H|H]; now left.
      now instantiate (2:="x[i]"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.

      econstructor.
      eapply splitCapR, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      eapply splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
         ◘ ("n"%string ↦ Tpre Tℕ ◘ [⋅]))))).
      easy. econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string)) ◘ [⋅])))).
      easy.

      econstructor.
      eapply splitCapR, splitNat, splitCapL, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      3,2,1: eapply splitNat, splitCapL, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      instantiate (2:="yℓ"%string).
      econstructor.
      2: now instantiate (3:="x[i]"%string ↦ Tpre Tℕ ◘ [⋅]).
      intros x [H|H]; now left.
      easy.
      econstructor.
      intros x [H|H]; now left.
      now instantiate (2:="x[i]"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.
      econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
         ◘ ("n"%string ↦ Tpre Tℕ ◘ [⋅]))))).
      easy.
      econstructor. easy.
      now instantiate (2:=[⋅]).
      easy.
      econstructor.
      econstructor.
      eapply splitCapR, splitNat, splitCapR, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. instantiate (1:=strncpyparams__ty).
      easy. easy.
      now instantiate (2:=
  (dontcare ↦ Tpre Tℕ
   ◘ ("x[i]"%string ↦ Tpre Tℕ
      ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
         ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
            ◘ ("n"%string ↦ Tpre Tℕ
               ◘ ("i"%string ↦ Tpre Tℕ
                  ◘ ("main"%string ↦ Tfun Tℕ Tℕ
                     ◘ ("main'"%string ↦ Tfun Tℕ Tℕ ◘ [⋅]))))))))).
      easy.
      econstructor.
      eapply splitCapR, splitNat, splitCapR, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      eapply splitNat, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor.
      easy.
      now instantiate (2:=
  (dontcare ↦ Tpre Tℕ
   ◘ ("x[i]"%string ↦ Tpre Tℕ
      ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
         ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
            ◘ ("n"%string ↦ Tpre Tℕ ◘ [⋅])))))).
      easy. econstructor. easy.

      econstructor.
      eapply splitCapR, splitNat, splitCapR, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=
  (dontcare ↦ Tpre Tℕ
   ◘ ("x[i]"%string ↦ Tpre Tℕ
      ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
         ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string)) ◘ [⋅]))))).
      easy.

      econstructor.
      eapply splitCapR, splitNat, splitCapL, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. instantiate (1:="xℓ"%string).
      right; now left.

      econstructor.
      eapply splitNat, splitCapL, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      1,2: rewrite eq_refl. econstructor.
      intros x [H|H]; right; now left.
      now instantiate (2:=dontcare ↦ Tpre Tℕ ◘ [⋅]).
      easy. econstructor.
      intros x [H|H]; right; now left.
      now instantiate (2:=
  (dontcare ↦ Tpre Tℕ
   ◘ ("x[i]"%string ↦ Tpre Tℕ
      ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string)) ◘ [⋅])))
      ).
      easy.

      econstructor. instantiate (1:="yℓ"%string).
      now left.

      econstructor.
      eapply splitCapL, splitNat, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      1,2: rewrite eq_refl. econstructor.
      intros x [H|H]; now left.
      now instantiate (2:=[⋅]).
      easy. econstructor.
      intros x [H|H]; now left.
      now instantiate (2:=
  (dontcare ↦ Tpre Tℕ
   ◘ ("x[i]"%string ↦ Tpre Tℕ ◘ [⋅]))).
      easy.

      econstructor. econstructor.
      eapply splitCapR, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string))
         ◘ ("n"%string ↦ Tpre Tℕ ◘ [⋅]))))).
      easy. econstructor.
      eapply splitCapR, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      econstructor. easy.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string))
      ◘ (("x" ++ "ptr")%string ↦ Tpre(Tptr (LVar "xℓ"%string)) ◘ [⋅])))).
      easy.
      econstructor.
      eapply splitCapL, splitNat, splitCapR, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.

      econstructor. instantiate (1:="xℓ"%string); right; now left.
      econstructor.
      eapply splitCapL, splitNat, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. econstructor.
      intros x [H|H]; right; now left.
      now instantiate (2:=[⋅]).
      easy.
      rewrite eq_refl. econstructor. intros x [H|H]; right; now left.
      now instantiate (2:=
  ("x[i]"%string ↦ Tpre Tℕ
   ◘ (("y" ++ "ptr")%string ↦ Tpre(Tptr (LVar "yℓ"%string)) ◘ [⋅]
                  ))).
      easy.

      econstructor. instantiate (1:="yℓ"%string); now left.
      econstructor.
      eapply splitNat, splitCapL, splitPtr, splitPtr, splitNat, splitNat, splitSymb, splitSymb, splitSymb, splitEmpty.
      rewrite eq_refl. econstructor.
      intros x [H|H]; now left.
      now instantiate (2:="x[i]"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.
      rewrite eq_refl. econstructor.
      intros x [H|H]; now left.
      now instantiate (2:="x[i]"%string ↦ Tpre Tℕ ◘ [⋅]).
      easy.
Qed.

Goal [false ; nil ; [⋅] |- Xlet "x" (Xnew (Xval 5) (Xval 4)) (seq (Xdel (Xvar "x")) (Xdel (Xvar "x"))) : Tℕ ]%string.
  econstructor.
  eapply splitEmpty. econstructor. eapply splitEmpty.
  now econstructor. now econstructor.
  instantiate (1:="ℓ"%string).

  econstructor. eapply splitExistsL, splitEmpty.
  econstructor. econstructor.  2: now instantiate (6:=[⋅]).
  now cbn.
  easy.
  econstructor.
  econstructor. 1,3: shelve.
Abort.

(** We now come to the second part and prove that well-typed programs are temporal memory safe. *)

Require Import CSC.Mon.


Definition specev_of_ev (ev : option event) : option Props.Event :=
  let* ev := ev in
  match ev with
  | SCrash => Some(Props.Aborted)
  | Sev ev t =>
    match ev with
    | Sstart | Send _ => None
    | Salloc ℓ n => Some(Props.PreEv (Props.Alloc ℓ n) t SUnlock)
    | Sdealloc ℓ => Some(Props.PreEv (Props.Dealloc ℓ) t SUnlock)
    | Sget ℓ n => Some(Props.PreEv (Props.Use ℓ n) t SUnlock)
    | Sset ℓ n _ => Some(Props.PreEv (Props.Use ℓ n) t SUnlock)
    | Scall _ _ _ => None
    | Sret _ _ => None
    end
  end
.
Fixpoint spectracepref_of_tracepref (tr : tracepref) : Props.tracepref :=
  match tr with
  | nil => nil
  | a :: tr' =>
    match specev_of_ev (Some a) with
    | Some a' => a' :: (spectracepref_of_tracepref tr')
    | None => spectracepref_of_tracepref tr'
    end
  end
.

(** Store agreement between our stores and the TMS monitor. *)
Inductive tms_store_agree : TMSMonAux.AbsState -> ptrstore -> Prop :=
| TMSEmptyAgree : tms_store_agree TMSMonAux.EmptyState snil
| TMSConsAgree : forall (ℓ : loc) (t : ControlTag) (n : nat) (T__TMS T__TMS' : TMSMonAux.AbsState) (Δ : ptrstore),
    ~(List.In (ℓ,t) (TMSMonAux.alloced T__TMS)) ->
    ~(List.In (ℓ,t) (TMSMonAux.freed T__TMS)) ->
    tms_store_agree T__TMS Δ ->
    T__TMS' = {|
               TMSMonAux.alloced := List.app (TMSMonAux.alloced T__TMS) (List.cons (ℓ,t) List.nil) ;
               TMSMonAux.freed := TMSMonAux.freed T__TMS ;
            |} ->
    tms_store_agree T__TMS' (dK(ℓ ; t) ↦ dL(◻ ; n) ◘ Δ)
| TMSPoisonAgree : forall (ℓ : loc) (t : ControlTag) (n : nat) (T__TMS : TMSMonAux.AbsState) (Δ : ptrstore),
    tms_store_agree T__TMS Δ ->
    tms_store_agree T__TMS (dK(ℓ ; t) ↦ dL(☣ ; n) ◘ Δ)
.
Inductive tms_state_agree : TMSMonAux.AbsState -> state -> Prop :=
| TMSStateAgree : forall (Ω : state) (T__TMS : TMSMonAux.AbsState),
    tms_store_agree T__TMS Ω.(SΦ).(MΔ) ->
    tms_state_agree T__TMS Ω
.

(** Store splitting. We don't need a case for e.g. nat, since identifiers with type nat get substituted at runtime. *)
Inductive ptrstore_split (Ξ : symbols) : ptrstore -> Delta -> Gamma -> Prop :=
| TemptyΔ : forall (Γ : Gamma), gamma_from_symbols Ξ = Γ -> ptrstore_split Ξ snil nil Γ
| Tref1ℕ : forall (x γ : vart) (Γ : Gamma) (Δ__ptrs : Delta) (Δ : ptrstore) (ℓ : loc) (t : ControlTag) (n : nat),
    ptrstore_split Ξ Δ Δ__ptrs Γ ->
    ptrstore_split Ξ (dK(ℓ ; t) ↦ dL(◻ ; n) ◘ Δ) (γ :: Δ__ptrs)%list (x ↦ Tpre(Tptr (LVar γ)) ◘ Γ)
| Tref1ℕpoison : forall (x : vart) (Γ : Gamma) (Δ__ptrs : Delta) (Δ : ptrstore) (x : vart) (ℓ : loc) (t : ControlTag) (n : nat),
    ptrstore_split Ξ Δ Δ__ptrs Γ ->
    ptrstore_split Ξ (dK(ℓ ; t) ↦ dL(☣ ; n) ◘ Δ) Δ__ptrs (x ↦ Tpre(Tptr(LConst ℓ)) ◘ Γ) (*FIXME*)
.
Inductive ptrstate_split : state -> Delta -> Gamma -> Prop :=
| TΩ : forall (Ω : state) (Γ : Gamma) (Δ : Delta),
    ptrstore_split Ω.(SΨ).(CΞ) Ω.(SΦ).(MΔ) Δ Γ ->
    ptrstate_split Ω Δ Γ
.
Inductive rt_check : state -> expr -> ty -> Prop :=
| Trtcheck : forall (Ω : state) (e : expr) (τ : ty) (Γ : Gamma) (Δ__ptrs : Delta),
    ptrstate_split Ω Δ__ptrs Γ ->
    [false ; Δ__ptrs ; Γ |- e : τ] ->
    rt_check Ω e τ
.
Definition ectx_rt_check (Ω : state) (K : evalctx) (τ τ' : ty) :=
  forall (e : expr), rt_check Ω e τ' -> rt_check Ω (insert K e) τ
.
Lemma rt_check_recompose (Ω : state) (K : evalctx) (e : expr) (τ : ty) :
  rt_check Ω (insert K e) τ ->
  exists τ', ectx_rt_check Ω K τ' τ /\ rt_check Ω e τ'
.
Proof. Admitted.
Lemma rt_check_decompose (Ω : state) (K : evalctx) (e : expr) (τ τ' : ty) :
  ectx_rt_check Ω K τ' τ ->
  rt_check Ω e τ' ->
  rt_check Ω (insert K e) τ
.
Proof. Admitted.

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

Lemma store_agree_split T__TMS Δ1 ℓ ρ t n Δ2 :
  tms_store_agree T__TMS (Δ1 ◘ dK((addr ℓ) ; t) ↦ dL(ρ ; n) ◘ Δ2) ->
  exists T__TMS1 T__TMS2, tms_store_agree T__TMS1 Δ1 /\
                 tms_store_agree T__TMS2 Δ2 /\
                 tms_store_agree (TMSMonAux.singleton (addr ℓ) t) (dK((addr ℓ) ; t) ↦ dL(ρ ; n) ◘ snil) /\
                 T__TMS = TMSMonAux.append T__TMS1 (TMSMonAux.append (TMSMonAux.singleton (addr ℓ) t) T__TMS2)
.
Proof. Admitted.

Lemma store_agree_rsplit T__TMS1 T__TMS2 Δ1 Δ2 :
  tms_store_agree T__TMS1 Δ1 ->
  tms_store_agree T__TMS2 Δ2 ->
  tms_store_agree (TMSMonAux.append T__TMS1 T__TMS2) (Δ1 ◘ Δ2)
.
Proof. Admitted.

Lemma store_agree_notin_comm Δ ℓ t v T__TMS :
  tms_store_agree T__TMS Δ ->
  ~ In (dK(ℓ ; t)) (dom Δ) ->
  Util.nodupinv (dK(ℓ ; t) ↦ v ◘ Δ) ->
  ~ List.In (ℓ,t) (TMSMonAux.alloced T__TMS) /\
  ~ List.In (ℓ,t) (TMSMonAux.freed T__TMS)
.
Proof.
Admitted.

Lemma base_tms_via_monitor (Ω Ω' : state) (e e' : expr) (τ : ty) (a : option event)
                           (T__TMS : TMSMonAux.AbsState) :
  rt_check Ω e τ ->
  (Ω ▷ e --[, a ]--> Ω' ▷ e') ->
  tms_state_agree T__TMS Ω ->
  exists (b : option TMSMonAux.AbsEv) (T__TMS' : TMSMonAux.AbsState),
    TMSMonAux.cong_e (specev_of_ev a) b
  /\ (TMSMonAux.MonCheck T__TMS b T__TMS')
  /\ tms_state_agree T__TMS' Ω'
.
Proof.
  intros Aa Ab Ac. remember (Ω ▷ e) as r1. remember (Ω' ▷ e') as r2.
  pattern Ω'. match goal with
  | [|- context E [Ω']] =>
    let next := context E [match Ω' ▷ e' with
                           | RCrash => Ω'
                           | RTerm Ω' e' => Ω'
                           end] in
    change next
  end.
  cbv in Ab; dependent destruction Ab; subst.
  - (* binop *) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (* ifz-true *) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (* ifz-false *) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (* pair *) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (* abort *) inv Heqr1; inv Heqr2.
  - (* let *) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (* unpair *) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (* new *) inv Heqr1; inv Heqr2. remember (addr (List.length (getH Φ t))) as ℓ.
    inv Ac; assert (H':=H). cbn in H. destruct t; cbn.
    + apply push_ok in H1 as H1'. unfold push in H1. crush_undup (dK(addr(List.length(getH Φ CCtx)) ; CCtx) ↦ {| dρ := ◻; dn := n |} ◘ MΔ Φ).
      inv H1.
      exists (Some (TMSMonAux.AAlloc(addr (List.length (MH__ctx Φ))) CCtx)).
      exists (TMSMonAux.append T__TMS (TMSMonAux.singleton (addr (List.length (MH__ctx Φ))) CCtx)).
      assert (H'':=H1'). inv H''.
      enough ((~ List.In (addr (List.length (MH__ctx Φ)), CCtx) (TMSMonAux.alloced T__TMS)) /\ (~ List.In (addr (List.length (MH__ctx Φ)), CCtx) (TMSMonAux.freed T__TMS))) as [Ha Hb].
      repeat split; eauto; try constructor; try easy. unfold TMSMonAux.append; unfold TMSMonAux.singleton; rewrite List.app_nil_r; reflexivity.
      econstructor; eauto. unfold TMSMonAux.append; unfold TMSMonAux.singleton; rewrite List.app_nil_r; reflexivity.
      revert H H3 H1'; clear. revert T__TMS. remember (MΔ Φ) as Δ; remember (addr(List.length (MH__ctx Φ))) as ℓ.
      clear HeqΔ; clear Heqℓ; clear Φ. revert ℓ n. induction Δ; intros. now inv H.
      rename a into ℓ'. eapply store_agree_notin_comm in H; eauto.
    + apply push_ok in H1 as H1'. unfold push in H1. crush_undup (dK(addr(List.length(getH Φ CComp)) ; CComp) ↦ {| dρ := ◻; dn := n |} ◘ MΔ Φ).
      inv H1.
      exists (Some (TMSMonAux.AAlloc(addr (List.length (MH__comp Φ))) CComp)).
      exists (TMSMonAux.append T__TMS (TMSMonAux.singleton (addr (List.length (MH__comp Φ))) CComp)).
      assert (H'':=H1'). inv H''.
      enough ((~ List.In (addr (List.length (MH__comp Φ)), CComp) (TMSMonAux.alloced T__TMS)) /\ (~ List.In (addr (List.length (MH__comp Φ)), CComp) (TMSMonAux.freed T__TMS))) as [Ha Hb].
      repeat split; eauto; try constructor; try easy. unfold TMSMonAux.append; unfold TMSMonAux.singleton; rewrite List.app_nil_r; reflexivity.
      econstructor; eauto. unfold TMSMonAux.append; unfold TMSMonAux.singleton; rewrite List.app_nil_r; reflexivity.
      revert H H3 H1'; clear. revert T__TMS. remember (MΔ Φ) as Δ; remember (addr(List.length (MH__comp Φ))) as ℓ.
      clear HeqΔ; clear Heqℓ; clear Φ. revert ℓ n. induction Δ; intros. now inv H.
      rename a into ℓ'. eapply store_agree_notin_comm in H; eauto.
  - (*del*) inv Heqr1; inv Heqr2.
    inv Ac; assert (H1':=H1). cbn in H1; rewrite H0 in H1; destruct ℓ as [ℓ]; apply store_agree_split in H1; deex.
    destruct H1 as [H1a [H1b [H1c H1d]]].
    inv Aa. inv H2. inv H1c; try inv H4.
    inv H11. cbn in H12.
    exists (Some(TMSMonAux.ADealloc (addr ℓ) t)). exists (TMSMonAux.append T__TMS1 T__TMS2).
    repeat split; try constructor. econstructor; now cbn. cbn. eapply store_agree_rsplit. easy.
    econstructor. easy.
  - (*get*) inv Heqr1; inv Heqr2.
    inv Ac; assert (H2':=H2). cbn in H2; rewrite H0 in H2; apply store_agree_split in H2; deex.
    destruct H2 as [H2a [H2b [H2c H2d]]].
    inv Aa. inv H3. inv H2c; try inv H5. inv H16. cbn in H17.
    exists (Some(TMSMonAux.AUse (addr ℓ) t)). exists (TMSMonAux.append T__TMS1 (TMSMonAux.append (TMSMonAux.singleton (addr ℓ) t) T__TMS2)).
    repeat split; try constructor; easy.
  - (*set*) inv Heqr1; inv Heqr2. inv Aa. inv H3. inv H16. (* FIXME? this is kinda bad for runtime-type preservation isn't it *)
  - (*unpack*) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (*pack*) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
Qed.

Lemma ctx_tms_via_monitor (Ω Ω' : state) (e e' : expr) (τ : ty) (a : option event)
                          (T__TMS : TMSMonAux.AbsState) :
  rt_check Ω e τ ->
  (Ω ▷ e ==[, a ]==> Ω' ▷ e') ->
  tms_state_agree T__TMS Ω ->
  exists (b : option TMSMonAux.AbsEv) (T__TMS' : TMSMonAux.AbsState),
    TMSMonAux.cong_e (specev_of_ev a) b
  /\ (TMSMonAux.MonCheck T__TMS b T__TMS')
  /\ tms_state_agree T__TMS' Ω'
.
Proof.
  intros Aa Ab Ac; inv Ab.
  - (*E_ectx*)
    eapply rt_check_recompose in Aa as [τ' [Aa0 Aa1]].
    eapply base_tms_via_monitor in H7; eauto.
  - (*E_start*) exists None; exists T__TMS; repeat split; eauto; try easy; cbn; try constructor. now inv Ac.
  - (*E_call*) exists None; exists T__TMS; repeat split; eauto; try easy; cbn; try constructor. now inv Ac.
  - (*E_ret*) exists None; exists T__TMS; repeat split; eauto; try easy; cbn; try constructor. now inv Ac.
  - (*E_end*) exists None; exists T__TMS; repeat split; eauto; try easy; cbn; try constructor. now inv Ac.
Qed.
Lemma ctx_tms_via_monitor_abrt (Ω : state) (e : expr) (τ : ty)
                          (T__TMS : TMSMonAux.AbsState) :
  rt_check Ω e τ ->
  (Ω ▷ e ==[ SCrash ]==> ↯ ▷ stuck) ->
  tms_state_agree T__TMS Ω ->
  exists (b : option TMSMonAux.AbsEv) (T__TMS' : TMSMonAux.AbsState),
    TMSMonAux.cong_e (specev_of_ev (Some(SCrash))) b
  /\ (TMSMonAux.MonCheck T__TMS b T__TMS')
.
Proof.
  (*E_abort*)
  intros Aa Ab Ac; inv Ab; inv H3;
  exists (Some TMSMonAux.AAbort); exists (T__TMS); split; constructor.
Qed.

Lemma rtvalue_is_monvalue Ω v (T__TMS : TMSMonAux.AbsState) :
  is_value (Ω ▷ (Xval v)) ->
  tms_state_agree T__TMS Ω ->
  TMSMon.ValueState T__TMS
.
Proof.
  intros. inv H0. revert v H;
  dependent induction H1; intros.
  - constructor.
  - inv H3. specialize (H6 ℓ t (dL(◻ ; n))). rewrite <- x in H6. cbn in H6.
    eq_to_defeq (ptr_key_eqb). rewrite eq_refl in H6.
    assert (Some(dL(◻ ; n)) = Some(dL(◻ ; n))) by reflexivity.
    now specialize (H6 H2).
  - inv H. inv H4. pose (Ω' := Ω <| SΦ := Ω.(SΦ) <| MΔ := Δ |> |>).
    specialize (IHtms_store_agree Ω'). eapply IHtms_store_agree; eauto.
    instantiate (1:=v0). econstructor; eauto. shelve.
    rewrite <- x in H0. inv H0. constructor; eauto.
    Unshelve.
    intros. cbn in H. rewrite <- x in *. inv H0. cbn in H3. eapply H3.
    instantiate (1:=t0); instantiate(1:=l).
    destruct (eq_dec (dK(ℓ ; t)) (dK(l ; t0))).
    + apply mget_min in H2. cbn in H2. apply Min_in in H2 as [H2a H2b]. inv H0. contradiction.
    + apply neqb_neq in H0. eq_to_defeq ptr_key_eqb. rewrite H0. assumption.
Qed.

Lemma steps_tms_via_monitor (Ω Ω' : state) (e : expr) (v : value) (τ : ty) (As : tracepref)
                            (T__TMS : TMSMonAux.AbsState) :
  rt_check Ω e τ ->
  (Ω ▷ e ==[ As ]==>* Ω' ▷ (Xval v)) ->
  tms_state_agree T__TMS Ω ->
  exists (Bs : TMSMon.tracepref) (T__TMS' : TMSMonAux.AbsState),
    TMSMon.cong (spectracepref_of_tracepref As) Bs
  /\ (@star_step TMSMon.MonInstance T__TMS Bs T__TMS')
  /\ tms_state_agree T__TMS' Ω'
.
Proof.
  intros Aa Ab; revert T__TMS; dependent induction Ab; intros T__TMS Ac.
  - (* refl *)
    exists (nil). exists T__TMS. repeat split; try now inv Ac. constructor. constructor.
    eapply rtvalue_is_monvalue; eauto.
  - (* trans-imp *)
    destruct r2 as [Ω2 e2|].
    + eapply estep_preservation in Aa as Aa'; eauto.
      eapply ctx_tms_via_monitor in Aa as Aa''; eauto; deex; destruct Aa'' as [Ha [Hb Hc]].
      specialize (IHAb Ω2 Ω' e2 v As0 Aa' JMeq_refl JMeq_refl JMeq_refl T__TMS' Hc).
      deex; rename T__TMS'0 into T__TMS''; destruct IHAb as [IHAb1 [IHAb2 IHAb3]].
      destruct a; cbn in Ha. inv H. inv H8.
      destruct e__b; inversion Ha; subst.
      all: try now (exists Bs; exists T__TMS''; repeat split; cbn; try now inv Ha; try now inv Hb; try now inv IHAb3).
      * exists (TMSMonAux.AAlloc ℓ t :: Bs)%list. exists T__TMS''. repeat split; cbn.
        now econstructor 4. econstructor 2; eassumption. now inv IHAb3.
      * exists (TMSMonAux.ADealloc ℓ t :: Bs)%list. exists T__TMS''. repeat split; cbn.
        now econstructor 4. econstructor 2; eassumption. now inv IHAb3.
      * exists (TMSMonAux.AUse ℓ t :: Bs)%list. exists T__TMS''. repeat split; cbn.
        now econstructor 4. econstructor 2; eassumption. now inv IHAb3.
      * exists (TMSMonAux.AUse ℓ t :: Bs)%list. exists T__TMS''. repeat split; cbn.
        now econstructor 4. econstructor 2; eassumption. now inv IHAb3.
    + inv H. inv H5. inv Ab. inv H. inv H.
  - (* unimp *)
    destruct r2 as [Ω2 e2|].
    + eapply estep_preservation in Aa as Aa'; eauto.
      eapply ctx_tms_via_monitor in Aa as Aa''; eauto; deex; destruct Aa'' as [Ha [Hb Hc]].
      specialize (IHAb Ω2 Ω' e2 v As Aa' JMeq_refl JMeq_refl JMeq_refl T__TMS' Hc); deex.
      destruct IHAb as [IHAb1 [IHAb2 IHAb3]].
      inversion Ha; subst. inv Hb.
      exists Bs. exists T__TMS'0. split; eauto.
    + inv H.
Qed.

Lemma symbols_split Ξ0 :
  gamma_from_symbols Ξ0 ≡ (gamma_from_symbols Ξ0) ∘ (gamma_from_symbols Ξ0)
.
Proof.
  induction Ξ0; cbn.
  eapply splitEmpty.
  destruct b as [[[arg t0] t1] e]; cbn.
  now eapply splitSymb.
Qed.

Lemma symbols_noowned Ξ0 :
 NoOwnedPtr (gamma_from_symbols Ξ0)
.
Proof.
  induction Ξ0.
  easy. cbn. destruct b as [[[arg t0] t1] e]. cbn.
  unfold NoOwnedPtr in IHΞ0.
  fold (img (gamma_from_symbols Ξ0)).
  pattern (True /\ True).
  (* ??? should be easy ??? *)
  admit.
Admitted.

Lemma comm_gamma_from_symbols (Ξ1 Ξ2 : symbols) (x : vart) (s : symbol) :
  gamma_from_symbols (Ξ1 ◘ x ↦ s ◘ Ξ2) =
     ((gamma_from_symbols Ξ1) ◘ x ↦ (ty_of_symbol s) ◘ (gamma_from_symbols Ξ2)).
Proof. Admitted.

Lemma link_check_is_init_check (Ξ__ctx Ξ__comp Ξ0 : symbols) :
  link Ξ__ctx Ξ__comp Ξ0 ->
  check_symbols (gamma_from_symbols Ξ0) Ξ0 ->
  exists τ, rt_check (mkΩ Fresh.empty_fresh (mkΨ Ξ0 (dom Ξ__comp) nil) CComp (mkΦ hNil hNil snil))
                (Xcall "main"%string (Xval 0))
                τ
.
Proof.
  intros H0 H1.
  unfold check_symbols in H1.
  crush_undup Ξ0; try now rewrite Hx in H1.
  crush_option (mget Ξ0 "main"%string); try now rewrite Hx0 in H1.
  remember (ty_of_symbol x0) as ty__main.
  destruct (ty__main); try easy; destruct p, p0; try easy.
  apply mget_min in Hx0 as Hx0'. apply Min_in in Hx0' as [Hx0' Hx1].
  apply nodupinv_equiv_undup in Hx.
  eapply dom_split in Hx0'; eauto; deex; destruct Hx0' as [Hxa Hxb].

  exists Tℕ. econstructor. instantiate (1:=(gamma_from_symbols Ξ0)). instantiate (1:=nil).
  repeat constructor. econstructor.
  eapply symbols_split. instantiate (1:=Tℕ). 2: constructor; auto using symbols_noowned.
  econstructor; try easy.
  instantiate (1:=gamma_from_symbols m2).
  instantiate (1:=gamma_from_symbols m1).
  rewrite Hxb.
  eapply mget_splitat_same_el in Hx0; eauto; subst.
  rewrite Heqty__main.
  apply comm_gamma_from_symbols.
  apply noownedptr_split; split; apply symbols_noowned.
Qed.

Lemma link_determ (Ξ__ctx Ξ__comp Ξ0 Ξ1 : symbols) :
  link Ξ__ctx Ξ__comp Ξ0 ->
  link Ξ__ctx Ξ__comp Ξ1 ->
  Ξ0 = Ξ1
.
Proof.
  intros H0%linkf_equiv_link H1%linkf_equiv_link.
  revert Ξ__comp Ξ0 Ξ1 H0 H1; induction Ξ__ctx; cbn in *; intros; inv H0. now inv H1.
  crush_option (linkf Ξ__ctx0 Ξ__comp0).
  crush_option (List.find (fun x : vart => vareq x a) (dom x)).
  inv H1.
Qed.

Lemma strengthen_stms_goal Ω' As T__TMS :
  (exists (Bs : TMSMon.tracepref) (T__TMS' : TMSMonAux.AbsState),
    TMSMon.cong (spectracepref_of_tracepref As) Bs
  /\ (@star_step TMSMon.MonInstance T__TMS Bs T__TMS')
  /\ tms_state_agree T__TMS' Ω') ->
  (exists (Bs : TMSMon.tracepref) (T__TMS' : TMSMonAux.AbsState),
    TMSMon.cong (spectracepref_of_tracepref As) Bs
  /\ (@star_step TMSMon.MonInstance T__TMS Bs T__TMS'))
.
Proof.
  intros; deex; eauto; exists Bs; exists T__TMS'; destruct H as [Ha [Hb Hc]]; eauto.
Qed.

(** Every well-typed L__tms program is TMS. *)
Theorem s_is_tms (Ξ__ctx Ξ__comp : symbols) (ξ : commlib) As Ω v :
  wstep (Cprog Ξ__ctx Ξ__comp) As (Ω ▷ (Xval v)) ->
  Props.tms (spectracepref_of_tracepref As).
Proof.
  intros Ha. apply Mon.TMSMon_is_TMS. unfold TMSMon.sat.
  inv Ha. eapply strengthen_stms_goal.
  inv H6. destruct H0 as [H0 [Ξ0 [Ha Hb]]]; cbn in *.
  eapply link_determ in H1; eauto; subst.
  eapply link_check_is_init_check in Ha; deex; eauto.
  eapply steps_tms_via_monitor; eauto.
  repeat constructor.
Qed.
