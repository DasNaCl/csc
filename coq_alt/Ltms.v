Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef.
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
| Xnew (e : expr) : expr
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
  | Xnew e => Xnew (h e)
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
| Knew (K : evalctx) : evalctx
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

(** Symbols look like `fn foo x : τ := e` *)
Definition symbol : Type := vart * ty * expr.
Definition symbols := mapind varteq__Instance symbol.

Definition vart_of_symbol (s : symbol) := let '(v, t, e) := s in v.
Definition expr_of_symbol (s : symbol) := let '(v, t, e) := s in e.
Definition ty_of_symbol (s : symbol) := let '(v, t, e) := s in t.

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
  | Knew K' => Xnew (R K')
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

(** Simple projection giving us the names of the symbols *)
Fixpoint interfaces (s : symbols) : option(Gamma) :=
  match s with
  | mapNil _ _ => Some (mapNil _ _)
  | mapCons name EL s' =>
    let ty := ty_of_symbol EL in
    let name := vart_of_symbol EL in
    let* a := interfaces s' in
    Some(name ↦ ty ◘ a)
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
  dℓ : loc ;        (* concrete location on heap *)
  dρ : poison ;     (* wether the location is already deallocated *)
  dt : ControlTag ; (* which heap the data lies on  *)
  dn : nat ;          (* allocation size *)
}.
#[local]
Instance etaDynloc : Settable _ := settable! mkdL <dℓ; dρ; dt; dn>.
Definition dynloc_eqb :=
  fun (dℓ1 dℓ2 : dynloc) =>
    andb  (dℓ1.(dℓ) == dℓ2.(dℓ))
    (andb (dℓ1.(dρ) == dℓ2.(dρ))
    (andb (dℓ1.(dt) == dℓ2.(dt))
          (Nat.eqb dℓ1.(dn) dℓ2.(dn))))
.
Lemma dynloc_eqb_eq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = true <-> dℓ0 = dℓ1.
Proof.
  unfold dynloc_eqb; split; intros.
  eq_to_defeq Nat.eqb. apply Nat.eqb_eq in H2. cbv in *; destruct dℓ0, dℓ1; inv H; inv H3; reflexivity.
  inv H; eq_to_defeq Nat.eqb; try apply Nat.eqb_eq. repeat split; try apply eq_refl. apply Nat.eqb_refl.
Qed.
#[local]
Instance dynloceq__Instance : HasEquality dynloc := {
  eq := dynloc_eqb ;
  eqb_eq := dynloc_eqb_eq ;
}.
Notation "'dL(' bℓ ';' bρ ';' bt ';' bn ')'" := (({| dℓ := bℓ ;
                                                     dρ := bρ ;
                                                     dt := bt ;
                                                     dn := bn |}) : dynloc) (at level 80).
(** Stores map variables to potentially poisoned locations. *)
Definition store := mapind varteq__Instance dynloc.
Definition sNil : store := mapNil varteq__Instance dynloc.

(** Stores pointers and their respective metadata. *)
Definition ptrstore := mapind loceq__Instance dynloc.
Definition snil : ptrstore := mapNil loceq__Instance dynloc.

Fixpoint δ_of_Δ (Δ : store) :=
  match Δ with
  | mapNil _ _ => mapNil _ _
  | mapCons _ ddℓ Δ' => let '(addr a) := ddℓ.(dℓ) in mapCons (addr a) (Util.addr a) (δ_of_Δ Δ')
  end
.

Inductive snodupinv : store -> Prop :=
| snodupmapNil : snodupinv (sNil)
| snodupmapCons : forall (x : vart) (ℓ : loc) (ρ : poison) (t : ControlTag) (n : nat) (Δ : store),
    ~(List.In x (dom Δ)) ->
    ~(List.In ℓ (dom(δ_of_Δ Δ))) ->
    snodupinv Δ ->
    snodupinv (x ↦ dL(ℓ ; ρ ; t ; n) ◘ Δ)
.
Lemma nodupinv_of_snodupinv (Δ : store) :
  snodupinv Δ ->
  nodupinv Δ
.
Proof. induction 1; constructor; eauto. Qed.

Fixpoint sundup (Δ : store) : option(store) :=
  match Δ with
  | mapNil _ _ => Some(mapNil _ _)
  | mapCons a ddℓ Δ' =>
    let thedom := dom Δ' in
    let theimg := img Δ' in
    match List.find (fun x => eq a x) thedom, List.find (fun x => loc_eqb x.(dℓ) ddℓ.(dℓ)) theimg, sundup Δ' with
    | None, None, Some Δ'' => Some(mapCons a ddℓ Δ'')
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
    cbn in H. crush_option (List.find (fun x => loc_eqb (dℓ x) dℓ0) (img Δ)).
    + inv H.
    + rewrite Hx in H. destruct (option_dec (sundup Δ)) as [Hx1|Hy1].
      * apply not_eq_None_Some in Hx1 as [Δ__x Hx1]; rewrite Hx1 in H.
        specialize (IHΔ Δ__x Hx1) as ->; now inv H.
      * rewrite Hy1 in H; congruence.
Qed.
Lemma δ_of_Δ_in_dom (Δ : store) ℓ :
  In ℓ (dom (δ_of_Δ Δ)) ->
  exists ρ t n, In (dL(ℓ ; ρ ; t ; n)) (img Δ)
.
Proof.
  revert ℓ; induction Δ; cbn; intros; try easy.
  destruct b, dℓ0; destruct H as [H|H].
  - inv H. exists dρ0; exists dt0; exists dn0; now left.
  - specialize (IHΔ ℓ H); deex; exists ρ; exists t; exists n0; now right.
Qed.
Lemma δ_of_Δ_in_img (Δ : store) ℓ ρ t n :
  In (dL(ℓ ; ρ ; t ; n)) (img Δ) ->
  In ℓ (dom (δ_of_Δ Δ))
.
Proof.
  induction Δ; cbn; intros H; try easy.
  destruct H as [H|H]; destruct b, dℓ0.
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
    + rewrite Hy in H. cbn in H. destruct (option_dec (List.find (fun x => loc_eqb (dℓ x) dℓ0) (img Δ))) as [Hx0|Hy0].
      * apply not_eq_None_Some in Hx0 as [Δ__x0 Hx0]; rewrite Hx0 in H; congruence.
      * rewrite Hy0 in H. destruct (option_dec (sundup Δ)) as [Hx1|Hy1].
        -- apply not_eq_None_Some in Hx1 as [Δ__x Hx1]; rewrite Hx1 in H.
           rewrite <- (sundup_refl _ Hx1) in Hx1. specialize (IHΔ Hx1).
           econstructor; eauto.
           intros H__a. eapply find_none in Hy as Hy__f; eauto. unfold vareq in Hy__f.
           now rewrite String.eqb_refl in Hy__f.
           intros H__a.
           apply δ_of_Δ_in_dom in H__a as H__a'; deex.
           eapply find_none in Hy0 as Hy0__f; eauto; cbn in Hy0__f; eq_to_defeq loc_eqb. apply neqb_neq in Hy0__f. congruence.
        -- rewrite Hy1 in H; congruence.
  - induction H; cbn; try easy.
    destruct (option_dec (List.find (fun x0 : vart => vareq x x0) (dom Δ))) as [Hx|Hy].
    + apply not_eq_None_Some in Hx as [x__x Hx].
      apply find_some in Hx as [Hx1 Hx2]. unfold vareq in Hx2. apply String.eqb_eq in Hx2; subst. contradiction.
    + rewrite Hy. destruct (option_dec (List.find (fun x => loc_eqb (dℓ x) ℓ) (img Δ))) as [Hx0|Hy0].
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
  rewrite Hy0 in Hx. cbn in Hx. destruct (option_dec (List.find (fun x => loc_eqb (dℓ x) dℓ0) (img Δ))) as [Hx1|Hy1].
  apply not_eq_None_Some in Hx1 as [Δ__x Hx1]; rewrite Hx1 in Hx; inv Hx.
  rewrite Hy1 in Hx. destruct (option_dec (sundup Δ)) as [Hx2|Hy2].
  apply not_eq_None_Some in Hx2 as [Δ__x Hx1]. rewrite Hx1 in Hx.
  inv Hx. cbn. apply sundup_refl in Hx1 as Hx1'. rewrite Hx1' in Hy0.
  rewrite (sundup_refl Δ Hx1) in Hx1. rewrite Hx1' in Hy1. rewrite Hy0, Hy1, Hx1; easy.
  rewrite Hy2 in Hx; congruence.
Qed.
Lemma snodupinv_whocares0 (a : vart) (ℓ : loc) (ρ ρ' : poison) (t t' : ControlTag) (n n' : nat) (Δ : store) :
  snodupinv (a ↦ (dL(ℓ ; ρ ; t ; n)) ◘ Δ) <-> snodupinv (a ↦ (dL(ℓ ; ρ' ; t' ; n')) ◘ Δ)
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
        cbn in H1; destruct b, dℓ0; inv H1. apply H0; now left.
        assert (~ In ℓ (dom(δ_of_Δ (Δ ◘ v0 ↦ d0 ◘ Δ')))) as H2 by (intros H2; apply H0; now right); auto.
Qed.

Lemma snodupinv_whocares (a : vart) (ℓ : loc) (ρ ρ' : poison) (t t' : ControlTag) (n n' : nat) (Δ Δ' : store) :
  snodupinv (Δ ◘ a ↦ (dL(ℓ ; ρ ; t ; n)) ◘ Δ') <-> snodupinv (Δ ◘ a ↦ (dL(ℓ ; ρ' ; t' ; n')) ◘ Δ')
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
  eqb_eq := Nat.eqb_eq ;
}.
Definition heap := mapind nateq__Instance (option value).
Definition hNil : heap := mapNil nateq__Instance (option value).
Fixpoint Hgrow_aux (H : heap) (s len : nat) : option heap :=
  match s with
  | 0 => Some(H)
  | S n' =>
    let* Hi := Hgrow_aux H n' len in
    push (len + n') None Hi
  end
.
Definition Hgrow (H : heap) (s : nat) : option heap :=
  Hgrow_aux H s (List.length (dom H))
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
Proof.
  destruct q1, q2; now cbn.
Qed.
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

Definition Htgrow (Φ : MemState) (s : nat) (t : ControlTag) : option MemState :=
  match t with
  | CCtx => let* H := Hgrow Φ.(MH__ctx) s in Some(Φ <| MH__ctx := H |>)
  | CComp => let* H := Hgrow Φ.(MH__comp) s in Some(Φ <| MH__comp := H |>)
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
  nodupinv (Ω.(SΨ).(CΞ)) /\ nodupinv (Ω.(SΦ).(MH__ctx)) /\ nodupinv (Ω.(SΦ).(MH__comp)) /\ nodupinv (Ω.(SΦ).(MΔ))
.
Lemma nodupinv_empty (Ξ : symbols) (ξ : commlib) :
  Util.nodupinv Ξ ->
  nodupinv (Ω(Fresh.empty_fresh; Ξ; ξ; List.nil; CComp; hNil; hNil; snil)).
Proof. intros H; cbn; repeat split; eauto; constructor. Qed.
Lemma nodupinv_grow_H__ctx F Ξ ξ Ks t H__ctx H__comp Δ n H__ctx':
  nodupinv (Ω(F;Ξ;ξ;Ks;t;H__ctx;H__comp;Δ)) ->
  Hgrow H__ctx n = Some H__ctx' ->
  nodupinv (Ω(F;Ξ;ξ;Ks;t;H__ctx';H__comp;Δ))
.
Proof.
  intros [Ha [Hb [Hc Hd]]]; repeat split; eauto; cbn in Ha, Hb, Hc, Hd.
  revert H__ctx' H__ctx Hb H; induction n; intros H' H Hb H0.
  - now inv H0.
  - cbn in H0. destruct (option_dec (Hgrow_aux H n (List.length (dom H)))) as [Hx|Hy]; try (rewrite Hy in H0; congruence).
    apply not_eq_None_Some in Hx as [H__x Hx].
    rewrite Hx in H0.
    cbn in H0. now apply push_ok in H0.
Qed.
Lemma nodupinv_grow_H__comp F Ξ ξ Ks t H__ctx H__comp Δ n H__comp':
  nodupinv (Ω(F;Ξ;ξ;Ks;t;H__ctx;H__comp;Δ)) ->
  Hgrow H__comp n = Some H__comp' ->
  nodupinv (Ω(F;Ξ;ξ;Ks;t;H__ctx;H__comp';Δ))
.
Proof.
  intros [Ha [Hb [Hc Hd]]]; repeat split; eauto; cbn in Ha, Hb, Hc, Hd.
  revert H__comp' H__comp Hc H; induction n; intros H' H Hc H0.
  - now inv H0.
  - cbn in H0. destruct (option_dec (Hgrow_aux H n (List.length (dom H)))) as [Hx|Hy]; try (rewrite Hy in H0; congruence).
    apply not_eq_None_Some in Hx as [H__x Hx].
    rewrite Hx in H0.
    cbn in H0. now apply push_ok in H0.
Qed.
(** Types of events that may occur in a trace. *)
Variant preevent : Type :=
| Sstart : preevent
| Send (v : value) : preevent
| Salloc (ℓ : loc) (n : nat) : preevent
| Sdealloc (ℓ : loc) : preevent
| Sget (ℓ : loc) (n : nat) : preevent
| Sset (ℓ : loc) (n : value) (v : value) : preevent
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
  - inv H; repeat split; easy.
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
    | Xnew e => Xnew (R e)
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
              (Φ Φ' : MemState) (n : nat) (ℓ : loc) (Δ' : ptrstore),
    ℓ = addr(Util.length (getH Φ t)) ->
    push ℓ (dL(ℓ ; ◻ ; t ; n)) Φ.(MΔ) = Some Δ' ->
    Some Φ' = Htgrow (Φ <| MΔ := Δ' |>) n t ->
    (Ωa(F ; Ψ ; t ; Φ)) ▷ Xnew (Xval n) --[ ev( Salloc ℓ n ; t ) ]--> (Ωa(F ; Ψ ; t ; Φ')) ▷ (Xval (Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ))))
| e_delete : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
               (Φ Φ' : MemState) (n : nat) (ℓ : loc) (ρ : poison) (Δ1 Δ2 : ptrstore),
    Util.nodupinv (Δ1 ◘ ℓ ↦ (dL(ℓ ; ρ ; t ; n)) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ ℓ ↦ dL(ℓ ; ρ ; t ; n) ◘ Δ2) ->
    Φ' = Φ <| MΔ := Δ1 ◘ ℓ ↦ (dL(ℓ ; ☣ ; t ; n)) ◘ Δ2 |> ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xdel (Xval (Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ)))) --[ ev( Sdealloc ℓ ; t ) ]--> Ωa(F ; Ψ ; t ; Φ') ▷ Xval 0
| e_get : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
            (Φ : MemState) (n m ℓ : nat) (v : value)  (ρ : poison) (Δ1 Δ2 : ptrstore),
    Util.nodupinv (Δ1 ◘ (addr ℓ) ↦ dL(addr ℓ ; ρ ; t ; m) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (addr ℓ) ↦ dL(addr ℓ ; ρ ; t ; m) ◘ Δ2) ->
    (mget (getH Φ t) (ℓ + n) = Some(Some v) \/ v = Vnat 1729) ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xget (Xval Vcap) (Xval(Vptr (addr ℓ))) (Xval n) --[ ev( Sget (addr ℓ) n ; t ) ]--> Ωa(F ; Ψ ; t ; Φ) ▷ Xval v
| e_set : forall (F : CSC.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag) (H' : heap)
            (Φ Φ' : MemState) (n m ℓ : nat) (w : value) (ρ : poison) (Δ1 Δ2 : ptrstore),
    Util.nodupinv (Δ1 ◘ (addr ℓ) ↦ dL(addr ℓ ; ρ ; t ; m) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (addr ℓ) ↦ dL(addr ℓ ; ρ ; t ; m) ◘ Δ2) ->
    (mset (getH Φ t) (ℓ + n) (Some w) = Some H' \/ H' = getH Φ t) ->
    Φ' = setH Φ t H' ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xset (Xval Vcap) (Xval(Vptr (addr ℓ))) (Xval n) (Xval w) --[ ev( Sset (addr ℓ) n w ; t ) ]--> Ωa(F ; Ψ ; t ; Φ') ▷ Xval w
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
  remember (Ω ▷ e) as r0; remember (Ω' ▷ e') as r1.
  induction 1; inv Heqr0; inv Heqr1; try easy.
  - (* e_delete *) admit.
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
    | Xnew (Xval(Vnat n)) =>
      let ℓ := addr(Util.length (getH Ω.(SΦ) Ω.(St))) in
      let* Δ' := push ℓ (dL(ℓ ; ◻ ; Ω.(St) ; n)) Ω.(SΦ).(MΔ) in
      let* Φ' := Htgrow (Ω.(SΦ) <| MΔ := Δ' |>) n Ω.(St) in
      let Ω' := Ω <| SΦ := Φ' |> in
      Some(Some(ev(Salloc ℓ n ; Ω.(St))), Ω' ▷ Xval(Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ))))
    | Xdel (Xval(Vpack (LConst ℓ) (Vpair Vcap (Vptr ℓ')))) =>
      if ℓ == ℓ' then
        let* Δ := undup Ω.(SΦ).(MΔ) in
        let* (Δ1, l, dl, Δ2) := splitat Δ ℓ in
        if ℓ == l then
          let dl' := dl <| dρ := ☣ |> in
          let Φ' := Ω.(SΦ) <| MΔ := Δ1 ◘ ℓ ↦ dl' ◘ Δ2 |> in
          let Ω' := Ω <| SΦ := Φ' |> in
          Some(Some(ev(Sdealloc ℓ ; Ω.(St))), Ω' ▷ Xval 0)
        else
          None
      else
        None
    | Xget (Xval Vcap) (Xval(Vptr(addr ℓ))) (Xval(Vnat n)) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, l, dl, Δ2) := splitat Δ (addr ℓ) in
      let '(addr ln) := l in
      if ℓ == ln then
        let v := match mget (getH Ω.(SΦ) Ω.(St)) (ℓ+n) with
                 | Some(Some v) => v
                 | _ => Vnat 1729
                 end
        in
        Some(Some(ev(Sget (addr ℓ) n ; Ω.(St))), Ω ▷ Xval v)
      else
        None
    | Xset (Xval Vcap) (Xval(Vptr(addr ℓ))) (Xval(Vnat n)) (Xval w) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, l, dl, Δ2) := splitat Δ (addr ℓ) in
      let '(addr ln) := l in
      if ℓ == ln then
        let H' := match mset (getH Ω.(SΦ) Ω.(St)) (ℓ+n) (Some w) with
                  | Some(H') => H'
                  | _ => getH Ω.(SΦ) Ω.(St)
                  end
        in
        let Φ' := setH Ω.(SΦ) Ω.(St) H' in
        let Ω' := Ω <| SΦ := Φ' |> in
        Some(Some(ev(Sset (addr ℓ) (Vnat n) w ; Ω.(St))), Ω' ▷ Xval w)
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
Admitted.
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
  | Xnew e =>
    match e  with
    | Xval(v) =>
      Some(Khole, Xnew (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Knew K, e')
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
  | Xnew (Xval v) => Some(Xnew (Xval v))
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
  | Xnew (Xval v) => Some(Xnew (Xval v))
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
    Ω ▷ e --[ SCrash ]--> ↯ ▷ stuck
| E_start : forall (Ω Ω' : state) (Ξ1 Ξ2 : symbols) (main : symbol) (Ψ' : CfState) (e : expr),
    Ω.(SΨ).(CKs) = nil ->
    Ω.(St) = CComp ->
    Ω.(SΦ) = EmptyΦ ->
    ((Ω.(SΨ).(CΞ)) = (Ξ1 ◘ "main"%string ↦ main ◘ Ξ2)) ->
    e = subst (vart_of_symbol main) (expr_of_symbol main) (Xval 0) ->
    Ψ' = Ω.(SΨ) <| CKs := ((Khole, "main"%string) :: nil)%list |> ->
    Ω' = Ω <| St := CCtx |> <| SΨ := Ψ' |> ->
    Ω ▷ Xcall "main"%string (Xval 0) --[ ev(Sstart ; CComp) ]--> Ω' ▷ e
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
    Ω.(St) = CCtx ->
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
           (andb (Nat.eqb (Util.length Ω.(SΦ).(MH__ctx)) 0)
           (andb (Nat.eqb (Util.length Ω.(SΦ).(MH__comp)) 0)
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
          match Ω.(St) with
          | CCtx =>
            let Ψ' := Ω.(SΨ) <| CKs := nil |> in
            let Ω' := Ω <| St := CComp |> <| SΨ := Ψ' |> in
            Some(Some(ev(Send v ; CCtx)), Ω ▷ Xval v)
          | CComp => None
          end
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
Inductive rtexpr_is_val : rtexpr -> Prop :=
| CRTval : forall (Ω : state) (e : expr) (v : value), e = Xval v -> rtexpr_is_val (Ω ▷ e)
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
  - (* new *) grab_value e.
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
  - (* new *) grab_value e.
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
(* FIXME: perform typechecking *)
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

Definition initΩ (Ξ__ctx Ξ__comp : symbols) : option state :=
  let* Ξ := linkf Ξ__ctx Ξ__comp in
  let ξ := dom Ξ__comp in
  Some(Ω(Fresh.empty_fresh; Ξ ; ξ ; nil ; CComp ; hNil ; hNil ; snil))
.

(* Allocate an array of size 5. *)
Example binop57 :=
  Xreturn (
    Xunpack "ℓ"%string "p"%string
      (Xnew (Xval 5))
      (Xunpair "cap"%string "ptr"%string
          (Xvar "p"%string)
          (Xlet "y"%string
            (Xlet dontcare (Xset (Xvar "cap"%string)
                              (Xvar "ptr"%string)
                              (Xval 2)
                              (Xval 42)
                            )
                  (Xget (Xvar "cap"%string)
                        (Xvar "ptr"%string)
                        (Xval 2)
                  )
            )
            (Xbinop Badd (Xdel (Xpack (Xvar "ℓ"%string) (Xpair (Xvar "cap"%string)
                                                               (Xvar "ptr"%string))
                               )
                         )
                         (Xbinop Badd (Xvar "y"%string) (Xval 27))
            )
          )
      )
  )
.
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
    (* ifz x[i] = 0 then *)
    Xifz (Xget (Xvar "xcap") (Xvar "xptr") (Xvar "i"))
      (Xreturn (strncpy_pack_params (Xvar "i") (Xvar "n") "x" "y"))
    (* else if i < n then *)
      (Xifz (Xbinop Bless (Xvar "i") (Xvar "n"))
        (seq
          (* y[i] = x[i] *)
          (Xset (Xvar "ycap") (Xvar "yptr") (Xvar "i")
              (Xget (Xvar "xcap") (Xvar "xptr") (Xvar "i")))
          (* recursive call to simulate the loop *)
          (Xreturn (Xcall "strncpy" (strncpy_pack_params (Xbinop Badd (Xvar "i") (Xval 1)) (Xvar "n") "x" "y")))
        )
        (Xreturn (strncpy_pack_params (Xvar "i") (Xvar "n") "x" "y"))
      )
  )
)%string.

(* Simple, correct context that calls strncpy *)
Example main' := (
  L_unpackptr "xℓ" "xcap" "xptr" (Xnew (Xval 3)) (
    L_unpackptr "yℓ" "ycap" "yptr" (Xnew (Xval 3)) (
      seq (Xset (Xvar "xcap") (Xvar "xptr") (Xval 0) (Xval 1))
     (seq (Xset (Xvar "xcap") (Xvar "xptr") (Xval 1) (Xval 2))
       (seq (Xset (Xvar "xcap") (Xvar "xptr") (Xval 2) (Xval 3))
         (seq
             (Xlet "r" (Xcall "strncpy" (strncpy_pack_params (Xval 0) (Xval 3) "x" "y"))
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

Example main := (Xcall "main'"%string (Xval 0)).

Example Ξ__ctx : symbols := ("main"%string ↦ (dontcare, Tfun Tℕ Tℕ, main) ◘ (mapNil _ _)).
Example Ξ__comp : symbols := ("main'"%string ↦ (dontcare, Tfun Tℕ Tℕ, main') ◘ ("strncpy"%string ↦ ("p"%string, Tfun Tℕ Tℕ, strncpy) ◘ (mapNil _ _))).

Local Set Warnings "-abstract-large-number".
Compute ((fun n => (let* iΩ := initΩ Ξ__ctx Ξ__comp in
         let* (As, r) := star_stepf n (iΩ ▷ (Xcall "main"%string (Xval 0))) in
         match r with
         | RCrash => None
         | RTerm Ω e => Some(As, e)
         end
        ))
135).

Abort.

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

Lemma substi Γ e x y t :
  check Γ e t ->
  check (substτ Γ x y) (subst x e (Fvar y)) t
.
Proof.
Admitted.


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
