Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef Lia.
Require Import CSC.Sets CSC.Util CSC.Fresh CSC.Props.

Require Import CSC.Ltms.syntax CSC.Ltms.dynamic.

From RecordUpdate Require Import RecordUpdate.

Import LangNotations.
Open Scope LangNotationsScope.

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
  remember (Γ1 ◘ Γ2) as Γ; revert Γ1 Γ2 HeqΓ; induction Γ; split; intros.
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
| T_vcap : forall (b : bool) (Δ : Delta) (Γ : Gamma) (γ : vart) (τ : pre_ty),
    List.In γ Δ ->
    [b ; Δ ; Γ |- Xval(Vcap) : Tcap (LVar γ) τ]
| T_vptr : forall (b : bool) (Δ : Delta) (Γ : Gamma) (γ : vart) (ℓ : loc),
    List.In γ Δ ->
    [b ; Δ ; Γ |- Xval(Vptr ℓ γ) : Tptr (LVar γ)]
| T_vpack : forall (b : bool) (Δ : Delta) (Γ : Gamma) (γ γ' : vart) (v : value) (τ : pre_ty),
    List.In γ' Δ ->
    [b ; Δ ; Γ |- Xval v: substτ γ τ γ'] ->
    [b ; Δ ; Γ |- Xval(Vpack (LVar γ) v) : Texists γ τ]
| T_cpack : forall (b : bool) (Δ : Delta) (Γ : Gamma) (ℓ : loc) (γ γ' : vart) (v : value) (τ : pre_ty),
    List.In γ' Δ ->
    [b ; Δ ; Γ |- Xval v: Tptr (LVar γ')] ->
    [b ; Δ ; Γ |- Xval(Vpack (LConst ℓ γ) (Vpair Vcap v)) : Texists γ (Tpair (Tcap (LVar γ) τ) (Tptr (LVar γ)))]
| T_pair : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (e1 e2 : expr) (τ1 τ2 : pre_ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [b ; Δ ; Γ1 |- e1 : τ1] ->
    [b ; Δ ; Γ2 |- e2 : τ2] ->
    [b ; Δ ; Γ |- Xpair e1 e2 : Tpair τ1 τ2]
| T_unpair : forall (b : bool) (Δ : Delta) (Γ Γ1 Γ2 : Gamma) (x1 x2 : vart) (e0 e1 : expr) (τ1 τ2 : pre_ty) (τ3 : ty),
    Γ ≡ Γ1 ∘ Γ2 ->
    [false ; Δ ; Γ1 |- e0 : Tpair τ1 τ2] ->
    [false ; Δ ; x2 ↦ (Tpre τ2) ◘ (x1 ↦ (Tpre τ1) ◘ Γ2) |- e1 : τ3]%list ->
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
    [b ; Δ ; Γ |- Xnew γ e0 e1 : Texists γ (Tpair (Tcap (LVar γ) τ) (Tptr (LVar γ)))]
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

(* **********************************************************************
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

*)

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
| TMSConsAgree : forall (ℓ : loc) (t : ControlTag) (n : nat) (γ : vart) (T__TMS T__TMS' : TMSMonAux.AbsState) (Δ : ptrstore),
    ~(List.In (ℓ,t) (TMSMonAux.alloced T__TMS)) ->
    ~(List.In (ℓ,t) (TMSMonAux.freed T__TMS)) ->
    tms_store_agree T__TMS Δ ->
    T__TMS' = {|
               TMSMonAux.alloced := List.app (TMSMonAux.alloced T__TMS) (List.cons (ℓ,t) List.nil) ;
               TMSMonAux.freed := TMSMonAux.freed T__TMS ;
            |} ->
    tms_store_agree T__TMS' (dK(ℓ ; t) ↦ dL(◻ ; n ; γ) ◘ Δ)
| TMSPoisonAgree : forall (ℓ : loc) (t : ControlTag) (n : nat) (γ : vart) (T__TMS T__TMS' : TMSMonAux.AbsState) (Δ : ptrstore),
    ~(List.In (ℓ,t) (TMSMonAux.alloced T__TMS)) ->
    ~(List.In (ℓ,t) (TMSMonAux.freed T__TMS)) ->
    T__TMS' = {|
               TMSMonAux.alloced := TMSMonAux.alloced T__TMS ;
               TMSMonAux.freed := List.app (TMSMonAux.freed T__TMS) (List.cons (ℓ,t) List.nil) ;
            |} ->
    tms_store_agree T__TMS Δ ->
    tms_store_agree T__TMS' (dK(ℓ ; t) ↦ dL(☣ ; n ; γ) ◘ Δ)
.
Inductive tms_state_agree : TMSMonAux.AbsState -> state -> Prop :=
| TMSStateAgree : forall (Ω : state) (T__TMS : TMSMonAux.AbsState),
    tms_store_agree T__TMS Ω.(SΦ).(MΔ) ->
    tms_state_agree T__TMS Ω
.

(** Store splitting. We don't need a case for e.g. nat, since identifiers with type nat get substituted at runtime. *)
Inductive ptrstore_split (Ξ : symbols) : ptrstore -> Delta -> Gamma -> Prop :=
| TemptyΔ : forall (Γ : Gamma), gamma_from_symbols Ξ = Γ -> ptrstore_split Ξ snil nil Γ
| Tref1ℕ : forall (γ : vart) (Γ : Gamma) (Δ__ptrs : Delta) (Δ : ptrstore) (ℓ : loc) (t : ControlTag) (n : nat),
    ptrstore_split Ξ Δ Δ__ptrs Γ ->
    ptrstore_split Ξ (dK(ℓ ; t) ↦ dL(◻ ; n ; γ) ◘ Δ) (γ :: Δ__ptrs)%list (Γ)
| Tref1ℕpoison : forall (γ : vart) (Γ : Gamma) (Δ__ptrs : Delta) (Δ : ptrstore) (ℓ : loc) (t : ControlTag) (n : nat),
    ptrstore_split Ξ Δ Δ__ptrs Γ ->
    ptrstore_split Ξ (dK(ℓ ; t) ↦ dL(☣ ; n ; γ) ◘ Δ) Δ__ptrs (Γ)
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
Lemma ptrstate_split_determ Ω Δ__ptrs0 Δ__ptrs1 Γ0 Γ1 :
  ptrstate_split Ω Δ__ptrs0 Γ0 ->
  ptrstate_split Ω Δ__ptrs1 Γ1 ->
  Δ__ptrs0 = Δ__ptrs1 /\ Γ0 = Γ1
.
Proof.
Admitted.

Definition ectx_check (b : bool) (Δ__ptrs : Delta) (Γ : Gamma) (K : evalctx) (τ τ' : ty) :=
  forall (e : expr), [b ; Δ__ptrs ; Γ |- e : τ' ] -> [b ; Δ__ptrs ; Γ |- insert K e : τ]
.
Definition ectx_rt_check (Ω : state) (K : evalctx) (τ τ' : ty) :=
  forall (e : expr), rt_check Ω e τ' -> rt_check Ω (insert K e) τ
.

Lemma check_recompose (K : evalctx) (e : expr) (b : bool) (Γ : Gamma) (Δ__ptrs : Delta) (τ : ty) :
  [b; Δ__ptrs; Γ |- insert K e : τ ] ->
  exists τ', ectx_check b Δ__ptrs Γ K τ' τ /\ [b ; Δ__ptrs ; Γ |- e : τ']
.
Proof. Admitted.
Lemma rt_check_recompose (Ω : state) (K : evalctx) (e : expr) (τ : ty) :
  rt_check Ω (insert K e) τ ->
  exists τ', ectx_rt_check Ω K τ' τ /\ rt_check Ω e τ'
.
Proof.
  intros H; inv H; apply check_recompose in H1; deex; destruct H1 as [H1a H1b].
  exists τ'. split.
  - intros e' H; econstructor; eauto; eapply H1a; inv H;
    eapply ptrstate_split_determ in H0; eauto; destruct H0 as [H0a H0b]; subst; assumption.
  - econstructor; eauto.
Qed.

Lemma rt_check_decompose (Ω : state) (K : evalctx) (e : expr) (τ τ' : ty) :
  ectx_rt_check Ω K τ' τ ->
  rt_check Ω e τ' ->
  rt_check Ω (insert K e) τ
.
Proof. Admitted.

Lemma ptrstate_split_noownedptr Ω Δ Γ :
  ptrstate_split Ω Δ Γ ->
  NoOwnedPtr Γ
.
Proof. Admitted.
Lemma ptrstore_split_noownedptr Ξ Δ Δ__ptrs Γ :
  ptrstore_split Ξ Δ Δ__ptrs Γ ->
  NoOwnedPtr Γ
.
Proof. Admitted.

Lemma ptrstate_Γ Ω Δ__ptrs Γ :
  ptrstate_split Ω Δ__ptrs Γ ->
  Γ = gamma_from_symbols (Ω.(SΨ).(CΞ))
.
Proof.
  intros H; inv H. dependent induction H0; trivial.
  - specialize (IHptrstore_split (Ω <| SΦ := Ω.(SΦ) <| MΔ := Δ |> |>)). eapply IHptrstore_split; reflexivity.
  - specialize (IHptrstore_split (Ω <| SΦ := Ω.(SΦ) <| MΔ := Δ |> |>)). eapply IHptrstore_split; reflexivity.
Qed.

Lemma Γ_split_xi Γ Γ1 Γ2 Ξ :
  Γ ≡ Γ1 ∘ Γ2 ->
  Γ = gamma_from_symbols (Ξ) ->
  Γ1 = Γ /\ Γ2 = Γ
.
Proof.
  intros H; revert Ξ; dependent induction H; cbn; eauto; intros.
  - split; f_equal; eapply IHsplitting. (*eZ*)
Admitted.

Lemma ptrstore_split_weaken_poisoned Ξ Δ1 Δ2 dk n γ Δ__ptrs Γ :
  ptrstore_split Ξ (Δ1 ◘ Δ2) Δ__ptrs Γ  ->
  ptrstore_split Ξ (Δ1 ◘ dk ↦ {| dρ := ☣; dn := n; dx := γ |} ◘ Δ2) Δ__ptrs Γ
.
Proof. Admitted.

Lemma ptrstore_split_setH_ign Ξ Φ t H Δ__ptrs Γ :
  ptrstore_split (Ξ) (MΔ (Φ)) Δ__ptrs Γ ->
  ptrstore_split (Ξ) (MΔ (setH Φ t H)) Δ__ptrs Γ
.
Proof. Admitted.

Lemma ptrstore_split_split Ξ Δ1 Δ2 dk dl Δ__ptrs Γ :
  ptrstore_split (Ξ) (Δ1 ◘ dk ↦ dl ◘ Δ2) Δ__ptrs Γ ->
  exists Δptrs1 γ Δptrs2, ptrstore_split (Ξ) (Δ1 ◘ Δ2) (Δptrs1 ++ Δptrs2)%list Γ /\
                     (Δ__ptrs = Δptrs1 ++ γ :: Δptrs2)%list /\
                     (~List.In γ (Δptrs1 ++ Δptrs2))
.
Proof. Admitted.

Lemma substitution Γ Γ1 Γ2 v τ1 τ2 x Δ__ptrs b b' b'' e :
  Γ ≡ Γ1 ∘ Γ2 ->
  [b; Δ__ptrs; Γ1 |- Xval v : τ1 ] ->
  [b'; Δ__ptrs; (x ↦ τ1 ◘ Γ2) |- e : τ2 ] ->
  [b''; Δ__ptrs; Γ |- subst x e (Xval v) : τ2]
.
Proof. Admitted.

Lemma pstep_preservation Ω e τ Ω' e' a :
  rt_check Ω e τ ->
  Ω ▷ e --[, a ]--> Ω' ▷ e' ->
  rt_check Ω' e' τ
.
Proof.
  intros H0 H1; cbv in H1; dependent induction H1.
  - inv H0. inv H1. econstructor; eauto. econstructor. eapply ptrstate_split_noownedptr; eauto.
  - inv H0. inv H1. econstructor; eauto. eapply ptrstate_Γ in H as H'. eapply Γ_split_xi in H4 as H4'; eauto.
    destruct H4' as [H4a H4b]; subst. easy.
  - inv H0. inv H2. econstructor; eauto. eapply ptrstate_Γ in H1 as H1'. eapply Γ_split_xi in H5 as H5'; eauto.
    destruct H5' as [H5a H5b]; subst. easy.
  - inv H0. inv H1. econstructor; eauto. econstructor; eauto.
  - inv H0. inv H1. econstructor; eauto. eapply substitution; eauto.
  - inv H0. inv H1. inv H10. econstructor; eauto. eapply ptrstate_Γ in H as H'. eapply Γ_split_xi in H9 as H9'; eauto.
    destruct H9' as [H9a H9b]; subst. eapply Γ_split_xi in H7 as H7'; eauto. destruct H7' as [H7a H7b]; subst.
    eapply substitution; eauto. instantiate (1:=false). eapply substitution; eauto. admit. (* may need to preserve split info *)
  - inv H0. inv H5. remember (addr (Datatypes.length (getH Φ t))) as ℓ.
    apply push_ok in H1 as H1'. unfold push in H1. crush_option (undup ({| dL := ℓ ; dt := t |} ↦ {| dρ := ◻ ; dn := n ; dx := γ |} ◘ MΔ Φ)).
    apply undup_refl in Hx as Hx'; rewrite <- Hx' in *. inv H1. inv H4. cbn in H. econstructor.
    + econstructor. cbn. rewrite Htgrow_Δ_passthrough. econstructor. eassumption.
    + eapply T_cpack. now left. econstructor. now left.
  - inv H0. inv H4. inv H7. inv H14. inv H3; cbn in *. rewrite H2 in *.
    assert (H0':=H0); eapply ptrstore_split_split in H0'; deex; destruct H0' as [H0' [H0'' H0''']].
    econstructor.
    + econstructor; cbn. eapply ptrstore_split_weaken_poisoned. eapply ptrstore_split_split in H0; deex. eassumption.
    + econstructor. eapply ptrstore_split_noownedptr; eauto.
  - inv H0. inv H4. inversion H12; subst. inversion H14; subst.
    eapply ptrstate_Γ in H3 as H3'. eapply Γ_split_xi in H8 as H8'; eauto. destruct H8' as [H8a H8b]; subst.
    eapply Γ_split_xi in H7 as H7'; eauto. destruct H7' as [H7a H7b]; subst.
    inv H3; cbn in *. econstructor.
    + econstructor; cbn; rewrite H2 in *; cbn in *. eassumption.
    + econstructor; eauto. destruct H1 as [H1|[H1a H1b]].
      * admit. (* value typechecks *)
      * inv H1a. admit. (* value typechecks *)
  - inv H0. inv H5. inversion H14; subst. inversion H16; subst.
    eapply ptrstate_Γ in H4 as H4'. eapply Γ_split_xi in H10 as H10'; eauto. destruct H10' as [H10a H10b]; subst.
    eapply Γ_split_xi in H9 as H9'; eauto. destruct H9' as [H9a H9b]; subst.
    eapply Γ_split_xi in H8 as H8'; eauto. destruct H8' as [H8a H8b]; subst.
    inv H4; cbn in *. econstructor.
    + econstructor; cbn; rewrite H3 in *; cbn in *. eapply ptrstore_split_setH_ign. rewrite H3. eassumption.
    + econstructor; eauto. destruct H1 as [H1|[H1a H1b]].
      * admit. (* value typechecks, true/false doesn't matter *)
      * admit. (* value typechecks, true/false doesn't matter *)
  - inv H0. inv H1. inv H10. eapply ptrstate_Γ in H as H'. inv H. cbn in H0.
    eapply Γ_split_xi in H8 as H8'; eauto. destruct H8' as [H8a H8b]; subst.
    econstructor.
    + econstructor; eauto.
    + eapply substitution; eauto; admit. (* nested subst application *)
  - inv H0. inv H1.
Admitted.

Lemma estep_preservation Ω e τ Ω' e' a :
  rt_check Ω e τ ->
  Ω ▷ e ==[, a ]==> Ω' ▷ e' ->
  rt_check Ω' e' τ
.
Proof.
  intros H0 H1; cbv in H1; dependent induction H1.
  - eapply rt_check_recompose in H0; deex; destruct H0 as [H0a H0b].
    eapply pstep_preservation in H2; eauto.
    eapply rt_check_decompose; eauto. (*compat of Ω and Ω'*) admit.
  - inv H0. inv H4. inv H3. econstructor; eauto.
    + econstructor; cbn. eassumption.
    + (* substitution lemma *) admit.
  - inv H0. inv H1. econstructor; eauto.
    + econstructor; cbn. eassumption.
    + admit.
  - inv H0. inv H2. econstructor; eauto.
    + econstructor; cbn. eassumption.
    + (* should be easy with syntactic (de-/re-)compo *) admit.
  - inv H0. inv H1. econstructor; eauto.
    + econstructor; cbn. eassumption.
    + (* syntactic (de-/re-)compo *) admit.
Admitted.

Lemma store_agree_split T__TMS Δ1 ℓ ρ t n γ Δ2 :
  tms_store_agree T__TMS (Δ1 ◘ dK((addr ℓ) ; t) ↦ dL(ρ ; n ; γ) ◘ Δ2) ->
  exists T__TMS1 T__TMS2, tms_store_agree T__TMS1 Δ1 /\
                 tms_store_agree T__TMS2 Δ2 /\
                 tms_store_agree (TMSMonAux.singleton (addr ℓ) t) (dK((addr ℓ) ; t) ↦ dL(ρ ; n ; γ) ◘ snil) /\
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
    + apply push_ok in H1 as H1'. unfold push in H1. crush_undup (dK(addr(List.length(getH Φ CCtx)) ; CCtx) ↦ {| dρ := ◻; dn := n; dx := γ |} ◘ MΔ Φ).
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
    + apply push_ok in H1 as H1'. unfold push in H1. crush_undup (dK(addr(List.length(getH Φ CComp)) ; CComp) ↦ {| dρ := ◻; dn := n; dx := γ |} ◘ MΔ Φ).
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
    inv Aa. inv H2. inv H1c; try (inv H12; exfalso; revert H4; clear; intros H; induction (TMSMonAux.freed T__TMS); easy).
    inv H13. cbn in *.
    exists (Some(TMSMonAux.ADealloc (addr ℓ) t)). exists (TMSMonAux.append (TMSMonAux.append T__TMS1 T__TMS2) (TMSMonAux.freed_singleton (addr ℓ) t)).
    repeat split; try constructor. econstructor.
    clear; cbn; induction (TMSMonAux.alloced T__TMS1); cbn. now left. now right.
    cbn. admit. (* ℓ is not in T__TMS1 and T__TMS2, since nodupinv *)
    now cbn.
    cbn. unfold TMSMonAux.append; cbn. rewrite List.app_nil_r. easy.
    cbn. rewrite TMSMonAux.app_assoc. eapply store_agree_rsplit.
    easy. econstructor; try exact H1b.
    admit. admit. (*from nodupinv*)
    unfold TMSMonAux.append; cbn. rewrite List.app_nil_r. easy.
  - (*get*) inv Heqr1; inv Heqr2.
    inv Ac; assert (H2':=H2). cbn in H2; rewrite H0 in H2; apply store_agree_split in H2; deex.
    destruct H2 as [H2a [H2b [H2c H2d]]].
    inv Aa. inv H3. inv H2c; try now (inv H17; exfalso; revert H5; clear; intros H; induction (TMSMonAux.freed T__TMS); easy).
    inv H18. cbn in *.
    exists (Some(TMSMonAux.AUse (addr ℓ) t)). exists (TMSMonAux.append T__TMS1 (TMSMonAux.append (TMSMonAux.singleton (addr ℓ) t) T__TMS2)).
    repeat split; try constructor; try easy.
    clear; cbn; induction (TMSMonAux.alloced T__TMS1); cbn. now left. now right.
    cbn. admit. (* ℓ is not in T__TMS1 and T__TMS2, since nodupinv *)
  - (*set*) inv Heqr1; inv Heqr2. inv Aa. inv H3. (* similar to get *) admit.
  - (*unpack*) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
  - (*pack*) inv Heqr1; inv Heqr2. exists None. exists T__TMS. repeat split; try constructor.
    now inv Ac.
Admitted.

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
  - inv H3. specialize (H6 ℓ t (dL(◻ ; n; γ))). rewrite <- x in H6. cbn in H6.
    eq_to_defeq (ptr_key_eqb). rewrite eq_refl in H6.
    assert (Some(dL(◻ ; n; γ)) = Some(dL(◻ ; n; γ))) by reflexivity.
    now specialize (H6 H2).
  - inv H3. inv H8. pose (Ω' := Ω <| SΦ := Ω.(SΦ) <| MΔ := Δ |> |>).
    specialize (IHtms_store_agree Ω'). eapply IHtms_store_agree; eauto.
    instantiate (1:=v0). econstructor; eauto. shelve.
    inv H7. rewrite <- x in *. inv H3. constructor; eauto.
    Unshelve.
    intros. cbn in H. rewrite <- x in *. inv H1. eapply H6; cbn.
    instantiate (1:=t0); instantiate(1:=l).
    destruct (eq_dec (dK(ℓ ; t)) (dK(l ; t0))).
    + apply mget_min in H4. cbn in H4. apply Min_in in H4 as [H4a H4b]. inv H1. (* contradicts with ~(In (l,t0) T__TMs) using tms_store_agree *) admit.
    + apply neqb_neq in H1. eq_to_defeq ptr_key_eqb. rewrite H1. assumption.
Admitted.

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
Proof.
  induction Ξ1; cbn.
  - reflexivity.
  - f_equal; auto.
Qed.

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
