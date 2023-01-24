Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef.
Require Import CSC.Sets CSC.Util CSC.Fresh CSC.Langs.Util.
Require CSC.Langs.TMMon CSC.Langs.S CSC.Langs.T.

(** * Secure Compiler from S to T *)

(** compilation of binary operator symbols *)
Definition comp__b (b : S.binopsymb) : T.binopsymb :=
  match b with
  | S.Badd => T.Badd
  | S.Bsub => T.Bsub
  | S.Bmul => T.Bmul
  | S.Bless => T.Bless
  end
.
(** compilation of expressions *)
Fixpoint comp__e (e : S.expr) : T.expr :=
  match e with
  | S.Xabort => T.Xabort
  | S.Xres(S.Fabrt) => T.Xres(T.Fabrt)
  | S.Xres(S.Fres f) =>
      match f with
      | S.Fvar x => T.Xres(T.Fres(T.Fvar x))
      | S.Fval(S.Vnat n) => T.Xres(T.Fres(T.Fval(T.Vnat n)))
      end
  | S.Xbinop b e1 e2 =>
      let c1 := comp__e e1 in
      let c2 := comp__e e2 in
      let bb := comp__b b in
      T.Xbinop bb c1 c2
  | S.Xget x e =>
      let c := comp__e e in
      T.Xget x c
  | S.Xset x e0 e1 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      T.Xset x c0 c1
  | S.Xlet x e0 e1 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      T.Xlet x c0 c1
  | S.Xnew x e0 e1 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      T.Xnew x c0 c1
  | S.Xdel x => T.Xdel x
  | S.Xreturn e =>
      let c := comp__e e in
      T.Xreturn c
  | S.Xcall foo e =>
      let c := comp__e e in
      T.Xcall foo c
  | S.Xifz e0 e1 e2 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      let c2 := comp__e e2 in
      T.Xifz c0 c1 c2
  end
.

(** Compiling symbols *)
Definition comp__symb (F : S.symbol) : option(T.symbol) :=
  let '(x__arg', τ__fn, e__bdy) := F in
  let x__arg := T.Xres(T.Fres(T.Fvar(x__arg'))) in
  match τ__fn with
  | S.Tectx(S.Tarrow τ0 _τ1) =>
     match τ0 with
     | S.Tnat =>
         Some(x__arg', T.Xifz (T.Xhas x__arg T.Tnat) (comp__e e__bdy) (T.Xabort))
     | S.Tnatptr S.Qhalf =>
         Some(x__arg', T.Xifz (T.Xhas x__arg T.Tnat)
                      (T.Xabort)
                      (T.Xifz (T.Xhas x__arg T.Tpair)
                              (T.Xabort)
                              (T.Xifz (T.Xispoison x__arg')
                                      (T.Xabort)
                                      (comp__e e__bdy))))
     | _ => None
     end
  | _ => None
  end
.
Fixpoint comp__symbs (Fs : S.symbols) : option(T.symbols) :=
  match Fs with
  | mapNil _ _ => Some(mapNil _ _)
  | mapCons foo symb rest =>
      let* thesymb := comp__symb symb in
      let* therest := comp__symbs rest in
      Some(mapCons foo thesymb therest)
  end
.

(** Definition of various relations *)
Definition locmap_st := mapind S.loceq__Instance T.loc.
Inductive poison_eq : S.poison -> T.poison -> Prop :=
| poisonedEqual : poison_eq S.poisoned T.poisoned
| poisonlessEqual : poison_eq S.poisonless T.poisonless
.
Inductive heap_agree : nat -> S.heap -> T.heap -> S.heap -> T.heap -> Prop :=
| heap_agree_zero : forall (sH : S.heap) (tH : T.heap),
    heap_agree 0 sH tH sH tH
| heap_agree_cons : forall (sH sH' : S.heap) (tH tH' : T.heap) (sx tx sn tn m : nat),
    sx = tx ->
    sn = tn ->
    heap_agree m sH tH sH' tH' ->
    heap_agree (S m) (sx ↦ sn ◘ sH) (tx ↦ tn ◘ tH) sH' tH'
.
Inductive heap_skip : nat -> S.heap -> S.heap -> Prop :=
| heap_skip_nil : forall (H : S.heap),
    heap_skip 0 H H
| heap_skip_cons : forall (H H' : S.heap) (x n m : nat),
    heap_skip n H H' ->
    heap_skip (S n) (x ↦ m ◘ H) H'
.
(** This relation describes the agreement between the memory states in S and T.
    It's indexed by a map from source locations to target locatoions and  by
    a list of source locations that should simply be ignored by the relation. *)
Inductive memstate_eq (δ : locmap_st) (sL : list S.loc) : (S.heap * S.store) -> (T.heap * T.store) -> Prop :=
| empty_memstate_eq : memstate_eq δ sL (mapNil _ _, mapNil _ _) (mapNil _ _, mapNil _ _)
| cons_memstate_eq : forall (sℓ sℓ' : S.loc) (tℓ tℓ' : T.loc) (n0 n1 n2 n3 : nat) (sx sy : S.vart) (tx ty : T.vart)
                       (sρ sρ' : S.poison) (tρ tρ' : T.poison) (sΔ : S.store) (tΔ : T.store)
                       (sH sH' : S.heap) (tH tH' : T.heap),
    ~(List.In (sℓ) sL) ->
    sx = tx ->
    Util.mget δ (sℓ) = Some (tℓ) ->
    poison_eq sρ tρ ->
    (sℓ, sℓ', tℓ, tℓ') = (S.addr n0, S.addr n1, T.addr n2, T.addr n3) ->
    n1 - n0 = n3 - n2 ->
    heap_agree (n1 - n0) sH tH sH' tH' ->
    memstate_eq δ sL (sH, (sy ↦ (sℓ', sρ') ◘ sΔ)) (tH, (ty ↦ (tℓ', tρ') ◘ tΔ)) ->
    memstate_eq δ sL (sH, (sx ↦ (sℓ, sρ) ◘ (sy ↦ (sℓ', sρ') ◘ sΔ)))
                     (tH, (ty ↦ (tℓ, tρ) ◘ (ty ↦ (tℓ', tρ') ◘ tΔ)))
| lastcons_memstate_eq : forall (sℓ : S.loc) (tℓ : T.loc) (n0 n1 : nat) (sx : S.vart) (tx : T.vart)
                       (sρ : S.poison) (tρ : T.poison)
                       (sH : S.heap) (tH : T.heap),
    ~(List.In (sℓ) sL) ->
    sx = tx ->
    Util.mget δ (sℓ) = Some (tℓ) ->
    poison_eq sρ tρ ->
    heap_agree (Util.length sH) sH tH (mapNil _ _) (mapNil _ _) ->
    memstate_eq δ sL (sH, (sx ↦ (sℓ, sρ) ◘ mapNil _ _)) (tH, (tx ↦ (tℓ, tρ) ◘ mapNil _ _))
| cons_ignore_memstate_eq : forall (sℓ : S.loc) (sρ : S.poison) (sH' sH : S.heap) (sΔ : S.store)
                              (tH : T.heap) (tΔ : T.store) (x : S.vart),
    List.In sℓ sL ->
    heap_skip 42 sH' sH ->
    memstate_eq δ sL (sH, sΔ) (tH, tΔ) ->
    memstate_eq δ sL (sH', x ↦ (sℓ, sρ) ◘ sΔ) (tH, tΔ)
.
Inductive lib_eq : S.symbols -> T.symbols -> Prop :=
| empty_commlib_lib_eq : forall (tΞ : T.symbols),
    lib_eq (mapNil _ _) tΞ
| cons_commlib_lib_eq : forall (sfoo sx : S.vart) (tfoo tx : T.vart) (se__bdy : S.expr) (τ : S.Ty)
                          (te__bdy : T.expr) (sΞ : S.symbols) (tΞ1 tΞ2 : T.symbols),
    sfoo = tfoo ->
    comp__symb (sx, τ, se__bdy) = Some(tx, te__bdy) ->
    lib_eq sΞ (tΞ1 ◘ tΞ2) ->
    lib_eq (sfoo ↦ (sx, τ, se__bdy) ◘ sΞ) (tΞ1 ◘ tfoo ↦ (tx, te__bdy) ◘ tΞ2)
.
Inductive kont_eq : S.active_ectx -> T.active_ectx -> Prop :=
| empty_kontstack : kont_eq (List.nil) (List.nil)
| cons_kontstack : forall (sK : S.evalctx) (tK : T.evalctx) (sKs : S.active_ectx) (tKs : T.active_ectx),
    kont_eq sKs tKs ->
    kont_eq (sK :: sKs) (tK :: tKs)
.
Inductive cfstate_eq : (S.symbols * S.active_ectx) -> (T.symbols * T.active_ectx) -> Prop :=
| Ccfstate_eq : forall (sΞ : S.symbols) (sK : S.active_ectx) (tΞ : T.symbols) (tK : T.active_ectx),
    lib_eq sΞ tΞ ->
    kont_eq sK tK ->
    cfstate_eq (sΞ, sK) (tΞ, tK)
.
Inductive state_eq (δ : locmap_st) (sL : list S.loc) : S.state -> T.state -> Prop :=
| Cstate_eq : forall (sF : CSC.Fresh.fresh_state) (sΞ : S.symbols) (sK : S.active_ectx) (sH : S.heap) (sΔ : S.store)
                (tF : CSC.Fresh.fresh_state) (tΞ : T.symbols) (tK : T.active_ectx) (tH : T.heap) (tΔ : T.store),
    cfstate_eq (sΞ, sK) (tΞ, tK) ->
    memstate_eq δ sL (sH, sΔ) (tH, tΔ) ->
    state_eq δ sL (sF, sΞ, sK, sH, sΔ) (tF, tΞ, tK, tH, tΔ)
.

Inductive xlang_value_eq : S.value -> T.value -> Prop :=
| natval_eq : forall (n1 n2 : nat),
    xlang_value_eq (S.Vnat n1) (T.Vnat n2)
.
Inductive xlang_fnoerr_eq : S.fnoerr -> T.fnoerr -> Prop :=
| fnoerr_val_eq : forall (sv : S.value) (tv : T.value),
    xlang_value_eq sv tv ->
    xlang_fnoerr_eq (S.Fval sv) (T.Fval tv)
| fnoerr_var_eq : forall (sx : S.vart) (tx : T.vart),
    (* FIXME: this is way too strict. Lookup identifiers somewhere and grab the location, those should be equal, but not the identifiers*)
    sx = tx ->
    xlang_fnoerr_eq (S.Fvar sx) (T.Fvar tx)
.
(** Crosslanguage Relation between Traces/Actions *)
Inductive event_eq (δ : locmap_st) : option S.event -> option T.event -> Prop :=
| empty_event_eq : event_eq δ None None
| start_event_eq : event_eq δ (Some S.Sstart) (Some T.Sstart)
| end_event_eq : forall (sv : S.value) (tv : T.value),
    xlang_value_eq sv tv ->
    event_eq δ (Some(S.Send sv)) (Some(T.Send tv))
| alloc_event_eq : forall (sℓ : S.loc) (tℓ : T.loc) (sn tn : nat),
    sn = tn ->
    Util.mget δ sℓ = Some(tℓ) ->
    event_eq δ (Some(S.Salloc sℓ sn)) (Some(T.Salloc tℓ tn))
| dealloc_event_eq : forall (sℓ : S.loc) (tℓ : T.loc),
    Util.mget δ sℓ = Some(tℓ) ->
    event_eq δ (Some(S.Sdealloc sℓ)) (Some(T.Sdealloc tℓ))
| get_event_eq : forall (sℓ : S.loc) (tℓ : T.loc) (sn tn : nat),
    sn = tn ->
    Util.mget δ sℓ = Some(tℓ) ->
    event_eq δ (Some(S.Sget sℓ sn)) (Some(T.Sget tℓ tn))
| set_event_eq : forall (sℓ : S.loc) (tℓ : T.loc) (sn tn : nat) (sv : S.value) (tv : T.value),
    sn = tn ->
    xlang_value_eq sv tv ->
    Util.mget δ sℓ = Some(tℓ) ->
    event_eq δ (Some(S.Sset sℓ sn sv)) (Some(T.Sset tℓ tn tv))
| crash_event_eq : event_eq δ (Some S.Scrash) (Some T.Scrash)
| return_event_eq : forall (sv : S.fnoerr) (tv : T.fnoerr),
    xlang_fnoerr_eq sv tv ->
    event_eq δ (Some(S.Sret sv)) (Some(T.Sret tv))
| call_event_eq : forall (sfoo : S.vart) (tfoo : T.vart) (sv : S.fnoerr) (tv : T.fnoerr),
    sfoo = tfoo ->
    xlang_fnoerr_eq sv tv ->
    event_eq δ (Some(S.Scall tfoo sv)) (Some(T.Scall tfoo tv))
.
Inductive trace_eq (δ : locmap_st) (X : list(option S.event)) : list(option S.event) -> list(option T.event) -> Prop :=
| empty_trace_eq : trace_eq δ X List.nil List.nil
| cons_trace_eq : forall (sa : option S.event) (ta : option T.event)
                    (sAs : list(option S.event)) (tAs : list(option T.event)),
    ~(List.In sa X) ->
    event_eq δ sa ta ->
    trace_eq δ X sAs tAs ->
    trace_eq δ X (sa :: sAs) (ta :: tAs)
| ignore_trace_eq : forall (sa : option S.event) (ta : option T.event)
                      (sAs : list(option S.event)) (tAs : list(option T.event)),
    List.In sa X ->
    trace_eq δ X sAs tAs ->
    trace_eq δ X (sa :: sAs) (ta :: tAs)
.

(** Lemmas *)
Lemma injective_comp__e (e : S.expr) (et₁ et₂ : T.expr) :
  comp__e e = et₁ ->
  comp__e e = et₂ ->
  et₁ = et₂
.
Proof.
  now induction e; intros H1 H2; match goal with | [H: _ = et₁ |- et₁ = et₂] => inv H end.
Qed.


(* FIXME: cannot use notation for some reason... maybe 'cause we are across a module? *)
Lemma forward_simulation_pstep (sΩ sΩ' : S.state) (se se' : S.expr) (sa : option S.event) (δ : locmap_st)
                               (sL : list S.loc) (tΩ : T.state) (τ : S.Ty) :
  (S.pstep (Some sΩ, se) sa (Some sΩ', se')) ->
  state_eq δ sL sΩ tΩ ->
  S.rt_check sΩ se τ ->
  exists (δ' : locmap_st) (tΩ' : T.state) (ta : option T.event),
    Util.MSubset δ δ' /\
    (T.pstep (Some tΩ, comp__e(se)) ta (Some tΩ', comp__e(se'))) /\
    (* FIXME: relate actions *) True /\
    state_eq δ sL sΩ' tΩ'
.
Proof.
Admitted.
