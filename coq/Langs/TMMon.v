Set Implicit Arguments.
Require Import Strings.String CSC.Langs.Util CSC.Util.

(** The type used for variable names. *)
Definition vart := string.

(** References *)
Inductive loc : Type :=
| addr : nat -> loc
.
Lemma loc_dec (x y : loc) : {x = y} + {x <> y}.
Proof.
  destruct x, y, (PeanoNat.Nat.eq_dec n n0); subst; ((now left) + right); congruence.
Defined.
(** Types of temporal memory safe events. *)
Variant event : Type :=
| Salloc (ℓ : loc) : event
| Sdealloc (ℓ : loc) : event
| Suse (ℓ : loc) : event
| Scrash : event
.
#[local]
Instance event__Instance : TraceEvent event := {}.
Definition ev_to_tracepref := @Langs.Util.ev_to_tracepref event event__Instance.
Coercion ev_to_tracepref : event >-> tracepref.
Definition eventeq (a0 a1 : event) : bool :=
  match a0, a1 with
  | Salloc(addr ℓ0), Salloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Sdealloc(addr ℓ0), Sdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Suse(addr ℓ0), Suse(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Scrash, Scrash => true
  | _, _ => false
  end
.

(** Locations *)
Definition Loc := list loc.
(** Abstract Store *)
Record TMSMonitor := {
  A: Loc ;
  F: Loc
}.
#[local]
Instance tmsmon__Instance : RuntimeExprClass TMSMonitor := {}.

Definition emptytmsmon : TMSMonitor := {|
  A := List.nil ;
  F := List.nil
|}.
#[local]
Notation "∅" := (emptytmsmon) (at level 82).

Definition entails (T1 T2 : TMSMonitor) := forall x, List.In x T1.(F) -> List.In x T2.(F).
Definition contains (ℓ : loc) (T : TMSMonitor) := List.In ℓ T.(A) /\ ~(List.In ℓ T.(F)).
Definition notin (ℓ : loc) (T : TMSMonitor) := ~(List.In ℓ T.(F)) /\ ~(List.In ℓ T.(A)).
Definition extend (ℓ : loc) (T : TMSMonitor) : TMSMonitor := {|
  A := List.cons ℓ T.(A) ;
  F := T.(F)
|}.
Definition without (T : TMSMonitor) (ℓ : loc) : TMSMonitor := {|
  A := List.remove loc_dec ℓ T.(A) ;
  F := List.cons ℓ T.(F)
|}.
#[local]
Notation "T1 '⊆__F' T2" := (entails T1 T2) (at level 82, T2 at next level).
#[local]
Notation "ℓ '∈' T" := (contains ℓ T) (at level 82, T at next level).
#[local]
Notation "ℓ '∉' T" := (notin ℓ T) (at level 82, T at next level).
#[local]
Notation "'{' ℓ '}' '∪' T" := (extend ℓ T) (at level 82, T at next level).
#[local]
Notation "T '∖' '{' ℓ '}'" := (without T ℓ) (at level 82, ℓ at next level).

(** Step Relations *)
Inductive step : CtxStep :=
| TMS_uninteresting : forall (T__TMS : TMSMonitor),
    T__TMS ==[]==> T__TMS
| TMS_use : forall (T__TMS : TMSMonitor) (ℓ : loc),
    ℓ ∈ T__TMS ->
    T__TMS ==[Suse ℓ]==> T__TMS
| TMS_alloc : forall (T__TMS T__TMS' : TMSMonitor) (ℓ : loc),
    T__TMS' = ({ ℓ } ∪ T__TMS) ->
    ℓ ∉ T__TMS ->
    T__TMS ==[Salloc ℓ]==> T__TMS'
| TMS_dealloc : forall (T__TMS T__TMS' : TMSMonitor) (ℓ : loc),
    ℓ ∈ T__TMS ->
    T__TMS' = (T__TMS ∖ { ℓ }) ->
    T__TMS ==[Sdealloc ℓ]==> T__TMS'
.
#[local]
Existing Instance step.
Inductive star_step : MultStep :=
| TMS_refl : forall (T__TMS : TMSMonitor),
    T__TMS ==[]==>* T__TMS
| TMS_trans : forall (T__TMS T__TMS' T__TMS'' : TMSMonitor) (a : event) (As : tracepref),
    T__TMS ==[a]==> T__TMS' ->
    T__TMS' ==[As]==>* T__TMS'' ->
    T__TMS ==[Tcons a As]==>* T__TMS''
| TMS_trans_uninteresting : forall (T__TMS T__TMS' T__TMS'' : TMSMonitor) (As : tracepref),
    T__TMS ==[]==> T__TMS' ->
    T__TMS' ==[As]==>* T__TMS'' ->
    T__TMS ==[As]==>* T__TMS''
.
#[local]
Existing Instance star_step.

(** Definition of Temporal Memory Safety on Traces *)
Definition tmssafe (As : tracepref) :=
  forall ℓ, (before eventeq (Salloc ℓ) (Sdealloc ℓ) As
    /\ ~(before eventeq (Suse ℓ) (Salloc ℓ)) As
    /\ ~(before eventeq (Sdealloc ℓ) (Suse ℓ)) As)
.
(** Definition of Temporal Memory Safety on Traces, using our monitor. *)
Definition TMS (As : tracepref) :=
  exists T__TMS, ∅ ==[As]==>* T__TMS
.

Definition simptmssafe (As : tracepref) :=
  forall ℓ, before eventeq (Salloc ℓ) (Sdealloc ℓ) As.

(* Show the above are equally strong...? *)
Theorem TMS_refines_tmssafe As :
  TMS As -> simptmssafe As.
Proof.
  intros [T__TMS H]; induction H; try easy.
  destruct a as [[ℓ] | [ℓ] | [ℓ] | ].
  - intros [ℓ0] x Ha.
    destruct (PeanoNat.Nat.eq_dec ℓ ℓ0); subst.
    destruct x.
    + cbn in Ha. clear Ha.
Admitted.


Module TMMonNotation.
Notation "T1 '⊆__F' T2" := (entails T1 T2) (at level 82, T2 at next level).
Notation "ℓ '∈' T" := (contains ℓ T) (at level 82, T at next level).
Notation "ℓ '∉' T" := (notin ℓ T) (at level 82, T at next level).
Notation "'{' ℓ '}' '∪' T" := (extend ℓ T) (at level 82, T at next level).
Notation "T '∖' '{' ℓ '}'" := (without T ℓ) (at level 82, ℓ at next level).
End TMMonNotation.
