Require Import Coq.Logic.FunctionalExtensionality.

(** Emptyset *)
Definition emptyset {A : Type} := fun (_ : A) => False.
Notation "∅" := emptyset.

(** Set operations *)
Definition subsets {A : Type} (set1 set2 : A -> Prop) : Prop :=
  forall (a : A), set1 a -> set2 a
.
Lemma subsets_refl {A : Type} (set : A -> Prop) :
  subsets set set
.
Proof. firstorder. Qed.

Definition set_eq {A : Type} (set1 set2 : A -> Prop) : Prop :=
  subsets set1 set2 /\ subsets set2 set1
.
Lemma set_eq_refl {A : Type} (set : A -> Prop) :
  set_eq set set
.
Proof. unfold set_eq; split; eauto using subsets_refl. Qed.

Axiom set_eq_is_eq : forall {A : Type} (set1 set2 : A -> Prop),
  set_eq set1 set2 -> set1 = set2
.
Lemma set_eq_equiv_eq {A : Type} (set1 set2 : A -> Prop) :
  set_eq set1 set2 <-> set1 = set2
.
Proof.
  split; intros; subst; auto using set_eq_refl, set_eq_is_eq.
Qed.

CoInductive Trace (Event : Type) : Type :=
| STcons : option Event -> Trace Event -> Trace Event
.
Section NoExplicitEvent.
  Variable Event : Type.

  (** (Hyper-)Properties *)
  Definition Property := Trace Event -> Prop.
  Definition Hyperproperty := Property -> Prop.

  (** Renamings of same concept. *)
  Definition Class := Hyperproperty.
  Definition Behavior := Property.

  (** Hyperproperty belonging to a class, i.e., must be a subset *)
  Definition belongs_to (Π : Hyperproperty) (C : Class) :=
    forall (π : Behavior), Π π -> C π
  .
  (** Intersection of Casses *)
  Definition intersect (C1 C2 : Class) : Class :=
    fun (π : Behavior) => C1 π /\ C2 π
  .
  Infix "∩" := (intersect) (at level 81, left associativity).
  Lemma belongs_to_commute (Π : Hyperproperty) (C1 C2 : Class) :
    belongs_to Π (C1 ∩ C2) ->
    belongs_to Π C1 /\ belongs_to Π C2
  .
  Proof.
    intros H; split; intros b H1; now apply H.
  Qed.
  Lemma always_belongs_to (C : Class) :
    exists Π, belongs_to Π C
  .
  Proof.
    (* the empty set is always a subset *)
    exists (fun _ => False); easy.
  Qed.

  (** Standard trace satisfaction. *)
  Definition hsat (behav : Property) (Π : Hyperproperty) := Π behav.
  Definition bsat (b : Behavior) (π : Property) :=
    forall (t : Trace Event), b t -> π t
  .
End NoExplicitEvent.

(** Abstract representation of programming Languages. *)
Record Language := {
  Partials : Type ;
  Contexts : Type ;
  Event : Type ;
  step : Contexts -> Partials -> Trace Event -> Prop ;
}.
(** Program satisfaction *)
Definition behav {L : Language} (C : Contexts L) (p : Partials L) : Behavior (Event L) :=
  fun (t : Trace (Event L)) => step _ C p t
.
Definition psat {L : Language} (C : Contexts L) (p : Partials L) (Π : Hyperproperty (Event L)) :=
  hsat (Event L) (behav C p) Π
.
(** Robust satisfaction *)
Definition rsat {L : Language} (p : Partials L) (Π : Hyperproperty (Event L)) :=
  forall (C : Contexts L), hsat (Event L) (behav C p) Π
.

(** Existential image *)
Definition tau {S T : Language} (rel : Trace (Event S) -> Trace (Event T) -> Prop) (π : Property (Event S)) : Property (Event T) :=
  fun (t : Trace (Event T)) =>
    exists (s : Trace (Event S)), rel s t /\ π s
.
Definition induced_tau {S T : Language} (rel : Trace (Event S) -> Trace (Event T) -> Prop) (Π : Hyperproperty (Event S)) : Hyperproperty (Event T) :=
  fun (πt : Property (Event T)) =>
    forall (πs : Property (Event S)),
    set_eq (tau rel πs) πt ->
    Π πs
.
Notation "'τ'" := tau.
Notation "'τ~'" := induced_tau.
(** Universal image *)
Definition sigma {S T : Language} (rel : Trace (Event S) -> Trace (Event T) -> Prop) (π : Property (Event T)) : Property (Event S) :=
  fun (s : Trace (Event S)) =>
    forall (t : Trace (Event T)), rel s t -> π t
.
Definition induced_sigma {S T : Language} (rel : Trace (Event S) -> Trace (Event T) -> Prop) (Π : Hyperproperty (Event T)) : Hyperproperty (Event S) :=
  fun (πs : Property (Event S)) =>
    forall (πt : Property (Event T)),
      set_eq πs (sigma rel πt) ->
      Π πt
.
Notation "'σ'" := sigma.
Notation "'σ~'" := induced_sigma.
(** Compilers *)
Definition Compiler (S T : Language) := Partials S -> Partials T.

(** Preservation of robust satisfaction. *)
Definition prsat__τ {S T : Language}
    (rel : Trace (Event S) -> Trace (Event T) -> Prop)
    (cc : Compiler S T) (C : Class (Event S)) :=
  forall (Π : Hyperproperty (Event S)),
    belongs_to (Event S) Π C ->
    forall (p : Partials S),
      rsat p Π ->
      rsat (cc p) (τ~ rel Π)
.
Notation "'[presτ|-' cc ':' rel ',' C ']'" := (prsat__τ rel cc C) (at level 11, cc at next level, rel at next level, C at next level).

Definition prsat__σ {S T : Language}
    (rel : Trace (Event S) -> Trace (Event T) -> Prop)
    (cc : Compiler S T) (C : Class (Event T)) :=
  forall (Π : Hyperproperty (Event T)),
    belongs_to (Event T) Π C ->
    forall (p : Partials S),
      rsat p (σ~ rel Π) ->
      rsat (cc p) Π 
.
Notation "'[presσ|-' cc ':' rel ',' C ']'" := (prsat__σ rel cc C) (at level 11, cc at next level, rel at next level, C at next level).

(** Sequential Composition *)
Notation "cc1 '∘' cc2" := (fun t => cc2(cc1 t)) (at level 81, left associativity, cc2 at next level).
Notation "r1 '◘' r2" := (fun a c => exists b, r1 a b /\ r2 b c) (at level 81, left associativity).
Infix "∩" := (intersect _) (at level 81, left associativity).

Notation "a '∈' b" := (hsat _ a b) (at level 89, no associativity, b at next level).

Lemma rsat_trim_inducedτ' {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (π : Property (Event S)) :
  set_eq (tau (rel1 ◘ rel2) π) (tau rel2 (tau rel1 π))
.
Proof.
  split; intros x Hx. 
  - destruct Hx as [s [[i [Hx1 Hx2]] Hs]]. unfold tau in *.
    exists i; split; trivial; exists s; firstorder.
  - destruct Hx as [i [Hi [s [Hs Hx]]]].
    exists s; split; trivial; exists i; firstorder.
Qed.
Lemma rsat_trim_inducedτ'' {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (π : Property (Event S)) :
  set_eq (tau rel2 (tau rel1 π)) (tau (rel1 ◘ rel2) π) 
.
Proof.
  apply set_eq_equiv_eq; symmetry; apply set_eq_equiv_eq; eauto using rsat_trim_inducedτ'.
Qed.
Lemma rsat_trim_inducedτ {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (Π : Hyperproperty (Event S)) :
  τ~ (rel1 ◘ rel2) Π = τ~ rel2 (τ~ rel1 Π)
.
Proof.
  apply set_eq_equiv_eq; split; intros πt Hx. 
  - intros πi Heq%set_eq_equiv_eq πs Heq'%set_eq_equiv_eq; subst.
    eapply Hx; eauto using rsat_trim_inducedτ'.
  - intros πs Heq%set_eq_equiv_eq; subst.
    specialize (Hx (τ rel1 πs)).
    eapply Hx; eauto using rsat_trim_inducedτ''.
    apply set_eq_equiv_eq; reflexivity.
Qed.

Lemma rsat_trim_σ {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (π : Property (Event T)) :
  sigma (rel1 ◘ rel2) π = sigma rel1 (sigma rel2 π)
.
Proof.
  apply set_eq_equiv_eq; split; intros As Hx.
  - intros πi Hi At Ht.
    specialize (Hx At); eauto.
  - intros At [Ai [Ha Hb]].
    specialize (Hx Ai Ha At Hb); eauto.
Qed.
Lemma rsat_trim_σ' {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (π : Property (Event T)) :
  sigma rel1 (sigma rel2 π) = sigma (rel1 ◘ rel2) π 
.
Proof.
  symmetry; auto using rsat_trim_σ.
Qed.
Lemma rsat_trim_inducedσ {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (Π : Hyperproperty (Event T)) :
  σ~ (rel1 ◘ rel2) Π = σ~ rel1 (σ~ rel2 Π)
.
Proof.
  apply set_eq_equiv_eq; split; intros πs Hx. 
  - intros πi Heq%set_eq_equiv_eq πt Heq'%set_eq_equiv_eq; subst.
    eapply Hx; apply set_eq_equiv_eq; eauto using rsat_trim_σ'.
  - intros πt Heq%set_eq_equiv_eq; subst.
    specialize (Hx (σ rel2 πt)).
    eapply Hx; try apply set_eq_equiv_eq; eauto using rsat_trim_σ.
Qed.

Definition wfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event S)) :=
    forall (π : Property (Event S)),
      Π π ->
      (τ~ rel Π) (tau rel π)
.
Notation "'|-wfτ' rel ':' Π" := (wfτ rel Π) (at level 81, rel at next level, Π at next level).

Theorem seqcompoτ {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    (|-wfτ rel1 : C2) ->
    [presτ|- cc1 : rel1, C1] ->
    [presτ|- cc2 : rel2, τ~ rel1 C2] ->
    [presτ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H__wf H1 H2 Π HΠ p Hsat Ct.
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠa HΠb].
  unfold prsat__τ in H2.
  rewrite rsat_trim_inducedτ.
  eapply H2.
  intros bI HΠbI πs Heq%set_eq_equiv_eq; subst.
  specialize (HΠbI πs).
  eapply H__wf; try now eapply HΠb, HΠbI.
  apply set_eq_equiv_eq; reflexivity.
  eapply H1; try exact HΠa.
  exact Hsat.
Qed.
Definition nwfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event S)) :=
    exists (π : Property (Event S)),
      Π π /\ ~((τ~ rel Π) (tau rel π))
.
Notation "'¬|-wfτ' rel ':' Π" := ((nwfτ rel Π)) (at level 81, rel at next level, Π at next level).

Lemma tau_eq {S I : Language} (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (πs πs' : Property (Event S)) :
  τ rel πs = τ rel πs' ->
  πs = πs'
.
Proof.
Admitted.

Theorem empty_compo {S I T : Language} 
  (C : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (H__wf : |-wfτ rel1 : C)
  (H__nwf : ¬|-wfτ rel2 : τ~ rel1 C)
  :
    τ~ (rel1 ◘ rel2) C = ∅
.
Proof.
  apply set_eq_equiv_eq; split; intros πt Ht; (try now cbv in Ht); cbv.
  destruct H__nwf as [πi [Hπi Hn]].
  eapply Hn; clear Hn.
  intros πi' Heq%set_eq_equiv_eq πs Heq'%set_eq_equiv_eq; subst.
  eapply tau_eq in Heq; subst.
  eapply Hπi; now apply set_eq_equiv_eq.
Qed.

Corollary swappable {I : Language} (cc1 cc2 : Compiler I I)
  (C1 C2 : Class (Event I))
  (rel1 : Trace (Event I) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event I) -> Prop) :
    (|-wfτ rel2 : C1) ->
    (|-wfτ rel1 : C2) ->
    [presτ|- cc1 : rel1, τ~ rel2 C1] ->
    [presτ|- cc2 : rel2, C2] ->
    [presτ|- cc1 : rel1, C1] ->
    [presτ|- cc2 : rel2, τ~ rel1 C2] ->
    [presτ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
 /\ [presτ|- (cc2 ∘ cc1) : rel2 ◘ rel1, C2 ∩ C1 ]
.
Proof.
  split; intros.
  - apply seqcompoτ; auto.
  - apply seqcompoτ; auto.
Qed.

Definition wfσ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event I)) :=
    forall (π : Property (Event I)),
      Π π ->
      (σ~ rel Π) (σ rel π)
.
Notation "'|-wfσ' rel ':' Π" := (wfσ rel Π) (at level 81, rel at next level, Π at next level).

Definition wfrel {S I : Language} (rel : Trace (Event S) -> Trace (Event I) -> Prop) := forall As At At',
  rel As At ->
  rel As At' ->
  At = At'
.
Goal forall {S I : Language} (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (πi : Property (Event I)) As Ai,
  wfrel rel ->
  πi Ai ->
  rel As Ai ->
  σ rel πi As
.
Proof.
  intros. intros Ai' Hrel.
  eapply (H _ _ _ H1) in Hrel. now subst.
Qed.
Definition wfrel' {S I : Language} (rel : Trace (Event S) -> Trace (Event I) -> Prop) := forall As As' At,
  rel As At ->
  rel As' At ->
  As = As'
.
Goal forall {S I : Language} (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (πs : Property (Event S)) As Ai,
  wfrel' rel ->
  τ rel πs Ai ->
  rel As Ai ->
  πs As
.
Proof.
  intros. destruct H0 as [As' [Hrel Hs]].
  eapply (H _ _ _ H1) in Hrel. now subst.
Qed.

Theorem seqcompoσ {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event T))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    (|-wfσ rel2 : C1) ->
    [presσ|- cc1 : rel1, σ~ rel2 C1] ->
    [presσ|- cc2 : rel2, C2] ->
    [presσ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H__wf H1 H2 Π HΠ p Hsat Ct.
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠa HΠb].
  unfold prsat__σ in H1, H2.
  rewrite rsat_trim_inducedσ in Hsat.
  eapply H2; try exact HΠb.
  eapply H1; try exact Hsat.

  intros bI HbI πt Heq%set_eq_equiv_eq; subst. 
  eapply HΠa, HbI. now apply set_eq_equiv_eq.
Qed.


(** Case Study *)
Variant SecurityTag : Type :=
| Secure
| v1
| v2
| v4
| v5
.
Variant PreEvent : Type :=
| Eif
| Eget
| Ebarrier
| Erlb
.
Definition event : Type := PreEvent * SecurityTag.

Axiom partials contexts : Type.
Axiom dostep : forall (Event : Type), contexts -> partials -> Trace Event -> Prop.

Definition S : Language := {|
  Partials := partials ;
  Contexts := contexts ;
  Event := event ;
  step := dostep event ;
|}.
Definition T : Language := {|
  Partials := partials ;
  Contexts := contexts ;
  Event := event ;
  step := dostep event ;
|}.
Inductive msrrel (As : Trace (Event S)) : Trace (Event T) -> Prop :=
  | msrrelc : forall b c Bs',
      c <> Secure ->
      c <> v1 ->
      msrrel As Bs' ->
      msrrel As (STcons _ (Some(b,c)) Bs')
.
Inductive πss (variant : SecurityTag) : Trace (Event T) -> Prop :=
  | pissc : forall b c Bs',
      c <> variant ->
      πss variant Bs' ->
      πss variant (STcons _ (Some(b,c)) Bs')
.
Definition powerset (π : Trace (Event T) -> Prop) : (Trace (Event T) -> Prop) -> Prop :=
  fun (π' : Trace (Event T) -> Prop) =>
  forall t, π' t -> π t
.
Goal forall v, |-wfσ msrrel : powerset(πss v).
Proof.
  intros v πt Hπt πt' Heq%set_eq_equiv_eq At HAt; subst. 
  eapply Hπt.
Admitted.
