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
    exists (πs : Property (Event S)), Π πs /\ set_eq πt (tau rel πs)
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
    forall (πt : Property (Event T)), Π πt -> set_eq πs (sigma rel πt)
.
Notation "'σ'" := sigma.
Notation "'σ~'" := induced_sigma.
(** Compilers *)
Definition Compiler (S T : Language) := Partials S -> Partials T.

(** Preservation of robust satisfaction.
    Requires classes to be subset closed *)
Definition prsat__τ {S T : Language}
    (rel : Trace (Event S) -> Trace (Event T) -> Prop)
    (cc : Compiler S T) (C : Class (Event S)) :=
  forall (Π : Hyperproperty (Event S)),
    belongs_to (Event S) Π C ->
    forall (p : Partials S),
      rsat p Π ->
      rsat (cc p) (induced_tau rel Π)
.
Notation "'[pres|-' cc ':' rel ',' C ']'" := (prsat__τ rel cc C) (at level 11, cc at next level, rel at next level, C at next level).

(** Sequential Composition *)
Notation "cc1 '∘' cc2" := (fun t => cc2(cc1 t)) (at level 81, left associativity, cc2 at next level).
Notation "r1 '◘' r2" := (fun a c => exists b, r1 a b /\ r2 b c) (at level 81, left associativity).
Infix "∩" := (intersect _) (at level 81, left associativity).

Notation "a '∈' b" := (hsat _ a b) (at level 89, no associativity, b at next level).

Lemma rsat_trim' {S I T : Language} 
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
Lemma rsat_trim {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (Π : Hyperproperty (Event S)) :
  induced_tau (rel1 ◘ rel2) Π = induced_tau rel2 (induced_tau rel1 Π)
.
Proof.
  apply set_eq_equiv_eq; split; intros πt Hx. 
  - destruct Hx as [πs [Hs Hx]].
    apply set_eq_equiv_eq in Hx.
    exists (tau rel1 πs).
    split; subst; eauto using rsat_trim'.
    exists πs; split; trivial; apply set_eq_equiv_eq; easy.
  - destruct Hx as [πi [[πs [Hs Hi]] Hx]].
    exists πs; split; trivial.
    apply set_eq_equiv_eq in Hi, Hx.
    apply set_eq_equiv_eq; symmetry; apply set_eq_equiv_eq.
    subst; eauto using rsat_trim'.
Qed.

Definition wf {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Class (Event S)) :=
    forall (Π : Hyperproperty (Event S)),
      belongs_to (Event S) Π C ->
      belongs_to (Event I) (induced_tau rel Π) (induced_tau rel C)
.
Notation "'[' '|-wf' rel ':' C ']'" := (wf rel C) (at level 81, rel at next level, C at next level).

Theorem seqcompo {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (H__wf : [ |-wf rel1 : C2 ]) : 
    [pres|- cc1 : rel1, C1] ->
    [pres|- cc2 : rel2, induced_tau rel1 C2] ->
    [pres|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H1 H2 Π HΠ p Hsat Ct.
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠa HΠb].
  unfold prsat__τ in H2.
  rewrite rsat_trim.
  eapply H2; try now eapply H__wf.
  eapply H1; try exact HΠa.
  exact Hsat.
Qed.

Definition wf' {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event S)) :=
    forall (π : Property (Event S)),
      Π π ->
      (induced_tau rel Π) (tau rel π)
.
Definition nwf' {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event S)) :=
    exists (π : Property (Event S)),
      Π π /\
      ~(induced_tau rel Π) (tau rel π)
.

Theorem empty_compo {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (H__wf : wf' rel1 C1)
  (H__nwf : nwf' rel2 (induced_tau rel1 C1))
  :
    induced_tau (rel1 ◘ rel2) (C1 ∩ C2) = ∅
.
Proof.
  apply set_eq_equiv_eq; split; intros πt Ht; try easy; cbv.
  destruct Ht as [πs [Hs Hx]]; apply set_eq_equiv_eq in Hx; subst.
  destruct Hs as [Hs1 Hs2].
  specialize (H__wf πs Hs1).
  destruct H__wf as [πs' [Hs' Hx]]; apply set_eq_equiv_eq in Hx; subst.
  destruct H__nwf as [πi [Hi Hx']]; apply Hx'; clear Hx'.
  exists πi; split; trivial. apply set_eq_equiv_eq; reflexivity.
Qed.
