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
    exists (πt : Property (Event T)), Π πt /\ set_eq πs (sigma rel πt)
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
Lemma rsat_trim_inducedτ {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (Π : Hyperproperty (Event S)) :
  τ~ (rel1 ◘ rel2) Π = τ~ rel2 (τ~ rel1 Π)
.
Proof.
  apply set_eq_equiv_eq; split; intros πt Hx. 
  - destruct Hx as [πs [Hs Hx]].
    apply set_eq_equiv_eq in Hx.
    exists (tau rel1 πs).
    split; subst; eauto using rsat_trim_inducedτ'.
    exists πs; split; trivial; apply set_eq_equiv_eq; easy.
  - destruct Hx as [πi [[πs [Hs Hi]] Hx]].
    exists πs; split; trivial.
    apply set_eq_equiv_eq in Hi, Hx.
    apply set_eq_equiv_eq; symmetry; apply set_eq_equiv_eq.
    subst; eauto using rsat_trim_inducedτ'.
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
Lemma rsat_trim_inducedσ {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (Π : Hyperproperty (Event T)) :
  σ~ (rel1 ◘ rel2) Π = σ~ rel1 (σ~ rel2 Π)
.
Proof.
  apply set_eq_equiv_eq; split; intros πs [πt [Ht Hx]].
  - apply set_eq_equiv_eq in Hx; subst.
    exists (σ rel2 πt); split; eauto.
    + exists πt; split; eapply set_eq_equiv_eq; eauto.
    + apply set_eq_equiv_eq, rsat_trim_σ.
  - destruct Ht as [πt' [Ht Hy%set_eq_equiv_eq]]; subst.
    apply set_eq_equiv_eq in Hx; subst. 
    exists πt'; split; eauto.
    eapply set_eq_equiv_eq; eauto using rsat_trim_σ.
Qed.

Definition wfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event S)) :=
    forall (π : Property (Event S)),
      Π π ->
      (τ~ rel Π) (tau rel π)
.
Notation "'|-wfτ' rel ':' Π" := (wfτ rel Π) (at level 81, rel at next level, Π at next level).
Definition gwfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Class (Event S)) :=
    forall (Π : Hyperproperty (Event S)),
      belongs_to (Event S) Π C ->
      belongs_to (Event I) (τ~ rel Π) (τ~ rel C)
.
Notation "'|-gwfτ' rel ':' Π" := (gwfτ rel Π) (at level 81, rel at next level, Π at next level).

Lemma wfτ_is_gwfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Hyperproperty (Event S)) :
  (|-wfτ rel : C) ->
  (|-gwfτ rel : C)
.
Proof.
  intros H Π HΠC bI [πs [Hs Hx]]; apply set_eq_equiv_eq in Hx; subst.
  specialize (HΠC πs Hs).
  specialize (H πs HΠC).
  assumption.
Qed.
Lemma gwfτ_is_wfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Hyperproperty (Event S)) :
  (|-gwfτ rel : C) ->
  (|-wfτ rel : C)
.
Proof.
  intros H πs Hπs; exists πs; split; trivial;
  apply set_eq_equiv_eq; reflexivity.
Qed.
Corollary wfτ_equiv_gwfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Hyperproperty (Event S)) :
  (|-gwfτ rel : C) <->
  (|-wfτ rel : C)
.
Proof. split; auto using gwfτ_is_wfτ, wfτ_is_gwfτ. Qed.

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
  intros H__wf%wfτ_equiv_gwfτ H1 H2 Π HΠ p Hsat Ct.
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠa HΠb].
  unfold prsat__τ in H2.
  rewrite rsat_trim_inducedτ.
  eapply H2; try now eapply H__wf.
  eapply H1; try exact HΠa.
  exact Hsat.
Qed.
Definition nwfτ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (Π : Hyperproperty (Event S)) :=
    exists (π : Property (Event S)),
      Π π /\
      ~(τ~ rel Π) (tau rel π)
.
Notation "'¬|-wfτ' rel ':' Π" := (nwfτ rel Π) (at level 81, rel at next level, Π at next level).

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
  apply set_eq_equiv_eq; split; intros πt Ht; try easy; cbv.
  destruct Ht as [πs [Hs Hx]]; apply set_eq_equiv_eq in Hx; subst.
  specialize (H__wf πs Hs).
  destruct H__wf as [πs' [Hs' Hx]]; apply set_eq_equiv_eq in Hx; subst.
  destruct H__nwf as [πi [Hi Hx']]; apply Hx'; clear Hx'.
  exists πi; split; trivial. apply set_eq_equiv_eq; reflexivity.
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
      (σ~ rel Π) (sigma rel π)
.
Notation "'|-wfσ' rel ':' Π" := (wfσ rel Π) (at level 81, rel at next level, Π at next level).
Definition gwfσ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Class (Event I)) :=
    forall (Π : Hyperproperty (Event I)),
      belongs_to (Event I) Π C ->
      belongs_to (Event S) (σ~ rel Π) (σ~ rel C)
.
Notation "'|-gwfσ' rel ':' Π" := (gwfσ rel Π) (at level 81, rel at next level, Π at next level).

Lemma wfσ_is_gwfσ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Hyperproperty (Event I)) :
  (|-wfσ rel : C) ->
  (|-gwfσ rel : C)
.
Proof.
  intros H Π HΠC bI [πs [Hs Hx]]; apply set_eq_equiv_eq in Hx; subst.
  specialize (HΠC πs Hs).
  specialize (H πs HΠC).
  assumption.
Qed.
Lemma gwfσ_is_wfσ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Hyperproperty (Event I)) :
  (|-gwfσ rel : C) ->
  (|-wfσ rel : C)
.
Proof.
  intros H πs Hπs; exists πs; split; trivial;
  apply set_eq_equiv_eq; reflexivity.
Qed.
Corollary wfσ_equiv_gwfσ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Hyperproperty (Event I)) :
  (|-gwfσ rel : C) <->
  (|-wfσ rel : C)
.
Proof. split; auto using gwfσ_is_wfσ, wfσ_is_gwfσ. Qed.

Theorem seqcompoσ {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event T))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    (|-gwfσ rel2 : C1) ->
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
  eapply H1; try now eapply H__wf.
  exact Hsat.
Qed.


(** Preservation of robust satisfaction.
    Requires classes to be subset closed *)
Definition enfsat__τ {S T : Language}
    (rel : Trace (Event S) -> Trace (Event T) -> Prop)
    (cc : Compiler S T) (C : Class (Event S)) :=
  forall (Π : Hyperproperty (Event S)),
    belongs_to (Event S) Π C ->
    forall (p : Partials S),
      rsat (cc p) (induced_tau rel Π)
.
Notation "'[enf|-' cc ':' rel ',' C ']'" := (enfsat__τ rel cc C) (at level 11, cc at next level, rel at next level, C at next level).

(* beware of empty compo *)
Theorem enfcompo {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    [enf|- cc2 : rel2, induced_tau rel1 C2] ->
    [presτ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H1 Π HΠ p Hsat Ct.
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠa HΠb].
  rewrite rsat_trim_inducedτ.
  apply H1.
  intros bI H. destruct H as [πs [Ha Hb]].
  specialize (HΠ πs Ha).
  exists πs; split; trivial; apply HΠ.
Qed.
