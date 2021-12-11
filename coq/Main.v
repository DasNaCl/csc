Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat Strings.String Lists.List Lia Program.Equality.

Ltac inv H := (inversion H; subst; clear H).

Section Compositionality.

Axiom Trace : Set.

(* Set of traces *)
Definition Property := Trace -> Prop.

(* Set of sets of traces *)
Definition Hyperproperty := Property -> Prop.

(* Sets of hyperproperties *)
Definition PClass := Hyperproperty -> Prop.


(* Set Theory Stuff *)
Definition el { A } (x : A) (C : A -> Prop) := C x.
Notation "x '∈' A" := (el x A) (at level 50).

Definition subset { A } (C1 C2 : A -> Prop) := forall x, x ∈ C1 -> x ∈ C2.
Notation "A '⊆' B" := (subset A B) (at level 50).
Notation "A '≡' B" := (A ⊆ B /\ B ⊆ A) (at level 50).
Axiom set_ext : forall A, forall (X Y : A -> Prop), X ≡ Y -> X = Y.

Definition intersect { A } (C1 C2 : A -> Prop) := forall x, x ∈ C1 /\ x ∈ C2.

Axiom Intersection : forall A, forall (C1 C2 : A -> Prop), A -> Prop.
Notation "A '∩' B" := (Intersection A B) (at level 50).
Axiom IntroIntersect : forall A, forall (X Y : A -> Prop), forall x, x ∈ X -> x ∈ Y -> x ∈ (X ∩ Y).
Axiom ElimIntersect : forall A, forall (X Y : A -> Prop), forall x, x ∈ (X ∩ Y) -> x ∈ X /\ x ∈ Y.


Definition union { A } (C1 C2 : A -> Prop) := forall x, x ∈ C1 \/ x ∈ C2.

Axiom Union : forall A, forall (C1 C2 : A -> Prop), A -> Prop.
Notation "A '∪' B" := (Union A B) (at level 50).
Axiom IntroUnion : forall A, forall (X Y : A -> Prop), forall x, x ∈ X \/ x ∈ Y -> x ∈ (X ∪ Y).
Axiom ElimUnion : forall A, forall (X Y : A -> Prop), forall x, x ∈ (X ∪ Y) -> x ∈ X \/ x ∈ Y.


Lemma self_intersect { A } (C : A -> Prop) :
  C ∩ C = C.
Proof.
  apply set_ext; split; intros x H.
  - apply ElimIntersect in H; apply H.
  - apply IntroIntersect; trivial.
Qed.

Lemma self_union { A } (C : A -> Prop) :
  C ∪ C = C.
Proof.
  apply set_ext; split; intros x H.
  - apply ElimUnion in H as []; trivial.
  - apply IntroUnion; left; trivial.
Qed.

Record Language :=
{
  Partials : Set;
  whole : Partials -> Prop;
  link : Partials -> Partials -> Partials;
  step : forall (p : Partials), whole p -> Property;
}.

(* Languages *)
Definition Compiler (L0 L1 : Language) := Partials L0 -> Partials L1.

Notation "C '[' P ']'" := (link _ P C) (at level 50).

Definition seqcomp {L0 L1 L2 : Language} (f : Compiler L1 L2) (g : Compiler L0 L1) := fun x => f (g x).
Notation "f '∘' g" := (seqcomp g f) (at level 50).

Section Satisfaction.

Context {K : Language}.

Definition sat (p : Partials K) (π : Property) : Prop := forall (H : whole K p), forall t, step K p H t -> t ∈ π.
Definition rsat (p : Partials K) (π : Property) : Prop := forall (c : Partials K), sat (c[p]) π.

Definition behaviour (p : Partials K) (H : whole K p) : Property := fun b => step K p H b.

Definition hsat (p : Partials K) (Π : Hyperproperty) : Prop := forall (H : whole K p), behaviour p H ∈ Π.
Definition rhsat (p : Partials K) (Π : Hyperproperty) : Prop := forall (c : Partials K), hsat (c[p]) Π.

Definition csat (p : Partials K) (C : PClass) : Prop := forall Π, Π ∈ C -> hsat p Π.
Definition rcsat (p : Partials K) (C : PClass) : Prop := forall Π, Π ∈ C -> rhsat p Π.

End Satisfaction.

Notation "p '|-' C" := (rcsat p C) (at level 50).
Notation "p '|=' Π" := (rhsat p Π) (at level 50).

Lemma weakening_rcsat { K : Language } C1 C2 (p : Partials K) :
  C1 ⊆ C2 -> p |- C2 -> p |- C1.
Proof.
  intros H H0 Π H1; apply H0, H, H1.
Qed.

Section Main.

Variable S I T : Language.

(* Robust Compilation *)
Definition RC { L0 L1 : Language } (γ : Compiler L0 L1) (C : PClass) :=
  forall Π, Π ∈ C -> forall (p : Partials L0), p |= Π -> γ p |= Π.
Notation "'|-' γ ':' C" := (RC γ C) (at level 50, γ at next level).

Lemma seqcomp_compose (γ0 : Compiler S I) (γ1 : Compiler I T) (C0 C1 : PClass) :
  |- γ0 : C0 -> |- γ1 : C1 -> |- (γ0 ∘ γ1) : (C0 ∩ C1).
Proof.
  intros H0 H1 Π H2 p H3.
  apply ElimIntersect in H2 as [H2a H2b].
  apply H1; trivial.
  apply H0; trivial.
Qed.

Corollary swappable (γ0 γ1 : Compiler I I) (C0 C1 : PClass) :
  |- γ0 : C0 -> |- γ1 : C1 -> |- (γ0 ∘ γ1) : (C0 ∩ C1) /\ |- (γ1 ∘ γ0) : (C0 ∩ C1).
Proof.
  intros H0 H1; split.
  all:
  intros Π H2 p H3;
  apply ElimIntersect in H2 as [H2a H2b];
  (apply H1, H0 || apply H0, H1); trivial.
Qed.

Lemma weakening_RC (γ : Compiler S T) (C0 C1 : PClass) :
  C0 ⊆ C1 -> |- γ : C1 -> |- γ : C0.
Proof.
  intros H0 H1 Π H2 p H3.
  apply H1; trivial.
  apply H0; trivial.
Qed.

(* Secure Instrumentations *)
Definition instrumentation { L0 L1 : Language } (γ : Compiler L0 L1) (C : PClass) := forall (p : Partials L0), rcsat (γ p) C.
Definition secure_instrumentation { L0 L1 : Language } (γ : Compiler L0 L1) (C0 C1 : PClass) := |- γ : C0 /\ instrumentation γ C1.
Notation "γ '-' C0 '-≻' C1" := (secure_instrumentation γ C0 C1) (at level 50).

Lemma glue (γ0 : Compiler S I) (γ1 : Compiler I T) (C0 C1 : PClass) :
  |- γ0 : C0 -> γ1 -C0-≻ C1 -> |- (γ0 ∘ γ1) : (C0 ∪ C1).
Proof.
  intros H0 [H1a H1b] Π H2 p H3.
  apply ElimUnion in H2 as [H2a|H2b].
  - eapply seqcomp_compose; eauto; rewrite self_intersect; trivial.
  - apply H1b, H2b.
Qed.

End Main.
End Compositionality.

