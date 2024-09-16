Require Import Coq.Logic.FunctionalExtensionality PeanoNat List.

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
| STnil : Trace Event
| STcons : option Event -> Trace Event -> Trace Event
.
Fixpoint get_finite_prefix { Event : Type} (n : nat) (tr : Trace Event) : list (option Event) :=
  match n, tr with
  | 0, _ => nil
  | S n, STnil _ => nil
  | S n, STcons _ a tr => cons a (get_finite_prefix n tr)
  end
.
Fixpoint index_of {A : Type} (a_dec : forall (a a': A), {a = a'} + {a <> a'}) 
  (a : A) (As : list A) : option nat :=
  match As with
  | nil => None
  | cons a' As => 
    if a_dec a a' then
      Some (List.length As)
    else
      match index_of a_dec a As with
      | None => None
      | Some x => Some(S x)
      end
  end
.
Lemma option_dec {A : Type} (a_dec : forall (a a': A), {a = a'} + {a <> a'}) :
  forall (o o' : option A), {o = o'} + {o <> o'} 
.
Proof.
  destruct o as [a|],o' as [a'|]; (try destruct (a_dec a a'));
  subst; (left; reflexivity) + (right; congruence).
Qed.
Section NoExplicitEvent.
  Variable Event : Type.

  (** (Hyper-)Properties *)
  Definition Property := Trace Event -> Prop.
  Definition Hyperproperty := Property -> Prop.

  (** Renamings of same concept. *)
  Definition Class := Hyperproperty -> Prop.
  Definition Behavior := Property.

  (** Hyperproperty belonging to a class *)
  Definition belongs_to (Π : Hyperproperty) (C : Class) :=
    C Π
  .
  (** Intersection of Casses *)
  Definition intersect (C1 C2 : Class) : Class :=
    fun π => C1 π /\ C2 π
  .
  Infix "∩" := (intersect) (at level 81, left associativity).
  Lemma belongs_to_commute (Π : Hyperproperty) (C1 C2 : Class) :
    belongs_to Π (C1 ∩ C2) ->
    belongs_to Π C1 /\ belongs_to Π C2
  .
  Proof.
    firstorder.
  Qed.

  (** Standard trace satisfaction. *)
  Definition hsat (behav : Property) (Π : Hyperproperty) := Π behav.
  Definition bsat (b : Behavior) (π : Property) :=
    forall (t : Trace Event), b t -> π t
  .
End NoExplicitEvent.

Section Composition.
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
Definition psat {L : Language} (C : Contexts L) (p : Partials L) (Π : Property (Event L)) :=
  bsat (Event L) (behav C p) Π
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
Definition class_induced_tau {S T : Language} (rel : Trace (Event S) -> Trace (Event T) -> Prop) (C : Class (Event S)) : Class (Event T) :=
  fun (Πt : Hyperproperty (Event T)) =>
    forall (Πs : Hyperproperty (Event S)),
      set_eq (induced_tau rel Πs) Πt ->
      C Πs
.
Notation "'τ'" := tau.
Notation "'τ~'" := induced_tau.
Notation "'τ~~'" := class_induced_tau.
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
Definition class_induced_sigma {S T : Language} (rel : Trace (Event S) -> Trace (Event T) -> Prop) (C : Class (Event T)) : Class (Event S) :=
  fun (Πs : Hyperproperty (Event S)) =>
    forall (Πt : Hyperproperty (Event T)),
      set_eq Πs (induced_sigma rel Πt) ->
      C Πt
.
Notation "'σ'" := sigma.
Notation "'σ~'" := induced_sigma.
Notation "'σ~~'" := class_induced_sigma.
(** Compilers *)
Definition Compiler (S T : Language) := Partials S -> Partials T.

(** Preservation of robust satisfaction. *)
Definition prsat__τ {S T : Language}
    (rel : Trace (Event S) -> Trace (Event T) -> Prop)
    (cc : Compiler S T) (C : Class (Event S)) :=
  forall (Π : Hyperproperty (Event S)),
    C Π ->
    forall (p : Partials S),
      rsat p Π ->
      rsat (cc p) (τ~ rel Π)
.
Notation "'[presτ|-' cc ':' rel ',' C ']'" := (prsat__τ rel cc C) (at level 11, cc at next level, rel at next level, C at next level).

Definition prsat__σ {S T : Language}
    (rel : Trace (Event S) -> Trace (Event T) -> Prop)
    (cc : Compiler S T) (C : Class (Event T)) :=
  forall (Π : Hyperproperty (Event T)),
    C Π ->
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

Lemma rsat_trim_τ {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (π : Property (Event S)) :
  (tau (rel1 ◘ rel2) π) = (tau rel2 (tau rel1 π))
.
Proof.
  apply set_eq_equiv_eq.
  split; intros x Hx. 
  - destruct Hx as [s [[i [Hx1 Hx2]] Hs]]. unfold tau in *.
    exists i; split; trivial; exists s; firstorder.
  - destruct Hx as [i [Hi [s [Hs Hx]]]].
    exists s; split; trivial; exists i; firstorder.
Qed.
Lemma rsat_trim_τ' {S I T : Language} 
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop)
  (π : Property (Event S)) :
  set_eq (tau rel2 (tau rel1 π)) (tau (rel1 ◘ rel2) π) 
.
Proof.
  apply set_eq_equiv_eq; symmetry; eauto using rsat_trim_τ.
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
    eapply Hx, set_eq_equiv_eq; eauto using rsat_trim_τ.
  - intros πs Heq%set_eq_equiv_eq; subst.
    specialize (Hx (τ rel1 πs)).
    eapply Hx, set_eq_equiv_eq; eauto using rsat_trim_τ'.
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
   (C : Class (Event S)) :=
    forall (Π : Hyperproperty (Event S)),
      C Π ->
      (τ~~ rel C) (τ~ rel Π)
.
Notation "'|-wfτ' rel ':' C" := (wfτ rel C) (at level 81, rel at next level, C at next level).
Theorem seqcompoτ {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    |-wfτ rel1 : C2 ->
    [presτ|- cc1 : rel1, C1] ->
    [presτ|- cc2 : rel2, τ~~ rel1 C2] ->
    [presτ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H__wf H1 H2 Π HΠ p Hsat Ct.
  destruct HΠ as [HΠa HΠb].
  unfold prsat__τ in H2.
  rewrite rsat_trim_inducedτ.
  eapply H2.
  eapply H__wf; exact HΠb.
  eapply H1; try exact HΠa.
  exact Hsat.
Qed.

Corollary swappableτ {I : Language} (cc1 cc2 : Compiler I I)
  (C1 C2 : Class (Event I))
  (rel1 : Trace (Event I) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event I) -> Prop) :
    (|-wfτ rel2 : C1) ->
    (|-wfτ rel1 : C2) ->
    [presτ|- cc1 : rel1, τ~~ rel2 C1] ->
    [presτ|- cc2 : rel2, C2] ->
    [presτ|- cc1 : rel1, C1] ->
    [presτ|- cc2 : rel2, τ~~ rel1 C2] ->
    [presτ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
 /\ [presτ|- (cc2 ∘ cc1) : rel2 ◘ rel1, C2 ∩ C1 ]
.
Proof.
  split; intros.
  - apply seqcompoτ; auto.
  - apply seqcompoτ; auto.
Qed.

Corollary better_swappableτ {I : Language} (cc1 cc2 : Compiler I I)
  (C1 C2 : Class (Event I))
  (rel1 : Trace (Event I) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event I) -> Prop) :
    (|-wfτ rel2 : C1) ->
    (|-wfτ rel1 : C2) ->
    (τ~~ rel2 C1 = C1) ->
    (τ~~ rel1 C2 = C2) ->
    [presτ|- cc1 : rel1, C1] ->
    [presτ|- cc2 : rel2, C2] ->
    [presτ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
 /\ [presτ|- (cc2 ∘ cc1) : rel2 ◘ rel1, C2 ∩ C1 ]
.
Proof.
  intros Hwf1 Hwf2 H1 H2 ? ?; split; subst.
  - apply seqcompoτ; auto; now rewrite H2. 
  - apply seqcompoτ; auto; now rewrite H1.
Qed.

Definition wfσ {S I : Language}
  (rel : Trace (Event S) -> Trace (Event I) -> Prop)
  (C : Class (Event I)) :=
    forall (Π : Hyperproperty (Event I)),
      C Π ->
      (σ~~ rel C) (σ~ rel Π)
.
Notation "'|-wfσ' rel ':' Π" := (wfσ rel Π) (at level 81, rel at next level, Π at next level).

Theorem seqcompoσ {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event T))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    (|-wfσ rel2 : C1) ->
    [presσ|- cc1 : rel1, σ~~ rel2 C1] ->
    [presσ|- cc2 : rel2, C2] ->
    [presσ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H__wf H1 H2 Π HΠ p Hsat Ct.
  destruct HΠ as [HΠa HΠb].
  unfold prsat__σ in H2.
  eapply H2; trivial.
  eapply H1.
  eapply H__wf; assumption.
  now rewrite <- rsat_trim_inducedσ.
Qed.

Corollary swappableσ {I : Language} (cc1 cc2 : Compiler I I)
  (C1 C2 : Class (Event I))
  (rel1 : Trace (Event I) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event I) -> Prop) :
    (|-wfσ rel2 : C1) ->
    (|-wfσ rel1 : C2) ->
    [presσ|- cc1 : rel1, σ~~ rel2 C1] ->
    [presσ|- cc2 : rel2, C2] ->
    [presσ|- cc1 : rel1, C1] ->
    [presσ|- cc2 : rel2, σ~~ rel1 C2] ->
    [presσ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
 /\ [presσ|- (cc2 ∘ cc1) : rel2 ◘ rel1, C2 ∩ C1 ]
.
Proof.
  split; intros.
  - apply seqcompoσ; auto.
  - apply seqcompoσ; auto.
Qed.

Corollary better_swappableσ {I : Language} (cc1 cc2 : Compiler I I)
  (C1 C2 : Class (Event I))
  (rel1 : Trace (Event I) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event I) -> Prop) :
    (|-wfσ rel2 : C1) ->
    (|-wfσ rel1 : C2) ->
    (σ~~ rel2 C1 = C1) ->
    (σ~~ rel1 C2 = C2) ->
    [presσ|- cc1 : rel1, C1] ->
    [presσ|- cc2 : rel2, C2] ->
    [presσ|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
 /\ [presσ|- (cc2 ∘ cc1) : rel2 ◘ rel1, C2 ∩ C1 ]
.
Proof.
  intros Hwf1 Hwf2 H1 H2 ? ?; split; subst.
  - apply seqcompoσ; auto; now rewrite H1. 
  - apply seqcompoσ; auto; now rewrite H2.
Qed.
End Composition.

Section TraceRelations.

Axiom LTMS LSMS LMS LSCCT LSPEC Specification : Type.
Axiom PartialsGenerator ContextsGenerator : Type -> Type.
Axiom loc symbol : Type.
Axiom loc_dec : forall (l l' : loc), { l = l' } + { l <> l' }.
Axiom symbol_dec : forall (f g : symbol), { f = g } + { f <> g }.

Inductive Communication : Type :=
| CtxToComp
| CompToCtx
| Internal
.
Lemma Communication_dec (c c' : Communication) : { c = c' } + { c <> c' }.
Proof. destruct c,c'; try now (left + right). Qed.
Inductive SecurityTagCCT : Type :=
| CCTLeak
| CCTNoLeak
.
Lemma SecurityTagCCT_dec (q q' : SecurityTagCCT) : { q = q' } + { q <> q' }.
Proof. destruct q,q'; try now (left + right). Qed.
Inductive SecurityTagSPEC : Type :=
| SPECLeak (version : nat) 
| SPECNoLeak
.
Lemma SecurityTagSPEC_dec (q q' : SecurityTagSPEC) : { q = q' } + { q <> q' }.
Proof.
  destruct q as [v|],q' as [v'|]; (try now (left + right));
  destruct (Nat.eq_dec v v'); subst; (now left + right; congruence).
Qed.

(** ** Language-Specific Events *)
Inductive LTMSEv : Type :=
| LTMSEvStart 
| LTMSEvEnd
| LTMSEvCall : Communication -> symbol -> LTMSEv
| LTMSEvRet : Communication -> LTMSEv
| LTMSEvAlloc : loc -> nat -> LTMSEv
| LTMSEvDealloc : loc -> LTMSEv
| LTMSEvGet : loc -> nat -> LTMSEv
| LTMSEvSet : loc -> nat -> nat -> LTMSEv
.
Lemma LTMSEv_dec (e e' : LTMSEv) : { e = e' } + { e <> e' }.
Proof.
  destruct e as [| |q f|q|l n|l|l n|l n m],e' as [| |q' f'|q'|l' n'|l'|l' n'|l' n' m'];
  (try now (left + right)).
  1,2: destruct (Communication_dec q q'); subst; try (now left + (right; congruence)).
  destruct (symbol_dec f f'); subst; now left + (right; congruence).
  all: destruct (loc_dec l l'); subst; try (now left + (right; congruence)).
  all: destruct (Nat.eq_dec n n'); subst; try (now left + (right; congruence)).
  destruct (Nat.eq_dec m m'); subst; try (now left + (right; congruence)).
Qed.
Inductive LSMSEv : Type :=
| LSMSEvStart 
| LSMSEvEnd
| LSMSEvCall : Communication -> symbol -> LSMSEv
| LSMSEvRet : Communication -> LSMSEv
| LSMSEvAlloc : loc -> nat -> LSMSEv
| LSMSEvDealloc : loc -> LSMSEv
| LSMSEvGet : loc -> nat -> LSMSEv
| LSMSEvSet : loc -> nat -> nat -> LSMSEv
.
Lemma LSMSEv_dec (e e' : LTMSEv) : { e = e' } + { e <> e' }.
Proof.
  destruct e as [| |q f|q|l n|l|l n|l n m],e' as [| |q' f'|q'|l' n'|l'|l' n'|l' n' m'];
  (try now (left + right)).
  1,2: destruct (Communication_dec q q'); subst; try (now left + (right; congruence)).
  destruct (symbol_dec f f'); subst; now left + (right; congruence).
  all: destruct (loc_dec l l'); subst; try (now left + (right; congruence)).
  all: destruct (Nat.eq_dec n n'); subst; try (now left + (right; congruence)).
  destruct (Nat.eq_dec m m'); subst; try (now left + (right; congruence)).
Qed.
Inductive LMSEv : Type :=
| LMSEvStart 
| LMSEvEnd
| LMSEvCall : Communication -> symbol -> LMSEv
| LMSEvRet : Communication -> LMSEv
| LMSEvAlloc : loc -> nat -> LMSEv
| LMSEvDealloc : loc -> LMSEv
| LMSEvGet : loc -> nat -> LMSEv
| LMSEvSet : loc -> nat -> nat -> LMSEv
.
Inductive LSCCTEv : Type :=
| LSCCTEvStart 
| LSCCTEvEnd
| LSCCTEvCall : Communication -> symbol -> LSCCTEv
| LSCCTEvRet : Communication -> LSCCTEv
| LSCCTEvAlloc : loc -> nat -> LSCCTEv
| LSCCTEvDealloc : loc -> LSCCTEv
| LSCCTEvGet : loc -> nat -> LSCCTEv
| LSCCTEvSet : loc -> nat -> nat -> LSCCTEv
.
Inductive LSPECEv : Type :=
| LSPECEvStart 
| LSPECEvEnd
| LSPECEvCall : Communication -> symbol -> LSPECEv
| LSPECEvRet : Communication -> LSPECEv
| LSPECEvAlloc : loc -> nat -> LSPECEv
| LSPECEvDealloc : loc -> LSPECEv
| LSPECEvGet : loc -> nat -> LSPECEv
| LSPECEvSet : loc -> nat -> nat -> LSPECEv
.
(** ** Monitor Trace Models *)
Inductive TMSMonEv : Type :=
| TMSMonAlloc : loc -> TMSMonEv
| TMSMonDealloc : loc -> TMSMonEv
| TMSMonUse : loc -> TMSMonEv
.
Lemma TMSMonEv_dec (e e' : TMSMonEv) : { e = e' } + { e <> e' }.
Proof.
  destruct e as [l|l|l],e' as [l'|l'|l']; destruct (loc_dec l l'); subst;
  (left; reflexivity) + (right; congruence).
Qed.
Inductive SMSMonEv : Type :=
| SMSMonAlloc : loc -> nat -> SMSMonEv
| SMSMonUse : loc -> nat -> SMSMonEv
.
Lemma SMSMonEv_dec (e e' : SMSMonEv) : { e = e' } + { e <> e' }.
Proof.
  destruct e as [l n|l n],e' as [l' n'|l' n']; destruct (loc_dec l l'); subst;
  destruct (Nat.eq_dec n n'); subst; (left; reflexivity) + (right; congruence).
Qed.
Definition MSMonEv : Type := (option TMSMonEv) * (option SMSMonEv).
Lemma MSMonEv_dec (e e' : MSMonEv) : { e = e' } + { e <> e' }.
Proof.
  destruct e as [[eTMS|] [eSMS|]], e' as [[eTMS'|] [eSMS'|]];
  (try destruct (TMSMonEv_dec eTMS eTMS')); (try destruct (SMSMonEv_dec eSMS eSMS'));
  subst; (left; reflexivity) + (right; congruence).
Qed.
Inductive SCCTMonEv : Type :=
| SCCTMonAny : SecurityTagCCT -> SCCTMonEv
.
Inductive SPECMonEv : Type :=
| SPECMonAny : SecurityTagSPEC -> SPECMonEv 
.
(** ** Projections to monitor traces *)
Inductive LTMSEvtoTMSMonEv : option LTMSEv -> option TMSMonEv -> Prop :=
  | LTMSEvtoTMSMonEv_Alloc : forall l n, LTMSEvtoTMSMonEv (Some (LTMSEvAlloc l n)) (Some (TMSMonAlloc l))
  | LTMSEvtoTMSMonEv_Dealloc : forall l, LTMSEvtoTMSMonEv (Some (LTMSEvDealloc l)) (Some (TMSMonDealloc l))
  | LTMSEvtoTMSMonEv_Get : forall l n, LTMSEvtoTMSMonEv (Some (LTMSEvGet l n)) (Some (TMSMonUse l))
  | LTMSEvtoTMSMonEv_Set : forall l n m, LTMSEvtoTMSMonEv (Some (LTMSEvSet l n m)) (Some (TMSMonUse l))
  (*nonsense*)
  | LTMSEvToTMSMonEv_Start : LTMSEvtoTMSMonEv (Some LTMSEvStart) None
  | LTMSEvToTMSMonEv_End : LTMSEvtoTMSMonEv (Some LTMSEvEnd) None
  | LTMSEvToTMSMonEv_Call : forall c f, LTMSEvtoTMSMonEv (Some (LTMSEvCall c f)) None
  | LTMSEvToTMSMonEv_Ret : forall c, LTMSEvtoTMSMonEv (Some (LTMSEvRet c)) None
  | LTMSEvToTMSMonEv_None : LTMSEvtoTMSMonEv None None
.
Inductive LSMSEvtoTMSMonEv : option LSMSEv -> option TMSMonEv -> Prop :=
  | LSMSEvtoTMSMonEv_Alloc : forall l n, LSMSEvtoTMSMonEv (Some (LSMSEvAlloc l n)) (Some (TMSMonAlloc l))
  | LSMSEvtoTMSMonEv_Dealloc : forall l, LSMSEvtoTMSMonEv (Some (LSMSEvDealloc l)) (Some (TMSMonDealloc l))
  | LSMSEvtoTMSMonEv_Get : forall l n, LSMSEvtoTMSMonEv (Some (LSMSEvGet l n)) (Some (TMSMonUse l))
  | LSMSEvtoTMSMonEv_Set : forall l n m, LSMSEvtoTMSMonEv (Some (LSMSEvSet l n m)) (Some (TMSMonUse l))
  (*nonsense*)
  | LSMSEvToTMSMonEv_Start : LSMSEvtoTMSMonEv (Some LSMSEvStart) None
  | LSMSEvToTMSMonEv_End : LSMSEvtoTMSMonEv (Some LSMSEvEnd) None
  | LSMSEvToTMSMonEv_Call : forall c f, LSMSEvtoTMSMonEv (Some (LSMSEvCall c f)) None
  | LSMSEvToTMSMonEv_Ret : forall c, LSMSEvtoTMSMonEv (Some (LSMSEvRet c)) None
  | LSMSEvToTMSMonEv_None : LSMSEvtoTMSMonEv None None
.
Inductive LSMSEvtoSMSMonEv : option LSMSEv -> option SMSMonEv -> Prop :=
  | LSMSEvtoSMSMonEv_Alloc : forall l n, LSMSEvtoSMSMonEv (Some (LSMSEvAlloc l n)) (Some (SMSMonAlloc l n))
  | LSMSEvtoSMSMonEv_Get : forall l n, LSMSEvtoSMSMonEv (Some (LSMSEvGet l n)) (Some (SMSMonUse l n))
  | LSMSEvtoSMSMonEv_Set : forall l n m, LSMSEvtoSMSMonEv (Some (LSMSEvSet l n m)) (Some (SMSMonUse l n))
  (*nonsense*)
  | LSMSEvtoSMSMonEv_Dealloc : forall l, LSMSEvtoSMSMonEv (Some (LSMSEvDealloc l)) None 
  | LSMSEvToSMSMonEv_Start : LSMSEvtoSMSMonEv (Some LSMSEvStart) None
  | LSMSEvToSMSMonEv_End : LSMSEvtoSMSMonEv (Some LSMSEvEnd) None
  | LSMSEvToSMSMonEv_Call : forall c f, LSMSEvtoSMSMonEv (Some (LSMSEvCall c f)) None
  | LSMSEvToSMSMonEv_Ret : forall c, LSMSEvtoSMSMonEv (Some (LSMSEvRet c)) None
  | LSMSEvToSMSMonEv_None : LSMSEvtoSMSMonEv None None
.
Inductive LMSEvtoMSMonEv : option LMSEv -> option MSMonEv -> Prop :=
  | LMSEvtoMSMonEv_Alloc : forall l n, LMSEvtoMSMonEv (Some (LMSEvAlloc l n)) (Some (Some(TMSMonAlloc l),Some(SMSMonAlloc l n)))
  | LMSEvtoMSMonEv_Dealloc : forall l, LMSEvtoMSMonEv (Some (LMSEvDealloc l)) (Some (Some(TMSMonDealloc l),None)) 
  | LMSEvtoMSMonEv_Get : forall l n, LMSEvtoMSMonEv (Some (LMSEvGet l n)) (Some (Some(TMSMonUse l),Some(SMSMonUse l n)))
  | LMSEvtoMSMonEv_Set : forall l n m, LMSEvtoMSMonEv (Some (LMSEvSet l n m)) (Some (Some(TMSMonUse l),Some(SMSMonUse l n)))
  (*nonsense*)
  | LMSEvToMSMonEv_Start : LMSEvtoMSMonEv (Some LMSEvStart) None
  | LMSEvToMSMonEv_End : LMSEvtoMSMonEv (Some LMSEvEnd) None
  | LMSEvToMSMonEv_Call : forall c f, LMSEvtoMSMonEv (Some (LMSEvCall c f)) None
  | LMSEvToMSMonEv_Ret : forall c, LMSEvtoMSMonEv (Some (LMSEvRet c)) None
  | LMSEvToMSMonEv_None : LMSEvtoMSMonEv None None
.

(** Compilation xlang *)
Inductive LTMSEvtoLSMSEv : option LTMSEv -> option LSMSEv -> Prop :=
  | LTMSEvtoLSMSEv_Alloc : forall l n, LTMSEvtoLSMSEv (Some (LTMSEvAlloc l n)) (Some (LSMSEvAlloc l n))
  | LTMSEvtoLSMSEv_Dealloc : forall l, LTMSEvtoLSMSEv (Some (LTMSEvDealloc l)) (Some (LSMSEvDealloc l))
  | LTMSEvtoLSMSEv_Get : forall l n, LTMSEvtoLSMSEv (Some (LTMSEvGet l n)) (Some (LSMSEvGet l n))
  | LTMSEvtoLSMSEv_Set : forall l n m, LTMSEvtoLSMSEv (Some (LTMSEvSet l n m)) (Some (LSMSEvSet l n m))
  | LTMSEvToLSMSEv_Start : LTMSEvtoLSMSEv (Some LTMSEvStart) (Some LSMSEvStart)
  | LTMSEvToLSMSEv_End : LTMSEvtoLSMSEv (Some LTMSEvEnd) (Some LSMSEvEnd)
  | LTMSEvToLSMSEv_Call : forall c f, LTMSEvtoLSMSEv (Some (LTMSEvCall c f)) (Some (LSMSEvCall c f))
  | LTMSEvToLSMSEv_Ret : forall c, LTMSEvtoLSMSEv (Some (LTMSEvRet c)) (Some (LSMSEvRet c))
  | LTMSEvToLSMSEv_None : LTMSEvtoLSMSEv None None
.

Arguments STnil {_}.
Arguments STcons {_} _ _.
Inductive xtrace_rel {E1 E2 : Type} 
    (E1E2rel : option E1 -> option E2 -> Prop) : Trace E1 -> Trace E2 -> Prop :=
  | xtrace_rel_empty : xtrace_rel E1E2rel STnil STnil
  | xtrace_rel_consL : forall (a : E1) (As : Trace E1) (Bs : Trace E2),
      E1E2rel (Some a) None ->
      xtrace_rel E1E2rel As Bs ->
      xtrace_rel E1E2rel (STcons (Some a) As) Bs
  | xtrace_rel_consR : forall (As : Trace E1) (b : E2) (Bs : Trace E2),
      E1E2rel None (Some b) ->
      xtrace_rel E1E2rel As Bs ->
      xtrace_rel E1E2rel As (STcons (Some b) Bs)
  | xtrace_rel_cons : forall (a : E1) (As : Trace E1) (b : E2) (Bs : Trace E2),
      E1E2rel (Some a) (Some b) ->
      xtrace_rel E1E2rel As Bs ->
      xtrace_rel E1E2rel (STcons (Some a) As) (STcons (Some b) Bs)
.


(* Step relations *)
Axiom LTMSstep : ContextsGenerator LTMS -> PartialsGenerator LTMS -> Trace LTMSEv -> Prop.
Axiom LSMSstep : ContextsGenerator LSMS -> PartialsGenerator LSMS -> Trace LSMSEv -> Prop.
Axiom LMSstep : ContextsGenerator LMS -> PartialsGenerator LMS -> Trace LMSEv -> Prop.
Axiom LSCCTstep : ContextsGenerator LSCCT -> PartialsGenerator LSCCT -> Trace LSCCTEv -> Prop.
Axiom LSPECstep : ContextsGenerator LSPEC -> PartialsGenerator LSPEC -> Trace LSPECEv -> Prop.

Axiom TMSMonstep : ContextsGenerator TMSMonEv -> PartialsGenerator TMSMonEv -> Trace TMSMonEv -> Prop.
Axiom SMSMonstep : ContextsGenerator SMSMonEv -> PartialsGenerator SMSMonEv -> Trace SMSMonEv -> Prop.
Axiom MSMonstep : ContextsGenerator MSMonEv -> PartialsGenerator MSMonEv -> Trace MSMonEv -> Prop.
Axiom SCCTMonstep : ContextsGenerator SCCTMonEv -> PartialsGenerator SCCTMonEv -> Trace SCCTMonEv -> Prop.
Axiom SPECMonstep : ContextsGenerator SPECMonEv -> PartialsGenerator SPECMonEv -> Trace SPECMonEv -> Prop.

(** Concrete language definitions *)
Definition LTMSLanguage : Language := {|
  Partials := PartialsGenerator LTMS ;
  Contexts := ContextsGenerator LTMS ;
  Event := LTMSEv ;
  step := LTMSstep ;
|}.
Definition LSMSLanguage : Language := {|
  Partials := PartialsGenerator LSMS ;
  Contexts := ContextsGenerator LSMS ;
  Event := LSMSEv ;
  step := LSMSstep ;
|}.
Definition LMSLanguage : Language := {|
  Partials := PartialsGenerator LMS ;
  Contexts := ContextsGenerator LMS ;
  Event := LMSEv ;
  step := LMSstep ;
|}.
Definition TMSMonLanguage : Language := {|
  Partials := PartialsGenerator TMSMonEv ;
  Contexts := ContextsGenerator TMSMonEv ;
  Event := TMSMonEv ;
  step := TMSMonstep ;
|}.
Definition SMSMonLanguage : Language := {|
  Partials := PartialsGenerator SMSMonEv ;
  Contexts := ContextsGenerator SMSMonEv ;
  Event := SMSMonEv ;
  step := SMSMonstep ;
|}.
Definition MSMonLanguage : Language := {|
  Partials := PartialsGenerator MSMonEv ;
  Contexts := ContextsGenerator MSMonEv ;
  Event := MSMonEv ;
  step := MSMonstep ;
|}.


Definition tms : Property (TMSMonEv).
Proof.
  Require Import List.
  intros tr; refine (forall (n:nat) As, As = get_finite_prefix n tr -> _ /\ _ /\ _ /\ _).
  - (* Alloc before Dealloc *)
    refine (forall m l, index_of (option_dec TMSMonEv_dec) (Some(TMSMonAlloc l)) As = Some m -> _).
    refine (forall m', index_of (option_dec TMSMonEv_dec) (Some(TMSMonDealloc l)) As = Some m' -> _).
    exact (m < m').
  - (* Use before Dealloc *)
    refine (forall m l, index_of (option_dec TMSMonEv_dec) (Some(TMSMonUse l)) As = Some m -> _).
    refine (forall m', index_of (option_dec TMSMonEv_dec) (Some(TMSMonDealloc l)) As = Some m' -> _).
    exact (m < m').
  - (* at most one Dealloc *)
    exact True.
  - (* at most one Alloc *)
    exact True.
Defined.

Definition xtrace_rel_properties {E1 E2 : Type} 
    (E1E2rel : option E1 -> option E2 -> Prop) : Property E1 -> Property E2 -> Prop :=
  fun π1 π2 => forall tr1 tr2, π1 tr1 -> π2 tr2 -> xtrace_rel E1E2rel tr1 tr2
.

Check (@sigma LSMSLanguage TMSMonLanguage (xtrace_rel LSMSEvtoTMSMonEv) tms).

(** Theorem VII.1 *)
Theorem properties_relation_correctness_tms :
  let redπ := (@sigma LSMSLanguage TMSMonLanguage (xtrace_rel LSMSEvtoTMSMonEv) tms) in
  let blueπ := (@sigma LTMSLanguage LSMSLanguage (xtrace_rel LTMSEvtoLSMSEv) redπ) in
  xtrace_rel_properties LSMSEvtoTMSMonEv
    redπ
    tms
  ->
  xtrace_rel_properties LTMSEvtoLSMSEv 
    blueπ
    redπ
  ->
  xtrace_rel_properties LTMSEvtoTMSMonEv 
    blueπ
    tms
.
Proof.
  cbn; intros H0 H1 tr1 tr2 Hin1 Hin2.
  specialize (H1 tr1).
Admitted.


End TraceRelations.


