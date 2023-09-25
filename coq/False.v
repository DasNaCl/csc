Require Import Coq.Logic.FunctionalExtensionality.

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
  apply set_eq_equiv_eq; split; intros x Hx. 
  (*should be similar to above*)
Admitted.

Lemma belongs_to_rel_comm { S I : Language } (C1 : Class (Event S))
  (Π : Hyperproperty (Event S)) (C2 : Class (Event I))
  (rel : Trace (Event S) -> Trace (Event I) -> Prop) :
  belongs_to (Event S) Π C1 ->
  belongs_to (Event I) (induced_tau rel Π) C2
.
Proof.
Admitted.

Theorem seqcompo {S I T : Language} (cc1 : Compiler S I) (cc2 : Compiler I T)
  (C1 C2 : Class (Event S))
  (rel1 : Trace (Event S) -> Trace (Event I) -> Prop)
  (rel2 : Trace (Event I) -> Trace (Event T) -> Prop) :
    [pres|- cc1 : rel1, C1] ->
    [pres|- cc2 : rel2, induced_tau rel1 C2] ->
    [pres|- (cc1 ∘ cc2) : rel1 ◘ rel2, C1 ∩ C2 ]
.
Proof.
  intros H1 H2 Π HΠ p Hsat Ct.
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠa HΠb].
  unfold prsat__τ in H2.
  rewrite rsat_trim.
  eapply H2. 1: (*the belongs_to_rel_comm needs more ass*) eauto using belongs_to_rel_comm.
  eapply H1; try exact HΠa.
  exact Hsat.
Qed.

(** I think up to here everything is ok, there are axioms besides the one of Coq. *)
(** So, the above theorem definitely holds. *)


(** But now, suppose we have two classes of properties, one that describes TMS behavior and the other describing SMS behavior. *)
Axiom (TMS SMS : Class).
Definition MS : Class := TMS ∩ SMS.

(** Likewise, say we have compilers that preserve robust satisfaction of behavior from these casses. *)
Axiom (S I T : Language).
Axiom (cc__TMS : Compiler S I) (cc__SMS : Compiler I T).
Axiom prsat_cc__TMS : [pres|- cc__TMS : TMS].
Axiom prsat_cc__SMS : [pres|- cc__SMS : SMS].

(** Furthermore, now suppose we have an S program that is robustly MS *)
Axiom robust_MS : forall (Π : Hyperproperty),
  belongs_to Π MS ->
  exists (p : Partials S), rsat p Π
.

(** What if cc__SMS has a table and forgets to allocate this?
    -> all components resulting from cc__SMS violate TMS! *)
Axiom cc__SMS_not_TMS : forall (Π : Hyperproperty) (p : Partials I),
  belongs_to Π TMS -> ~(rsat (cc__SMS p) Π)
.

(* Classical Lemma for pushing negation into quantifiers *)
Require Import Classical.

Definition XM := classic.
Definition DN := NNPP.

Lemma rw_not_forall {A : Type} (P : A -> Prop) :
  (~ forall (x : A), P x) <-> (exists x, ~ P x).
Proof.
  split.
  - apply (not_all_ex_not A P).
  - apply (ex_not_not_all A P).
Qed.

(** But assuming this exists is somehow invalid (??) *)
(** I guess the question really is whether this table-driven SMS
    compiler can actually be proven to be prsat SMS *)
Goal False.
Proof.
  (** Pick any hyperproperty from the class *)
  destruct (always_belongs_to MS) as [Π HΠ];
  assert (HΠ':=HΠ); apply belongs_to_commute in HΠ' as [HΠ__TMS HΠ__SMS].

  (** Assume a source-level execution exists that is MS. *)
  destruct (robust_MS Π HΠ) as [p Hrsat].
  (** Assume that no component that is the output of cc__SMS can give us a behavior from MS. *)
  specialize (cc__SMS_not_TMS Π (cc__TMS p) HΠ__TMS); intros H.

  (** Just push the negation inwards. *)
  unfold rsat in H; rewrite rw_not_forall in H; destruct H as [Ct H].

  (** Use the sequential composition lemma to obtain a secure MS compiler *)
  specialize (seqcompo cc__TMS cc__SMS TMS SMS prsat_cc__TMS prsat_cc__SMS); intros Hprsat.

  (** Now just compile the S component p and use the fact that the obtained
      compiler is prsat MS, thus obtaining that the compiled program is also 
     robustly satisfying a subset of MS properties. *)
  apply Hprsat in Hrsat; try exact HΠ.

  (** Finally, just provide the target context at hand, obtaining a contradiction *)
  specialize (Hrsat Ct).
  contradiction.
Qed.
