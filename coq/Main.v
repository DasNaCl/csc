Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat Strings.String Lists.List Lia Program.Equality.
Require Import CSC.Sets.

Ltac inv H := (inversion H; subst; clear H).

Axiom Events : Set.

(** * Traces *)
CoInductive Trace : Set :=
| TCons (e : Events) (t : Trace) : Trace
.
(** * Abstract description of a Programming Language

  Programming languages consist of:
    - A set of (admissible) partial programs.
      Basically, partial programs are syntactically and semantically correct.
    - A judgement that checks whether a partial program is partial or not.
      Only whole programs can be executed.
    - A judgement that checks whether a partial program is a value (e.g. `42`).
    - The linker is self-explanatory.
    - The step relation, as mentioned before, works on whole programs.
      Instead of directly emitting the behavior, we require languages to be defined
      in a small-step like manner, which will allow us to combine languages later in
      interesting ways.
    - Lastly, there is a lemma any language must satisfy: Given a whole program,
      it may perform a step to another whole program emitting an event or terminate
      in a value.
*)
(** Unfortunately, Coq 8.14.1 seems to have some issues with regards to dependent pattern
    matching that don't allow us to state the lemma as a property of the record.
    Henceforth, we pose it as a variable. *)
Record Language : Type :=
{
  Partials : Set;
  whole : Partials -> Prop;
  value : Partials -> Prop;
  link : Partials -> Partials -> option Partials;
  steps : forall (p : Partials), whole p -> Trace -> Prop;
}.

Module PropSetM <: SetBase.
  Definition A := Trace.
End PropSetM.
Module PropSet <: Sig := SetTheoryAbstract PropSetM.

Module HPropSetM <: SetBase.
  Definition A := PropSet.set.
End HPropSetM.
Module HPropSet <: Sig := SetTheoryAbstract HPropSetM.

Module HPropClassM <: SetBase.
  Definition A := HPropSet.set.
End HPropClassM.
Module HPropClass <: Sig := SetTheoryAbstract HPropClassM.

(** Set of traces. *)
Definition Property := PropSet.set.

(** Set of sets of traces. *)
Definition Hyperproperty := HPropSet.set.

(** Sets of hyperproperties *)
Definition PClass := HPropClass.set.

Notation "C '⋈' P" := (link _ P C) (at level 50).
Section Satisfaction.

(** * Different kinds of Satisfaction Criteria *)
Context {K : Language}.

Definition behav (p : Partials K) (H : whole K p) : HPropSet.A :=
  fun (t : Trace) => steps K p H t.

Section A.
Import HPropSet HPropSet.Notations.
Definition hsat (p : Partials K) (Π : Hyperproperty) : Prop :=
  forall (H : whole K p), HPropSet.el (behav p H) Π.
End A.
Section A.
(* TODO: notation of sets should somehow work on a typeclass*)
Import HPropSet HPropSet.Notations.
Definition subset_closed (Π : Hyperproperty) :=
  forall (π : Property), π ∈ Π -> forall (π' : Property), PropSet.subset π' π -> π' ∈ Π.
End A.
Definition rhsat (p : Partials K) (Π : Hyperproperty) : Prop :=
  forall (c : Partials K),
    match (c ⋈ p) with
    | None => False
    | Some L => hsat L Π
    end.

Import HPropClass HPropClass.Notations.
Definition csat (p : Partials K) (C : PClass) : Prop := forall Π, Π ∈ C -> hsat p Π.
Definition rcsat (p : Partials K) (C : PClass) : Prop := forall Π, Π ∈ C -> rhsat p Π.

End Satisfaction.

Definition SumLanguage (L0 L1 : Language)
           (cross_linker : Partials L0 -> Partials L1 -> option (Partials L0 + Partials L1))
  :=
{|
  Partials := Partials L0 + Partials L1 ;
  whole := fun (p : Partials L0 + Partials L1) =>
             match p with
             | inl p0 => whole L0 p0
             | inr p1 => whole L1 p1
             end
          ;
  value := fun (p : Partials L0 + Partials L1) =>
             match p with
             | inl p0 => value L0 p0
             | inr p1 => value L1 p1
             end
          ;
  link := fun (p0 p1 : Partials L0 + Partials L1) =>
            match p0, p1 with
            | inl pa, inl pb => match (link L0 pa pb) with
                               | Some L => Some(inl L)
                               | None => None
                               end
            | inr pa, inr pb => match (link L1 pa pb) with
                               | Some L => Some(inr L)
                               | None => None
                               end
            | inl pa, inr pb => cross_linker pa pb
            | inr pa, inl pb => cross_linker pb pa
            end
          ;
  steps := fun p =>
            match p with
            | inl p0 => (fun (H' : whole L0 p0) => steps L0 p0 H')
            | inr p1 => (fun (H' : whole L1 p1) => steps L1 p1 H')
            end
          ;
|}.
Definition ProdLanguage (L0 L1 : Language) :=
{|
  Partials := (Partials L0) * (Partials L1) ;
  whole := fun (p : (Partials L0) * (Partials L1)) =>
             match p with
             | (p0, p1) => whole L0 p0 /\ whole L1 p1
             end
           ;
  value := fun (p : (Partials L0) * (Partials L1)) =>
             match p with
             | (p0, p1) => value L0 p0 /\ value L1 p1
             end
           ;
  link := fun (p0 p1 : (Partials L0) * (Partials L1)) =>
            match p0, p1 with
            | (pa0, pa1), (pb0, pb1) =>
                match link L0 pa0 pb0, link L1 pa1 pb1 with
                | Some A, Some B => Some (A,B)
                | _, _ => None
                end
            end
          ;
  steps := fun p =>
            let '(p0a, p1a) := p in
            fun H =>
            match H with
            | conj H0a H1a => fun t => steps L0 p0a H0a t /\ steps L1 p1a H1a t
            end
          ;
|}.
Notation "L0 'L*' L1" := (ProdLanguage L0 L1) (at level 80).


(** * Compilers *)
Definition Compiler (L0 L1 : Language) := Partials L0 -> Partials L1.

Definition seqcomp {L0 L1 L2 : Language} (f : Compiler L1 L2) (g : Compiler L0 L1) := fun x => f (g x).
Notation "f '∘' g" := (seqcomp g f) (at level 50).

Notation "p '|-' C" := (rcsat p C) (at level 50).
Notation "p '|=' Π" := (rhsat p Π) (at level 50).

Section Main.

Variable S I T : Language.
Variable linkSI : Partials S -> Partials I -> option (Partials S + Partials I).

(** * Property mappings *)
(** Given must be a relation between traces of a source and a target language. *)

(** TODO: Add ext. image and all that. See
    https://github.com/secure-compilation/different_traces/blob/master/SSCHPreservation.v *)

Import HPropClass HPropClass.Notations.
Definition RC { L0 L1 : Language } (γ : Compiler L0 L1) (C : PClass) :=
  forall (Π : Hyperproperty), Π ∈ C ->
    forall (p : Partials L0), p |= Π -> γ p |= Π.
Notation "'pres|-' γ ':' C" := (RC γ C) (at level 50, γ at next level).

(** * Main Results *)

Lemma sequential_composition (γ0 : Compiler S I) (γ1 : Compiler I T) (C0 C1 : PClass) :
  pres|- γ0 : C0 -> pres|- γ1 : C1 -> pres|- (γ0 ∘ γ1) : (C0 ∩ C1).
Proof.
  intros H0 H1 Π H2 p H3.
  apply ElimIntersect in H2 as [H2a H2b].
  apply H1; trivial.
  apply H0; trivial.
Qed.

Corollary swappable (γ0 γ1 : Compiler I I) (C0 C1 : PClass) :
  pres|- γ0 : C0 -> pres|- γ1 : C1 -> pres|- (γ0 ∘ γ1) : (C0 ∩ C1) /\ pres|- (γ1 ∘ γ0) : (C0 ∩ C1).
Proof.
  intros H0 H1; split.
  all:
  intros Π H2 p H3;
  apply ElimIntersect in H2 as [H2a H2b];
  (apply H1, H0 || apply H0, H1); trivial.
Qed.

Definition UpperComposition { L0 L1 L2 : Language } { cross_link }
    (γ0 : Compiler L0 L2) (γ1 : Compiler L1 L2)
  : Partials (SumLanguage L0 L1 cross_link) -> Partials L2
  :=
  fun (pab : Partials (SumLanguage L0 L1 cross_link)) =>
    match pab with
    | inl p => γ0 p
    | inr p => γ1 p
    end
.
Lemma upper_compose (γ0 : Compiler S T) (γ1 : Compiler I T) (C0 C1 : PClass) :
  pres|- γ0 : C0 -> pres|- γ1 : C1 -> pres|- (@UpperComposition S I T linkSI γ0 γ1) : (C0 ∩ C1).
Proof.
  intros H0 H1 Π H2 [pS | pI] H3; apply ElimIntersect in H2 as [H2a H2b].
  - apply H0; try easy.
    intros Cs; specialize (H3 (inl Cs)).
    (* exact H3. *)
    (** This doesn't work out, since programs in the SumLang might go from S to I
        in intermediate steps. *)
    admit.
  - apply H1; try easy.
    intros Cs; specialize (H3 (inr Cs)).
    (* exact H3. *)
    (** Same business. *)
    admit.
Admitted.
(* Secure Enforcements *)
Definition enforcement { L0 L1 : Language } (γ : Compiler L0 L1) (C : PClass) := forall (p : Partials L0), rcsat (γ p) C.
Notation "'enf|-' γ '--≻' C" := (enforcement γ C) (at level 80).

Definition secure_enforcement { L0 L1 : Language } (γ : Compiler L0 L1) (C0 C1 : PClass) :=
  pres|- γ : C0 /\ enf|- γ --≻ C1.
Notation "'senf|-' γ '-[' C0 ']-≻' C1" := (secure_enforcement γ C0 C1) (at level 50).

Lemma senf_and_rc (γ0 : Compiler S I) (γ1 : Compiler I T) (C0 C1 : PClass) :
  pres|- γ0 : C0 -> senf|- γ1 -[ C0 ]-≻ C1 -> pres|- (γ0 ∘ γ1) : (C0 ∪ C1).
Proof.
  intros H0 [H1a H1b] Π H2 p H3.
  apply ElimUnion in H2 as [H2a|H2b].
  - apply H1a; trivial. apply H0; trivial.
  - apply H1b; trivial.
Qed.

Lemma rc_and_senf (γ0 : Compiler S I) (γ1 : Compiler I T) (C0 C1 : PClass) :
  senf|- γ0 -[ C0 ]-≻ C1 -> pres|- γ1 : C0 -> pres|- (γ0 ∘ γ1) : (C0 ∪ C1).
Proof.
  intros [H0a H0b] H1 Π H2 p H3.
  apply ElimUnion in H2 as [H2a|H2b].
  - apply H1; trivial. apply H0a; trivial.
  - (** This is where things go wrong. We can only apply H1, but this means
        we need to prove that our pi is in C0, which it isn't...!           *)
Abort.

(** * Bonus *)

Lemma join_sinstrus (γ1 : Compiler S I) (γ2 : Compiler I T) (C0 C1 C2 : PClass) :
  senf|- γ1 -[C0]-≻ C1 -> senf|- γ2 -[C1]-≻ C2 -> senf|- (γ1 ∘ γ2) -[C0 ∩ C1]-≻ (C1 ∪ C2).
Proof.
  intros [H0a H0b] [H1a H1b]; split.
  - intros Π H2 p H3; apply ElimIntersect in H2 as [H2a H2b].
    apply H1a; trivial; apply H0a; trivial.
  - intros p Π H2; apply ElimUnion in H2 as [H2a|H2b].
    + apply H1a; trivial; now apply H0b.
    + now apply H1b.
Qed.

Lemma instru_union (γ : Compiler S T) (C0 C1 : PClass) :
  senf|- γ -[C0]-≻ C1 -> pres|- γ : (C0 ∪ C1).
Proof.
  intros [H0a H0b] Π H2 p H3.
  apply ElimUnion in H2 as [H2a|H2b].
  - apply H0a; assumption.
  - apply H0b; assumption.
Qed.
Lemma instru_cap (γ : Compiler S T) (C0 C1 : PClass) :
  senf|- γ -[C0]-≻ C1 -> pres|- γ : (C0 ∩ C1).
Proof.
  intros [H0a H0b] Π H2 p H3.
  apply ElimIntersect in H2 as [H2a H2b].
  now apply H0a.
Qed.

Lemma join_instrus (γ0 : Compiler S I) (γ1 : Compiler I T) (C0 C1 : PClass) :
  senf|- γ0 -[C1]-≻ C0 -> senf|- γ1 -[C0]-≻ C1 -> senf|- (γ0 ∘ γ1) -[C1]-≻ C0 /\ senf|- (γ0 ∘ γ1) -[C0]-≻ C1.
Proof.
  intros [H0a H0b] [H1a H1b]; repeat split.
  - intros Π H2 p H3. now apply H1b.
  - intros p Π H2. apply H1a; try assumption. now apply H0b.
  - intros Π H2 p H3. apply H1a; try assumption. now apply H0b.
  - intros p Π H2. now apply H1b.
Qed.

Lemma swappable_instrus (γ0 : Compiler I I) (γ1 : Compiler I I) (C0 C1 : PClass) :
  senf|- γ0 -[C0]-≻ C1 -> senf|- γ1 -[C1]-≻ C0 -> senf|- (γ0 ∘ γ1) -[C0 ∪ C1]-≻ (C0 ∪ C1) /\
                                              senf|- (γ1 ∘ γ0) -[C0 ∪ C1]-≻ (C0 ∪ C1).
Proof.
  intros [H0a H0b] [H1a H1b]; repeat split.
  - intros Π H2 p H3; apply ElimUnion in H2 as [H2a|H2b].
    + now apply H1b.
    + apply H1a; trivial; now apply H0b.
  - intros p Π H2; apply ElimUnion in H2 as [H2a|H2b].
    + now apply H1b.
    + apply H1a; trivial; now apply H0b.
  - intros Π H2 p H3; apply ElimUnion in H2 as [H2a|H2b].
    + apply H0a; trivial; now apply H1b.
    + now apply H0b.
  - intros p Π H2; apply ElimUnion in H2 as [H2a|H2b].
    + apply H0a; trivial; now apply H1b.
    + now apply H0b.
Qed.


(* Lower Composition *)
Definition LowerComposition { L0 L1 L2 : Language } (γ0 : Compiler L0 L1) (γ1 : Compiler L0 L2)
  : Partials L0 -> Partials (ProdLanguage L1 L2)
  :=
  fun (p : Partials L0) => (γ0 p, γ1 p)
.

Definition ssc_class (C : PClass) :=
  forall (Π : Hyperproperty), Π ∈ C -> subset_closed Π.

Lemma lowercomp_compose (γ0 : Compiler S I) (γ1 : Compiler S T) (C0 C1 : PClass) :
  ssc_class C0 ->
  pres|- γ0 : C0 -> pres|- γ1 : C1 -> pres|- (LowerComposition γ0 γ1) : (C0 ∩ C1).
Proof.
  intros SSC0 H0 H1 Π H2 p H3; apply ElimIntersect in H2 as [H2a H2b].
  intros [Ci Ct]. unfold LowerComposition in *.
  apply H0 in H3 as H3a; apply H1 in H3 as H3b; trivial.
  unfold "_ |= _" in *.
  admit. (*
  unfold behaviour; cbn; destruct Hw as [Hw0 Hw1].
  specialize (H3a Ci Hw0); specialize (H3b Ct Hw1).
  unfold behaviour in H3a, H3b.
  change (fun b => ?h b) with h in H3a, H3b.
  apply SSC0 in H2a as SSPi. eapply SSPi in H3a, H3b.
  apply H3a. intros τ H4.
  change (τ ∈ (fun b : Trace => ?h b)) with (τ ∈ h) in H4.
  unfold "_ ∈ _" in *. destruct H4 as [H4a H4b]. assumption.
  *)
Admitted.

Lemma enforcement_implies_robustness (γ : Compiler S I) (C : PClass) :
  enf|- γ --≻ C -> pres|- γ : C.
Proof.
  intros H0 Π H1 p H2; now apply H0.
Qed.

Lemma enforcements_are_secure_for_fixed_class (γ : Compiler S I) (C : PClass) :
  enf|- γ --≻ C -> senf|- γ -[C]-≻ C.
Proof.
  intros H0; split.
  - intros H1 Π H2 p; now apply H0.
  - exact H0.
Qed.

End Main.
