Set Implicit Arguments.
Require Import Strings.String CSC.Util.

(** * This file defines the trace properties of the paper. *)

Variant ControlTag : Type :=
| CCtx
| CComp
.
Variant SecurityTag : Type :=
| SLock
| SUnlock
.
Variant PreEvent : Type :=
| Alloc (l : loc) (n : nat)
| Use (l : loc) (n : nat)
| Dealloc (l : loc)
| Branch (n : nat)
| Binop (n : nat)
.
Inductive Event : Type :=
| Aborted
| PreEv (a__b : PreEvent) (t : ControlTag) (σ : SecurityTag)
.
#[export]
Instance MGT__Instance : TraceParams := {
  Ev := Event ;
  string_of_event := fun _ => ""%string ;
}.

Definition control_tag_eq c0 c1 :=
  match c0, c1 with
  | CCtx, CCtx | CComp, CComp => true
  | _, _ => false
  end
.
Lemma control_tag_eqb_eq c0 c1 :
  control_tag_eq c0 c1 = true <-> c0 = c1.
Proof. destruct c0, c1; now cbn. Qed.
#[export]
Instance ControlTag__Instance : HasEquality ControlTag := {
  eq := control_tag_eq ;
  eqb_eq := control_tag_eqb_eq
}.
Definition string_of_controltag (t : ControlTag) : string :=
  match t with
  | CCtx => "ctx"%string
  | CComp => "comp"%string
  end
.
Definition security_tag_eq s0 s1 :=
  match s0, s1 with
  | SLock, SLock | SUnlock, SUnlock => true
  | _, _ => false
  end
.
Lemma security_tag_eqb_eq c0 c1 :
  security_tag_eq c0 c1 = true <-> c0 = c1.
Proof. destruct c0, c1; now cbn. Qed.
#[export]
Instance SecurityTag__Instance : HasEquality SecurityTag := {
  eq := security_tag_eq ;
  eqb_eq := security_tag_eqb_eq
}.
Definition preevent_eq p0 p1 :=
  match p0, p1 with
  | Alloc l0 n0, Alloc l1 n1 => andb (eq l0 l1) (Nat.eqb n0 n1)
  | Use l0 n0, Use l1 n1 => andb (eq l0 l1) (Nat.eqb n0 n1)
  | Dealloc l0, Dealloc l1 => eq l0 l1
  | Branch n0, Branch n1 => Nat.eqb n0 n1
  | Binop n0, Binop n1 => Nat.eqb n0 n1
  | _, _ => false
  end
.
Lemma preevent_eqb_eq p0 p1 :
  preevent_eq p0 p1 = true <-> p0 = p1.
Proof.
  destruct p0, p1; cbn; try easy; split; intros; repeat rewrite bool_and_equiv_prop in *.
  all: try
    (destruct H as [H0 H1]; change ((l == l0) = true) in H0; rewrite eqb_eq in H0; apply PeanoNat.Nat.eqb_eq in H1; now subst).
  - inv H; split. change ((l0 == l0) = true); apply eq_refl. apply PeanoNat.Nat.eqb_refl.
  - inv H; split. change ((l0 == l0) = true); apply eq_refl. apply PeanoNat.Nat.eqb_refl.
  - change ((l == l0) = true) in H; rewrite eqb_eq in H; now subst.
  - inv H; change ((l0 == l0) = true); apply eq_refl.
  - apply PeanoNat.Nat.eqb_eq in H; now subst.
  - inv H; apply PeanoNat.Nat.eqb_refl.
  - apply PeanoNat.Nat.eqb_eq in H; now subst.
  - inv H; apply PeanoNat.Nat.eqb_refl.
Qed.
#[export]
Instance PreEvent__Instance : HasEquality PreEvent := {
  eq := preevent_eq ;
  eqb_eq := preevent_eqb_eq
}.
Definition event_eq e0 e1 :=
  match e0, e1 with
  | Aborted, Aborted => true
  | PreEv a0 t0 σ0, PreEv a1 t1 σ1 => andb (preevent_eq a0 a1)
                                          (andb (control_tag_eq t0 t1) (security_tag_eq σ0 σ1))
  | _, _ => false
  end
.
Lemma event_eqb_eq e0 e1 :
  event_eq e0 e1 = true <-> e0 = e1.
Proof.
  destruct e0, e1; cbn; split; intros; try easy.
  - repeat rewrite bool_and_equiv_prop in H. destruct H as [H0 [H1 H2]].
    change ((a__b == a__b0) = true) in H0.
    change ((t == t0) = true) in H1.
    change ((σ == σ0) = true) in H2.
    apply eqb_eq in H0, H1, H2; now subst.
  - inv H; repeat rewrite bool_and_equiv_prop; repeat split.
    change ((a__b0 == a__b0) = true); apply eq_refl.
    change ((t0 == t0) = true); apply eq_refl.
    change ((σ0 == σ0) = true); apply eq_refl.
Qed.
#[export]
Instance Event__Instance : HasEquality Event := {
  eq := event_eq ;
  eqb_eq := event_eqb_eq
}.
Definition tracepref := Util.tracepref.

(** Trace property definitions *)

(** Safety Property *)
Definition prop := tracepref -> Prop.

(** Temporal Memory Safety *)
Definition tms : prop := fun (As : tracepref) =>
                           (forall l n t t' σ σ', in_t (PreEv (Alloc l n) t σ) As ->
                                             in_t (PreEv (Dealloc l) t' σ') As ->
                                             before (PreEv (Alloc l n) t σ) (PreEv (Dealloc l) t' σ') As)
                         /\ (forall l n m t t' σ σ', in_t (PreEv (Use l n) t σ) As ->
                                               in_t (PreEv (Alloc l m) t' σ') As ->
                                               ~before (PreEv (Use l n) t σ) (PreEv (Alloc l m) t' σ') As)
                         /\ (forall l n t t' σ σ', in_t (PreEv (Dealloc l) t σ) As ->
                                             in_t (PreEv (Use l n) t' σ') As ->
                                             ~before (PreEv (Dealloc l) t σ) (PreEv (Use l n) t' σ') As)
.
(** Spatial Memory Safety *)
Definition sms : prop := fun (As : tracepref) =>
                           (forall l n m t t' σ σ', before (PreEv (Alloc l m) t σ) (PreEv (Use l n) t' σ') As ->
                                               n < m)
.
(** Memory Safety *)
Definition ms : prop := fun (As : tracepref) =>
                          tms As /\ sms As
.
(** Strict Cryptographic Constant Time *)
Fixpoint no_secrets (As : tracepref) : tracepref :=
  match As with
  | List.nil => List.nil
  | List.cons a As =>
    match a with
    | Aborted => List.cons Aborted (no_secrets As)
    | PreEv a__b t SLock => no_secrets As
    | PreEv a__b t SUnlock => List.cons a (no_secrets As)
    end
  end
.
Definition sCCT : prop := fun (As : tracepref) =>
                            As = no_secrets As
.
(** Combined version of ms and scct *)
Definition MSSCCT : prop := fun (As : tracepref) =>
                              ms As /\ sCCT As
.
Module PropNotations.
  Declare Scope PropNotationsScope.
  Delimit Scope PropNotationsScope with propnotationsscope.

  Notation "e '∈' π" := (π e) (at level 81, π at next level) : PropNotationsScope.
  Notation "π1 '∩' π2" := ((fun (t : tracepref) => t ∈ π1 /\ t ∈ π2)%propnotationsscope) (at level 81, π2 at next level, left associativity) : PropNotationsScope.
End PropNotations.
