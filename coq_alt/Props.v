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
Definition tracepref := Util.tracepref.

(** Trace property definitions *)

(** Safety Property *)
Definition prop := tracepref -> Prop.

(** Temporal Memory Safety *)
Definition tms : prop := fun (As : tracepref) =>
                           (forall l n t t' σ σ', before (PreEv (Alloc l n) t σ) (PreEv (Dealloc l) t' σ') As)
                         /\ (forall l n m t t' σ σ', ~before (PreEv (Use l n) t σ) (PreEv (Alloc l m) t' σ') As)
                         /\ (forall l n t t' σ σ', ~before (PreEv (Dealloc l) t σ) (PreEv (Use l n) t' σ') As)
.
(** Spatial Memory Safety *)
Definition sms : prop := fun (As : tracepref) =>
                           forall l n m t t' σ σ', before (PreEv (Alloc l m) t σ) (PreEv (Use l n) t' σ') As ->
                                              n < m
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
