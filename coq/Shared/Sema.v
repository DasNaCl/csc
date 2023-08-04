Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Lists.List Lia.

Require Import CSC.Util.Convenience CSC.Util.HasEquality CSC.Util.NoDupInv.

From RecordUpdate Require Import RecordSet.

#[export]
Instance nateq__Instance : HasEquality nat := {
  eq := Nat.eqb ;
  eqb_eq := PeanoNat.Nat.eqb_eq ;
}.

(** Possible binary operations. *)
Variant binopsymb : Type :=
| Badd : binopsymb
| Bsub : binopsymb
| Bmul : binopsymb
| Bdiv : binopsymb
| Bless : binopsymb
.
Definition binopsymb_eqb :=
  fun (b1 b2 : binopsymb) =>
    match b1, b2 with
    | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Bdiv, Bdiv | Bless, Bless => true
    | _, _ => false
    end
.
Lemma binopsymb_eqb_eq b1 b2 :
  binopsymb_eqb b1 b2 = true <-> b1 = b2.
Proof. destruct b1, b2; now cbn. Qed.
#[export]
Instance binopsymb__Instance : HasEquality binopsymb := {
  eq := binopsymb_eqb ;
  eqb_eq := binopsymb_eqb_eq ;
}.
Definition string_of_symb s :=
  match s with
  | Badd => "+"
  | Bsub => "-"
  | Bmul => "*"
  | Bdiv => "/"
  | Bless => "<"
  end%string
.

(** Poison used to mark locations in our operational state. *)
Inductive poison : Type :=
| poisonless : poison
| poisoned : poison
.
#[global]
Notation "'◻'" := (poisonless).
#[global]
Notation "'☣'" := (poisoned).
Definition poison_eqb :=
  fun (ρ1 ρ2 : poison) =>
    match ρ1, ρ2 with
    | ◻, ◻ | ☣, ☣ => true
    | _, _ => false
    end
.
Lemma poison_eqb_eq ρ1 ρ2 :
  poison_eqb ρ1 ρ2 = true <-> ρ1 = ρ2.
Proof. destruct ρ1, ρ2; now cbn. Qed.
#[export]
Instance poisoneq__Instance : HasEquality poison := {
  eq := poison_eqb ;
  eqb_eq := poison_eqb_eq ;
}.

(** Context switch indicators. The paper calls these Transfer Tags *)
Variant comms : Type :=
| Qctxtocomp : comms
| Qcomptoctx : comms
| Qinternal : comms
.
Definition comms_eqb (q1 q2 : comms) :=
  match q1, q2 with
  | Qctxtocomp, Qctxtocomp => true
  | Qcomptoctx, Qcomptoctx => true
  | Qinternal, Qinternal => true
  | _, _ => false
  end
.
Lemma comms_eqb_eq (q1 q2 : comms) :
  comms_eqb q1 q2 = true <-> q1 = q2.
Proof. destruct q1, q2; now cbn. Qed.
#[export]
Instance commseq__Instance : HasEquality comms := {
  eq := comms_eqb ;
  eqb_eq := comms_eqb_eq ;
}.
Definition string_of_comms (q : comms) :=
  match q with
  | Qctxtocomp => "?"%string
  | Qcomptoctx => "!"%string
  | Qinternal => "∅"%string
  end
.

(** Evaluation of binary expressions. Note that 0 means `true` in S, so `5 < 42` evals to `0`. *)
Definition eval_binop (b : binopsymb) (n0 n1 : nat) : option nat :=
  Some((match b with
       | Bless => (if Nat.ltb n0 n1 then 0 else 1)
       | Badd => (n0 + n1)
       | Bdiv => (Nat.div n0 n1)
       | Bsub => (n0 - n1)
       | Bmul => (n0 * n1)
       end))
.

(** The type used for variable names. *)
Definition vart := string.
Definition vareq := fun x y => (x =? y)%string.
Definition dontcare := "_"%string.
#[export]
Instance varteq__Instance : HasEquality vart := {
  eq := vareq ;
  eqb_eq := String.eqb_eq ;
}.

(** References *)
Inductive loc : Type :=
| addr : nat -> loc
.
Definition loc_eqb :=
  fun ℓ1 ℓ2 =>
    match ℓ1, ℓ2 with
    | addr n1, addr n2 => Nat.eqb n1 n2
    end
.
Lemma loc_eqb_eq ℓ0 ℓ1 :
  loc_eqb ℓ0 ℓ1 = true <-> ℓ0 = ℓ1.
Proof.
  destruct ℓ0 as [n0], ℓ1 as [n1]; split; intros H.
  - cbn in H; rewrite PeanoNat.Nat.eqb_eq in H; now subst.
  - inv H; apply PeanoNat.Nat.eqb_refl.
Qed.
#[export]
Instance loceq__Instance : HasEquality loc := {
  eq := loc_eqb ;
  eqb_eq := loc_eqb_eq ;
}.

(** Operational state *)
Section Heap.
  (** Type of objects stored on heap. *)
  Context {value : Type} {valueeq__Instance : HasEquality value}.

  Definition heap := list (value).
  Definition hNil : heap := nil.
  Fixpoint Hgrow_aux (H : heap) (s : nat) (default : value) : heap :=
    match s with
    | 0 => H
    | S n' => default :: Hgrow_aux H n' default
    end
  .
  Definition Hgrow (H : heap) (s : nat) (default : value) : heap :=
    Hgrow_aux H s default
  .

  Lemma Hget_none (H : heap) (n : nat) :
    n >= List.length H -> List.nth_error H n = None.
  Proof.
    revert n; induction H; cbn; intros.
    - destruct n; easy.
    - destruct n; cbn; try easy. assert (n >= List.length H) by lia.
      now specialize (IHlist n H1).
  Qed.
  Lemma Hget_some (H : heap) (n : nat) :
    n < List.length H -> exists v, List.nth_error H n = Some v.
  Proof.
    revert n; induction H; cbn; intros.
    - destruct n; easy.
    - destruct n; cbn; try easy. exists a; easy.
      assert (n < List.length H) by lia.
      now specialize (IHlist n H1).
  Qed.
  Lemma Hset_none (H : heap) (n : nat) v :
    n >= List.length H -> NoDupList.swap_nth_aux H n v = None.
  Proof.
    revert n; induction H; cbn; intros.
    - now inv H.
    - destruct n; try easy. assert (n >= List.length H) by lia.
      specialize (IHlist n H1); now rewrite IHlist.
  Qed.
  Lemma Hset_some (H : heap) (n : nat) v :
    n < List.length H -> exists H', NoDupList.swap_nth_aux H n v = Some H'.
  Proof.
    revert n; induction H; cbn; intros.
    - destruct n; easy.
    - destruct n; cbn; try easy. exists (v :: H); easy.
      assert (n < List.length H) by lia.
      specialize (IHlist n H1); deex. exists (a :: H'); now rewrite IHlist.
  Qed.
End Heap.
