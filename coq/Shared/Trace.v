Set Implicit Arguments.
From Stdlib Require Import Strings.String Lists.List Lia Program.Equality.

Require Import CSC.Util.Convenience.

(** Typeclass to define trace model *)
Class TraceParams : Type := {
  Ev : Type ;
  string_of_event : Ev -> string ;
}.
Section Trace.
  Context {traceParams : TraceParams}.
  (** A trace is an infinite stream of events.
      Termination is modeled by infinitely many `None`.
   *)
  CoInductive trace :=
  | TCons : option Ev -> trace -> trace
  .
  (** It is sufficient to look at trace prefixes for safety properties. *)
  Definition tracepref := list Ev.

  Fixpoint Tappend (As Bs : tracepref) : tracepref :=
    match As with
    | nil => Bs
    | a :: As => a :: (Tappend As Bs)
    end
  .
  Definition string_of_tracepref (t : tracepref) : string :=
    let aux := fix string_of_tracepref_aux (t : tracepref) (acc : string) : string :=
      match t with
      | nil => acc
      | a :: nil => String.append acc (string_of_event a)
      | a :: As =>
          let acc' := String.append acc (String.append (string_of_event a) (" · "%string))
          in string_of_tracepref_aux As acc'
      end in
    aux t (""%string)
  .
  Inductive wherein : Ev -> tracepref -> nat -> Prop :=
  | whereinIn : forall a As, wherein a (a :: As) 0
  | whereinLook : forall a As b n, a <> b -> wherein a As n -> wherein a (b :: As) (S n)
  .
  Hint Constructors wherein : core.
  Definition in_t (a : Ev) (As : tracepref) := exists (n : nat), wherein a As n.
  Lemma wherein_nil (a : Ev) :
    forall n, wherein a nil n -> False.
  Proof. now induction n. Qed.
  Lemma wherein_predecessor (a b: Ev) (As : tracepref) :
    forall n, a <> b -> wherein a (b :: As) n -> wherein a As (pred n).
  Proof.
    intros.
    inv H0. congruence. destruct As. inv H6. now cbn.
  Qed.
  Lemma wherein_eq (a : Ev) (As : tracepref) n m :
    wherein a As n -> wherein a As m -> n = m.
  Proof.
    intros H; revert m; induction H; intros. inv H; easy.
    destruct m. inv H1. congruence. inv H1; auto.
  Qed.
  Lemma wherein_equiv_wherein_cons (a b : Ev) (As : tracepref) n :
    a <> b ->
    wherein a As n <-> wherein a (b :: As) (n + 1).
  Proof.
    split.
    - induction 1; intros. now constructor. specialize (IHwherein H). inv IHwherein; try easy.
      constructor; trivial. rewrite PeanoNat.Nat.add_comm. now constructor.
    - intros H0. inv H0. rewrite PeanoNat.Nat.add_comm in H5; congruence. rewrite PeanoNat.Nat.add_comm in H4. now inv H4.
  Qed.
  Definition before (a0 a1 : Ev) (As : tracepref) : Prop :=
    exists n0 n1, wherein a0 As n0 /\ wherein a1 As n1 /\ n0 < n1
  .
  Ltac unfold_before := match goal with
                       | [H: before _ _ _ |- _] =>
                         let H0 := fresh "H__before" in
                         let H1 := fresh "H__before" in
                         unfold before in H; deex; destruct H as [H [H1 H2]]
                       end.
  Lemma before_nothing a0 a1 :
    before a0 a1 nil -> False.
  Proof.
    intros. unfold_before; now induction n0, n1.
  Qed.
  Lemma before_split a As a0 a1 n :
    a <> a0 -> a <> a1 ->
    (before a0 a1 As) \/ (a0 = a /\ wherein a1 As n) ->
    before a0 a1 (a :: As)
  .
  Proof.
    intros Ha Hb [H1 | [H1 H2]]; try unfold_before.
    - exists (S n0); exists (S n1); repeat split; auto. now apply Arith_base.lt_n_S_stt.
    - subst; congruence.
  Qed.
  Lemma eat_front_in_t a b As :
    a <> b ->
    in_t (a) (b :: As)%list <->
    in_t (a) (As)%list
  .
  Proof.
    intros H0; split; intros [n H1].
    - destruct n; cbn in H1.
      + inv H1; contradiction.
      + exists n. now inv H1.
    - exists (S n); auto.
  Qed.
  Lemma eat_front_wherein a b As n :
    a <> b ->
    wherein a (b :: As) (S n) <->
    wherein a As n
  .
  Proof.
    intros H0; split; intros H1.
    - now inv H1.
    - now constructor.
  Qed.
  Lemma eat_front_before a b c As :
    a <> c ->
    b <> c ->
    before a b (As)%list <->
    before a b (c :: As)%list
  .
  Proof.
    intros H0 H1; split; intros.
    - unfold_before; exists (S n0). exists (S n1). repeat split.
      now rewrite eat_front_wherein.
      now rewrite eat_front_wherein.
      unfold "_ < _" in *. lia.
    - unfold_before.
      destruct n0, n1.
      inv H2. inv H; congruence. inv H__before0; congruence.
      inv H; inv H__before0. exists n0; exists n1; repeat split; auto; lia.
  Qed.
  Lemma eat_middle_before a b c As Bs :
    a <> c ->
    b <> c ->
    before a b (Bs ++ As)%list <->
    before a b (Bs ++ c :: As)%list
  .
  Proof.
  Admitted.
  Lemma before_from_wherein a b As x x0 :
    before (a) (b) (As)%list ->
    wherein (a) (As)%list (x) ->
    wherein (b) (As)%list (x0) ->
    x < x0
  .
  Proof.
    intros. unfold_before.
    eapply wherein_eq in H, H__before0; eauto; subst; easy.
  Qed.

  Local Set Warnings "-uniform-inheritance".
  (** Use this to define a coercion *)
  Definition ev_to_tracepref (e : Ev) : tracepref := e :: nil.
  Coercion ev_to_tracepref : Ev >-> tracepref.

End Trace.

Class PrimStep (State : Type) (Event : Type) : Type :=
  Pstep : State -> option Event -> State -> Prop
.
Notation "e0 '--[' a ']-->' e1" := (Pstep e0 (Some a) e1) (at level 82, e1 at next level).
Notation "e0 '--[,' a ']-->' e1" := (Pstep e0 a e1) (at level 82, e1 at next level).
Notation "e0 '--[]-->' e1" := (Pstep e0 None e1) (at level 82, e1 at next level).

Class EctxStep (State : Type) (Event : Type) : Type :=
  Estep : State -> option Event -> State -> Prop
.
Notation "e0 '==[' a ']==>' e1" := (Estep e0 (Some a) e1) (at level 82, e1 at next level).
Notation "e0 '==[,' a ']==>' e1" := (Estep e0 a e1) (at level 82, e1 at next level).
Notation "e0 '==[]==>' e1" := (Estep e0 None e1) (at level 82, e1 at next level).

(** Typeclass to define language with star step and all that. *)
Class LangParams : Type := {
  State : Type ;
  Trace__Instance : TraceParams ;
  step : State -> option Ev -> State -> Prop ;
  is_value : State -> Prop ;
}.


Section Lang.
  Context {langParams : LangParams}.
  Existing Instance Trace__Instance.

  Inductive star_step : State -> tracepref -> State -> Prop :=
  | ES_refl : forall (r1 : State),
      is_value r1 ->
      star_step r1 nil r1
  | ES_trans_important : forall (r1 r2 r3 : State) (a : Ev) (As : tracepref),
      step r1 (Some a) r2 ->
      star_step r2 As r3 ->
      star_step r1 (a :: As) r3
  | ES_trans_unimportant : forall (r1 r2 r3 : State) (As : tracepref),
      step r1 None r2 ->
      star_step r2 As r3 ->
      star_step r1 As r3
  .
  Hint Constructors star_step : core.

  Lemma must_step_once (S0 S2 : State) a (As : tracepref) :
    star_step S0 (a :: As)%list S2 ->
    exists S0' S1, step S0' (Some a) S1 /\ star_step S1 As S2
  .
  Proof.
    intros H; dependent induction H; eauto.
  Qed.

  Inductive n_step : State -> nat -> tracepref -> State -> Prop :=
  | ENS_refl : forall (r1 : State),
      is_value r1 ->
      n_step r1 0 nil r1
  | ENS_trans_important : forall (r1 r2 r3 : State) (a : Ev) (As : tracepref) (n : nat),
      step r1 (Some a) r2 ->
      n_step r2 n As r3 ->
      n_step r1 (S n) (a :: As) r3
  | ENS_trans_unimportant : forall (r1 r2 r3 : State) (As : tracepref) (n : nat),
      step r1 None r2 ->
      n_step r2 n As r3 ->
      n_step r1 (S n) As r3
  .
  Hint Constructors star_step : core.
End Lang.

Module LangNotations.
  #[local] Parameter (langParams : LangParams).

  Declare Scope LangNotationsScope.
  Delimit Scope LangNotationsScope with langnotationsscope.
  Notation "e0 '==[' a ']==>' e1" := (step e0 (Some a) e1) (at level 82, e1 at next level) : LangNotationsScope.
  Notation "e0 '==[,' a ']==>' e1" := (step e0 a e1) (at level 82, e1 at next level) : LangNotationsScope.
  Notation "e0 '==[]==>' e1" := (step e0 None e1) (at level 82, e1 at next level) : LangNotationsScope.

  Notation "e0 '==[' a ']==>*' e1" := (star_step e0 a e1) (at level 82, e1 at next level) : LangNotationsScope.
  Notation "e0 '==[]==>*' e1" := (star_step e0 (nil) e1) (at level 82, e1 at next level) : LangNotationsScope.

  Notation "e0 '=(' n ')=[' a ']==>' e1" := (n_step e0 n a e1) (at level 82, e1 at next level) : LangNotationsScope.
  Notation "e0 '=()=[]==>' e1" := (n_step e0 0 nil e1) (at level 82, e1 at next level) : LangNotationsScope.
End LangNotations.

#[global]
Ltac unfold_before := match goal with
                      | [H: before _ _ _ |- _] =>
                        let H0 := fresh "H__before" in
                        let H1 := fresh "H__before" in
                        unfold before in H; deex; destruct H as [H [H1 H2]]
                      end
.
