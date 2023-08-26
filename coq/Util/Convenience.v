Set Implicit Arguments.
Require Import Strings.String Lists.List.

Require Import FCS.Util.Sets.

(** This file defines some convenience features, e.g., simple properties on booleans or the option monad. *)

#[global]
Ltac inv H := (inversion H; subst; clear H).
#[global]
Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end.
#[global]
Ltac someinv :=
  repeat match goal with
         | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
         end.

Class Monad (m : Type -> Type) : Type := {
  ret : forall {t : Type}, t -> m t ;
  bind : forall {t u : Type}, m t -> (t -> m u) -> m u
}.

#[global]
Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).
#[global]
Notation "'$' pat '<-' c1 ';;' c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end)) (at level 61, pat pattern, c1 at next level, right associativity).
#[global]
Notation "'let*' p ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun p => c2)) (at level 61, p as pattern, c1 at next level, right associativity).

#[global]
Instance OptionMonad__Instance : Monad option := {
  ret T x := Some x ;
  bind T U m f := match m with
                  | None => None
                  | Some x => f x
                  end
}.
Lemma get_rid_of_letstar {A B:Type} (a : A) (x : A) (f : A -> option B):
  (let* a := Some x in f a) = f x.
Proof. now cbn. Qed.

#[global]
Hint Resolve get_rid_of_letstar : core.

Definition is_Some {A : Type} (mx : option A) := exists x, mx = Some x.
#[global]
Hint Unfold is_Some : core.

Lemma is_Some_alt {A : Type} (mx : option A) :
  is_Some mx <-> match mx with Some _ => True | None => False end.
Proof.
  unfold is_Some; destruct mx; split; try easy; try now exists a.
  intros; now destruct H.
Qed.

Lemma not_eq_None_Some {A : Type} (mx : option A) : mx <> None <-> is_Some mx.
Proof. rewrite is_Some_alt; destruct mx; try easy; congruence. Qed.

Lemma option_dec {A : Type} (mx : option A) : { mx <> None } + { mx = None }.
Proof. destruct mx; now (left + right). Qed.

#[global]
Ltac crush_option X :=
  let Hx := fresh "Hx" in
  destruct (option_dec X) as [Hx | Hx];
  try (rewrite Hx in *; congruence);
  try (let x := fresh "x" in apply not_eq_None_Some in Hx as [x Hx]; rewrite Hx in *)
.

Module StringList <: ListBase.
  Definition A := string.
  Definition eqb := String.eqb.
End StringList.
Module StrListSets <: Sig := SetTheoryList (StringList).
Definition StrListSet := StrListSets.set.

Section Bool.
  Import StrListSets StrListSets.Notations.
  Import List.ListNotations.

  Fixpoint bool_In (X : StrListSet) (x : string) : bool :=
    match X with
    | nil => false
    | y :: Y => if string_dec x y then true else bool_In Y x
    end
  .

  Lemma bool_In_equiv_In X x : (if bool_In X x then True else False) <-> In x X.
  Proof.
    induction X; split; cbn; intros; try congruence || contradiction.
    - destruct (string_dec x a); subst.
      + now left.
      + right; now apply IHX.
    - destruct H; destruct (string_dec x a); subst; trivial; congruence + now apply IHX.
  Qed.

  Lemma bool_eq_equiv_if (x : bool) : (if x then True else False) <-> x = true.
  Proof. now destruct x. Qed.

  Lemma bool_and_equiv_prop (x y : bool) : (x && y)%bool = true <-> (x = true) /\ (y = true).
  Proof. now destruct x,y. Qed.

  Lemma nbool_and_equiv_nprop (x y : bool) : (x && y)%bool = false <-> (x = false) \/ (y = false).
  Proof. destruct x,y; split; cbn in *; (try now (left + right)); intros []; congruence. Qed.

  Lemma bool_or_equiv_prop (x y : bool) : (x || y)%bool = true <-> (x = true) \/ (y = true).
  Proof. destruct x,y; split; try now (left + right). all: intros []; easy. Qed.

  Lemma nbool_or_equiv_prop (x y : bool) : (x || y)%bool = false <-> (x = false) /\ (y = false).
  Proof. now destruct x,y. Qed.

  Lemma bool_eqb_eq (x y : bool) : (Bool.eqb x y = true) <-> x = y.
  Proof. now destruct x, y. Qed.

  Lemma subset_equiv_bool_in_subset (X Y : StrListSet) : X ⊆ Y <-> (forall x, bool_In X x = true -> bool_In Y x = true).
  Proof.
    split; intros H x H0.
    - apply bool_eq_equiv_if in H0; apply bool_In_equiv_In in H0;
      apply bool_eq_equiv_if; apply bool_In_equiv_In; now apply H.
    - apply bool_In_equiv_In in H0; apply bool_eq_equiv_if in H0;
      apply bool_In_equiv_In; apply bool_eq_equiv_if; now apply H.
  Qed.

  Lemma nested_bool_pred (x y : bool) : ((if x then y else false) = true) <-> (andb x y = true).
  Proof. now destruct x,y. Qed.
End Bool.

Require Import Strings.Ascii Numbers.Natural.Peano.NPeano.
Definition ascii_of_nat (n : nat) : ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end
.
Definition string_of_nat (n : nat) : string :=
  let fix string_of_nat_aux (time n : nat) (acc : string) : string :=
    let acc' := String (ascii_of_nat (n mod 10)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
      | 0 => acc'
      | n' => string_of_nat_aux time' n' acc'
      end
    end
  in string_of_nat_aux n n ""%string
.
Definition string_of_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end%string
.

Lemma in_cons_variant (A : Type) (a b : A) (l : list A) : In b (a :: l) <-> a = b \/ In b l.
Proof.
  split.
  - intros H; induction H.
    + left; assumption.
    + right; assumption.
  - intros H; destruct H.
    + rewrite H; cbn; left; reflexivity.
    + now apply in_cons with (a := a) in H.
Qed.

Lemma in_propagate {A : Type} l0 l (L0 L1 : list A) :
  List.In l (L0 ++ l0 :: L1)%list ->
  l <> l0 ->
  List.In l (L0 ++ L1)%list
.
Proof.
  induction L0; cbn; intros H H0.
  - destruct H; subst; easy.
  - destruct H.
    + now left.
    + right. now apply IHL0.
Qed.

Lemma notin_propagate {A : Type} l0 l (L0 L1 : list A) :
  ~List.In l (L0 ++ l0 :: L1)%list ->
  ~List.In l (L0 ++ L1)%list
.
Proof.
  induction L0; cbn; intros H H0.
  - apply H; now right.
  - destruct H0 as [H0 | H0].
    + apply H; now left.
    + apply IHL0; auto.
Qed.

Lemma notin_cons {A : Type} l0 l (L : list A) :
  ~ List.In l0 L ->
  l <> l0 ->
  ~ List.In l0 (L ++ l::nil)%list
.
Proof.
  induction L; cbn; intros H H0 H1.
  - now destruct H1.
  - destruct H1.
    + apply H; now left.
    + apply IHL; auto.
Qed.

Lemma notin_unsnoc' {A : Type} l0 l (L : list A) :
  ~ List.In l0 L ->
  l <> l0 ->
  ~ List.In l0 (L ++ l :: nil)%list
.
Proof.
  induction L; cbn; intros H H0 H1.
  - now destruct H1.
  - apply IHL; auto. destruct H1; auto. exfalso; apply H; now left.
Qed.

Lemma notin_unsnoc {A : Type} l0 l (L : list A) :
  ~ List.In l0 (L ++ l :: nil)%list  ->
  l <> l0 ->
  ~ List.In l0 L
.
Proof.
  induction L; cbn; intros H H0 H1.
  - exact H1.
  - destruct H1.
    + apply H. now left.
    + apply IHL; auto.
Qed.

Lemma in_unsnoc {A : Type} l0 l (L : list A) :
  List.In l0 L ->
  l <> l0 ->
  List.In l0 (L ++ l :: nil)%list
.
Proof.
  induction L; cbn; intros H H0.
  - easy.
  - destruct H.
    + now left.
    + right; apply IHL; auto.
Qed.

Lemma in_unsnoc' {A : Type} l0 l (L0 L1 : list A) :
  List.In l0 (L0 ++ l :: L1)%list ->
  l <> l0 ->
  List.In l0 (L0 ++ L1)
.
Proof.
  induction L0; cbn; intros H H0.
  - now destruct H.
  - destruct H; auto.
Qed.

Fixpoint opt { A : Type } (As : list A) : list(option A) :=
  match As with
  | nil => nil
  | cons a As => Some a :: opt As
  end
.

Lemma opt_nil { A : Type } (As : list A) :
  opt As = nil ->
  As = nil
.
Proof. now induction As. Qed.

Lemma opt_cons { A : Type } (As : list A) Bs (a : option A) :
  opt As = (a :: Bs)%list ->
  As <> nil
.
Proof. induction As; now cbn. Qed.

Lemma opt_some { A : Type } (As : list A) Bs (a : option A) :
  opt As = (a :: Bs)%list ->
  exists a' As', a = Some a' /\ (As = a' :: As')%list /\ Bs = opt As'
.
Proof.
  intros H; apply opt_cons in H as H'.
  revert a Bs H; induction As; try congruence; intros.
  cbn in H. inv H. exists a. exists As. repeat split; reflexivity.
Qed.

Fixpoint zip { A B : Type } (As : list A) (Bs : list B) : option (list (A * B)) :=
  match As, Bs with
  | nil, nil => Some(nil)
  | (a :: As')%list, (b :: Bs')%list =>
    let* (xs) := zip As' Bs' in
    Some ((a, b) :: xs)%list
  | _, _ => None
  end
.

Lemma zip_empty { A B : Type } (As : list A) (Bs : list B) :
  zip As Bs = Some nil ->
  As = nil /\ Bs = nil
.
Proof.
  destruct As; intros H.
  - now destruct Bs.
  - destruct Bs. inv H. cbn in H.
    change ((fun xz => match xz with
            | Some x => Some ((a, b ) :: x)%list
            | None => None
            end = Some nil) (zip As Bs)) in H.
    destruct (zip As Bs); inv H.
Qed.

Lemma zip_cons { A B : Type } (As : list A) (Bs : list B) xs (a : A) (b : B) :
  zip As Bs = Some ((a,b) :: xs)%list ->
  exists As' Bs', As = (a :: As')%list /\ Bs = (b :: Bs')%list /\ Some xs = zip As' Bs'
.
Proof.
  destruct As; intros H.
  - now destruct Bs.
  - destruct Bs. inv H. cbn in H.
    assert (H':=H);
    change ((fun xz => match xz with
            | Some x => Some((a0, b0) :: x)%list
            | None => None
            end = Some ((a, b) :: xs)%list) (zip As Bs)) in H.
    destruct (zip As Bs) in H; inv H.
    exists As. exists Bs. repeat split; eauto.
    remember (zip As Bs) as ys.
    crush_option ys. now inv H'.
Qed.

Lemma zip_singleton { A B : Type } (As : list A) (Bs : list B) (a : A) (b : B) :
  zip As Bs = Some ((a, b) :: nil)%list ->
  (As = a :: nil /\ Bs = b :: nil)%list
.
Proof.
  intros.
  apply zip_cons in H. deex; destruct H as [H1 [H2 H3]]; subst.
  symmetry in H3; apply zip_empty in H3 as [H3a H3b]; subst; easy.
Qed.

Lemma zip_opt_extend { A B : Type } (As : list A) (Bs : list B) Cs (a : A) (b : B) :
  zip (opt As) (opt Bs) = Some Cs ->
  zip (opt (a :: As)) (opt (b :: Bs)) = Some ((Some a, Some b) :: Cs)%list
.
Proof.
  revert As Bs a b; induction Cs; intros.
  - apply zip_empty in H as [Ha Hb]; cbn; subst. now rewrite Ha, Hb; cbn.
  - destruct a as [a' b']. apply zip_cons in H. deex. destruct H as [H1 [H2 H3]].
    cbn; rewrite H1, H2; cbn; now rewrite <- H3.
Qed.
