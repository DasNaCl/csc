Set Implicit Arguments.
Require Import Strings.String List Coq.Logic.Decidable.

Ltac inv H := (inversion H; subst; clear H).

Definition delete {A : Type} (x : string) (Δ : list (string * A)) :=
  match Δ with
  | nil => nil
  | (y, v) :: Δ' => if string_dec x y then Δ' else (y,v) :: Δ' (* delete x Δ' *)
  end
.
Fixpoint find {A B : Type} (f : A -> bool) (Δ : list (A * B)) :=
  match Δ with
  | nil => None
  | (y, v) :: Δ' => if f y then Some v else find f Δ'
  end
.
Lemma find_dec {A B : Type} (f : A -> bool) (Δ : list (A * B)) :
  { find f Δ = None } + { find f Δ <> None }.
Proof.
  induction Δ; cbn; try now left.
  destruct IHΔ, a, (f a); repeat ((try now right); (try now left)).
Defined.
Fixpoint grow (H : list nat) (n : nat) :=
  match n with
  | 0 => H
  | S n' => 0 :: (grow H n')
  end
.
Fixpoint replace { A } (n : nat) (H : list A) (a : A) :=
  match H with
  | nil => nil
  | cons a' H' => match n with
                 | 0 => cons a H'
                 | S n' => cons a' (replace n' H' a)
                 end
  end
.

Require Import CSC.Sets.
Module StringList <: ListBase.
  Definition A := string.
  Definition eqb := String.eqb.
End StringList.
Module StrListSets <: Sig := SetTheoryList (StringList).
Definition StrListSet := StrListSets.set.
Section Bool.

Import StrListSets StrListSets.Notations.
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
  - destruct H; destruct (string_dec x a); subst; trivial.
    congruence. now apply IHX.
Qed.
Lemma bool_eq_equiv_if (x : bool) : (if x then True else False) <-> x = true.
Proof. now destruct x. Qed.
Lemma bool_and_equiv_prop (x y : bool) : (x && y)%bool = true <-> (x = true) /\ (y = true).
Proof. now destruct x,y. Qed.

Lemma subset_equiv_bool_in_subset (X Y : StrListSet) : X ⊆ Y <-> (forall x, bool_In X x = true -> bool_In Y x = true).
Proof.
  split.
  - intros H x H0; apply bool_eq_equiv_if in H0; apply bool_In_equiv_In in H0;
    apply bool_eq_equiv_if; apply bool_In_equiv_In; now apply H.
  - intros H x H0; apply bool_In_equiv_In in H0; apply bool_eq_equiv_if in H0;
    apply bool_In_equiv_In; apply bool_eq_equiv_if; now apply H.
Qed.
Lemma nested_bool_pred (x y : bool) : ((if x then y else false) = true) <-> (andb x y = true).
Proof. now destruct x,y. Qed.

Definition is_Some {A : Type} (mx : option A) := exists x, mx = Some x.

Lemma is_Some_alt {A : Type} (mx : option A) :
  is_Some mx <-> match mx with Some _ => True | None => False end.
Proof.
  unfold is_Some; destruct mx; split; try easy; try now exists a.
  intros; now destruct H.
Qed.

Lemma not_eq_None_Some {A : Type} (mx : option A) : mx <> None <-> is_Some mx.
Proof. rewrite is_Some_alt; destruct mx; try easy; congruence. Qed.

End Bool.

(** Since we only care about security properties anyways, it's fine to stay in "traces are lists"-land *)
Inductive tracepref (Ev : Type) : Type :=
| Tnil : tracepref Ev
| Tcons (e : Ev) (a : tracepref Ev) : tracepref Ev
.
