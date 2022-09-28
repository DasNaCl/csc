Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano List Coq.Logic.Decidable.

#[global]
Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end.

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
End Bool.

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
