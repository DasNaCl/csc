
Require Import Strings.String List Coq.Logic.Decidable.

Ltac inv H := (inversion H; subst; clear H).

Fixpoint delete {A : Type} (x : string) (Δ : list (string * A)) :=
  match Δ with
  | nil => nil
  | (y, v) :: Δ' => if string_dec x y then Δ' else (y,v) :: delete x Δ'
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
  induction Δ; cbn.
  - now left.
  - destruct IHΔ, a.
    + destruct (f a).
      * now right.
      * subst; now left.
    + destruct (f a).
      * now right.
      * now right.
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
