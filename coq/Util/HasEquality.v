Set Implicit Arguments.
Require Import Setoid.

Class HasEquality (A : Type) := {
  eq : A -> A -> bool ;
  eqb_eq : forall (a b : A), eq a b = true <-> a = b ;
}.
#[global]
Infix "==" := eq (at level 81, left associativity).

Lemma eq_refl { A : Type } { H : HasEquality A } (a : A) :
  eq a a = true.
Proof. now apply eqb_eq. Qed.

Lemma eqb_dec { A : Type } { H : HasEquality A } (a x : A) :
  eq a x = true \/ eq a x = false.
Proof. destruct (eq a x); now (left + right). Qed.

Lemma eqb_equiv_neqb { A : Type } { H : HasEquality A } (a b : A) :
  eq a b = true <-> negb(eq a b) = negb true.
Proof.
  split; intros H0.
  - rewrite H0; now cbn.
  - destruct (eq a b); cbn in H0; auto.
Qed.

Lemma neqb_equiv_eqb { A : Type } { H : HasEquality A } (a b : A) :
  eq a b = false <-> negb(eq a b) = negb false.
Proof.
  split; intros H0.
  - rewrite H0; now cbn.
  - destruct (eq a b); cbn in H0; auto.
Qed.

Lemma neqb_neq { A : Type } { H : HasEquality A } (a b : A) :
  eq a b = false <-> a <> b.
Proof.
  split; intros H0.
  - intros H1; subst; now rewrite eq_refl in H0.
  - rewrite neqb_equiv_eqb; assert ((eq a b = true) -> False) by (intros H1; apply H0; now apply eqb_eq in H1);
    destruct (eq a b); now cbn in *.
Qed.
Lemma eq_dec { A : Type } { H : HasEquality A } (a x : A) :
  a = x \/ a <> x.
Proof.
  destruct (eqb_dec a x).
  - apply eqb_eq in H0; now left.
  - apply neqb_neq in H0; now right.
Qed.

Lemma eq_sym { A : Type } { H : HasEquality A } (a b : A) :
  eq a b = eq b a.
Proof.
  destruct (eq_dec a b).
  - subst; now rewrite eq_refl.
  - apply neqb_neq in H0 as H0'; rewrite H0'.
    destruct (eq_dec b a).
    + subst; congruence.
    + now apply neqb_neq in H1 as ->.
Qed.

#[global]
Hint Resolve eq_refl eqb_dec eqb_equiv_neqb neqb_equiv_eqb neqb_neq eq_dec : core.

Require Import CSC.Util.Convenience.

Module BoolEqb.
#[export]
Instance eqb__Instance : HasEquality bool := {
  eq := Bool.eqb ;
  eqb_eq := bool_eqb_eq ;
}.
End BoolEqb.

Ltac eq_to_defeq eq := repeat match goal with
  | [H: context E [eq ?x ?x0] |- _] =>
    let new := context E [(x == x0)] in
    change new in H
  | [ |- context E [eq ?x ?x0] ] =>
    let new := context E [(x == x0)] in
    change new
  | [H: (?x == ?x0) = true |- _ ] =>
    apply eqb_eq in H; subst
  | [H: context E [ andb ?x ?y ] |- _] =>
    rewrite bool_and_equiv_prop in H;
    destruct H; subst
  | [ |- context E [ andb ?x ?y ] ] =>
    rewrite bool_and_equiv_prop
  | [ |- (?x == ?x) = true ] =>
    apply eq_refl
  end; try easy
.
