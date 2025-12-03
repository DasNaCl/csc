Set Implicit Arguments.
Require Import Lists.List.
Require Import Classes.RelationClasses Morphisms Setoid.


(** * Set Theory *)
Module Type Sig.
  #[local]
  Parameter A : Type.
  Parameter set : Type.
  Parameter el : forall (x : A) (C : set), Prop.
  Parameter Intersection : forall (C1 C2 : set), set.
  Parameter Union : forall (C1 C2 : set), set.

  Definition subset (C1 C2 : set) := forall x, el x C1 -> el x C2.

  Module Notations.
    Declare Scope set_scope.
    Delimit Scope set_scope with sets.
    Open Scope set_scope.
    Notation "x '∈' A" := (el x A) (at level 50) : set_scope.
    Notation "A '⊆' B" := (subset A B) (at level 50) : set_scope.
    Notation "A '≡' B" := (A ⊆ B /\ B ⊆ A) (at level 50) : set_scope.
    Notation "A '∩' B" := (Intersection A B) (at level 50) : set_scope.
    Notation "A '∪' B" := (Union A B) (at level 50) : set_scope.
  End Notations.
  Import Notations.

  Axiom equiv_is_equal : forall Γ0 Γ1, Γ0 ≡ Γ1 <-> Γ0 = Γ1.

  Axiom intersect : forall (C1 C2 : set) x, x ∈ C1 /\ x ∈ C2.
  Axiom IntroIntersect : forall (X Y : set), forall x, x ∈ X -> x ∈ Y -> x ∈ (X ∩ Y).
  Axiom ElimIntersect : forall (X Y : set), forall x, x ∈ (X ∩ Y) -> x ∈ X /\ x ∈ Y.

  Axiom union : forall (C1 C2 : set) x, x ∈ C1 \/ x ∈ C2.
  Axiom IntroUnion : forall (X Y : set), forall x, x ∈ X \/ x ∈ Y -> x ∈ (X ∪ Y).
  Axiom ElimUnion : forall (X Y : set), forall x, x ∈ (X ∪ Y) -> x ∈ X \/ x ∈ Y.

  Conjecture self_intersect : forall (C : set), C ∩ C = C.
  Conjecture self_union : forall (C : set), C ∪ C = C.
End Sig.

(** * Abstract Sets *)
Module Type SetBase.
  Parameter A : Type.
End SetBase.

Module SetTheoryAbstract (Base : SetBase) <: Sig.
  Definition A := Base.A.
  Definition set := A -> Prop.
  Definition el (x : A) (C : set) := C x.
  Axiom Intersection : forall (C1 C2 : set), set.
  Axiom Union : forall (C1 C2 : set), set.

  Definition subset (C1 C2 : set) := forall x, el x C1 -> el x C2.

  Module Notations.
    Declare Scope set_scope.
    Delimit Scope set_scope with sets.
    Open Scope set_scope.
    Notation "x '∈' A" := (el x A) (at level 50) : set_scope.
    Notation "A '⊆' B" := (subset A B) (at level 50) : set_scope.
    Notation "A '≡' B" := (A ⊆ B /\ B ⊆ A) (at level 50) : set_scope.
    Notation "A '∩' B" := (Intersection A B) (at level 50) : set_scope.
    Notation "A '∪' B" := (Union A B) (at level 50) : set_scope.
  End Notations.
  Import Notations.

  Axiom equiv_is_equal : forall Γ0 Γ1, Γ0 ≡ Γ1 <-> Γ0 = Γ1.

  Axiom intersect : forall (C1 C2 : set) x, x ∈ C1 /\ x ∈ C2.
  Axiom IntroIntersect : forall (X Y : set), forall x, x ∈ X -> x ∈ Y -> x ∈ (X ∩ Y).
  Axiom ElimIntersect : forall (X Y : set), forall x, x ∈ (X ∩ Y) -> x ∈ X /\ x ∈ Y.

  Axiom union : forall (C1 C2 : set) x, x ∈ C1 \/ x ∈ C2.
  Axiom IntroUnion : forall (X Y : set), forall x, x ∈ X \/ x ∈ Y -> x ∈ (X ∪ Y).
  Axiom ElimUnion : forall (X Y : set), forall x, x ∈ (X ∪ Y) -> x ∈ X \/ x ∈ Y.

  Lemma self_intersect (C : set) : C ∩ C = C.
  (* begin hide *)
  Proof.
    apply equiv_is_equal; split; intros x H.
    - apply ElimIntersect in H; apply H.
    - apply IntroIntersect; trivial.
  Qed.
  (* end hide *)
  Lemma self_union (C : set) :
    C ∪ C = C.
  (* begin hide *)
  Proof.
    apply equiv_is_equal; split; intros x H.
    - apply ElimUnion in H as []; trivial.
    - apply IntroUnion; left; trivial.
  Qed.
  (* end hide *)
End SetTheoryAbstract.

(** * Lists as Sets *)
Module Type ListBase.
  Parameter A : Type.
  Parameter eqb : A -> A -> bool.
End ListBase.

Module SetTheoryList (M : ListBase) <: Sig.
  Definition A := M.A.
  Definition set := list A.

  Definition el (x : A) (C : set) := List.In x C.
  Fixpoint Intersection (C1 C2 : set) : set :=
    match C1 with
    | nil => nil
    | a1 :: C1' => match List.find (M.eqb a1) C2 with
                 | Some _ => a1 :: (Intersection C1' C2)
                 | None => Intersection C1' C2
                 end
    end
  .
  Definition Union (C1 C2 : set) := C1 ++ C2.

  Definition subset (C1 C2 : set) := forall x, el x C1 -> el x C2.
  Definition equiv (C1 C2 : set) := subset C1 C2 /\ subset C2 C1.

  Module Notations.
    Declare Scope set_scope.
    Delimit Scope set_scope with sets.
    Open Scope set_scope.
    Notation "x '∈' A" := (el x A) (at level 50) : set_scope.
    Notation "A '⊆' B" := (subset A B) (at level 81) : set_scope.
    Notation "A '≡' B" := (equiv A B) (at level 81) : set_scope.
    Notation "A '∩' B" := (Intersection A B) (at level 50) : set_scope.
    Notation "A '∪' B" := (Union A B) (at level 50) : set_scope.
  End Notations.
  Import Notations.

  #[global]
  Instance subset_refl : Reflexive (subset).
  Proof. now intros Γ x H. Qed.
  #[global]
  Instance subset_tr : Transitive (subset).
  Proof. intros x y z H0 H1 a H2; apply H1; now apply H0. Qed.
  #[global]
  Instance equiv_is_equiv : Equivalence (equiv).
  Proof.
    split.
    - (* refl  *) now split.
    - (* symm  *) split; firstorder eauto.
    - (* trans *) split; firstorder eauto.
  Qed.
  (* Extensionality axiom *)
  Axiom equiv_is_equal : forall Γ0 Γ1, Γ0 ≡ Γ1 <-> Γ0 = Γ1.

  Lemma nil_eq_sets (Γ1 Γ2 : set) :
    nil = Γ1 ++ Γ2 -> nil = Γ1 /\ nil = Γ2.
  Proof. intros; induction Γ1; firstorder; inversion H. Qed.

  #[global]
  Instance equiv_commutes (Γ : set) : Proper (equiv ==> Basics.flip Basics.impl)
                                        (fun l : set => l ≡ Γ).
  Proof. intros Γ0 Γ1 H H0; etransitivity; eauto. Qed.

  Lemma subset_swap_nil (Γ1 Γ3 : set) :
    (Γ1 ++ nil) ⊆ Γ3 -> (nil ++ Γ1) ⊆ Γ3.
  Proof. intros H; cbn; now rewrite app_nil_r in H. Qed.

  Lemma subset_swap_cons a (Γ1 Γ3 : set) :
    (Γ1 ++ a :: nil) ⊆ Γ3 -> (a :: Γ1) ⊆ Γ3.
  Proof.
    intros H0 x H1; apply H0; destruct H1; subst; induction Γ1; cbn; firstorder.
  Qed.
  Lemma subset_swap (Γ1 Γ2 Γ3 : set) :
    Γ1 ++ Γ2 ⊆ Γ3 -> Γ2 ++ Γ1 ⊆ Γ3.
  Proof.
    intros H0 x H1; apply H0. induction Γ2; cbn in *.
    now rewrite app_nil_r. destruct H1; subst.
    clear IHΓ2; induction Γ1; cbn; firstorder.
    clear IHΓ2 H0. induction Γ2; cbn in *; firstorder.
    eapply subset_swap_nil in H. exact H. clear H; rewrite app_nil_r.
    induction Γ1; cbn; firstorder eauto.
    subst; clear IHΓ2; induction Γ1; firstorder eauto.
    clear H; induction Γ1; firstorder eauto.
  Qed.
  Lemma subset_cons_swap a b (Γ1 Γ2 : set) :
    a :: b :: Γ1 ⊆ Γ2 -> b :: a :: Γ1 ⊆ Γ2.
  Proof. firstorder eauto. Qed.
  Lemma subset_weak a (Γ1 Γ2 : set) :
    a :: Γ1 ⊆ Γ2 -> Γ1 ⊆ Γ2.
  Proof. firstorder eauto. Qed.
  Lemma cons_subset a (Γ1 Γ2 : set) :
    Γ1 ⊆ Γ2 -> a :: Γ1 ⊆ a :: Γ2.
  Proof. firstorder eauto. Qed.
  Lemma subset_of_cons a (Γ : set) :
    Γ ⊆ a :: Γ.
  Proof. induction Γ; firstorder. Qed.
  Lemma cons_subset_eq a a0 :
    (a :: nil) ⊆ (a0 :: (nil : set)) -> a = a0.
  Proof. intros H; specialize (H a); firstorder eauto. Qed.
  Lemma subset_nil (Γ : set) :
    Γ ⊆ nil -> Γ = nil.
  Proof. induction Γ; firstorder; exfalso; apply (H a); now left. Qed.

  Axiom intersect : forall (C1 C2 : set) x, x ∈ C1 /\ x ∈ C2.
  Axiom IntroIntersect : forall (X Y : set), forall x, x ∈ X -> x ∈ Y -> x ∈ (X ∩ Y).
  Axiom ElimIntersect : forall (X Y : set), forall x, x ∈ (X ∩ Y) -> x ∈ X /\ x ∈ Y.

  Axiom union : forall (C1 C2 : set) x, x ∈ C1 \/ x ∈ C2.
  Axiom IntroUnion : forall (X Y : set), forall x, x ∈ X \/ x ∈ Y -> x ∈ (X ∪ Y).
  Axiom ElimUnion : forall (X Y : set), forall x, x ∈ (X ∪ Y) -> x ∈ X \/ x ∈ Y.

  Lemma self_intersect (C : set) : C ∩ C = C.
  (* begin hide *)
  Proof.
    apply equiv_is_equal; split; intros x H.
    - apply ElimIntersect in H; apply H.
    - apply IntroIntersect; trivial.
  Qed.
  (* end hide *)
  Lemma self_union (C : set) :
    C ∪ C = C.
  (* begin hide *)
  Proof.
    apply equiv_is_equal; split; intros x H.
    - apply ElimUnion in H as []; trivial.
    - apply IntroUnion; left; trivial.
  Qed.
  (* end hide *)

  #[global]
  Instance equiv_subset_proper {T : Type} Γ0 : Proper (equiv ==> Basics.flip Basics.impl)
                                      (fun (Γ : set) => Γ ⊆ Γ0).
  Proof.
    intros Γ1 Γ2 H0 H1 x H2.
    now apply H1, H0.
  Qed.
  #[global]
  Instance equiv_supset_proper {T : Type} Γ0 : Proper (equiv ==> Basics.flip Basics.impl)
                                      (fun (Γ : set) => Γ0 ⊆ Γ).
  Proof.
    intros Γ1 Γ2 H0 H1 x H2.
    now apply H0, H1.
  Qed.
End SetTheoryList.
