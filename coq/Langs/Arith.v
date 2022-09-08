Set Implicit Arguments.
Require Import Strings.String Lists.List Program.Equality.
Require Import CSC.Sets CSC.Util.


Class Expr (Expr : Type) := {}.
Class TraceEvent (Ev : Type) := {}.
Class PrimStep (A : Type) (Ev : Type) `{Expr A} `{TraceEvent Ev} := pstep__class : A -> Ev -> A -> Prop.
#[global]
Notation "e0 '--[' a ']-->' e1" := (pstep__class e0 a e1) (at level 82, e1 at next level).

Variant event : Type := empty : event.
#[local]
Instance event__Instance : TraceEvent event := {}.

Inductive expr :=
| lit : nat -> expr
| add : expr -> expr -> expr
.
#[local]
Instance expr__Instance : Expr expr := {}.

Inductive pstep : PrimStep :=
| pstep_add : forall (n1 n2 : nat), (add (lit n1) (lit n2)) --[ empty ]--> (lit(n1 + n2))
.
Global Existing Instance pstep.

Definition pstepf (e : expr) : option (event * expr) :=
  match e with
  | add (lit n1) (lit n2) => Some(empty, lit(n1 + n2))
  | _ => None
  end
.

Lemma equiv_pstep_pstepf (e0 : expr) (a : event) (e1 : expr) :
  e0 --[ a ]--> e1 <-> pstepf e0 = Some(a, e1).
Proof.
  split.
  - induction 1. (* Not an inductive product. *)


Ltac inv H := (inversion H; subst; clear H).

Unset Elimination Schemes.
Inductive arithB {α : Type} : Type :=
  | CLit : nat -> arithB
  | CPlus : α -> α -> arithB
  | CVar : string -> arithB
  | CLetin : string -> α -> α -> arithB
.
Inductive arith := | C :> @arithB arith -> arith.
Set Elimination Schemes.
Definition Lit n := C(CLit n).
Definition Plus a b := C(CPlus a b).
Definition Var x := C(CVar x).
Definition Letin x a b := C(CLetin x a b).

(** Originial inductive hypothesis is too weak, given that Coq doesn't know we recurse over the αs *)
Fixpoint arith_ind (P : arith -> Prop)
                   (lit : forall n : nat, P (Lit n))
                   (plus : forall e0 : arith, P e0 -> forall e1 : arith, P e1 -> P (Plus e0 e1))
                   (var : forall s : string, P (Var s))
                   (letin: forall (s : string) (e0 : arith), P e0 -> forall (e1 : arith), P e1 -> P (Letin s e0 e1))
                   (a : arith)
         : P a.
Proof.
  destruct a as [[]]; eauto.
  - eapply plus; eapply arith_ind; eauto.
  - eapply letin; eapply arith_ind; eauto.
Qed.

Definition to_value v :=
  match v with
  | C(CLit n) => Some(Lit n)
  | _ => None
  end
.
Fixpoint esubst what For inn :=
  match inn with
  | C(CLit _) => inn
  | C(CPlus a b) => Plus (esubst what For a) (esubst what For b)
  | C(CVar x) => if String.eqb what x then For else inn
  | C(CLetin x a b) => Letin x (esubst what For a) (if String.eqb x what then
                                                      b
                                                    else
                                                      esubst what For b)
  end
.

Inductive ty := tyNat.
Definition ty_eqb t0 t1 :=
  match t0, t1 with
  | tyNat, tyNat => true
  end
.
Lemma eqb_eq n m : (ty_eqb n m) = true <-> n = m.
Proof.
  destruct n, m; split; eauto.
Qed.
Lemma eqb_refl n : (ty_eqb n n) = true.
Proof.
  apply eqb_eq; reflexivity.
Qed.
Definition Gamma := list (string * ty).
Module GammaSetM <: ListBase.
  Definition A : Type := (string * ty).
  Definition eqb : A -> A -> bool := fun p0 p1 => let (s0,t0) := p0 in
                                              let (s1,t1) := p1 in
                                              andb (String.eqb s0 s1) (ty_eqb t0 t1).
End GammaSetM.
Module GammaSet <: Sets.Sig := Sets.SetTheoryList GammaSetM.

Import GammaSet.Notations.
Inductive check : Gamma -> arith -> ty -> Prop :=
| Tlit : forall Γ n, check Γ (Lit n) tyNat
| Tbin : forall Γ e0 e1, check Γ e0 tyNat ->
                    check Γ e1 tyNat ->
                    check Γ (Plus e0 e1) tyNat
| Tvar : forall x Γ, (x,tyNat) ∈ Γ ->
                check Γ (Var x) tyNat
| Tlet : forall Γ x e0 e1, check Γ e0 tyNat ->
                      check ((x,tyNat)::Γ) e1 tyNat ->
                      check Γ (Letin x e0 e1) tyNat
.
#[global]
Hint Constructors check : core.

Lemma find_equiv_In x A Γ :
  existsb (GammaSetM.eqb (x,A)) Γ = true <-> (x,A) ∈ Γ.
Proof.
  split; intros H.
  - apply List.existsb_exists in H as [x0 []].
    destruct x0. inv H0. apply Util.bool_and_equiv_prop in H2 as [H2a H2b].
    apply String.eqb_eq in H2a. apply eqb_eq in H2b. subst. exact H.
  - apply List.existsb_exists. exists (x,A). split; try easy. cbn.
    apply Util.bool_and_equiv_prop; split.
    apply String.eqb_refl. apply eqb_refl.
Qed.

Reserved Notation "e0 '-[]->' e1" (at level 81).
Inductive prim_step : arith -> arith -> Prop :=
| Ebin : forall n0 n1, (Plus (Lit n0) (Lit n1)) -[]-> (Lit (n0 + n1))
| Elet : forall x n e0 e, to_value e0 = Some n -> (Letin x e0 e) -[]-> (esubst x n e)
where "e0 '-[]->' e1" := (prim_step e0 e1)
.
Lemma weaken Γ Γ' A e :
  Γ ⊆ Γ' -> check Γ e A -> check Γ' e A.
Proof.
  revert Γ Γ' A; induction e; intros Γ Γ' A H H'; inv H'; eauto.
  - constructor; eauto. eapply IHe2; try eassumption. firstorder.
Qed.

Lemma equiv Γ Γ' A e :
  Γ ≡ Γ' -> check Γ e A -> check Γ' e A.
Proof.
  revert Γ Γ' A; induction e; intros Γ Γ' A H H'; inv H'; eauto.
  - constructor; now apply H.
  - constructor.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto; firstorder.
Qed.

Lemma swap Γ x A y B C e :
  check ((x,A)::(y,B)::Γ) e C -> check ((y,B)::(x,A)::Γ) e C.
Proof.
  revert Γ A B x y C; induction e; intros Γ A B x y C H; inv H; eauto.
  - constructor; firstorder.
  - constructor; eauto. eapply equiv in H6; try eassumption; firstorder.
Qed.

Lemma shadow Γ x A B C e :
  check ((x,A)::(x,B)::Γ) e C -> check ((x,A)::Γ) e C.
Proof.
  revert Γ x A B C; induction e; intros Γ x A B C H0; assert (H0':=H0); inv H0; eauto.
  - inv H0'; constructor. apply find_equiv_In in H2. apply find_equiv_In.
    cbn in *. destruct (String.string_dec s x); subst.
    + rewrite String.eqb_refl in *; cbn in *. (*this will likely break when adding more types*)
      destruct A; now cbn.
    + apply String.eqb_neq in n; rewrite n in *; cbn in *. easy.
  - constructor; eauto. eapply swap. eapply IHe2. eapply equiv in H6; try eassumption.
    firstorder eauto.
Qed.

Lemma substitution Γ x A e e' B :
  check ((x,A)::Γ) e B -> check nil e' A -> check Γ (esubst x e' e) B.
Proof.
  revert Γ x A e' B; induction e; intros Γ x A e' B H0 H1; assert (H0':=H0); subst; cbn in *; inv H0.
  - constructor; eauto.
  - constructor; eauto.
  - apply find_equiv_In in H3. cbn in H3.
    destruct (String.string_dec x s); subst.
    + inv H0'. cbn in H2. rewrite String.eqb_refl in *; cbn in H3.
      destruct H2.
      * inv H. eapply weaken; eauto; easy.
      * (* this will break with more type variants?? *) destruct A. eapply weaken; eauto; easy.
     + apply String.eqb_neq in n; rewrite n. rewrite String.eqb_sym in n. rewrite n in H3.
      cbn in H3. apply find_equiv_In in H3. now constructor.
  - constructor; eauto. destruct (String.string_dec s x).
    + rewrite e, String.eqb_refl. rewrite e in H7. now apply shadow in H7.
    + apply String.eqb_neq in n as ->. eapply IHe2; try eassumption.
      now eapply swap.
Qed.

Lemma prim_preservation e e' ty :
  check nil e ty -> e -[]-> e' -> check nil e' ty.
Proof.
  remember nil as Γ;
  induction 2; subst.
  - inv H; constructor.
  - destruct e0, a; inv H0; inv H; eauto using substitution.
Qed.


(** Evaluation Contexts *)
Inductive Ectx :=
  | HoleCtx : Ectx
  | LPlus : Ectx -> arith -> Ectx
  | RPlus : nat -> Ectx -> Ectx
  | LetCtx : string -> Ectx -> arith -> Ectx
.

Fixpoint fill (K : Ectx) (e : arith) :=
  match K with
  | HoleCtx => e
  | LPlus K' e' => Plus (fill K' e) e'
  | RPlus n K' => Plus (Lit n) (fill K' e)
  | LetCtx x K' e' => Letin x (fill K' e) e'
  end
.
Fixpoint comp_ctx (K K0 : Ectx) :=
  match K with
  | HoleCtx => K0
  | LPlus K' e' => LPlus (comp_ctx K' K0) e'
  | RPlus n K' => RPlus n (comp_ctx K' K0)
  | LetCtx x K' e' => LetCtx x (comp_ctx K' K0) e'
  end
.
Lemma fill_comp (K1 K2 : Ectx) e : fill K1 (fill K2 e) = fill (comp_ctx K1 K2) e.
Proof. induction K1; cbn; congruence. Qed.

Reserved Notation "e0 '=[]->' e1" (at level 81).
Inductive ctx_step : arith -> arith -> Prop :=
| Estep : forall e0 e1 K e0' e1',
    e0' = fill K e0 ->
    e1' = fill K e1 ->
    e0 -[]-> e1 ->
    e0' =[]-> e1'
where "e0 '=[]->' e1" := (ctx_step e0 e1)
.
Reserved Notation "e0 '=[]->*' e1" (at level 81).

Lemma fill_contextual_step e1 e2 K :
  e1 =[]-> e2 -> (fill K e1) =[]-> (fill K e2).
Proof. intros H; inv H; rewrite !fill_comp; econstructor; try reflexivity; assumption. Qed.

Inductive steps : arith -> arith -> Prop :=
| stepsRefl : forall e, e =[]->* e
| stepsTrans : forall e0 e1 e2, e0 =[]-> e1 -> e1 =[]->* e2 -> e0 =[]->* e2
where "e0 '=[]->*' e1" := (steps e0 e1)
.

Definition ctx_typing K A B :=
  forall e, check nil e A -> check nil (fill K e) B.
Ltac solve_ctx_typing := (intros ? ?; cbn; constructor; eauto).

Lemma composition e K A B :
  ctx_typing K A B ->
  check nil e A ->
  check nil (fill K e) B.
Proof. eauto. Qed.

Lemma decomposition e K B :
  check nil (fill K e) B ->
  exists A, ctx_typing K A B /\ check nil e A.
Proof.
  revert e B; induction K; intros e B H; assert(H':=H); inv H; cbn in *; try easy.
  - inv H1. eexists; split; firstorder eauto.
  - inv H3. eexists; split; firstorder eauto.
  - inv H3. eexists; split; firstorder eauto.
  - specialize (IHK e tyNat H3). destruct IHK as [IHA [IHKa IHKb]].
    exists IHA; split; eauto; solve_ctx_typing.
  - specialize (IHK e tyNat H5). destruct IHK as [IHA [IHKa IHKb]].
    exists IHA; split; eauto; solve_ctx_typing.
  - specialize (IHK e tyNat H5). destruct IHK as [IHA [IHKa IHKb]].
    exists IHA; split; eauto; solve_ctx_typing.
Qed.

Lemma ctx_preservation e e' ty :
  check nil e ty -> e =[]-> e' -> check nil e' ty.
Proof.
  intros H0 H1; inv H1.
  eapply decomposition in H0 as [A [H0a H0b]].
  eapply prim_preservation in H3; eauto using composition.
Qed.

Lemma star_preservation e e' ty :
  check nil e ty -> e =[]->* e' -> check nil e' ty.
Proof.
  intros H0 H1. induction H1; eauto.
  apply IHsteps. eapply ctx_preservation in H0; eassumption.
Qed.

Ltac context_solver C := (
                        match goal with
                        | [ H : _ =[]-> _ |- _ =[]-> _ ] =>
                            (eapply fill_contextual_step with (K:=C) in H; cbn in H; eauto)
                        | [ |- _ =[]-> _ ] =>
                            eapply Estep with (K:=C); try now cbn; constructor
                        end
                        ).
Definition is_value e := exists v, to_value e = Some v.
Lemma ctx_progress e ty :
  check nil e ty -> is_value e \/ exists e', e =[]-> e'.
Proof.
  remember nil as Γ; induction 1; subst.
  - left; unfold is_value; cbn; eauto.
  - right. destruct (IHcheck1 eq_refl), (IHcheck2 eq_refl).
    + destruct H1, H2; inv H1; inv H2.
      destruct e0, e1, a, a0; cbn in *; try congruence; inv H3; inv H4.
      exists (Lit (n + n0)); context_solver HoleCtx.
    + destruct H1; inv H1; destruct e0, a; cbn in H4; try congruence; inv H4.
      destruct H2 as [e1' H2]. exists (Plus (Lit n) e1'). context_solver (RPlus n HoleCtx).
    + destruct H1 as [e0' H1]; exists (Plus e0' e1); context_solver (LPlus HoleCtx e1).
    + destruct H1 as [e0' H1]; exists (Plus e0' e1); context_solver (LPlus HoleCtx e1).
  - inv H.
  - right; destruct (IHcheck1 eq_refl). destruct H1 as [v H1].
    + destruct e0, a; cbn in H1; try congruence; inv H1.
      exists (esubst x (Lit n) e1); context_solver HoleCtx.
    + destruct H1 as [e0' H1].
      exists (Letin x e0' e1); context_solver (LetCtx x HoleCtx e1).
Qed.
