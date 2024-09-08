Set Implicit Arguments.
Require Import ZArith List Program FunctionalExtensionality.
From RecordUpdate Require Import RecordSet.

Definition var : Type := nat.
Definition loc : Type := nat.

Definition total_map (B:Type) := var -> B.
Definition t_empty {B:Type} (v : B) : total_map B :=
  (fun _ => v)
.
Definition t_update {B:Type} (m : total_map B)
                    (x : var) (v : B) :=
  fun x' => if PeanoNat.Nat.eqb x x' then v else m x'.

Lemma t_apply_empty: forall B x v, @t_empty B v x = v.
Proof. easy. Qed.
Lemma t_update_eq : forall B (m: total_map B) x v,
  (t_update m x v) x = v.
Proof.
  intros; unfold t_update; now rewrite PeanoNat.Nat.eqb_refl.
Qed.
Theorem t_update_neq : forall (B:Type) v x1 x2 (m : total_map B),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros B v x1 x2 m H; unfold t_update; now apply PeanoNat.Nat.eqb_neq in H as ->.
Qed.
Lemma t_update_shadow : forall B (m: total_map B) v1 v2 x,
    t_update (t_update m x v1) x v2 = t_update m x v2.
Proof.
  intros; unfold t_update; extensionality y; now destruct (PeanoNat.Nat.eqb x y).
Qed.
Theorem t_update_same : forall B x (m : total_map B), t_update m x (m x) = m.
Proof.
  intros; unfold t_update; extensionality y.
  destruct (PeanoNat.Nat.eq_dec x y) as [H0|H0]; subst.
  - now rewrite PeanoNat.Nat.eqb_refl.
  - now apply PeanoNat.Nat.eqb_neq in H0 as ->.
Qed.
Theorem t_update_permute : forall (B:Type) v1 v2 x1 x2 (m : total_map B),
  x2 <> x1 ->
  (t_update (t_update m x2 v2) x1 v1) = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros; unfold t_update; extensionality y.
  destruct (PeanoNat.Nat.eq_dec x1 y) as [H0|H0]; subst.
  - rewrite PeanoNat.Nat.eqb_refl; now apply PeanoNat.Nat.eqb_neq in H as ->.
  - apply PeanoNat.Nat.eqb_neq in H0 as ->; now destruct (PeanoNat.Nat.eqb x2 y).
Qed.
Theorem t_update_rotate : forall (B:Type) v1 v2 v3 x1 x2 x3 (m : total_map B),
  x2 <> x1 ->
  x3 <> x2 ->
  x3 <> x1 ->
  (t_update (t_update (t_update m x3 v3) x2 v2) x1 v1) = (t_update (t_update (t_update m x2 v2) x1 v1) x3 v3).
Proof.
  intros B v1 v2 v3 x1 x2 x3 m H0 H1 H2; unfold t_update; extensionality y.
  destruct (PeanoNat.Nat.eq_dec x1 y) as [->|H'].
  - rewrite PeanoNat.Nat.eqb_refl; now apply PeanoNat.Nat.eqb_neq in H2 as ->.
  - apply PeanoNat.Nat.eqb_neq in H' as ->.
    destruct (PeanoNat.Nat.eq_dec x2 y) as [->|H'].
    + rewrite PeanoNat.Nat.eqb_refl; now apply PeanoNat.Nat.eqb_neq in H1 as ->.
    + now apply PeanoNat.Nat.eqb_neq in H' as ->.
Qed.
Definition partial_map (B:Type) := total_map (option B).
Definition empty {B:Type} : partial_map B := t_empty None.
Definition update {B:Type} (m : partial_map B) (x : var) (v : B) :=
  t_update m x (Some v)
.
Lemma apply_empty : forall B x, @empty B x = None.
Proof.
  intros; unfold empty; now rewrite t_apply_empty.
Qed.
Lemma update_eq : forall B (m: partial_map B) x v,
  (update m x v) x = Some v.
Proof.
  intros; unfold update; now rewrite t_update_eq.
Qed.
Theorem update_neq : forall (B:Type) v x1 x2 (m : partial_map B),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros; unfold update; now rewrite t_update_neq.
Qed.
Lemma update_shadow : forall B (m: partial_map B) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros; unfold update; now rewrite t_update_shadow.
Qed.
Theorem update_same : forall B v x (m : partial_map B),
  m x = Some v ->
  update m x v = m.
Proof.
  intros B v x m H0; unfold update; rewrite <- H0; apply t_update_same.
Qed.
Theorem update_permute : forall (B:Type) v1 v2 x1 x2 (m : partial_map B),
  x2 <> x1 ->
  (update (update m x2 v2) x1 v1) = (update (update m x1 v1) x2 v2).
Proof.
  intros; unfold update; now apply t_update_permute.
Qed.
Theorem update_rotate : forall (B:Type) v1 v2 v3 x1 x2 x3 (m : partial_map B),
  x2 <> x1 ->
  x3 <> x2 ->
  x3 <> x1 ->
  (update (update (update m x3 v3) x2 v2) x1 v1) = (update (update (update m x2 v2) x1 v1) x3 v3).
Proof.
  intros; unfold update; now apply t_update_rotate.
Qed.
Definition includedin {B} (m1 m2 : partial_map B) :=
  forall a b, m1 a = Some b -> m2 a = Some b
.
Lemma includedin_update B (m1 m2 : partial_map B) (a : var) (b : B) :
  includedin m1 m2  ->
  includedin (update m1 a b) (update m2 a b).
Proof.
  unfold includedin; intros;
  match goal with
  | [ |- (update _ ?a _) ?x = Some _ ] => destruct (PeanoNat.Nat.eq_dec a x)
  end; subst; (rewrite update_eq in * + rewrite update_neq in *); auto.
Qed.
Lemma includedin_empty B (m : partial_map B) : includedin empty m.
Proof.
  unfold includedin; intros;
  match goal with
  | [H: empty _ = Some _ |- _] => cbv in H; inversion H
  end.
Qed.
Lemma includedin_cons_propagate B (m1 m2 : partial_map B) (a : var) (b : B) :
  includedin (update m1 a b) m2 ->
  includedin (update m1 a b) (update m2 a b).
Proof.
  unfold includedin; intros H0 a0 b0 H1.
  destruct (PeanoNat.Nat.eq_dec a a0) as [H2|H2].
  - subst; rewrite update_eq in H1; inversion H1; subst; now rewrite update_eq.
  - rewrite update_neq in H1; trivial. rewrite update_neq; trivial.
    eapply H0; rewrite update_neq; trivial.
Qed.
Lemma includedin_cons_swap B (m : partial_map B) (a0 a1 : var) (b0 b1 : B) :
  a0 <> a1 ->
  includedin (update (update m a0 b0) a1 b1) (update (update m a1 b1) a0 b0).
Proof.
  unfold includedin; intros Hne a _ <-.
  destruct (PeanoNat.Nat.eq_dec a a0) as [->|H].
  - rewrite update_eq; trivial. unfold update, t_update.
    rewrite PeanoNat.Nat.eqb_sym; apply PeanoNat.Nat.eqb_neq in Hne as ->;
    rewrite PeanoNat.Nat.eqb_refl; reflexivity.
  - unfold update, t_update. rewrite PeanoNat.Nat.eqb_sym.
    now apply PeanoNat.Nat.eqb_neq in H as ->.
Qed.
#[global]
Notation "∅" := (empty).
#[global]
Notation "a '↦' b '◘' M" := (update M a b) (at level 80, b at next level).

Definition fresh (xs:list var) : var := 1 + List.list_max xs.
Lemma fresh_above_any (x : var) (xs : list var) :
  List.In x xs -> x < fresh xs
.
Proof.
  intros; induction xs; cbn; try now inversion H.
  destruct H; apply PeanoNat.Nat.lt_succ_r.
  - subst; apply PeanoNat.Nat.le_max_l.
  - specialize (IHxs H); unfold fresh in *.
    apply PeanoNat.Nat.le_succ_l, le_S_n in IHxs.
    transitivity (List.list_max xs); eauto using PeanoNat.Nat.le_max_r.
Qed.
Lemma above_fresh_not_in (y : var) (xs : list var) : 
  fresh xs <= y -> ~ List.In y xs
.
Proof. 
  intros H0 H1%fresh_above_any%PeanoNat.Nat.lt_nge; contradiction.
Qed.
Corollary fresh_not_in (xs : list var) :
  ~ List.In (fresh xs) xs
.
Proof.
  eauto using above_fresh_not_in.
Qed.
Definition fresh2 (xs ys : list var) := 
  max (fresh xs) (fresh ys)
.
Lemma above_fresh2_not_in (x : var) (xs ys : list var) :
  fresh2 xs ys <= x ->
  ~List.In x xs /\ ~List.In x ys
.
Proof.
  repeat split; eapply above_fresh_not_in; unfold fresh2 in *; trivial;
  transitivity (Nat.max (fresh xs) (fresh ys)); trivial;
  (apply PeanoNat.Nat.le_max_l + apply PeanoNat.Nat.le_max_r).
Qed.
Lemma fresh2_not_in (xs ys : list var) x :
  x = (fresh2 xs ys) ->
  ~List.In x xs /\ ~List.In x ys
.
Proof.
  intros ->; eapply above_fresh2_not_in; trivial.
Qed.

(** ** STLC+Ref *)
Inductive sty : Type :=
  | Bool
  | Num
.
Inductive ty : Type :=
  | Simple : sty -> ty
  | Ptr : ty -> ty
  | Arrow : ty -> ty -> ty
.
Definition stdom (t : sty) : Type :=
  match t with
  | Bool => bool
  | Num => Z
  end
.
Fixpoint dom (t : ty) : Type :=
  match t with
  | Simple s => stdom s
  | Ptr _ => loc
  | Arrow a b => (dom a) -> (dom b)
  end
.
Inductive ev : Type :=
  | eAlloc : loc -> sty -> nat -> ev (* where, what, how many *)
  | eDealloc : loc -> ev 
.
Definition Event := option ev.
Notation "'ε'" := (None : Event).
Inductive expr : Type := 
  | enum  : Z -> expr         (* constants 0,1,2,3,... *)
  | ebool : bool -> expr        (* constants 0,1,2,3,... *)
  | eloc : nat -> expr          (* location on heap *)
  | ebvar : var -> expr         (* bound variables *)
  | efvar : var -> expr         (* "free" variables, bound by a context *)
  | eapp : expr -> expr -> expr (* function application f a *)
  | elam : expr -> expr         (* lambda functions λ.e *)
  | erec : expr -> expr         (* lambda functions λ.e *)
  | eif : expr -> expr -> expr -> expr (* conditionals *)
  | enew : sty -> expr -> expr  (* allocates sty on heap *)
  | edel : expr -> expr         (* allocates sty on heap *)
.
Inductive value : expr -> Prop :=
  | vnum : forall n, value (enum n)
  | vbool : forall b, value (ebool b)
  | vlam : forall b, value (elam b)
  | vrec : forall b, value (erec b)
  | vloc : forall n, value (eloc n)
.
Hint Constructors expr value : core.

Fixpoint fv (e : expr) : list var := 
  match e with
  | enum n => nil
  | ebool b => nil
  | eloc l => nil
  | ebvar x => nil
  | efvar x => cons x nil
  | eapp a b => List.app (fv a) (fv b)
  | elam a => fv a
  | erec a => fv a
  | eif a b c => List.app (fv a) (List.app (fv b) (fv c)) 
  | enew _ a => fv a
  | edel a => fv a
  end
.
Fixpoint lc_at (k : var) (e : expr) : Prop :=
  match e with
  | enum n => True
  | ebool b => True
  | eloc l => True
  | ebvar x => x < k
  | efvar _ => True
  | eapp a b => lc_at k a /\ lc_at k b
  | elam a => lc_at (S k) a
  | erec a => lc_at (S(S k)) a
  | eif a b c => lc_at k a /\ lc_at k b /\ lc_at k c
  | enew _ a => lc_at k a
  | edel a => lc_at k a
  end
.
Lemma lc_at_le k x e :
  k < x ->
  lc_at k e ->
  lc_at x e
.
Proof.
  revert k x; induction e; cbn; intros; trivial.
  - etransitivity; eauto.
  - split; (eapply IHe1 + eapply IHe2); destruct H0; eauto.
  - eapply IHe; try exact H0; now apply le_n_S.
  - eapply IHe; try exact H0; now do 2 apply le_n_S.
  - repeat split; firstorder eauto.
  - eapply IHe; try exact H0; assumption.
  - eapply IHe; try exact H0; assumption.
Qed.
Lemma lc_at_Sx x e :
  lc_at x e ->
  lc_at (S x) e
.
Proof.
  apply lc_at_le; constructor.
Qed.

(** An expression can be "opened" by swapping a bound variable k 
    for a free variable y, thus "opening" up e. *)
Fixpoint open_at (k y : var) (e : expr) : expr :=
  match e with
  | enum n => enum n 
  | ebool b => ebool b 
  | eloc l => eloc l
  | ebvar x => if Nat.eqb x k then efvar y else ebvar x
  | efvar x => efvar x
  | eapp a b => eapp (open_at k y a) (open_at k y b)
  | elam b => elam (open_at (S k) y b)
  | erec b => erec (open_at (S(S k)) y b)
  | eif a b c => eif (open_at k y a) (open_at k y b) (open_at k y c)
  | enew s a => enew s (open_at k y a)
  | edel a => edel (open_at k y a)
  end
.
Definition unbind (x : var) (e : expr) : expr := open_at O x e.

Fixpoint substFV (ewhat : var) (efor ein : expr) : expr :=
  match ein with
  | enum n => enum n
  | ebool b => ebool b
  | eloc l => eloc l
  | ebvar x => ebvar x
  | efvar x => if Nat.eqb x ewhat then efor else efvar x 
  | eapp a b => eapp (substFV ewhat efor a) (substFV ewhat efor b)
  | elam b => elam (substFV ewhat efor b)
  | erec b => erec (substFV ewhat efor b)
  | eif a b c => eif (substFV ewhat efor a) (substFV ewhat efor b) (substFV ewhat efor c)
  | enew s a => enew s (substFV ewhat efor a)
  | edel a => edel (substFV ewhat efor a)
  end
.
Fixpoint substBV (ewhat : var) (efor ein : expr) : expr :=
  match ein with
  | enum n => enum n
  | ebool b => ebool b
  | eloc l => eloc l
  | ebvar x => if Nat.eqb x ewhat then efor else ebvar x 
  | efvar x => efvar x
  | eapp a b => eapp (substBV ewhat efor a) (substBV ewhat efor b)
  | elam b => elam (substBV (S ewhat) efor b)
  | erec b => erec (substBV (S(S ewhat)) efor b)
  | eif a b c => eif (substBV ewhat efor a) (substBV ewhat efor b) (substBV ewhat efor c)
  | enew s a => enew s (substBV ewhat efor a)
  | edel a => edel (substBV ewhat efor a)
  end
.
Lemma fv_open_at_subsets j x e :
  (forall y, List.In y (fv e) -> List.In y (fv (open_at j x e)))
.
Proof.
  revert j x; induction e; cbn; trivial; intros; try contradiction.
  - apply List.in_app_or in H as [H|H]; apply List.in_or_app;
    (now (left + right); eauto).
  - now eapply IHe.
  - now eapply IHe.
  - repeat apply List.in_app_or in H as [H|H]; apply List.in_or_app;
    (try now (left; eauto));
    right; apply List.in_or_app; try now ((left + right); eauto).
Qed.
Lemma fv_unbind_subsets x e :
  (forall y, List.In y (fv e) -> List.In y (fv (unbind x e)))
.
Proof. 
  intros; eauto using fv_open_at_subsets.
Qed.
Lemma fv_substBV_subsets x v e :
  lc_at 0 v ->
  (forall y, List.In y (fv e) -> List.In y (fv (substBV x v e)))
.
Proof. 
  revert x; induction e; cbn; intros; trivial.
  - destruct (PeanoNat.Nat.eqb v0 x); cbn; trivial; easy. 
  - eapply List.in_or_app; apply List.in_app_or in H0 as [H0|H0];
    now ((left; eapply IHe1) + (right; eapply IHe2)); eauto.
  - eapply IHe; eauto.
  - eapply IHe; eauto.
  - eapply List.in_or_app; apply List.in_app_or in H0 as [H0|H0].
    now (left; eapply IHe1; eauto).
    right. 
    eapply List.in_or_app; apply List.in_app_or in H0 as [H0|H0];
    (try now (left; eapply IHe2; eauto));
    now (right; eapply IHe3; eauto).
  - now eapply IHe.
  - now eapply IHe.
Qed.
Lemma substBV_fv_in k x v e :
  ~ In x (fv v) ->
  In x (fv (substBV k v e)) <-> In x (fv e)
.
Proof. 
  intros H; split; revert k H.
  - induction e; cbn; intros k H0 H1; eauto; try easy.
    + destruct (Nat.eqb v0 k); contradiction.
    + apply List.in_or_app; apply List.in_app_or in H1 as [H1|H1];
      now ((left + right); eauto).
    + eapply List.in_or_app; apply List.in_app_or in H1 as [H1|H1];
      try now left; eauto.
      right. apply List.in_or_app; apply List.in_app_or in H1 as [H1|H1];
      now ((left + right); eauto).
  - induction e; cbn; intros k H0 H; cbn; eauto; try easy.
    + apply List.in_or_app; apply List.in_app_or in H as [H|H];
      now ((left + right); eauto).
    + eapply List.in_or_app; apply List.in_app_or in H as [H|H];
      try now left; eauto.
      right. apply List.in_or_app; apply List.in_app_or in H as [H|H];
      now ((left + right); eauto).
Qed.
Lemma open_at_substBV k y e :
  open_at k y e = substBV k (efvar y) e
.
Proof.
  revert k; induction e; intros; cbn; eauto; try now rewrite IHe.
  now rewrite IHe1, IHe2.
  now rewrite IHe1, IHe2, IHe3.
Qed.
Lemma lc_at_open_at k y e :
  lc_at k (open_at k y e) -> 
  lc_at (S k) e 
.
Proof.
  revert k y; induction e; cbn; intros k y H; eauto.
  - destruct (PeanoNat.Nat.eq_dec v k) as [->|H'];
    try eapply PeanoNat.Nat.lt_succ_diag_r;
    eapply PeanoNat.Nat.eqb_neq in H'; rewrite H' in H; cbn in H;
    transitivity k; eauto.
  - destruct H; eauto.
  - destruct H as [Ha [Hb Hc]]; repeat split; eauto.
Qed.
Lemma lc_at_unbind y e :
  lc_at 0 (unbind y e) -> 
  lc_at 1 e 
.
Proof.
  apply lc_at_open_at.
Qed.
Lemma lc_at_unbind2 f y e :
  lc_at 0 (open_at 0 f (open_at 1 y e)) -> 
  lc_at 2 e 
.
Proof.
  intros H; do 2 eapply lc_at_open_at; eauto.
Qed.
Lemma unbind_substBV y e :
  unbind y e = substBV O (efvar y) e
.
Proof.
  eapply open_at_substBV.
Qed.
Lemma substBV_substFV_unbind k i v e :
  ~ List.In k (fv e) ->
  substBV i v e = substFV k v (open_at i k e)
.
Proof.
  revert i; induction e; intros; cbn; eauto; try now rewrite IHe.
  - destruct (Nat.eqb v0 i); cbn; try rewrite PeanoNat.Nat.eqb_refl; try easy.
  - destruct (PeanoNat.Nat.eq_dec v0 k); subst.
    + exfalso; apply H; now left.
    + now apply PeanoNat.Nat.eqb_neq in n as ->.
  - rewrite IHe1, IHe2; try easy.
    all:intros H'; apply H; cbn; apply List.in_or_app; now (right + left).
  - rewrite IHe1, IHe2, IHe3; eauto;
    intros H'; apply H; cbn; (try now repeat (apply List.in_or_app; right));
    (try now (apply List.in_or_app; left)).
    now (apply List.in_or_app; right; apply List.in_or_app; left).
Qed.
Lemma substFV_unbind k v e :
  ~ List.In k (fv e) ->
  substBV O v e = substFV k v (unbind k e)
.
Proof. apply substBV_substFV_unbind. Qed.
Lemma substBV_lc k x v e :
  k <= x ->
  lc_at k e ->
  substBV x v e = e
.
Proof.
  revert k x v; induction e; intros; cbn; try easy.
  - destruct (PeanoNat.Nat.eq_dec v x) as [->|H1].
    + eapply (PeanoNat.Nat.lt_le_trans x k x) in H0; eauto;
      exfalso; now eapply (PeanoNat.Nat.lt_irrefl x).
    + now apply PeanoNat.Nat.eqb_neq in H1 as ->.
  - erewrite IHe1, IHe2; eauto; now cbn in H0.
  - f_equal; revert H0; eapply IHe; eauto;
    now rewrite PeanoNat.Nat.add_le_mono_l with (p:=1) in H.
  - f_equal; revert H0; eapply IHe; eauto;
    now rewrite PeanoNat.Nat.add_le_mono_l with (p:=2) in H.
  - erewrite IHe1, IHe2, IHe3; eauto; now cbn in H0.
  - erewrite IHe; eauto.
  - erewrite IHe; eauto.
Qed.
Lemma commute_substFV_substBV x y v w e :
  lc_at x w ->
  substFV y w (substBV x v e) = substBV x (substFV y w v) (substFV y w e)
.
Proof.
  revert x y v w; induction e; intros; cbn; try easy; try (f_equal; eauto).
  - now destruct (PeanoNat.Nat.eqb v x).
  - destruct (PeanoNat.Nat.eqb v y); trivial;
    erewrite substBV_lc; eauto.
  - rewrite IHe; eauto using lc_at_Sx.
  - rewrite IHe; eauto using lc_at_Sx.
Qed.
Lemma substBV_lc_at k j v y :
  k <= j ->
  lc_at k v ->
  v = substBV j (efvar y) v
.
Proof.
  Require Import Lia.
  revert k j; induction v; intros k j H0 H1; cbn; eauto.
  - cbn in H1. destruct (PeanoNat.Nat.eq_dec v j) as [->|H]; try lia.
    now eapply PeanoNat.Nat.eqb_neq in H as ->.
  - f_equal; destruct H1; eauto.
  - f_equal; cbn in H1; erewrite <- IHv; try eassumption; trivial; now eapply le_n_S.
  - f_equal; cbn in H1; erewrite <- IHv; try eassumption; trivial; now do 2 eapply le_n_S.
  - f_equal; destruct H1 as [H1a [H1b H1c]]; eauto.
  - f_equal; cbn in H1; eauto.
  - f_equal; cbn in H1; eauto.
Qed.
Lemma substFV_open_at_comm x y v e j :
  x <> y -> lc_at j v ->
  substFV x v (open_at j y e) = open_at j y (substFV x v e)
.
Proof.
  intros H0 H2; repeat rewrite open_at_substBV.
  apply PeanoNat.Nat.eqb_neq in H0.
  rewrite commute_substFV_substBV; trivial.
  cbn; rewrite PeanoNat.Nat.eqb_sym; rewrite H0; cbn. 
  f_equal.
Qed.
Lemma substFV_open_at2_comm x y z v e k j :
  x <> y -> x <> z -> k < j -> lc_at k v ->
  substFV x v (open_at k z (open_at j y e)) = open_at k z (open_at j y (substFV x v e))
.
Proof.
  intros H0 H1 H2 H3; repeat rewrite open_at_substBV.
  apply PeanoNat.Nat.eqb_neq in H0, H1.
  rewrite commute_substFV_substBV; trivial.
  cbn; rewrite PeanoNat.Nat.eqb_sym; rewrite H1; cbn. 
  f_equal.
  revert k j H2 H3; induction e; intros; cbn; eauto; try (now f_equal; eauto).
  - destruct (PeanoNat.Nat.eqb v0 j); cbn; trivial; now rewrite PeanoNat.Nat.eqb_sym, H0.
  - destruct (PeanoNat.Nat.eqb v0 x); cbn; trivial; 
    erewrite <- substBV_lc_at; try eassumption; trivial; repeat constructor;
    now eapply lc_at_Sx.
Qed.
Lemma open_at2_comm y z v k j :
  k < j -> lc_at k v ->
  open_at k z (open_at j y v) = open_at j y (open_at k z v)
.
Proof.
  intros H0 H1; repeat rewrite open_at_substBV.
  eapply substBV_lc_at with (y:=y) in H0 as Hy; eauto;
  repeat rewrite <- Hy; try now apply lc_at_Sx.
  erewrite substBV_lc; eauto.
Qed.
Lemma substFV_unbind_comm x y v e :
  x <> y -> lc_at 0 v ->
  substFV x v (unbind y e) = unbind y (substFV x v e)
.
Proof.
  intros; repeat rewrite unbind_substBV.
  apply PeanoNat.Nat.eqb_neq in H.
  assert (substFV x v (efvar y) = efvar y) as H1 by (cbn; now rewrite PeanoNat.Nat.eqb_sym, H).
  rewrite commute_substFV_substBV; trivial.
  now rewrite H1.
Qed.

(** Due to memory operations, a runtime program is not just an expression,
    it needs to be a record containing operational state and the expression. *)
Record References := mkReferences {
  references_poisoned: bool ;
  references_type: ty ;
}.
Record RefData := mkRefData {
  refdata_type: ty ;
  refdata_data: dom type ;
}.
Record MemoryState := mkMemoryState {
  pointers: partial_map PointerData ;
  heap: partial_map 
}.


Inductive pstep : expr -> Event -> expr -> Prop :=
  | papp : forall a b, value b -> pstep (eapp (elam a) b) ε (substBV 0 b a)
  | papprec : forall a b, value b -> pstep (eapp (erec a) b) ε (substBV 0 (erec a) (substBV 1 b a))
  | piftrue : forall a b, pstep (eif (ebool true) a b) ε a
  | piffalse : forall a b, pstep (eif (ebool false) a b) ε b
  | 
.
Inductive Ectx :=
  | Ehole 
  | EappL : Ectx -> expr -> Ectx
  | EappR : expr -> Ectx -> Ectx
  | Eif : Ectx -> expr -> expr -> Ectx
.
Fixpoint fill_hole (K : Ectx) (e : expr) : expr :=
  match K with
  | Ehole => e
  | EappL K e' => eapp (fill_hole K e) e' 
  | EappR e' K => eapp e' (fill_hole K e)
  | Eif K e0 e1 => eif (fill_hole K e) e0 e1
  end
.
Inductive estep : expr -> Event -> expr -> Prop :=
  | estepc : forall e e' e0 e0' E o,
      e = fill_hole E e0 ->
      e' = fill_hole E e0' ->
      pstep e0 o e0' ->
      estep e o e'
.
Inductive star_step : expr -> list ev -> expr -> Prop :=
  | star_refl : forall e, star_step e nil e
  | star_trans_ign : forall e0 e1 e2 As,
      estep e0 ε e1 ->
      star_step e1 As e2 ->
      star_step e0 As e2
  | star_trans_imp : forall e0 e1 e2 e As,
      estep e0 (Some e) e1 ->
      star_step e1 As e2 ->
      star_step e0 (cons e As) e2
.

Definition Gamma : Type := partial_map ty.
Inductive sub_pred : Predicate -> Predicate -> Prop :=
  | subPTrue : forall p, sub_pred p TruePred
  | subPNeg : forall p p', sub_pred p p' -> sub_pred (NegPred p) (NegPred p')
.
Hint Constructors sub_pred : core.
Lemma sub_pred_refl p :
  sub_pred p p
.
Proof. induction p; eauto. Qed.
Lemma sub_pred_trans p0 p1 p2 :
  sub_pred p0 p1 ->
  sub_pred p1 p2 ->
  sub_pred p0 p2
.
Proof. 
  intros H; revert p2; induction H; intros; eauto.
  - inversion H; subst; now constructor.
  - inversion H0; subst; constructor; eauto.
Qed.
#[local]
Hint Resolve sub_pred_refl sub_pred_trans : core.

Inductive csub : ty -> ty -> Prop :=
  | cbase : forall st p p',
      sub_pred p p' ->
      csub (Refine st p) (Refine st p')
  | cfn : forall t0a t0b t1a t1b,
      csub t1a t0a ->
      csub t0b t1b ->
      csub (Arrow t0a t0b) (Arrow t1a t1b)
.
Hint Constructors csub : core.
Lemma csub_refl t :
  csub t t
.
Proof.
  induction t; cbn; eauto.
Qed.
Fixpoint depth (t : ty) : nat := 
  match t with
  | Refine _ _ => 0
  | Arrow a b => 1 + max (depth a) (depth b)
  end
.
Lemma csub_up_Refine t s p :
  csub (Refine s p) t ->
  exists p', t = Refine s p' /\ sub_pred p p'
.
Proof. 
  intros H; dependent induction H; eauto.
Qed.
Lemma csub_down_Refine t s p :
  csub t (Refine s p) ->
  exists p', t = Refine s p' /\ sub_pred p' p
.
Proof. 
  intros H; dependent induction H; eauto.
Qed.
Lemma csub_up_Arrow t a b :
  csub (Arrow a b) t ->
  exists a' b', t = Arrow a' b' /\ 
                csub a' a /\
                csub b b'
.
Proof. 
  intros H; dependent induction H; eauto.
Qed.
Lemma csub_down_Arrow t a b :
  csub t (Arrow a b) ->
  exists a' b', t = Arrow a' b' /\ 
                csub a a' /\
                csub b' b
.
Proof. 
  intros H; dependent induction H; eauto.
Qed.
Lemma csub_trans' t0 t1 t2 n :
  depth t0 + depth t1 + depth t2 <= n ->
  csub t0 t1 ->
  csub t1 t2 ->
  csub t0 t2
.
Proof.
  revert t0 t1 t2; induction n; intros; eauto.
  - destruct t0,t1,t2; try now apply PeanoNat.Nat.nle_succ_0 in H.
    inversion H0; inversion H1; subst; constructor; eauto.
  - destruct t2.
    + apply csub_down_Refine in H1 as [p1 [H1a H1b]]; subst;
      apply csub_down_Refine in H0 as [p0 [H0a H0b]]; subst.
      constructor; eauto.
    + eapply csub_down_Arrow in H1 as [ta1 [tb1 [H1a [H1b H1c]]]]; subst;
      eapply csub_down_Arrow in H0 as [ta0 [tb0 [H0a [H0b H0c]]]]; subst;
      econstructor; eapply IHn; eauto.
      rename t2_1 into ta2; rename t2_2 into tb2.
      Require Import Lia.
      all: cbn in *; lia.
      (* 
      assert (depth (Arrow ta0 tb0) <= S n - depth (Arrow ta2 tb2) - depth (Arrow ta1 tb1)) by now do 2 eapply PeanoNat.Nat.le_add_le_sub_r.
      assert (depth (Arrow ta1 tb1) <= S n - depth (Arrow ta2 tb2) - depth (Arrow ta0 tb0)) by now (eapply PeanoNat.Nat.le_add_le_sub_r; rewrite PeanoNat.Nat.add_comm; eapply PeanoNat.Nat.le_add_le_sub_r).
      assert (depth (Arrow ta2 tb2) <= S n - depth (Arrow ta1 tb1) - depth (Arrow ta0 tb0)) by (do 2 eapply PeanoNat.Nat.le_add_le_sub_r; now do 2 (rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.add_assoc)).
      cbn in H0, H1, H2.
      eapply PeanoNat.Nat.le_succ_l in H0.
      Search (S _ <= _).
      apply PeanoNat.Nat.add_le_mono_l in H0, H1, H2; fold (depth) in *.
      rewrite <- PeanoNat.Nat.le_max_l in H0, H1, H2.
      *)
Qed.
Lemma csub_trans t0 t1 t2 :
  csub t0 t1 ->
  csub t1 t2 ->
  csub t0 t2
.
Proof.
  eapply csub_trans'; reflexivity.
Qed.
#[local] Hint Resolve csub_refl csub_trans : core.

Inductive check : Gamma -> expr -> ty -> Prop :=
  | check_num : forall G n, check G (enum n) (Refine Num TruePred)
  | check_bool : forall G b, check G (ebool b) (Refine Bool TruePred)
  | check_var : forall G x t,
      G x = Some t ->
      check G (efvar x) t
  | check_app : forall G a b ta tb,
      check G a (Arrow ta tb) ->
      check G b ta ->
      check G (eapp a b) tb
  | check_lam : forall G a ta tb nms,
      (forall y, ~List.In y nms -> check (y ↦ ta ◘ G) (unbind y a) tb) ->
      check G (elam a) (Arrow ta tb)
  | check_rec : forall G a ta tb nms,
      (forall f y, ~List.In f nms -> ~List.In y (cons f nms) ->
                   check (f ↦ Arrow ta tb ◘ (y ↦ ta ◘ G)) (open_at 0 f (open_at 1 y a)) tb) ->
      check G (erec a) (Arrow ta tb)
  | check_if : forall G a b c p t,
      check G a (Refine Bool p) ->
      check G b t ->
      check G c t ->
      check G (eif a b c) t
  | check_sub : forall G e t t',
      check G e t ->
      csub t t' ->
      check G e t'
.
Hint Constructors check : core.

Lemma weakening G G' e t :
  check G e t ->
  includedin G G' ->
  check G' e t
.
Proof.
  intros Ht; revert G'; induction Ht; intros; eauto;
  try (eapply check_lam; intros; eapply H0; eauto using includedin_update);
  try (eapply check_rec; intros; eapply H0; eauto using includedin_update).
Qed.
Lemma cons_exchange G a aT b bt e t :
  a <> b ->
  check (a ↦ aT ◘ (b ↦ bt ◘ G)) e t ->
  check (b ↦ bt ◘ (a ↦ aT ◘ G)) e t
.
Proof.
  intros Hne H; eapply weakening; eauto; apply includedin_cons_swap;
  now apply PeanoNat.Nat.neq_sym.
Qed.
Lemma cf_int e p :
  check ∅ e (Refine Num p) ->
  value e ->
  exists n, e = enum n
.
Proof.
  intros H0 H1; dependent induction H0; eauto; inversion H1; subst.
  - eauto.
  - eapply csub_down_Refine in H as [p' [Ha Hb]]; subst; eauto. 
  - eapply csub_down_Refine in H as [p' [Ha Hb]]; subst; eauto. 
  - eapply csub_down_Refine in H as [p' [Ha Hb]]; subst; eauto. 
Qed.
Lemma cf_bool e p :
  check ∅ e (Refine Bool p) ->
  value e ->
  exists b, e = ebool b
.
Proof.
  intros H0 H1; dependent induction H0; eauto; inversion H1; subst.
  - eapply csub_down_Refine in H as [p' [Ha Hb]]; subst; eauto. 
  - eauto.
  - eapply csub_down_Refine in H as [p' [Ha Hb]]; subst; eauto. 
  - eapply csub_down_Refine in H as [p' [Ha Hb]]; subst; eauto. 
Qed.
Lemma cf_arrow e t0 t1 :
  check ∅ e (Arrow t0 t1) ->
  value e ->
  exists bdy, e = elam bdy \/ e = erec bdy
.
Proof.
  intros H0 H1; dependent induction H0; eauto; inversion H1; subst.
  - eapply csub_down_Arrow in H as [a' [b' [Ha [Hb Hc]]]]; subst; eauto.
  - eapply csub_down_Arrow in H as [a' [b' [Ha [Hb Hc]]]]; subst; eauto.
  - eapply csub_down_Arrow in H as [a' [b' [Ha [Hb Hc]]]]; subst; eauto.
  - eauto.
Qed.
Lemma invert_bool G b t :
  check G (ebool b) t ->
  (csub t (Refine Bool TruePred))
.
Proof.
  intros H; dependent induction H; eauto.
  specialize (IHcheck b Logic.eq_refl) as IHcheck.
  apply csub_down_Refine in IHcheck as [p' [IHchecka IHcheckb]]; subst.
  apply csub_up_Refine in H0 as [p'' [H0a H0b]]; subst.
  constructor; constructor.
Qed.
Lemma invert_number G n t :
  check G (enum n) t ->
  (csub t (Refine Num TruePred))
.
Proof.
  intros H; dependent induction H; eauto.
  specialize (IHcheck n Logic.eq_refl) as IHcheck.
  apply csub_down_Refine in IHcheck as [p' [IHchecka IHcheckb]]; subst.
  apply csub_up_Refine in H0 as [p'' [H0a H0b]]; subst.
  constructor; constructor.
Qed.
Lemma invert_lam G a t :
  check G (elam a) t ->
  (exists nms ta tb, forall y, ~List.In y nms ->
    check (y ↦ ta ◘ G) (unbind y a) tb /\
    csub (Arrow ta tb) t
  )
.
Proof.
  intros Ht; dependent induction Ht; eauto. 
  - exists nms, ta, tb; intros; split; eauto.
  - specialize (IHHt a Logic.eq_refl) as [nms [ta [tb IHHt]]].
    exists nms, ta, tb; intros y Hy; specialize (IHHt y Hy) as [IHHta IHHtb].
    split; eauto.
Qed.
Lemma invert_rec G a t :
  check G (erec a) t ->
  (exists nms ta tb, forall f y, ~List.In f nms -> ~List.In y (cons f nms) ->
    check (f ↦ Arrow ta tb ◘ (y ↦ ta ◘ G)) (open_at 0 f (open_at 1 y a)) tb /\
    csub (Arrow ta tb) t /\
    check G (erec a) (Arrow ta tb)
  )
.
Proof.
  intros Ht; dependent induction Ht; eauto. 
  - exists nms, ta, tb; intros; split; eauto.
  - specialize (IHHt a Logic.eq_refl) as [nms [ta [tb IHHt]]].
    exists nms, ta, tb; intros f y Hf Hy; specialize (IHHt f y Hf Hy) as [IHHta [IHHtb IHHtc]].
    repeat split; eauto.
Qed.
Lemma invert_app G a b t :
  check G (eapp a b) t ->
  (exists ta,
    check G a (Arrow ta t) /\
    check G b ta
  )
.
Proof.
  intros H; dependent induction H; eauto.
  specialize (IHcheck a b Logic.eq_refl) as [ta [IHchecka IHcheckb]]; eauto.
Qed.
Lemma abs_arrow a ta tb :
  check ∅ (elam a) (Arrow ta tb) ->
  (exists nms ta', forall y, ~List.In y nms ->
    csub ta ta' /\
    check (y ↦ ta' ◘ ∅) (unbind y a) tb
  )
.
Proof.
  intros H%invert_lam; destruct H as [nms [ta0 [tb0 H]]].
  exists nms, ta0; intros y Hy; specialize (H y Hy) as [Ha Hb].
  eapply csub_down_Arrow in Hb as [ta1 [ta2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst; repeat split; try easy.
  eapply check_sub; try eassumption.
Qed. 
Lemma abs_arrow' a ta tb :
  check ∅ (erec a) (Arrow ta tb) ->
  (exists nms ta' tb', forall f y, ~List.In f nms -> ~List.In y (cons f nms) ->
    csub ta ta' /\ csub tb' tb /\
    check (f ↦ Arrow ta' tb' ◘ (y ↦ ta' ◘ ∅)) (open_at 0 f (open_at 1 y a)) tb' /\
    check ∅ (erec a) (Arrow ta' tb')
  )
.
Proof.
  intros H%invert_rec; destruct H as [nms [ta0 [tb0 H]]].
  exists nms, ta0, tb0; intros f y Hf Hy; specialize (H f y Hf Hy) as [Ha [Hb Hc]].
  eapply csub_down_Arrow in Hb as [ta1 [ta2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst; repeat split; try easy.
Qed. 
Lemma invert_if G a b c t :
  check G (eif a b c) t ->
  exists p,
    check G a (Refine Bool p) /\
    check G b t /\
    check G c t
.
Proof.
  intros H; dependent induction H; eauto.
  specialize (IHcheck a b c Logic.eq_refl) as [p [IH1 [IH2 IH3]]]; firstorder eauto.
Qed.
Lemma check_empty_lc v t :
  check ∅ v t ->
  lc_at 0 v
.
Proof.
  induction 1; cbn; eauto. eapply lc_at_unbind, H0, fresh_not_in.
  eapply lc_at_unbind2, H0, fresh_not_in; try apply fresh_not_in.
Qed.
Lemma lem_fv_subset G e t :
  check G e t ->
  (forall x, List.In x (fv e) -> G x <> None)
.
Proof.
  induction 1; cbn; try easy; unfold includedin; intros.
  - destruct H0 as [-> | []]; intros ?; congruence.
  - apply List.in_app_or in H1 as [H1|H1]; eauto.
  - specialize (@fresh2_not_in nms (fv a) _ eq_refl); intros [H2a H2b] H3.
    enough (x <> fresh2 nms (fv a)) as Hne.
    eapply H0; eauto using fv_unbind_subsets.
    rewrite update_neq; eauto.
    intros ->; contradiction.
  - specialize (@fresh2_not_in nms (fv a) _ eq_refl);
    specialize (@fresh2_not_in (cons (fresh2 nms (fv a)) nms) (fv a) _ eq_refl); intros [H2a H2b] [H3a H3b] H4.
    enough (x <> fresh2 nms (fv a)) as Hne.
    enough (x <> fresh2 (cons (fresh2 nms (fv a)) nms) (fv a)) as Hne'.
    eapply H0; eauto using fv_open_at_subsets.
    do 2 (rewrite update_neq; eauto).
    all: intros ->; contradiction.
  - specialize (@fresh2_not_in (fv a) (fv b ++ fv c) _ eq_refl); intros [H2a H2b] H3.
    apply List.in_app_or in H2 as [H2|H2]; try apply List.in_app_or in H2 as [H2|H2].
    eapply IHcheck1; eauto.
    eapply IHcheck2; eauto.
    eapply IHcheck3; eauto.
Qed.
Lemma lem_fv_not_in G e t x :
  check G e t -> 
  G x = None ->
  ~ List.In x (fv e)
.
Proof.
  intros Ha Hb Hc; eapply lem_fv_subset; eauto.
Qed.

Lemma substitution G e t tv v x :
  G x = None ->
  check (x ↦ tv ◘ G) e t ->
  check ∅ v tv ->
  check G (substFV x v e) t
.
Proof.
  intros Hdom Ht Hv; remember (x ↦ tv ◘ G) as G';
  generalize dependent G; dependent induction Ht; intros; cbn; eauto.
  - destruct (PeanoNat.Nat.eq_dec x0 x) as [->|Hn].
    + subst; rewrite PeanoNat.Nat.eqb_refl. 
      rewrite update_eq in H; inversion H; subst; clear H.
      eapply weakening; eauto using includedin_empty.
    + assert (Hn':=Hn); apply PeanoNat.Nat.eqb_neq in Hn as ->; constructor; subst.
      rewrite update_neq in H; eauto.
  - eapply check_lam; intros; subst. instantiate (1:=cons x nms) in H1.
    assert (~In y nms) by (intros ?; apply H1; now right).
    specialize (H0 y H2 Hv (y ↦ ta ◘ G0)).
    assert (x <> y) as Hne by (intros ->; apply H1; now left).
    assert ((y ↦ ta ◘ G0) x = None) as Hno by (rewrite update_neq; eauto).
    assert ((y ↦ ta ◘ (x ↦ tv ◘ G0)) = (x ↦ tv ◘ (y ↦ ta ◘ G0))) as Heq by now rewrite update_permute.
    specialize (H0 Hno Heq).
    rewrite <- substFV_unbind_comm; eauto using check_empty_lc.
  - eapply check_rec; intros; subst. instantiate (1:=cons x nms) in H1.
    assert (~In f nms) by (intros ?; apply H1; now right).
    assert (~In y (cons f nms)) by (
    intros ?; destruct H4 as [->|H4]; try (exfalso; apply H2; now left);
    apply H2; now do 2 right).
    specialize (H0 f y H3 H4 Hv (f ↦ Arrow ta tb ◘ (y ↦ ta ◘ G0))).
    assert (x <> f) as Hnef by (intros ->; apply H1; now left).
    assert (x <> y) as Hney by (intros ->; apply H2; right; now left).
    assert ((f ↦ Arrow ta tb ◘ (y ↦ ta ◘ G0)) x = None) as Hno by repeat (rewrite update_neq; eauto).
    specialize (H0 Hno).
    rewrite <- substFV_open_at2_comm; eauto using check_empty_lc.
    eapply H0. rewrite update_rotate; eauto. intros ->; apply H4; now left.
Qed.

Definition check_Ectx (G : Gamma) (E : Ectx) (t0 t1 : ty) : Prop :=
  forall e, check G e t0 -> check G (fill_hole E e) t1
.
Lemma Ehole_typing G t :
  check_Ectx G Ehole t t
.
Proof.
  unfold check_Ectx; intros; now cbn.
Qed.
Hint Resolve Ehole_typing : core.

Lemma decomposition G E e t1 :
  check G (fill_hole E e) t1 ->
  exists t0, check_Ectx G E t0 t1 /\ check G e t0
.
Proof.
  revert t1; induction E; cbn; intros; eauto.
  - eapply invert_app in H as [ta' [Ha Hb]]. specialize (IHE _ Ha); destruct IHE as [x [IHE1 IHE2]].
    exists x; split; trivial. unfold check_Ectx; intros; cbn.
    eapply check_app; eauto.
  - eapply invert_app in H as [ta' [Ha Hb]]. specialize (IHE _ Hb); destruct IHE as [x [IHE1 IHE2]].
    exists x; split; trivial. unfold check_Ectx; intros; cbn.
    eapply check_app; eauto.
  - eapply invert_if in H as [p [H1 [H2 H3]]].
    specialize (IHE _ H1) as [t0' [IHE1 IHE2]].
    exists t0'; split; trivial. unfold check_Ectx; intros; cbn.
    eapply check_if; eauto.
Qed.
Lemma recomposition G E e t0 t1 :
  check_Ectx G E t0 t1 ->
  check G e t0 ->
  check G (fill_hole E e) t1
.
Proof. auto. Qed.

Lemma ppreservation e e' t o :
  check ∅ e t -> 
  pstep e o e' ->
  check ∅ e' t
.
Proof.
  intros H; remember ∅ as G; revert e' HeqG; induction H; intros; match goal with [H: pstep _ _ _ |- _] => inversion H; subst end; eauto.
  - assert (H':=H); apply abs_arrow in H as [nms [ta' H]].
    pose proof (fresh_not_in nms); specialize (H (fresh nms) H2) as [Ha Hb].
    erewrite substFV_unbind; try instantiate (1:=fresh nms);
    try (eapply lem_fv_not_in with (x:=fresh nms) in H'; easy).
    eapply substitution; eauto.
  - assert (H':=H); apply abs_arrow' in H as [nms [ta' [tb' H]]].
    pose proof (fresh_not_in nms) as H2;
    remember (fresh nms) as f; 
    pose proof (fresh_not_in (cons f nms)) as H3;
    remember (fresh (cons f nms)) as y.
    specialize (H f y H2 H3) as [Ha [Hb [Hc Hd]]].
    assert (~ In f (fv a0)) as Hfa0 by (eapply lem_fv_not_in with (x:=f) in H' as Hf; eauto).
    assert (f <> y) as Hfyne by (intros ->; apply H3; now left).
    assert (~ In f (fv (substBV 1 b a0))) by (intros H; apply Hfa0;
      rewrite <- substBV_fv_in; eauto using lem_fv_not_in).
    erewrite substFV_unbind; try instantiate (1:=f); trivial.
    eapply substitution; eauto.
    erewrite substBV_substFV_unbind with (k:=y); trivial;
    try now (eapply lem_fv_not_in with (x:=y) in H'; eauto).
    eapply check_sub in H0; eauto.
    unfold unbind; erewrite <- substFV_open_at_comm; eauto;
    try now eapply check_empty_lc in H0.
    eapply substitution; eauto using cons_exchange.
    rewrite update_neq, apply_empty; trivial.
Qed.
Corollary epreservation e e' t o :
  estep e o e' -> 
  check ∅ e t -> 
  check ∅ e' t
.
Proof.
  revert t; induction 1; intros; subst.
  eapply decomposition in H2 as [t' [H2a H2b]].
  eapply ppreservation in H1; eauto.
Qed.
Corollary preservation e e' t As :
  star_step e As e' ->
  check ∅ e t ->
  check ∅ e' t
.
Proof.
  intros H; revert t; induction H; intros; trivial;
  eapply epreservation in H; eauto.
Qed.

Definition progressive (e : expr) : Prop :=
  value e \/ exists o e', estep e o e'
.
Lemma progress e t :
  check ∅ e t ->
  progressive e
.
Proof.
  remember ∅ as G; induction 1; cbn; (try now left); subst; try easy; auto.
  - right; exists (Some(EvBr s)); destruct s;
    now ((exists (ebool true) + exists (enum 0)); econstructor; try (instantiate (2:=Ehole); now cbn); (try now cbn); (eapply pguessBool + eapply pguessNum)).
  - right; exists o, (enum 0); econstructor; try (instantiate (2:=Ehole); now cbn); (try now cbn); eapply pev.
  - right; destruct (IHcheck1 Logic.eq_refl).
    + assert (H':=H); apply cf_arrow in H' as [a' [H'|H']]; subst; trivial.
      * destruct (IHcheck2 Logic.eq_refl).
        -- exists ε, (substBV O b a'). econstructor. instantiate (2:=Ehole); now cbn.
          now cbn. now constructor.
        -- destruct H2 as [o' [b' H2]]. inversion H2; subst.
           exists o',(eapp (elam a') (fill_hole E e0')).
           econstructor. instantiate (2:=EappR (elam a') E); now cbn.
           now cbn. trivial.
      * destruct (IHcheck2 Logic.eq_refl).
        -- exists ε, (substBV 0 (erec a') (substBV 1 b a')); econstructor; (try (instantiate (2:=Ehole); now cbn)); try now cbn.
           now constructor.
        -- destruct H2 as [o' [b' H2]]. inversion H2; subst.
           exists o',(eapp (erec a') (fill_hole E e0')).
           econstructor. instantiate (2:=EappR (erec a') E); now cbn.
           now cbn. trivial.
    + destruct H1 as [o' [a' H1]]. inversion H1; subst.
      exists o',(eapp (fill_hole E e0') b). econstructor.
      instantiate (2:=EappL E b); now cbn. now cbn. trivial.
  - right; destruct (IHcheck1 Logic.eq_refl).
    + eapply cf_bool in H as [bo H]; subst; trivial.
      destruct bo; exists ε.
      * exists b; econstructor; (try (instantiate (2:=Ehole); now cbn));
        (try now cbn); eapply piftrue.
      * exists c; econstructor; (try (instantiate (2:=Ehole); now cbn));
        (try now cbn); eapply piffalse.
    + destruct H2 as [o [e' H2]]; inversion H2; subst.
      exists o, (eif (fill_hole E e0') b c).
      econstructor; (try (instantiate (2:=Eif E b c); now cbn));
      (try now cbn).
Qed.
Theorem type_safety e e' t As :
  check ∅ e t ->
  star_step e As e' ->
  progressive e'
.
Proof.
  eintros H Hs; eapply preservation in Hs as Hs'; eauto.
  eapply progress; eauto.
Qed.
