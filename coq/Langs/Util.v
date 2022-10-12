Set Implicit Arguments.
Require Import Lists.List Strings.String CSC.Util RelationClasses.

Section Util.

Class HasEquality (A : Type) := {
  eq : A -> A -> bool ;
  eq_refl : forall (a : A), eq a a = true ;
  eqb_eq : forall (a b : A), eq a b = true <-> a = b ;
  neqb_neq : forall (a b : A), eq a b = false <-> a <> b ;
}.
Lemma eqb_dec { A : Type } { H : HasEquality A } (a x : A) :
  eq a x = true \/ eq a x = false.
Proof. destruct (eq a x); now (left + right). Qed.
Lemma eq_dec { A : Type } { H : HasEquality A } (a x : A) :
  a = x \/ a <> x.
Proof.
  destruct (eqb_dec a x).
  apply eqb_eq in H0. now left.
  apply neqb_neq in H0. now right.
Qed.

Inductive mapind {A : Type} (H : HasEquality A) (B : Type) : Type :=
| mapNil : mapind H B
| mapCons : A -> B -> mapind H B -> mapind H B
.
Fixpoint length { A : Type } {H : HasEquality A} {B : Type} (x : mapind H B) : nat :=
  match x with
  | mapNil _ _ => 0
  | mapCons _a _b xs => 1 + (length xs)
  end
.

Definition dom { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) : list A :=
  let fix dom_aux (m : mapind H B) :=
    match m with
    | mapNil _ _ => @List.nil A
    | mapCons a _b m' => @List.cons A a (dom_aux m')
    end
  in dom_aux m
.
Lemma in_dom_dec { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) :
  In x (dom m) \/ ~ In x (dom m)
.
Proof.
  induction m; cbn.
  - now right.
  - fold (dom m). destruct IHm as [IHm|IHm]; eauto.
    destruct (eq_dec a x); subst.
    repeat left; easy. right. intros [H1|H1]; contradiction.
Qed.
Inductive nodupinv {A : Type} {H : HasEquality A} {B : Type} : mapind H B -> Prop :=
| nodupmapNil : nodupinv (mapNil H B)
| nodupmapCons : forall (a : A) (b : B) (m : mapind H B),
    ~(List.In a (dom m)) ->
    nodupinv m ->
    nodupinv (mapCons a b m)
.
(** Returns None if m contains any duplicates. *)
Fixpoint undup {A : Type} {H : HasEquality A} { B : Type } (m : mapind H B) : option(mapind H B) :=
  match m with
  | mapNil _ _ => Some(mapNil _ _)
  | mapCons a b m' =>
    let thedom := dom m' in
    match List.find (fun x => eq a x) thedom, undup m' with
    | None, Some xs' => Some(mapCons a b xs')
    | _, _ => None
    end
  end
.
Lemma undup_refl {A : Type} {H : HasEquality A} {B : Type} (m m' : mapind H B) :
  undup m = Some m' -> m = m'.
Proof.
  revert m'; induction m; intros m' H0; inv H0; trivial.
  destruct (option_dec (List.find (fun x : A => eq a x) (dom m))) as [Hx | Hy].
  apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H2; inv H2.
  rewrite Hy in H2.
  destruct (option_dec (undup m)) as [H__x | H__y]; try rewrite H__y in H2; inv H2.
  apply not_eq_None_Some in H__x as [m'' H__x]; rewrite H__x in H1.
  rewrite (IHm m'' H__x); now inv H1.
Qed.
Lemma nodupinv_equiv_undup {A : Type} {H : HasEquality A} { B : Type } (m : mapind H B) :
  undup m = Some m <-> nodupinv m.
Proof.
  induction m; cbn; split; try easy.
  - constructor.
  - intros H0; destruct (option_dec (List.find (fun x : A => eq a x) (dom m))) as [Hx | Hy].
    apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H0; inv H0.
    rewrite Hy in H0.
    destruct (option_dec (undup m)) as [Hx | Hy']; try rewrite Hy' in H0; inv H0.
    apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H2; inv H2.
    constructor; try apply IHm; eauto.
    intros Ha. eapply List.find_none in Hy; eauto. rewrite eq_refl in Hy. inv Hy.
  - intros H0; inv H0; destruct (option_dec (List.find (fun x : A => eq a x) (dom m))) as [Hx | Hy].
    apply not_eq_None_Some in Hx as [a' Hx].
    apply List.find_some in Hx as [Hx1 Hx2].
    rewrite eqb_eq in Hx2; subst; contradiction.
    rewrite Hy. destruct (option_dec (undup m)) as [Hx | Hy'].
    apply not_eq_None_Some in Hx as [m'' Hx]. rewrite Hx. f_equal. f_equal. apply undup_refl in Hx; easy.
    apply IHm in H5. congruence.
Qed.
Definition push { A : Type } { H : HasEquality A } { B : Type } (a : A) (b : B) (m : mapind H B) : option (mapind H B) :=
  match undup (mapCons a b m) with
  | Some m' => Some m'
  | None => None
  end
.
Lemma push_ok { A : Type } { H : HasEquality A } { B : Type } (a : A) (b : B) (m m' : mapind H B) :
  push a b m = Some m' -> nodupinv m'.
Proof.
  intros H0. unfold push in H0.
  destruct (option_dec (undup (mapCons a b m))) as [Hx|Hy]; try (rewrite Hy in *; congruence);
  apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H0; inv H0;
  apply nodupinv_equiv_undup; cbn in Hx.
  destruct (option_dec (List.find (fun x : A => eq a x) (dom m))) as [Hx0|Hy0]; try (rewrite Hy0 in *; congruence).
  apply not_eq_None_Some in Hx0 as [m'' Hx0]; rewrite Hx0 in Hx; inv Hx.
  rewrite Hy0 in Hx. destruct (option_dec (undup m)) as [Hx1|Hy1].
  apply not_eq_None_Some in Hx1 as [m'' Hx1]. rewrite Hx1 in Hx.
  inv Hx. cbn. apply undup_refl in Hx1 as Hx1'. rewrite Hx1' in Hy0. rewrite Hy0.
  rewrite (undup_refl m Hx1) in Hx1. now rewrite Hx1.
  rewrite Hy1 in Hx. easy.
Qed.

Lemma push_ko { A : Type } { H : HasEquality A } { B : Type } (a : A) (b : B) (m : mapind H B) :
  nodupinv m ->
  ~ In a (dom m) ->
  push a b m = Some (mapCons a b m)
.
Proof.
  unfold push, undup; intros H0 H1.
  destruct (option_dec (List.find (fun x : A => eq a x) (dom m))) as [Hx | Hy].
  apply not_eq_None_Some in Hx as [m__x Hx].
  apply List.find_some in Hx as [Hx0 Hx1]. apply eqb_eq in Hx1; subst.
  contradiction.
  rewrite Hy in *. fold (undup m).
  destruct (option_dec (undup m)) as [Hx | Hy''].
  apply not_eq_None_Some in Hx as [m__x Hx].
  rewrite Hx in *. apply undup_refl in Hx; subst; easy.
  apply nodupinv_equiv_undup in H0; congruence.
Qed.

Definition img { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) : list B :=
  let fix img_aux (m : mapind H B) :=
    match m with
    | mapNil _ _ => @List.nil B
    | mapCons _a b m' => @List.cons B b (img_aux m')
    end
  in img_aux m
.
Definition append { A : Type } {H : HasEquality A} {B : Type} (m0 m1 : mapind H B) : mapind H B :=
  let fix append_aux (m0 : mapind H B) :=
    match m0 with
    | mapNil _ _ => m1
    | mapCons a b m' => mapCons a b (append_aux m')
    end
  in append_aux m0
.
(* '↦' is `\mapsto` and '◘' is `\inversebullet`*)
Notation "a '↦' b '◘' M" := (push a b M) (at level 81, b at next level).
Notation "M1 '◘' M2" := (append M1 M2) (at level 82, M2 at next level).

Lemma append_nil { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) :
  append m (mapNil H B) = m
.
Proof. induction m; eauto; rewrite <- IHm at 2; now cbn. Qed.
Lemma append_assoc { A : Type } { H : HasEquality A } { B : Type } (m1 m2 m3 : mapind H B) :
  ((m1 ◘ m2) ◘ m3) = (m1 ◘ (m2 ◘ m3))
.
Proof.
  revert m2 m3; induction m1; intros.
  - now cbn.
  - change ((((mapCons a b m1) ◘ m2) ◘ m3) = (mapCons a b (m1 ◘ (m2 ◘ m3)))).
    now rewrite <- IHm1.
Qed.

Fixpoint splitat_aux { A : Type } {H : HasEquality A} {B : Type} (accM m : mapind H B) (x : A)
  : option((mapind H B) * A * B * (mapind H B)) :=
  match m with
  | mapNil _ _ => None
  | mapCons a b m' => if eq a x then
                        Some(accM, a, b, m')
                      else
                        splitat_aux (append accM (mapCons a b (mapNil H B))) m' x
  end
.
Definition splitat { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) (x : A)
  : option((mapind H B) * A * B * (mapind H B)) := splitat_aux (mapNil H B) m x.

Definition mget { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) : option B :=
  let fix doo (m : mapind H B) :=
    match m with
    | mapNil _ _=> None
    | mapCons a b m' => if eq a x then
                         Some b
                       else
                         doo m'
    end
  in doo m
.
Definition mset { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B)
  : option(mapind H B) :=
  let fix doo (m : mapind H B) :=
    match m with
    | mapNil _ _ => None
    | mapCons a b m'  => if eq a x then
                          Some(mapCons a v m')
                        else
                          match doo m' with
                          | None => None
                          | Some m'' => Some(mapCons a b m'')
                          end
    end
  in doo m
.

Lemma splitat_elim_cons { A : Type } {H : HasEquality A} {B : Type} (m2 : mapind H B) (x : A) (v : B) :
  nodupinv (mapCons x v m2) ->
  splitat (mapCons x v m2) x = Some (mapNil _ _, x, v, m2).
Proof. cbn; now rewrite eq_refl. Qed.

Lemma splitat_aux_elim_cons { A : Type } {H : HasEquality A} {B : Type} (accM m2 : mapind H B) (x : A) (v : B) :
  nodupinv (accM ◘ mapCons x v m2) ->
  splitat_aux accM (mapCons x v m2) x = Some (accM, x, v, m2).
Proof. intros H0; cbn; now rewrite eq_refl. Qed.
Lemma splitat_aux_prop_cons { A : Type } {H : HasEquality A} {B : Type} (accM m2 : mapind H B) (x y : A) (v : B) :
  y <> x ->
  splitat_aux accM (mapCons y v m2) x = splitat_aux (accM ◘ mapCons y v (mapNil H B)) m2 x
.
Proof. cbn; intros H0; now apply neqb_neq in H0 as ->. Qed.
Lemma splitat_aux_prop { A : Type } {H : HasEquality A} {B : Type} (accM m1 m2 : mapind H B) (x y : A) (v : B) :
  ~ In x (dom m1) ->
  splitat_aux accM (m1 ◘ m2) x = splitat_aux (accM ◘ m1) m2 x
.
Proof.
  revert m1 accM; induction m1; intros.
  - cbn; now rewrite append_nil.
  - destruct (eq_dec a x); subst.
    + exfalso. apply H0. now left.
    + cbn; apply neqb_neq in H1 as ->. fold (m1 ◘ m2). fold (m1 ◘ accM).
      enough (~ In x (dom m1)).
      specialize (IHm1 (accM ◘ mapCons a b (mapNil H B)) H1) as ->.
      rewrite append_assoc; now cbn.
      revert H0; clear; intros H0 H1; apply H0; now right.
Qed.
Lemma splitat_elim { A : Type } {H : HasEquality A} {B : Type} (m1 m2 : mapind H B) (x : A) (v : B) :
  nodupinv (m1 ◘ mapCons x v m2) ->
  splitat (m1 ◘ mapCons x v m2) x = Some (m1, x, v, m2).
Proof.
  unfold splitat; intros H0. rewrite splitat_aux_prop; eauto. cbn; now rewrite eq_refl.
  induction m1; try now cbn.
  intros H1. inv H0. apply IHm1; eauto.
  destruct H1; try easy; subst. exfalso; apply H4; clear.
  induction m1; cbn; eauto.
Qed.
Lemma mset_notin { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) :
  ~ In x (dom m) ->
  mset m x v = None
.
Proof.
  induction m; cbn; intros; trivial.
  destruct (eq_dec a x); fold (dom m) in H0.
  - exfalso; exact (H0 (or_introl H1)).
  - apply neqb_neq in H1; rewrite H1.
    fold (mset m x v); rewrite IHm; try easy.
    intros H2; exact (H0 (or_intror H2)).
Qed.
Lemma splitat_aux_notin { A : Type } { H : HasEquality A } { B : Type } (accM m : mapind H B) (x : A) :
  ~ In x (dom m) ->
  splitat_aux accM m x = None
.
Proof.
  revert accM; induction m; cbn; intros; trivial.
  destruct (eq_dec a x); fold (dom m) in H0.
  - exfalso; exact (H0 (or_introl H1)).
  - apply neqb_neq in H1; rewrite H1.
    fold (splitat m x); rewrite IHm; try easy.
    intros H2; exact (H0 (or_intror H2)).
Qed.
Lemma splitat_notin { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) :
  ~ In x (dom m) ->
  splitat m x = None
.
Proof. now eapply splitat_aux_notin. Qed.
Lemma splitat_aux_in { A : Type } { H : HasEquality A } { B : Type } (accM m : mapind H B) (x : A) :
  In x (dom m) ->
  exists m1 v m2, splitat_aux accM m x = splitat_aux accM (m1 ◘ mapCons x v m2) x
.
Proof.
  revert accM; induction m; cbn; intros; try easy.
  destruct (eq_dec a x) as [H1 | H1].
  - subst; rewrite eq_refl. exists (mapNil H B). exists b. exists m. cbn. now rewrite eq_refl.
  - apply neqb_neq in H1 as H1'; rewrite H1'.
    fold (dom m) in H0; assert (In x (dom m)) by (destruct H0; congruence).
    specialize (IHm (accM ◘ mapCons a b (mapNil H B)) H2); deex.
    exists (mapCons a b m1). exists v. exists m2.
    rewrite IHm. cbn. rewrite H1'. now fold (append m1 (mapCons x v m2)).
Qed.
Lemma in_dom_split { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) :
  nodupinv m ->
  In x (dom m) ->
  exists m1 m2 v, m = (m1 ◘ mapCons x v m2)
.
Proof.
  induction m; cbn; intros; try easy.
  destruct H1 as [H1 | H1]; fold (dom m) in H1; subst.
  - exists (mapNil H B). exists m. exists b. now cbn.
  - inv H0. specialize (IHm H6 H1); deex.
    exists (mapCons a b m1). exists m2. exists v. now rewrite IHm.
Qed.
Lemma splitat_not_none { A : Type } { H : HasEquality A } { B : Type } (accM m1 m2 : mapind H B) (x : A) (v : B) :
  splitat_aux accM (m1 ◘ mapCons x v m2) x <> None
.
Proof.
  revert accM; induction m1; cbn. now rewrite eq_refl.
  destruct (eq a x); easy.
Qed.

Lemma mset_in { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) :
  In x (dom m) ->
  exists m__x, mset m x v = Some m__x
.
Proof.
  induction m; cbn; intros; try easy.
  destruct (eq_dec a x) as [H1 | H1].
  - subst; rewrite eq_refl; exists (mapCons x v m); easy.
  - fold (dom m) in H0; fold (mset m x v).
    apply neqb_neq in H1 as H1'; rewrite H1'.
    assert (In x (dom m)) by (destruct H0; congruence).
    specialize (IHm H2); deex. exists (mapCons a b m__x); now rewrite IHm.
Qed.
Lemma dom_in_ex { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) :
  In x (dom m) ->
  exists m1 m2 v, m = (m1 ◘ (mapCons x v m2))
.
Proof.
  induction m; cbn; try easy.
  intros [H1|H1].
  - subst. exists (mapNil H B). do 2 eexists; cbn; eauto.
  - fold (dom m) in H1. specialize (IHm H1); deex; subst.
    exists (mapCons a b m1). exists m2. exists v. easy.
Qed.
Lemma dom_in_notin_split { A : Type } { H : HasEquality A } { B : Type } (m1 m2 : mapind H B) (x : A) (v : B) :
  nodupinv (m1 ◘ (mapCons x v m2)) ->
  In x (dom (m1 ◘ mapCons x v m2)) ->
  ~ In x (dom m1) /\ ~ In x (dom m2)
.
Proof.
  induction m1; cbn; intros.
  - split; try easy. now inv H0.
  - fold (append m1 (mapCons x v m2)) in *. fold (dom m1). fold (dom (m1 ◘ mapCons x v m2)) in *.
    inv H0. destruct H1 as [H1|H1]; subst.
    exfalso. apply H4; clear. induction m1; cbn; eauto.
    specialize (IHm1 H6 H1) as [IHm1__a IHm1__b].
    split; try easy. intros H2. destruct H2; subst.
    exfalso. apply H4; clear. induction m1; cbn; eauto.
    easy.
Qed.

Lemma dom_split { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) :
  nodupinv m ->
  In x (dom m) ->
  exists m1 m2 v, splitat m x = Some(m1, x, v, m2) /\ m = (m1 ◘ (mapCons x v m2))
.
Proof.
  intros H0 H1; apply dom_in_ex in H1 as H1'; deex.
  subst; cbn. exists m1. exists m2. exists v0.
  apply dom_in_notin_split in H1 as [H2a H2b]; eauto.
  split; try now apply splitat_elim. easy.
Qed.
Lemma splitat_refl { A : Type } { H : HasEquality A } { B : Type } (m m1 m2 : mapind H B) (x : A) (v : B) :
  nodupinv m ->
  splitat m x = Some(m1, x, v, m2) ->
  m = (m1 ◘ mapCons x v m2)
.
Proof.
  destruct (in_dom_dec m x); try (apply splitat_notin in H0; intros; congruence); intros.
  apply dom_split in H0; eauto; deex. destruct H0 as [H0__a H0__b].
  subst. rewrite H0__a in H2. inv H2. easy.
Qed.

Lemma mset_splitat { A : Type } { H : HasEquality A } { B : Type } (m1 m2 m : mapind H B) (x : A) (v b : B) :
  nodupinv(m1 ◘ (mapCons x v m2)) ->
  Some m = mset (m1 ◘ (mapCons x v m2)) x b ->
  m = (m1 ◘ (mapCons x b m2))
.
Proof.
  revert m m2; induction m1; cbn; intros.
  - rewrite eq_refl in H1. now inv H1.
  - fold (append m1 (mapCons x v m2)) in *; fold (append m1 (mapCons x b m2)) in *.
    fold (mset (m1 ◘ mapCons x v m2) x b) in H1.
    destruct (eq_dec a x) as [Hx | Hx]; subst.
    + rewrite eq_refl in H1. inv H1. inv H0. exfalso; apply H3; clear; induction m1; cbn; eauto.
    + apply neqb_neq in Hx as Hx'; rewrite Hx' in H1. inv H0.
      destruct (option_dec (mset (m1 ◘ mapCons x v m2) x b)) as [Hy | Hy]; try (rewrite Hy in H1; inv H1).
      apply not_eq_None_Some in Hy as [y__y Hy]. rewrite Hy in H1. symmetry in Hy.
      specialize (IHm1 y__y m2 H6 Hy). subst. inv H1. easy.
Qed.

Lemma dom_mset { A : Type } { H : HasEquality A } { B : Type } (m m' : mapind H B) (x : A) (v : B) :
  nodupinv m ->
  Some m' = mset m x v ->
  dom m = dom m'
.
Proof.
  destruct (in_dom_dec m x); intros.
  - apply dom_split in H0 as H3; deex; eauto; destruct H3 as [H3__a H3__b].
    subst. eapply mset_splitat in H1; eauto. rewrite H1.
    clear. induction m1; cbn; try easy; f_equal; easy.
  - eapply mset_notin in H0. rewrite H0 in H2. inv H2.
Qed.

Lemma dom_nodupinv { A : Type } { H : HasEquality A } { B : Type } (m m' : mapind H B) :
  nodupinv m ->
  dom m = dom m' ->
  nodupinv m'
.
Proof.
  revert m'; induction m; cbn; intros.
  - destruct m'; inv H1; constructor.
  - fold (dom m) in H1. assert (H1':=H1); destruct m'; inv H1; cbn in H1'.
    fold (dom m') in H1'. inv H0.
    specialize (IHm m' H6 H4).
    constructor; try easy. now rewrite <- H4.
Qed.

Lemma nodupinv_mset { A : Type } { H : HasEquality A } { B : Type } (m m' : mapind H B) (x : A) (v : B) :
  nodupinv m ->
  Some m' = mset m x v ->
  nodupinv m'
.
Proof. intros H0 H1; eauto using dom_mset, dom_nodupinv. Qed.

Definition MIn { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) : Prop :=
  mget m x = Some v
.
Definition MSubset { A : Type } { H : HasEquality A } { B : Type } (m1 m2 : mapind H B) : Prop :=
  forall (x : A) (v : B), MIn m1 x v -> MIn m2 x v
.

Lemma MIn_in { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) :
  MIn m x v -> In x (dom m) /\ In v (img m)
.
Proof.
  induction m; cbn; intros.
  - inv H0.
  - inv H0. remember (eq a x) as b__x; destruct b__x; symmetry in Heqb__x.
    + inv H2. apply eqb_eq in Heqb__x; subst; split; now left.
    + destruct (IHm H2) as [IHm1 IHm2].
      split; now right.
Qed.
Lemma cons_msubset { A : Type } { H : HasEquality A } { B : Type } (m m' : mapind H B) (x : A) (v : B) :
  Some m' = (x ↦ v ◘ m) ->
  MSubset m m'.
Proof.
  intros H0 a b H1. symmetry in H0. apply push_ok in H0 as H0'.
  unfold "_ ↦ _ ◘ _" in H0.
  unfold MIn in *.
  destruct (option_dec (undup (mapCons x v m))) as [Hx | Hy].
  apply not_eq_None_Some in Hx as [m'' Hx].
  rewrite Hx in H0; inv H0.
  apply undup_refl in Hx. inv Hx. cbn. inv H0'.
  destruct (Bool.bool_dec (eq x a) true) as [Hv | Hv].
  exfalso. apply H4. apply eqb_eq in Hv. apply MIn_in in H1 as [H1a H1b].
  subst; contradiction.
  apply Bool.not_true_is_false in Hv; now rewrite Hv.
  now rewrite Hy in H0.
Qed.

#[global]
Instance MSubset__Transitivity { A : Type } { H : HasEquality A } { B : Type } :
  Transitive (fun (a b : mapind H B) => MSubset a b).
Proof. intros x y z Ha Hb f w Hc; now apply Hb, Ha. Qed.

Lemma mget_min {A : Type} { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) :
  mget m x = Some v <-> MIn m x v
.
Proof. split; induction m; cbn; eauto. Qed.

Lemma mget_subset {A : Type} { H : HasEquality A } { B : Type } (m m' : mapind H B) (x : A) (v : B) :
  mget m x = Some v ->
  MSubset m m' ->
  mget m' x = Some v
.
Proof. intros Ha Hb; specialize (Hb x v); apply mget_min; apply mget_min in Ha; eauto. Qed.

(** These are synthetic. They simply allow us to write e.g. `PrimStep` instead of supplying it with parameters *)
Class ExprClass (Expr : Type) := {}.
Class RuntimeExprClass (Expr : Type) := {}.
Class EvalCtxClass (Ectx : Type) := {}.
Class TraceEvent (Ev : Type) := {}.
Class TyClass (T : Type) := {}.
Class SymbolClass (Symb : Type) := {}.

(** Definition of the symbol table. *)
Definition symbols {V E} `{H: HasEquality V} `{SymbolClass E} := mapind H E.
Definition nosymb {V E} `{H: HasEquality V} `{SymbolClass E} : symbols := mapNil H E.

Class ProgClass {V E} (Prog : Type) `{Hv: HasEquality V}
                      `{He: SymbolClass E} := Cprog__Class : symbols -> Prog.

Definition Gamma {K TheTy : Type} `{TyClass TheTy} `{H: HasEquality K} := mapind H TheTy.
Definition Gnil {K TheTy : Type} `{TyClass TheTy} `{H: HasEquality K} : Gamma := mapNil H TheTy.

(* Step-Relation typeclasses. Used as a hack for "overloading" notations *)
Class PrimStep (A : Type) (Ev : Type) `{RuntimeExprClass A} `{TraceEvent Ev} := pstep__Class : A -> (option Ev) -> A -> Prop.
Class CtxStep (A : Type) (Ev : Type) `{RuntimeExprClass A} `{TraceEvent Ev} := estep__Class : A -> (option Ev) -> A -> Prop.
Class VDash {K Expr TheTy : Type} `{ExprClass Expr} `{T: TyClass TheTy} `{H: HasEquality K} := vDash__Class : Gamma -> Expr -> TheTy -> Prop.

End Util.

#[global]
Notation "a '↦' b '◘' M" := (mapCons a b M) (at level 81, b at next level).
#[global]
Notation "M1 '◘' M2" := (append M1 M2) (at level 82, M2 at next level).
#[global]
Notation "e0 '--[]-->' e1" := (pstep__Class e0 (None) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[]==>' e1" := (estep__Class e0 (None) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '--[,' a ']-->' e1" := (pstep__Class e0 a e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[,' a ']==>' e1" := (estep__Class e0 a e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '--[' a ']-->' e1" := (pstep__Class e0 (Some a) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[' a ']==>' e1" := (estep__Class e0 (Some a) e1) (at level 82, e1 at next level).
#[global]
Notation "G '⊦' e ':' t" := (vDash__Class G e t) (at level 82, e at next level, t at next level).
#[global]
Notation "'[⋅]'" := (Gnil).

Lemma notin_dom_split { A : Type } { H : HasEquality A } { B : Type } (m1 m2 : mapind H B) (x : A) (v : B) :
  ~ In x (dom(m1 ◘ m2)) ->
  ~ In x (dom m1) /\ ~ In x (dom m2)
.
Proof.
  remember (m1 ◘ m2) as m0; revert m1 m2 Heqm0; induction m0; cbn; intros m1 m2 Heqm0 H0.
  - destruct m1, m2; inv Heqm0; split; intros [].
  - destruct (eq_dec a x); subst.
    + exfalso; exact (H0 (or_introl Logic.eq_refl)).
    + destruct m1, m2; cbn in Heqm0.
      * inv Heqm0.
      * inv Heqm0; cbn; split; easy.
      * fold (append m1 (mapNil _ _)) in Heqm0. fold (dom m0) in H0.
        rewrite append_nil in Heqm0. split; inv Heqm0; cbn; easy.
      * fold (append m1 (a1 ↦ b1 ◘ m2)) in Heqm0.
        fold (dom m0) in H0.
        inv Heqm0.
        assert (~ In x (dom(m1 ◘ a1 ↦ b1 ◘ m2))).
        intros X; specialize (H0 (or_intror X)); easy.
        specialize (IHm0 m1 (a1 ↦ b1 ◘ m2) Logic.eq_refl H2).
        destruct (IHm0) as [IHm0a IHm0b]; split; try easy.
        intros []; subst; easy.
Qed.
Lemma nodupinv_split { A : Type } { H : HasEquality A } { B : Type } (m1 m2 : mapind H B) :
  nodupinv (m1 ◘ m2) ->
  nodupinv m1 /\ nodupinv m2
.
Proof.
  remember (m1 ◘ m2) as m0; revert m1 m2 Heqm0; induction m0; cbn; intros m m' Heqm0 H'; inv H'.
  - inv Heqm0; destruct m, m'; inv H1; split; constructor.
  - destruct m; inv Heqm0.
    + split; cbn in H0; inv H0; now constructor.
    + destruct (IHm0 m m' Logic.eq_refl H4) as [IHm0__a IHm0__b].
      split; trivial; constructor; trivial.
      apply notin_dom_split in H2 as [H2__a H2__b]; trivial.
Qed.
Lemma nodupinv_cons_snoc { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (a : A) (b : B) :
  nodupinv (a ↦ b ◘ m) <-> nodupinv (m ◘ a ↦ b ◘ mapNil H B)
.
Proof.
  revert a b; induction m; intros; cbn; try easy.
  fold (append m (a0 ↦ b0 ◘ mapNil H B)).
  split; intros H0.
  - inv H0. constructor.
    + intros H1. inv H5. apply H4. revert H3 H1; clear; intros.
      destruct (eq_dec a0 a); subst.
      * exfalso; apply H3; now left.
      * clear H3. induction m; cbn in *.
        -- destruct H1; eauto.
        -- fold (dom m) in *. fold (m ◘ (a0 ↦ b0 ◘ mapNil H B)) in *.
           fold (dom (m ◘ a0 ↦ b0 ◘ mapNil H B)) in *.
           destruct H1; eauto.
    + apply IHm. inv H5. constructor; try easy. revert H3; clear; intros H0 H1; apply H0; now right.
  - inv H0. apply IHm in H5. inv H5. constructor.
    + intros H1. destruct (eq_dec a0 a); subst.
      * apply H3; clear; induction m; cbn; eauto.
      * destruct H1; congruence.
    + constructor; eauto. intros H1. apply H3; revert H1; clear; intros.
      induction m; cbn in *; eauto. fold (dom m) in *.
      fold (m ◘ (a0 ↦ b0 ◘ mapNil H B)). fold (dom (m ◘ (a0 ↦ b0 ◘ mapNil H B))).
      destruct H1; subst; eauto.
Qed.

Lemma nodupinv_swap { A : Type } { H : HasEquality A } { B : Type } (m1 m2 : mapind H B) :
  nodupinv (m1 ◘ m2) <-> nodupinv (m2 ◘ m1)
.
Proof.
  revert m2; induction m1; cbn; intros.
  - now rewrite append_nil.
  - fold (append m1 m2).
    change ((nodupinv ((a ↦ b ◘ m1) ◘ m2)) <-> (nodupinv (m2 ◘ a ↦ b ◘ m1))).
    split; intros H0.
    + change (nodupinv (m2 ◘ ((a ↦ b ◘ (mapNil H B)) ◘ m1))).
      rewrite <- append_assoc. apply IHm1. rewrite <- append_assoc. now apply nodupinv_cons_snoc.
    + change (nodupinv (m2 ◘ ((a ↦ b ◘ (mapNil H B)) ◘ m1))) in H0.
      rewrite <- append_assoc in H0. apply IHm1 in H0. rewrite <- append_assoc in H0. now apply nodupinv_cons_snoc.
Qed.

Module Type MOD.
  Parameter State : Type.
  Parameter Ev : Type.
  Parameter step : State -> option Ev -> State -> Prop.
  Parameter ev_eq : Ev -> Ev -> bool.
  Parameter string_of_event : Ev -> string.
  Parameter is_value : State -> bool.
  Parameter is_stuck : State -> Prop.
End MOD.
Module Mod (X : MOD).
  Export X.

  #[export]
  Instance State__Instance : RuntimeExprClass State := {}.
  #[export]
  Instance Event__Instance : TraceEvent Ev := {}.

  (** Since we only care about security properties anyways, it's fine to stay in "traces are lists"-land *)
  Inductive tracepref : Type :=
  | Tnil : tracepref
  | Tcons (e : Ev) (As : tracepref) : tracepref
  .
  Fixpoint Tappend (As Bs : tracepref) : tracepref :=
    match As with
    | Tnil => Bs
    | Tcons e Cs => Tcons e (Tappend Cs Bs)
    end
  .
  Notation "As '·' Bs" := (Tappend As Bs) (at level 81).

  Fixpoint string_of_tracepref_aux (t : tracepref) (acc : string) : string :=
    match t with
    | Tnil => acc
    | Tcons a Tnil => String.append acc (string_of_event a)
    | Tcons a As =>
        let acc' := String.append acc (String.append (string_of_event a) (" · "%string))
        in string_of_tracepref_aux As acc'
    end
  .
  Definition string_of_tracepref (t : tracepref) : string := string_of_tracepref_aux t (""%string).

  Inductive wherein (a : Ev) : tracepref -> nat -> Prop :=
  | whereinZ : forall (As : tracepref), wherein a (Tcons a As) 0
  | whereinS : forall (a0 : Ev) (As : tracepref) (n : nat),
               a <> a0 ->
               wherein a As n ->
               wherein a (Tcons a0 As) (S n)
  .
  Definition before (a0 a1 : Ev) (As : tracepref) : Prop :=
    exists n0 n1, wherein a0 As n0 /\ wherein a1 As n1 /\ n0 < n1
  .
  Lemma before_nothing a0 a1 :
    before a0 a1 Tnil -> False.
  Proof. unfold before; intros H; deex; destruct H as [H0 [H1 H2]]; inv H0. Qed.

  Lemma before_split a As a0 a1 n :
    before a0 a1 As \/ (a0 = a /\ wherein a1 As n) ->
    before a0 a1 (Tcons a As)
  .
  Proof.
  Admitted.

  Definition once (a : Ev) (As : tracepref) :=
    forall n m, wherein a As n -> wherein a As m -> n = m
  .
  (* Use this to define a coercion *)
  Definition ev_to_tracepref (e : Ev) : tracepref := Tcons e Tnil.

  Reserved Notation "e0 '==[' a ']==>*' e1" (at level 82, e1 at next level).
  Inductive star_step : State -> tracepref -> State -> Prop :=
  | ES_refl : forall (r1 : State),
      is_value r1 = true ->
      r1 ==[ Tnil ]==>* r1
  | ES_trans_important : forall (r1 r2 r3 : State) (a : Ev) (As : tracepref),
      step r1 (Some a) r2 ->
      ~is_stuck r2 ->
      r2 ==[ As ]==>* r3 ->
      r1 ==[ Tcons a As ]==>* r3
  | ES_trans_unimportant : forall (r1 r2 r3 : State) (As : tracepref),
      step r1 None r2 ->
      ~is_stuck r2 ->
      r2 ==[ As ]==>* r3 ->
      r1 ==[ As ]==>* r3
  where "e0 '==[' a ']==>*' e1" := (star_step e0 a e1).
  #[export]
  Hint Constructors star_step : core.
  Notation "e0 '==[]==>*' e1" := (star_step e0 (Tnil) e1) (at level 82, e1 at next level).
End Mod.

(*
Class ProgStep (A B C : Type) (Ev : Type) (Prog : Type)
               `{HasEquality C} `{SymbolClass A} `{RuntimeExprClass B} `{TraceEvent Ev} `{ProgClass C A Prog}
  := wstep__Class : Prog -> C -> tracepref -> B -> Prop.
#[global]
Notation "'PROG[' symbs '][' start ']====[' As ']===>' r" := (wstep__Class (Cprog__Class symbs) start As r) (at level 81, r at next level).
 *)

Module NoDupList.

Inductive nodupinv {A : Type} {H : HasEquality A} : list A -> Prop :=
| nodupinvNil : nodupinv (List.nil)
| nodupinvCons : forall (x : A) (xs : list A),
    ~(List.In x xs) ->
    nodupinv xs ->
    nodupinv (List.cons x xs)
.
Fixpoint undup {A : Type} {H : HasEquality A} (xs : list A) : option(list A) :=
  match xs with
  | List.nil => Some(List.nil)
  | List.cons x xs' =>
    match List.find (fun y => eq x y) xs', undup xs' with
    | None, Some xs' => Some(List.cons x xs')
    | _, _ => None
    end
  end
.
Lemma undup_refl {A : Type} {H : HasEquality A} (xs ys : list A) :
  undup xs = Some ys -> xs = ys.
Proof.
  revert ys; induction xs; intros ys H0.
  - now inv H0.
  - cbn in H0. destruct (option_dec (List.find (fun y : A => eq a y) xs)) as [Hx|Hy].
    + apply not_eq_None_Some in Hx as [zs Hx]; rewrite Hx in H0; congruence.
    + rewrite Hy in H0; destruct (option_dec (undup xs)) as [Ha|Hb].
      * apply not_eq_None_Some in Ha as [ys' Ha]; rewrite Ha in H0; rewrite (IHxs ys' Ha); now inv H0.
      * rewrite Hb in H0; congruence.
Qed.
Lemma nodupinv_equiv_undup {A : Type} {H : HasEquality A} (xs : list A) :
  undup xs = Some xs <-> nodupinv xs.
Proof.
  induction xs; cbn; split; try easy.
  - constructor.
  - intros H0; destruct (option_dec (List.find (fun y : A => eq a y) xs)) as [Hx | Hy].
    apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H0; inv H0.
    rewrite Hy in H0.
    destruct (option_dec (undup xs)) as [Hx | Hy']; try rewrite Hy' in H0; inv H0.
    apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H2; inv H2.
    constructor; try apply IHxs; eauto.
    intros Ha. eapply List.find_none in Hy; eauto. rewrite eq_refl in Hy. easy.
  - intros H0; inv H0; destruct (option_dec (List.find (fun x : A => eq a x) xs)) as [Hx | Hy].
    apply not_eq_None_Some in Hx as [a' Hx].
    apply List.find_some in Hx as [Hx1 Hx2].
    rewrite eqb_eq in Hx2; subst; contradiction.
    rewrite Hy. destruct (option_dec (undup xs)) as [Hx | Hy'].
    apply not_eq_None_Some in Hx as [m'' Hx]. rewrite Hx. f_equal. f_equal. apply undup_refl in Hx; easy.
    apply IHxs in H4. congruence.
Qed.
Definition push { A : Type } { H : HasEquality A } (x : A) (xs : list A) : option (list A) :=
  match undup (List.cons x xs) with
  | Some xs' => Some xs'
  | None => None
  end
.
Lemma push_refl { A : Type } { H : HasEquality A } (x : A) (xs ys : list A) :
  push x xs = Some ys -> cons x xs = ys.
Proof.
  intros H0; unfold push in H0; destruct (option_dec (undup xs)) as [Hx|Hy].
  - apply not_eq_None_Some in Hx as [zs Hx]. cbn in H0. rewrite (undup_refl xs Hx) in *.
    destruct (option_dec (List.find (fun y : A => eq x y) zs)) as [Ha|Hb].
    + apply not_eq_None_Some in Ha as [ws Ha]. now rewrite Ha in H0.
    + rewrite Hb in H0. rewrite <- (undup_refl xs Hx) in H0. rewrite Hx in H0. now inv H0.
  - cbn in H0. destruct (option_dec (List.find (fun y : A => eq x y) xs)) as [Ha|Hb].
    + apply not_eq_None_Some in Ha as [ws Ha]. now rewrite Ha in H0.
    + now rewrite Hb, Hy in H0.
Qed.
Lemma push_ok { A : Type } { H : HasEquality A } (x : A) (xs : list A) :
  push x xs = Some (List.cons x xs) -> nodupinv (List.cons x xs).
Proof.
  intros H0. unfold push in H0.
  destruct (option_dec (undup (List.cons x xs))) as [Hx|Hy]; try (rewrite Hy in *; congruence);
  apply not_eq_None_Some in Hx as [m'' Hx]; rewrite Hx in H0; inv H0;
  apply nodupinv_equiv_undup; cbn in Hx.
  destruct (option_dec (List.find (fun y : A => eq x y) xs)) as [Ha|Hb].
  - apply not_eq_None_Some in Ha as [ys Ha]; now rewrite Ha in Hx.
  - rewrite Hb in Hx.
    destruct (option_dec (undup xs)) as [Hc|Hd].
    + apply not_eq_None_Some in Hc as [ws Hc]; apply undup_refl in Hc as Hc'; rewrite Hc in *;
      inv Hx; cbn; rewrite Hb; now rewrite Hc.
    + now rewrite Hd in Hx.
Qed.

End NoDupList.
