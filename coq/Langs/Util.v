Set Implicit Arguments.
Require Import Lists.List Strings.String CSC.Util RelationClasses.

Section Util.

Class HasEquality (A : Type) := {
  eq : A -> A -> bool ;
  eq_refl : forall (a : A), eq a a = true ;
  eqb_eq : forall (a b : A), eq a b = true <-> a = b ;
  neqb_neq : forall (a b : A), eq a b = false <-> a <> b ;
}.

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
Proof. Admitted.
Lemma nodupinv_equiv_undup {A : Type} {H : HasEquality A} { B : Type } (m : mapind H B) :
  undup m = Some m <-> nodupinv m.
Proof. Admitted.
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

Definition splitat { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) (x : A)
  : option((mapind H B) * A * B * (mapind H B)) :=
  let fix doo (accM : mapind H B) (m : mapind H B) :=
    match m with
    | mapNil _ _ => None
    | mapCons a b m' => if eq a x then
                         Some(accM, a, b, m')
                       else
                         let* aM := a ↦ b ◘ accM in
                         doo aM m'
    end
  in doo (mapNil H B) m
.

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
                          | Some m'' => a ↦ b ◘ m''
                          end
    end
  in doo m
.
Lemma nodupinv_mset { A : Type } { H : HasEquality A } { B : Type } (m m' : mapind H B) (x : A) (v : B) :
  nodupinv m ->
  Some m' = mset m x v ->
  nodupinv m'
.
Proof. Admitted.
Definition MIn { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) : Prop :=
  mget m x = Some v
.
Definition MSubset { A : Type } { H : HasEquality A } { B : Type } (m1 m2 : mapind H B) : Prop :=
  forall (x : A) (v : B), MIn m1 x v -> MIn m2 x v
.
Lemma cons_msubset { A : Type } { H : HasEquality A } { B : Type } (m m' : mapind H B) (x : A) (v : B) :
  Some m' = (x ↦ v ◘ m) ->
  MSubset m m'.
Proof.
Admitted.

#[global]
Instance MSubset__Transitivity { A : Type } { H : HasEquality A } { B : Type } :
  Transitive (fun (a b : mapind H B) => MSubset a b).
Proof. intros x y z Ha Hb f w Hc; now apply Hb, Ha. Qed.

Lemma mget_min {A : Type} { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B) :
  mget m x = Some v <->
  MIn m x v
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

Lemma splitat_elim { A : Type } {H : HasEquality A} {B : Type} (m1 m2 : mapind H B) (x : A) (v : B) :
  splitat (m1 ◘ x ↦ v ◘ m2) x = Some (m1, x, v, m2).
Proof. Admitted.

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
  Fixpoint wherein_aux (As : tracepref) (a : Ev) (n : nat) : option nat :=
    match As with
    | Tnil => None
    | Tcons e As' => if ev_eq a e then Some n else wherein_aux As' a (S n)
    end
  .
  Lemma wherein_aux_impossible As a n :
    ~(wherein_aux As a (S n) = Some 0).
  Proof. revert n; induction As; try easy; cbn; destruct (ev_eq a e); try easy. Qed.
  Definition wherein (As : tracepref) (a : Ev) : option nat :=
    wherein_aux As a 0
  .
  Definition before (a0 a1 : Ev) (As : tracepref) :=
    forall n, (wherein As a0) = Some n -> exists m, (wherein As a1) = Some m /\ n < m
  .
  Lemma before_split a As a0 a1 :
    before a0 a1 As \/ (a0 = a /\ wherein As a1 <> None) ->
    before a0 a1 (Tcons a As).
  Proof. Admitted.
  Definition once (a : Ev) (As : tracepref) :=
    forall n, (wherein As a) = Some n -> ~exists m, (wherein As a) = Some m /\ n <> m
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

Lemma nodupinv_whocares { A : Type } { H : HasEquality A } { B : Type } (a : A) (b b' : B) (m m' : mapind H B) :
  nodupinv (m ◘ a ↦ b ◘ m') <-> nodupinv (m ◘ a ↦ b' ◘ m')
.
Proof. Admitted.

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
  split.
  - induction xs; intros H0; constructor.
    + destruct (option_dec (List.find (fun y : A => eq a y) xs)) as [Hx|Hy].
      * cbn in *; apply not_eq_None_Some in Hx as [zs Hx]; now rewrite Hx in H0.
      * cbn in *; rewrite Hy in H0. intros H1. admit.
    + apply IHxs. admit.
  - induction 1; eauto. cbn. rewrite IHnodupinv.
    destruct (option_dec (List.find (fun y : A => eq x y) xs)) as [Hx|Hy].
    + apply not_eq_None_Some in Hx as [zs Hx]. rewrite Hx. admit.
    + now rewrite Hy.
Admitted.
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
