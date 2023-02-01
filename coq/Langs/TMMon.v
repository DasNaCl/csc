Set Implicit Arguments.
Require Import Strings.String CSC.Langs.Util CSC.Util.

(** The type used for variable names. *)
Definition vart := string.

(** References *)
Inductive loc : Type :=
| addr : nat -> loc
.
Lemma loc_dec (x y : loc) : {x = y} + {x <> y}.
Proof.
  destruct x, y, (PeanoNat.Nat.eq_dec n n0); subst; ((now left) + right); congruence.
Defined.
(** Types of temporal memory safe events. *)
Variant event : Type :=
| Salloc (ℓ : loc) : event
| Sdealloc (ℓ : loc) : event
| Suse (ℓ : loc) : event
| Scrash : event
.
Definition eventeq (a0 a1 : event) : bool :=
  match a0, a1 with
  | Salloc(addr ℓ0), Salloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Sdealloc(addr ℓ0), Sdealloc(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Suse(addr ℓ0), Suse(addr ℓ1) => Nat.eqb ℓ0 ℓ1
  | Scrash, Scrash => true
  | _, _ => false
  end
.
(** Pretty-printing function for better debuggability *)
Definition string_of_event (e : event) :=
  match e with
  | (Salloc (addr ℓ)) => String.append ("Alloc ℓ"%string) (string_of_nat ℓ)
  | (Sdealloc (addr ℓ)) => String.append ("Dealloc ℓ"%string) (string_of_nat ℓ)
  | (Suse (addr ℓ)) => String.append ("Get ℓ"%string) (string_of_nat ℓ)
  | (Scrash) => "↯"%string
  end
.

(** Locations *)
Definition Loc := list loc.
(** Abstract Store *)
Record TMSMonitor := {
  A: Loc ;
  F: Loc
}.

Definition emptytmsmon : TMSMonitor := {|
  A := List.nil ;
  F := List.nil
|}.
#[local]
Notation "∅" := (emptytmsmon) (at level 82).

Definition entails (T1 T2 : TMSMonitor) := forall x, List.In x T1.(F) -> List.In x T2.(F).
Definition contains (ℓ : loc) (T : TMSMonitor) := List.In ℓ T.(A) /\ ~(List.In ℓ T.(F)).
Definition notin (ℓ : loc) (T : TMSMonitor) := ~(List.In ℓ T.(F)) /\ ~(List.In ℓ T.(A)).
Definition extend (ℓ : loc) (T : TMSMonitor) : TMSMonitor := {|
  A := List.cons ℓ T.(A) ;
  F := T.(F)
|}.
Definition without (T : TMSMonitor) (ℓ : loc) : TMSMonitor := {|
  A := List.remove loc_dec ℓ T.(A) ;
  F := List.cons ℓ T.(F)
|}.
Definition append (T1 T2 : TMSMonitor) := {|
  A := List.app T1.(A) T2.(A) ;
  F := List.app T1.(F) T2.(F) ;
|}.
#[local]
Notation "T1 '⊆__F' T2" := (entails T1 T2) (at level 82, T2 at next level).
#[local]
Notation "ℓ '∈' T" := (contains ℓ T) (at level 82, T at next level).
#[local]
Notation "ℓ '∉' T" := (notin ℓ T) (at level 82, T at next level).
#[local]
Notation "'{' ℓ '}' '∪' T" := (extend ℓ T) (at level 82, T at next level).
#[local]
Notation "T '∖' '{' ℓ '}'" := (without T ℓ) (at level 82, ℓ at next level).

Lemma same_tmon (T : TMSMonitor) :
  T = {| A := T.(A) ; F := T.(F) |}.
Proof. now destruct T. Qed.

Lemma fold_extend (ℓ : loc) (T : TMSMonitor) :
  ({ ℓ } ∪ T) = {| A := List.cons ℓ T.(A) ; F := T.(F) |}.
Proof. now destruct T. Qed.

Lemma fold_append_A (T1 T2 : TMSMonitor) :
  (append T1 T2).(A) = List.app T1.(A) T2.(A).
Proof.
  destruct T1; cbn.
  induction A0, F0; try unfold append; cbn; easy.
Qed.

Lemma fold_append_F (T1 T2 : TMSMonitor) :
  (append T1 T2).(F) = List.app T1.(F) T2.(F).
Proof.
  destruct T1; cbn.
  induction A0, F0; try unfold append; cbn; easy.
Qed.

Lemma fold_append (T1 T2 : TMSMonitor) :
  append T1 T2 = {| A := List.app T1.(A) T2.(A) ; F := List.app T1.(F) T2.(F) |}.
Proof.
  destruct T1; cbn.
  induction A0, F0; try unfold append; cbn; easy.
Qed.

Lemma loc_inside_split (T1 T2 : TMSMonitor) (ℓ : loc) :
  ℓ ∈ append T1 (append ({ℓ} ∪ TMMon.emptytmsmon) T2)
.
Proof.
  rewrite fold_append; unfold contains; cbn; split; 
  try (rewrite List.in_app_iff; right; cbn; left; auto).
  (* stuck because we need information that loc wasn't already in freed for T1 and T2 *)
Admitted.

#[global]
Hint Resolve loc_inside_split : core.

Lemma remove_loc_from_union (T1 T2 : TMSMonitor) (ℓ : loc) :
  append T1 T2 = (append T1 (append ({ℓ} ∪ emptytmsmon) T2) ∖ {ℓ})
.
Proof.
  repeat rewrite fold_append; cbn.
  unfold without; cbn.
  (* can this really be true ? *)
Admitted.

(** Step Relations *)
Inductive step : TMSMonitor -> option event -> TMSMonitor -> Prop :=
| TMS_uninteresting : forall (T__TMS : TMSMonitor),
    step T__TMS None T__TMS
| TMS_use : forall (T__TMS : TMSMonitor) (ℓ : loc),
    ℓ ∈ T__TMS ->
    step T__TMS (Some(Suse ℓ)) T__TMS
| TMS_alloc : forall (T__TMS T__TMS' : TMSMonitor) (ℓ : loc),
    T__TMS' = ({ ℓ } ∪ T__TMS) ->
    ℓ ∉ T__TMS ->
    step T__TMS (Some(Salloc ℓ)) T__TMS'
| TMS_dealloc : forall (T__TMS T__TMS' : TMSMonitor) (ℓ : loc),
    ℓ ∈ T__TMS ->
    T__TMS' = (T__TMS ∖ { ℓ }) ->
    step T__TMS (Some(Sdealloc ℓ)) T__TMS'
.

Module ModAux <: CSC.Langs.Util.MOD.
  Definition State := TMSMonitor.
  Definition Ev := event.
  Definition ev_eq := eventeq.
  Definition step := step.
  Definition string_of_event := string_of_event.
  Definition is_value := fun (_ : State) => true.
  Definition is_stuck := fun (x : State) => False.
End ModAux.
Module TMSMod := CSC.Langs.Util.Mod(ModAux).
Import TMSMod.

(** Definition of Temporal Memory Safety on Traces *)
Definition tmssafe (As : tracepref) :=
  forall ℓ, (before (Salloc ℓ) (Sdealloc ℓ) As
    /\ ~(before (Suse ℓ) (Salloc ℓ)) As
    /\ ~(before (Sdealloc ℓ) (Suse ℓ)) As)
.
(** Definition of Temporal Memory Safety on Traces, using our monitor. *)
Definition TMS (As : tracepref) :=
  exists T__TMS, ∅ ==[As]==>* T__TMS
.

Axiom Salloc_imp_Sdealloc : forall As ℓ x, wherein (Salloc ℓ) As x -> (exists x, wherein (Sdealloc ℓ) As x).

Definition simptmssafe (As : tracepref) :=
  forall ℓ n, wherein (Salloc ℓ) As n -> before (Salloc ℓ) (Sdealloc ℓ) As
.

Lemma simptmssafe_nil : simptmssafe nil.
Proof.
  unfold simptmssafe; intros.
  apply wherein_nil in H; contradiction.
Qed.

(* Show the above are equally strong...? *)
Theorem TMS_refines_tmssafe As :
  TMS As -> simptmssafe As.
Proof.
  intros [T__TMS H].
  induction H; try easy; try apply simptmssafe_nil.
  intros ℓ n H2.  
  inv H. 
  - unfold simptmssafe;
    apply before_split with (n := n); left.
    destruct (IHstar_step ℓ (pred n)).
    apply wherein_predecessor with (b := Suse ℓ0); try easy.
    deex; destruct H as [H6 [H7 H8]];
    exists x,n1; repeat split; easy.
  - unfold notin in H6; destruct H6 as [H3 H4].
    assert (H5 : exists x, wherein (Sdealloc ℓ) (Salloc ℓ0 :: As)%list x).
      { apply Salloc_imp_Sdealloc with (x := n); assumption. }
    deex.
    destruct n. 
    + apply whereinE in H2; inversion H2; rewrite H6 in H5.
      exists 0,x; repeat split; try assumption.
      destruct x.
      * apply whereinE in H5; inversion H5.
      * apply Gt.gt_Sn_O. 
    + unfold simptmssafe in IHstar_step.
      destruct (IHstar_step ℓ (pred (S n))).
      * apply whereinE in H2; inversion H2.
        apply whereinE in H6.
        rewrite PeanoNat.Nat.pred_succ; assumption. 
      * deex; destruct H as [H6 [H7 H8]].
        exists (x0 + 1), (n1 + 1).
        apply wherein_implies_wherein_cons with (b := Salloc ℓ0) in H7.
        assert (x_eq: x = n1 + 1).
          { eapply wherein_eq. apply H5. apply H7. }
        apply wherein_implies_wherein_cons with (b := Salloc ℓ0) in H6.
        assert (n_eq: x0 + 1 = S n).
          { eapply wherein_eq. apply H6. apply H2. }
        rewrite PeanoNat.Nat.add_1_r in n_eq; injection n_eq as n_eq.
        subst; repeat split; try assumption.
        repeat rewrite PeanoNat.Nat.add_1_r; now apply Lt.lt_n_S.
  - unfold simptmssafe;
    apply before_split with (n := n); left;
    destruct (IHstar_step ℓ (pred n)).
    apply wherein_predecessor with (b := Sdealloc ℓ0); try easy.
    deex; destruct H as [H6 [H7 H8]];
    exists x,n1; repeat split; easy.
  Qed. 
  
Module TMMonNotation.
Notation "T1 '⊆__F' T2" := (entails T1 T2) (at level 82, T2 at next level).
Notation "ℓ '∈' T" := (contains ℓ T) (at level 82, T at next level).
Notation "ℓ '∉' T" := (notin ℓ T) (at level 82, T at next level).
Notation "'{' ℓ '}' '∪' T" := (extend ℓ T) (at level 82, T at next level).
Notation "T '∖' '{' ℓ '}'" := (without T ℓ) (at level 82, ℓ at next level).
End TMMonNotation.
