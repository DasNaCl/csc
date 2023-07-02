Set Implicit Arguments.
Require Import Strings.String CSC.Util CSC.Sets CSC.Props Coq.Program.Equality Lia.


(** * This file defines the various monitors from the paper. *)

(** General structure of monitors. This time as module for namespacing. *)
Module Type MonitorT.
  Parameter AbsState : Type.
  Parameter EmptyState : AbsState.
  Parameter ValueState : AbsState -> Prop.
  Parameter AbsEv : Type.
  Parameter MonCheck : AbsState -> option AbsEv -> AbsState -> Prop.
  Parameter string_of_absev : AbsEv -> string.

  Parameter cong_e : option Props.Event -> option AbsEv -> Prop.
End MonitorT.

Module Monitor (M : MonitorT) <: MonitorT.
  Include M.
  #[export]
  Instance Trace__Instance : TraceParams := {
    Ev := AbsEv ;
    string_of_event := string_of_absev ;
  }.
  #[export]
  Instance MonInstance : LangParams := {
    State := AbsState;
    Trace__Instance := Trace__Instance;
    step := MonCheck;
    is_value := ValueState;
  }.
  Definition tracepref := @Util.tracepref Trace__Instance.
  (** Monitor traces must not stutter, which makes sense, because monitors should operate on relevant information. *)
  (** The empty event is not relevant, in case you wondered. *)
  Inductive cong : Props.tracepref -> tracepref -> Prop :=
  | cong_refl : cong nil nil
  | cong_stutter_L : forall (b : AbsEv)
                       (Bs : tracepref)
                       (As : Props.tracepref),
      cong_e None (Some b) ->
      cong As Bs ->
      cong As (List.cons b Bs)
  | cong_stutter_R : forall (a : Props.Event)
                       (Bs : tracepref)
                       (As : Props.tracepref),
      cong_e (Some a) None ->
      cong As Bs ->
      cong (List.cons a As) Bs
  | cong_trans : forall (b : AbsEv)
                   (a : Props.Event)
                   (Bs : tracepref)
                   (As : Props.tracepref),
      cong_e (Some a) (Some b) ->
      cong As Bs ->
      cong (List.cons a As) (List.cons b Bs)
  .
  #[export]
  Hint Constructors cong : core.

  Definition sat (As : Props.tracepref) : Prop :=
    exists (Bs : tracepref) (T : State),
      cong As Bs /\ @star_step MonInstance EmptyState Bs T
  .
  Definition gsat (As : Props.tracepref) (T0 : State) : Prop :=
    exists (Bs : tracepref) (T : State),
      cong As Bs /\ @star_step MonInstance T0 Bs T
  .
End Monitor.

(** Monitor Composition *)
Module CompMonitor (M1 M2 : MonitorT) <: MonitorT.
  Definition AbsState : Type := (M1.AbsState * M2.AbsState).
  Definition EmptyState : AbsState := (M1.EmptyState, M2.EmptyState).
  Definition AbsEv : Type := (option M1.AbsEv * option M2.AbsEv).
  Definition ValueState (S : AbsState) :=
    let '(S1, S2) := S in
    M1.ValueState S1 /\ M2.ValueState S2
  .
  Inductive MonCheck_i : AbsState -> option AbsEv -> AbsState -> Prop :=
  | combinedCheck (T1 T1' : M1.AbsState) (T2 T2' : M2.AbsState)
      (a1 : option M1.AbsEv) (a2 : option M2.AbsEv) :
    M1.MonCheck T1 a1 T1' ->
    M2.MonCheck T2 a2 T2' ->
    MonCheck_i (T1, T2) (Some (a1, a2)) (T1', T2')
  .
  Definition MonCheck := MonCheck_i.
  #[export]
  Hint Unfold MonCheck : core.
  Definition string_of_absev :=
    fun a => let '(a1, a2) := a in
          let s1 := match a1 with
                    | Some x => M1.string_of_absev x
                    | None => "ε"%string
                    end in
          let s2 := match a2 with
                    | Some x => M2.string_of_absev x
                    | None => "ε"%string
                    end in
          String.append "("%string (String.append s1
                                      (String.append ";"%string
                                         (String.append s2
                                            ")"%string)))
  .
  Definition cong_e := fun b (a : option AbsEv) =>
                         match a with
                         | Some(a1, a2) =>
                           M1.cong_e b a1 /\ M2.cong_e b a2
                         | None =>
                           M1.cong_e b None /\ M2.cong_e b None
                         end
  .
End CompMonitor.

(** Temporal Memory Safety Monitor *)
Module TMSMonAux <: MonitorT.
  Record AbsState_r : Type := {
      alloced : Props.LocControlListSet ;
      freed : Props.LocControlListSet ;
    }.
  Definition AbsState := AbsState_r.
  #[export]
  Hint Unfold AbsState : core.
  Definition EmptyState : AbsState := {|
    alloced := List.nil ;
    freed := List.nil ;
  |}.
  (** This enforces that all allocations must have been deallocated. *)
  Definition ValueState (S : AbsState) := S.(alloced) = nil.
  Definition append (T__TMS T__TMS' : AbsState) := {|
    alloced := List.app T__TMS.(alloced) T__TMS'.(alloced) ;
    freed := List.app T__TMS.(freed) T__TMS'.(freed)
  |}.
  Definition singleton (ℓ : loc) (σ : ControlTag) := {|
    alloced := List.cons (ℓ, σ) nil ;
    freed := nil
  |}.
  Variant AbsEv_d : Type :=
  | AAbort
  | AAlloc (l : loc) (σ : ControlTag)
  | AUse (l : loc) (σ : ControlTag)
  | ADealloc (l : loc) (σ : ControlTag)
  .
  Definition AbsEv := AbsEv_d.
  #[export]
  Hint Unfold AbsEv : core.

  Inductive MonCheck_i : AbsState -> option AbsEv -> AbsState -> Prop :=
  | sms_uninteresting (T : AbsState) : MonCheck_i T None T
  | sms_abort (T : AbsState) : MonCheck_i T (Some AAbort) T
  | sms_use (T : AbsState) (l : loc) (σ : ControlTag) :
    List.In (l, σ) T.(alloced) ->
    ~(List.In (l, σ) T.(freed)) ->
    MonCheck_i T (Some(AUse l σ)) T
  | sms_alloc (T T' : AbsState) (l : loc) (σ : ControlTag) :
    ~(List.In (l, σ) T.(alloced)) ->
    ~(List.In (l, σ) T.(freed)) ->
    T' = {|
           alloced := List.app T.(alloced) (List.cons (l, σ) List.nil) ;
           freed := T.(freed) ;
         |} ->
    MonCheck_i T (Some(AAlloc l σ)) T'
  | sms_dealloc (T T' : AbsState) (l : loc) (σ : ControlTag) L0 L1 :
    List.In (l, σ) T.(alloced) ->
    ~(List.In (l, σ) T.(freed)) ->
    T.(alloced) = List.app L0 (List.cons (l, σ) L1) ->
    T' = {|
           alloced := List.app L0 L1 ;
           freed := List.app T.(freed) (List.cons (l, σ) List.nil) ;
         |} ->
    MonCheck_i T (Some(ADealloc l σ)) T'
  .
  Definition MonCheck := MonCheck_i.
  #[export]
  Hint Unfold MonCheck : core.
  Definition string_of_absev :=
    fun a => match a with
          | AAbort => "abs↯"%string
          | AAlloc (addr _n) _ => "absAlloc ℓ"%string
          | ADealloc (addr _n) _ => "absDealloc ℓ"%string
          | AUse (addr _n) _ => "absUse ℓ"%string
          end
  .
  Inductive cong_i : option Props.Event -> option AbsEv -> Prop :=
  | tms_alloc_authentic : forall l n t,
      cong_i (Some(Props.PreEv (Props.Alloc l n) t SUnlock))
             (Some(AAlloc l t))
  | tms_dealloc_authentic : forall l t,
      cong_i (Some(Props.PreEv (Props.Dealloc l) t SUnlock))
             (Some(ADealloc l t))
  | tms_use_authentic : forall l n t σ,
      cong_i (Some(Props.PreEv (Props.Use l n) t σ))
             (Some(AUse l t))
  | tms_branch_authentic : forall n t σ,
      cong_i (Some(Props.PreEv (Props.Branch n) t σ))
             None
  | tms_binop_authentic : forall n t σ,
      cong_i (Some(Props.PreEv (Props.Binop n) t σ))
             None
  | tms_empty_authentic :
      cong_i None None
  | tms_abort_authentic :
      cong_i (Some(Props.Aborted))
             (Some(AAbort))
  .
  Definition cong_e := cong_i.
  #[export]
  Hint Unfold cong_e : core.
End TMSMonAux.
Module TMSMon := Monitor TMSMonAux.
(** Spatial Memory Safety Monitor *)
Module LocNatList <: ListBase.
  Definition A : Type := loc * nat.
  Definition eqb := fun x y =>
                      let '(l0, n0) := x in
                      let '(l1, n1) := y in
                      (andb (loc_eqb l0 l1) (Nat.eqb n0 n1)).
  Lemma eqb_eq_lem : forall (a b : A), eqb a b = true <-> a = b.
  Proof.
    split; intros.
    - destruct a, b; unfold eqb in H. apply bool_and_equiv_prop in H as [H H'].
      change ((l == l0) = true) in H; rewrite eqb_eq in H;
      apply PeanoNat.Nat.eqb_eq in H'; subst. reflexivity.
    - subst. destruct b; cbn. apply bool_and_equiv_prop; split.
      change ((l == l) = true). apply eq_refl. apply PeanoNat.Nat.eqb_eq. reflexivity.
  Qed.
  #[export]
  Instance LocNatList__Instance : HasEquality A := {|
    eq := eqb ;
    eqb_eq := eqb_eq_lem ;
  |}.
End LocNatList.
Module LocNatListSets <: Sig := SetTheoryList (LocNatList).
Definition LocNatListSet := LocNatListSets.set.
Module SMSMonAux <: MonitorT.
  Definition AbsState := LocNatListSet.
  #[export]
  Hint Unfold AbsState : core.
  Definition EmptyState : AbsState := List.nil.
  Definition ValueState (_ : AbsState) := True.
  Variant AbsEv_d : Type :=
  | AAbort
  | AAlloc (l : loc) (n : nat)
  | AUse (l : loc) (n : nat)
  .
  Definition AbsEv := AbsEv_d.
  #[export]
  Hint Unfold AbsEv : core.

  Inductive MonCheck_i : AbsState -> option AbsEv -> AbsState -> Prop :=
  | sms_uninteresting (T : AbsState) : MonCheck_i T None T
  | sms_abort (T : AbsState) : MonCheck_i T (Some AAbort) T
  | sms_use (T : AbsState) (l : loc) (n m : nat) :
    List.In (l, m) T ->
    NoDupList.undup (List.map (fun '(a,_b) => a) T) <> None ->
    n < m ->
    MonCheck_i T (Some(AUse l n)) T
  | sms_alloc (T T' : AbsState) (l : loc) (n : nat) :
    (forall (m : nat), ~ LocNatListSets.el (l, m) T) ->
    T' = (List.cons (l,n) T) ->
    MonCheck_i T (Some(AAlloc l n)) T'
  .
  Definition MonCheck := MonCheck_i.
  #[export]
  Hint Unfold MonCheck : core.
  Definition string_of_absev :=
    fun a => match a with
          | AAbort => "abs↯"%string
          | AAlloc (addr _n) n => "absAlloc ℓ"%string
          | AUse (addr _n) n => "absUse ℓ"%string
          end
  .
  Inductive cong_i : option Props.Event -> option AbsEv -> Prop :=
  | sms_alloc_authentic : forall l n t σ,
      cong_i (Some(Props.PreEv (Props.Alloc l n) t σ))
             (Some(AAlloc l n))
  | sms_dealloc_authentic : forall l t σ,
      cong_i (Some(Props.PreEv (Props.Dealloc l) t σ))
             None
  | sms_use_authentic : forall l n t σ,
      cong_i (Some(Props.PreEv (Props.Use l n) t σ))
             (Some(AUse l n))
  | sms_branch_authentic : forall n t σ,
      cong_i (Some(Props.PreEv (Props.Branch n) t σ))
             None
  | sms_binop_authentic : forall n t σ,
      cong_i (Some(Props.PreEv (Props.Binop n) t σ))
             None
  | sms_empty_authentic :
      cong_i None None
  | sms_abort_authentic :
      cong_i (Some(Props.Aborted))
             (Some(AAbort))
  .
  Definition cong_e := cong_i.
  #[export]
  Hint Unfold cong_e : core.
End SMSMonAux.
Module SMSMon := Monitor SMSMonAux.

(** Memory Safety *)
Module MSMonAux := CompMonitor TMSMonAux SMSMonAux.
Module MSMon := Monitor MSMonAux.

(** Strict Cryptographic Constan Time *)
Module sCCTMonAux <: MonitorT.
  Definition AbsState : Type := unit.
  Definition EmptyState : AbsState := tt.
  Definition ValueState (_ : AbsState) := True.
  Variant AbsEv_d : Type :=
  | AAbort
  | AAny
  .
  Definition AbsEv := AbsEv_d.
  #[export]
  Hint Unfold AbsEv : core.

  Inductive MonCheck_i : AbsState -> option AbsEv -> AbsState -> Prop :=
  | scct_abort (T : AbsState) : MonCheck_i T (Some AAbort) T
  .
  Definition MonCheck := MonCheck_i.
  #[export]
  Hint Unfold MonCheck : core.
  Definition string_of_absev :=
    fun a => match a with
          | AAbort => "abs↯"%string
          | AAny => "absAny"%string
          end
  .
  Inductive cong_i : option Props.Event -> option AbsEv -> Prop :=
  | scct_low_authentic : forall a__b t,
      cong_i (Some(Props.PreEv a__b t Props.SUnlock))
             None
  | scct_high_authentic : forall a__b t,
      cong_i (Some(Props.PreEv a__b t Props.SLock))
             (Some AAny)
  | scct_empty_authentic :
      cong_i None None
  | scct_abort_authentic :
      cong_i (Some(Props.Aborted))
             (Some(AAbort))
  .
  Definition cong_e := cong_i.
  #[export]
  Hint Unfold cong_e : core.
End sCCTMonAux.
Module sCCTMon := Monitor sCCTMonAux.

(** scct and ms *)
Module MSSCCTMonAux := CompMonitor MSMonAux sCCTMonAux.
Module MSSCCTMon := Monitor MSSCCTMonAux.

(** Proofs *)

(** Suitable generalized versions of the trace properties. Just a technical proof artefact. *)
Definition gsms (T__SMS : SMSMon.AbsState) : Props.prop :=
  fun As => (forall l n m t t' σ σ', (before (PreEv (Alloc l m) t σ) (PreEv (Use l n) t' σ') As \/ (in_t (PreEv (Use l n) t' σ') As /\ List.In (l, m) T__SMS)) ->
                              n < m)
.
Definition no_double_alloc : Props.prop :=
  fun As => forall l n m t p0 p1, wherein (PreEv(Alloc l n) t SUnlock) As p0 ->
                          wherein (PreEv(Alloc l m) t SUnlock) As p1 ->
                          p0 = p1
.
Definition gno_double_alloc (T__TMS : TMSMonAux.AbsState) : Props.prop :=
  fun As => forall l n t,
                    (List.In (l,t) T__TMS.(TMSMonAux.alloced) ->
                     ~exists p, wherein (PreEv (Alloc l n) t SUnlock) As p) \/
                    (~List.In (l,t) T__TMS.(TMSMonAux.alloced) ->
                     forall p' m, wherein (PreEv (Alloc l n) t SUnlock) As p' ->
                     ~exists p, wherein (PreEv (Alloc l m) t SUnlock) As p /\ p <> p')
.
Lemma step_nodoublealloc_abort T__TMS T__TMS' As :
  @step TMSMon.MonInstance T__TMS (Some(TMSMonAux.AAbort)) T__TMS' ->
  gno_double_alloc T__TMS' As ->
  gno_double_alloc T__TMS (Aborted :: As)%list
.
Proof.
Admitted.
Lemma step_nodoublealloc_use T__TMS T__TMS' l t n σ As :
  @step TMSMon.MonInstance T__TMS (Some(TMSMonAux.AUse l t)) T__TMS' ->
  gno_double_alloc T__TMS' As ->
  gno_double_alloc T__TMS (PreEv(Use l n) t σ :: As)%list
.
Proof.
Admitted.
Lemma step_nodoublealloc_dealloc T__TMS T__TMS' l t As :
  @step TMSMon.MonInstance T__TMS (Some(TMSMonAux.ADealloc l t)) T__TMS' ->
  gno_double_alloc T__TMS' As ->
  gno_double_alloc T__TMS (PreEv(Dealloc l) t SUnlock :: As)%list
.
Proof.
Admitted.
Lemma step_nodoublealloc_alloc T__TMS T__TMS' l n t As :
  @step TMSMon.MonInstance T__TMS (Some(TMSMonAux.AAlloc l t)) T__TMS' ->
  gno_double_alloc T__TMS' As ->
  gno_double_alloc T__TMS (PreEv(Alloc l n) t SUnlock :: As)%list
.
Proof.
  intros H; cbv in H; dependent induction H; intros.
  unfold gno_double_alloc; intros l' n' t'.
  destruct (eq_dec (l, t) (l', t')).
  - left; intros Ha Hb; deex. inv H2. contradiction.
  - specialize (H1 l' n' t'). destruct H1 as [H1 | H1].
    + left; intros Ha Hb; deex. eapply in_unsnoc in Ha as Ha'; eauto.
      specialize (H1 Ha'). apply H1.
      inv Hb; try easy. eauto.
    + right; intros Ha p' m Hb Hc; deex; destruct Hc as [Hc Hd].
      eapply notin_unsnoc' in Ha as Ha'; eauto.
      inv Hb; try easy. inv Hc; try easy.
      specialize (H1 Ha' n0 m H8). apply H1. exists n1. split; auto.
Qed.
Lemma no_double_alloc_true As T__TMS :
  TMSMon.gsat As T__TMS ->
  gno_double_alloc T__TMS As
.
Proof.
  unfold TMSMon.gsat; intros; deex; destruct H as [H0 H1].
  revert As H0; dependent induction H1; intros.
  - dependent induction H0.
    + left; cbv; intros; deex. inv H1.
    + assert ((nil : TMSMon.tracepref) ~= nil) by easy; specialize (IHcong H2); clear H2.
      unfold gno_double_alloc; intros. specialize (IHcong l n t). destruct IHcong as [IH|IH].
      * left; intros. specialize (IH H2). intros H3; deex; apply IH. inv H0; inv H3; try easy; exists n1; assumption.
      * right; intros. intros H4; deex; destruct H4 as [Ha Hb].
        inv H0; inv H3; inv Ha; try easy; specialize (IH H2 n1 m H8); eapply IH; exists n2; auto.
  - dependent induction H0; try easy.
    + inv H2. admit. admit.
    + inv H2; inversion H; subst; try easy; eauto using step_nodoublealloc_alloc,
                                                        step_nodoublealloc_dealloc,
                                                        step_nodoublealloc_use,
                                                        step_nodoublealloc_abort.
  - inv H. eauto.
Admitted.

Definition all_freed (T__TMS : ) : Props.prop :=
  star_step @TMSMonAux.MonInstance T__TMS

Definition gtms (T__TMS : TMSMon.AbsState) : Props.prop :=
  fun As => (forall l t, in_t (PreEv(Dealloc l) t SUnlock) ->
                 (in_t (PreEv(Alloc l n) t SUnlock) ->
                  before (PreEv(Alloc l n) t SUnlock) (PreEv(Dealloc l n) t SUnlock)))
.
Lemma nil_tms :
  Props.tms nil
.
Proof.
  repeat split; intros; inv H; exfalso; revert H1; clear; intros H; induction x; try inv H.
Qed.
Lemma nil_gtms T__TMS :
  gtms T__TMS nil
.
Proof.
  unfold gtms; repeat split; left; exists 0; intros; inv H; try (now inv H3 + now inv H2).
Qed.

Lemma nil_sms :
  Props.sms nil
.
Proof.
  unfold sms; intros; unfold_before; inv H.
Qed.
Lemma nil_gsms T__SMS :
  gsms T__SMS nil
.
Proof.
  unfold gsms; intros; destruct H; try unfold_before; inv H. inv H0. inv H.
Qed.

Lemma nil_ms :
  Props.ms nil
.
Proof.
  unfold Props.ms; eauto using nil_tms, nil_sms.
Qed.
Lemma binop_tms n t σ As :
  tms As ->
  tms (PreEv (Binop n) t σ :: As)%list
.
Proof.
  intros [H__TMS0 [H__TMS1 H__TMS2]]; repeat split; intros.
  - assert (PreEv (Alloc l n0) t0 SUnlock <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Dealloc l) t0 SUnlock <> PreEv (Binop n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto; erewrite eat_front_in_t in H0.
    erewrite <- eat_front_before; eauto. eauto.
  - assert (PreEv (Use l n0) t0 σ0 <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Alloc l m) t0 SUnlock <> PreEv (Binop n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto; try easy. erewrite eat_front_in_t in H0; eauto; try easy.
    erewrite <- eat_front_before; eauto; try easy.
  - assert (PreEv (Dealloc l) t0 SUnlock <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Use l n0) t0 σ0 <> PreEv (Binop n) t σ) by congruence.
    erewrite eat_front_in_t in H; erewrite eat_front_in_t in H0; eauto.
    erewrite <- eat_front_before; eauto.
Qed.
Lemma binop_gtms n t σ As T__TMS :
  gtms T__TMS As ->
  gtms T__TMS (PreEv (Binop n) t σ :: As)%list
.
Proof.
  (*
  induction As; intros H; unfold gtms, in_t; intros.
  - specialize (H l n0 t0 t' σ0 σ'); destruct H as [H|H].
    + left; intros; deex. inv H0. inv H7.
    + right; intros. specialize (H H0 H1); inv H. inv H2.
  - specialize (H l n0 t0 t' σ0 σ'); destruct H as [H|H].
    + left; intros; deex. inv H0. inv H1.
      assert (in_t (PreEv (Alloc l n0) t0 σ0) (a :: As))%list by (now exists n3).
      assert (in_t (PreEv (Dealloc l) t' σ') (a :: As))%list by (now exists n2).
      specialize (H H0 H1). destruct H as [Ha [Hb Hc]]. unfold_before. eapply wherein_eq in Ha, H__before0; eauto; subst.
      repeat split; try easy. exists (S n1); exists (S n4); repeat split; try (now constructor); lia.
    + right; intros. specialize (H H0 H1); unfold in_t in H; deex.
      exists (S n1). now constructor. *)
  (*
  induction As; cbn in *; intros H.
  - unfold gtms; unfold in_t; repeat split; intros; deex.
    inv H0. inv H7. inv H0. inv H7. inv H0. inv H7.
  - destruct H as [H0 [H1 H2]].
    unfold gtms; repeat split; intros.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Alloc l n0) t0 σ0) (a :: As))%list by (exists n3; eauto).
      assert (in_t (PreEv(Dealloc l) t' σ') (a::As))%list by (exists n2; eauto).
      specialize (H0 l n0 t0 t' σ0 σ' H H3) as [H0 | H0].
      * left. unfold before in H0; deex; destruct H0 as [H0 [H0' H0'']]. exists (S n1); exists (S n4).
        repeat split; try now constructor. lia.
      * now right.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Use l n0) t0 σ0) (a :: As))%list by (exists n3; eauto).
      assert (in_t (PreEv(Alloc l m) t' σ') (a::As))%list by (exists n2; eauto).
      specialize (H1 l n0 m t0 t' σ0 σ' H H3) as [H1 | H1].
      * left. intros H4; unfold before in H4; deex; destruct H4 as [H4 [H4' H4'']]; apply H1.
        inv H4. inv H4'. exists n5. exists n1. repeat split; try easy. lia.
      * now right.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Dealloc l) t0 σ0) (a::As))%list by (exists n3; eauto).
      assert (in_t (PreEv(Use l n0) t' σ') (a :: As))%list by (exists n2; eauto).
      specialize (H2 l n0 t0 t' σ0 σ' H H3) as [H2 | H2].
      * left. intros H4; unfold before in H4; deex; destruct H4 as [H4 [H4' H4'']]; apply H2.
        inv H4. inv H4'. exists n5. exists n1. repeat split; try easy. lia.
      * now right. *)
Admitted.
Lemma binop_sms n t σ As :
  sms As ->
  sms (PreEv (Binop n) t σ :: As)%list
.
Proof.
  intros H__SMS; unfold sms in *; intros.
    assert (PreEv (Alloc l m) t0 σ0 <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Use l n0) t' σ' <> PreEv (Binop n) t σ) by congruence.
    erewrite <- eat_front_before in H; eauto.
Qed.
Lemma binop_gsms n t σ As T__SMS :
  gsms T__SMS As ->
  gsms T__SMS (PreEv (Binop n) t σ :: As)%list
.
Proof.
  induction As; cbn in *; intros H; unfold gsms; intros; destruct H0 as [H0 | [H0a H0b]]; try unfold_before.
  inv H0. inv H7. inv H0a. inv H0. inv H6.
  destruct n1; try easy; destruct n2; try easy.
  specialize (H l n0 m t0 t' σ0 σ'). apply H; left. exists n1; exists n2. inv H0. inv H__before0. repeat split; eauto. lia.
  specialize (H l n0 m t0 t' σ0 σ'). apply H; right. inv H0a. destruct x; inv H0.
  split. exists x; easy. assumption.
Qed.
Lemma binop_ms n t σ As :
  ms As ->
  ms (PreEv (Binop n) t σ :: As)%list
.
Proof.
  unfold ms; intros [H__TMS H__SMS]; eauto using binop_sms, binop_tms.
Qed.
Lemma use_sms l n t σ As :
  sms As ->
  sms (PreEv (Use l n) t σ :: As)%list
.
Proof.
  intros H__SMS; unfold sms in *; intros.
    assert (PreEv (Alloc l0 m) t0 σ0 <> PreEv (Use l n) t σ) by congruence.
    destruct (eq_dec (PreEv (Use l0 n0) t' σ') (PreEv (Use l n) t σ)); subst.
    - unfold before in H1; deex; destruct H1 as [H1a [H1b H1c]]. unfold_before. inv H. inv H__before0; try congruence.
      lia.
    - erewrite <- eat_front_before in H; eauto.
Qed.
Lemma branch_tms n t σ As :
  tms As ->
  tms (PreEv (Branch n) t σ :: As)%list
.
Proof.
  intros [H__TMS0 [H__TMS1 H__TMS2]]; repeat split; intros.
  - assert (PreEv (Alloc l n0) t0 SUnlock <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Dealloc l) t0 SUnlock <> PreEv (Branch n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto; erewrite eat_front_in_t in H0.
    erewrite <- eat_front_before; eauto. eauto.
  - assert (PreEv (Use l n0) t0 σ0 <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Alloc l m) t0 SUnlock <> PreEv (Branch n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto; try easy. erewrite eat_front_in_t in H0; eauto; try easy.
    erewrite <- eat_front_before; eauto; try easy.
  - assert (PreEv (Dealloc l) t0 SUnlock <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Use l n0) t0 σ0 <> PreEv (Branch n) t σ) by congruence.
    erewrite eat_front_in_t in H; erewrite eat_front_in_t in H0; eauto.
    erewrite <- eat_front_before; eauto.
Qed.
Lemma branch_gtms n t σ As T__TMS :
  gtms T__TMS As ->
  gtms T__TMS (PreEv (Branch n) t σ :: As)%list
.
Proof.
  (*
  induction As; intros H; unfold gtms, in_t; intros.
  - specialize (H l n0 t0 t' σ0 σ'); destruct H as [H|H].
    + left; intros; deex. inv H0. inv H7.
    + right; intros. specialize (H H0 H1); inv H. inv H2.
  - specialize (H l n0 t0 t' σ0 σ'); destruct H as [H|H].
    + left; intros; deex. inv H0. inv H1.
      assert (in_t (PreEv (Alloc l n0) t0 σ0) (a :: As))%list by (now exists n3).
      assert (in_t (PreEv (Dealloc l) t' σ') (a :: As))%list by (now exists n2).
      specialize (H H0 H1). destruct H as [Ha [Hb Hc]]. unfold_before. eapply wherein_eq in Ha, H__before0; eauto; subst.
      repeat split; try easy. exists (S n1); exists (S n4); repeat split; try (now constructor); lia.
    + right; intros. specialize (H H0 H1); unfold in_t in H; deex.
      exists (S n1). now constructor. *)
  (*
  induction As; cbn in *; intros H.
  - unfold gtms; unfold in_t; repeat split; intros; deex.
    inv H0. inv H7. inv H0. inv H7. inv H0. inv H7.
  - destruct H as [H0 [H1 H2]].
    unfold gtms; repeat split; intros.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Alloc l n0) t0 σ0) (a :: As))%list by (exists n3; eauto).
      assert (in_t (PreEv(Dealloc l) t' σ') (a::As))%list by (exists n2; eauto).
      specialize (H0 l n0 t0 t' σ0 σ' H H3) as [H0 | H0].
      * left. unfold before in H0; deex; destruct H0 as [H0 [H0' H0'']]. exists (S n1); exists (S n4).
        repeat split; try now constructor. lia.
      * now right.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Use l n0) t0 σ0) (a :: As))%list by (exists n3; eauto).
      assert (in_t (PreEv(Alloc l m) t' σ') (a::As))%list by (exists n2; eauto).
      specialize (H1 l n0 m t0 t' σ0 σ' H H3) as [H1 | H1].
      * left. intros H4; unfold before in H4; deex; destruct H4 as [H4 [H4' H4'']]; apply H1.
        inv H4. inv H4'. exists n5. exists n1. repeat split; try easy. lia.
      * now right.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Dealloc l) t0 σ0) (a::As))%list by (exists n3; eauto).
      assert (in_t (PreEv(Use l n0) t' σ') (a :: As))%list by (exists n2; eauto).
      specialize (H2 l n0 t0 t' σ0 σ' H H3) as [H2 | H2].
      * left. intros H4; unfold before in H4; deex; destruct H4 as [H4 [H4' H4'']]; apply H2.
        inv H4. inv H4'. exists n5. exists n1. repeat split; try easy. lia.
      * now right. *)
Admitted.
Lemma branch_sms n t σ As :
  sms As ->
  sms (PreEv (Branch n) t σ :: As)%list
.
Proof.
  intros H__SMS; unfold sms in *; intros.
    assert (PreEv (Alloc l m) t0 σ0 <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Use l n0) t' σ' <> PreEv (Branch n) t σ) by congruence.
    erewrite <- eat_front_before in H; eauto.
Qed.
Lemma branch_gsms n t σ T__SMS As :
  gsms T__SMS As ->
  gsms T__SMS (PreEv (Branch n) t σ :: As)%list
.
Proof.
  induction As; cbn in *; intros H; unfold gsms; intros; destruct H0 as [H0 | [H0a H0b]]; try unfold_before.
  inv H0. inv H7. inv H0a. inv H0. inv H6.
  destruct n1; try easy; destruct n2; try easy.
  specialize (H l n0 m t0 t' σ0 σ'). apply H; left. exists n1; exists n2. inv H0. inv H__before0. repeat split; eauto. lia.
  specialize (H l n0 m t0 t' σ0 σ'). apply H; right. inv H0a. destruct x; inv H0.
  split. exists x; easy. assumption.
Qed.
Lemma branch_ms n t σ As :
  ms As ->
  ms (PreEv (Branch n) t σ :: As)%list
.
Proof.
  unfold ms; intros [H__TMS H__SMS]; eauto using branch_sms, branch_tms.
Qed.
Lemma dealloc_sms l t σ As :
  sms As ->
  sms (PreEv (Dealloc l) t σ :: As)%list
.
Proof.
    intros H__SMS; unfold sms in *; intros.
    assert (PreEv (Alloc l0 m) t0 σ0 <> PreEv (Dealloc l) t σ) by congruence.
    assert (PreEv (Use l0 n) t' σ' <> PreEv (Dealloc l) t σ) by congruence.
    erewrite <- eat_front_before in H; eauto.
Qed.
Lemma dealloc_gsms l t σ As T__SMS :
  gsms T__SMS As ->
  gsms T__SMS (PreEv (Dealloc l) t σ :: As)%list
.
Proof.
  induction As; cbn in *; intros H; unfold gsms; intros; destruct H0 as [H0 | [H0a H0b]]; try unfold_before.
  inv H0. inv H7. inv H0a. inv H0. inv H6.
  inv H0. inv H__before0.
  specialize (H l0 n m t0 t' σ0 σ'). apply H; left. exists n2; exists n0. repeat split; eauto. lia.
  specialize (H l0 n m t0 t' σ0 σ'). apply H; right. inv H0a. destruct x; inv H0.
  split. exists x; easy. assumption.
Qed.
Lemma aborted_sms As :
  sms As ->
  sms (Aborted :: As)%list
.
Proof.
  intros H__SMS; unfold sms in *; intros.
    assert (PreEv (Alloc l m) t σ <> Aborted) by congruence.
    assert (PreEv (Use l n) t' σ' <> Aborted) by congruence.
    erewrite <- eat_front_before in H; eauto.
Qed.
Lemma aborted_gsms As T__SMS :
  gsms T__SMS As ->
  gsms T__SMS (Aborted :: As)%list
.
Proof.
  induction As; cbn in *; intros H; unfold gsms; intros; destruct H0 as [H0 | [H0a H0b]]; try unfold_before.
  inv H0; inv H7. inv H0a; inv H0; inv H6.
  destruct n0; try easy; destruct n1; try easy;
  specialize (H l n m t t' σ σ'); apply H; left; exists n0; exists n1; inv H0; inv H__before0; repeat split; eauto; lia.
  specialize (H l n m t t' σ σ'); apply H; right; inv H0a; destruct x; inv H0;
  split; try (exists x; easy); assumption.
Qed.
Lemma aborted_gtms As T__TMS :
  gtms T__TMS As ->
  gtms T__TMS (Aborted :: As)%list
.
Proof.
  (*
  induction As; intros H; unfold gtms, in_t; intros.
  - specialize (H l n t t' σ σ'); destruct H as [H|H].
    + left; intros; deex. inv H0. inv H7.
    + right; intros. specialize (H H0 H1); inv H. inv H2.
  - specialize (H l n t t' σ σ'); destruct H as [H|H].
    + left; intros; deex. inv H0. inv H1.
      assert (in_t (PreEv (Alloc l n) t σ) (a :: As))%list by (now exists n2).
      assert (in_t (PreEv (Dealloc l) t' σ') (a :: As))%list by (now exists n1).
      specialize (H H0 H1). destruct H as [Ha [Hb Hc]]. unfold_before. eapply wherein_eq in Ha, H__before0; eauto; subst.
      repeat split; try easy. exists (S n0); exists (S n3); repeat split; try (now constructor); lia.
    + right; intros. specialize (H H0 H1); unfold in_t in H; deex.
      exists (S n0). now constructor. *)
  (*
  induction As; cbn in *; intros H.
  - unfold gtms; unfold in_t; repeat split; intros; deex.
    inv H0. inv H7. inv H0. inv H7. inv H0. inv H7.
  - destruct H as [H0 [H1 H2]].
    unfold gtms; repeat split; intros.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Alloc l n) t σ) (a :: As))%list by (exists n2; eauto).
      assert (in_t (PreEv(Dealloc l) t' σ') (a::As))%list by (exists n1; eauto).
      specialize (H0 l n t t' σ σ' H H3) as [H0 | H0].
      * left. unfold before in H0; deex; destruct H0 as [H0 [H0' H0'']]. exists (S n0); exists (S n3).
        repeat split; try now constructor. lia.
      * now right.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Use l n) t σ) (a :: As))%list by (exists n2; eauto).
      assert (in_t (PreEv(Alloc l m) t' σ') (a::As))%list by (exists n1; eauto).
      specialize (H1 l n m t t' σ σ' H H3) as [H1 | H1].
      * left. intros H4; unfold before in H4; deex; destruct H4 as [H4 [H4' H4'']]; apply H1.
        inv H4. inv H4'. exists n4. exists n0. repeat split; try easy. lia.
      * now right.
    + unfold in_t in H, H3; deex. inv H; inv H3. assert (in_t (PreEv(Dealloc l) t σ) (a::As))%list by (exists n2; eauto).
      assert (in_t (PreEv(Use l n) t' σ') (a :: As))%list by (exists n1; eauto).
      specialize (H2 l n t t' σ σ' H H3) as [H2 | H2].
      * left. intros H4; unfold before in H4; deex; destruct H4 as [H4 [H4' H4'']]; apply H2.
        inv H4. inv H4'. exists n4. exists n0. repeat split; try easy. lia.
      * now right. *)
Admitted.
Lemma SMSMon_step_use (T0 T1 : SMSMon.AbsState) l n :
  @step SMSMon.MonInstance T0 (Some (SMSMonAux.AUse l n)) T1 ->
  T0 = T1
.
Proof. intros H; now inv H. Qed.
Lemma SMSMon_step_aborted (T0 T1 : SMSMon.AbsState) :
  @step SMSMon.MonInstance T0 (Some (SMSMonAux.AAbort)) T1 ->
  T0 = T1
.
Proof. intros H; now inv H. Qed.
Lemma TMSMon_step_aborted (T0 T1 : TMSMon.AbsState) :
  @step TMSMon.MonInstance T0 (Some (TMSMonAux.AAbort)) T1 ->
  T0 = T1
.
Proof. intros H; now inv H. Qed.
Lemma SMSMon_step_alloc (T0 T1 : SMSMon.AbsState) l n t σ As :
  @step SMSMon.MonInstance T0 (Some (SMSMonAux.AAlloc l n)) T1 ->
  gsms T1 (As)%list ->
  gsms T0 (PreEv (Alloc l n) t σ :: As)%list
.
Proof.
  intros; inv H. unfold gsms; intros.
  destruct H as [Ha | Hb].
  specialize (H0 l0 n0 m t0 t' σ0 σ').
  - destruct (eq_dec (PreEv (Alloc l0 m) t0 σ0) (PreEv (Alloc l n) t σ)).
    inv H. all: unfold_before. apply H0; right; split; try now left.
    inv H__before0. now exists n3.
    apply H0. inv Ha. easy. inv H__before0.
    left; exists n3; exists n1; repeat split; eauto. lia.
  - specialize (H0 l0 n0 m t t' σ σ'). eapply H0. right; split; destruct Hb as [Ha Hb].
    inv Ha. inv H. exists n1; easy. apply List.in_cons. eassumption.
Qed.
Lemma TMSMon_step_use (T0 T1 : TMSMon.AbsState) l n t σ As :
  @step TMSMon.MonInstance T0 (Some (TMSMonAux.AUse l t)) T1 ->
  gtms T1 (As)%list ->
  gtms T0 (PreEv (Use l n) t σ :: As)%list
.
Proof.
  (*c)
  intros H Ha; inv H. unfold gtms; repeat split; intros.
  - specialize (Ha l0 n0 t0 t' σ0 σ'). destruct Ha as [Ha|Ha].
    + left; intros. unfold in_t in H, H0; inv H; inv H0.
      inv H2. inv H.
      specialize (Ha H H0); destruct Ha as [Ha [Hb Hc]]; unfold before in Ha; deex; destruct Ha as [Ha [Ha' Ha'']].
      repeat split; try easy. exists (S n3); exists (S n4); repeat split; try (now constructor); lia.
    + right; intros. specialize (Ha H H0); unfold in_t in Ha; deex. exists (S n1); now constructor. *)
Admitted.
Lemma SMSMon_step_dealloc (T0 T1 : SMSMon.AbsState) l t σ As :
  @step SMSMon.MonInstance T0 (None) T1 ->
  gsms T1 (As)%list ->
  gsms T0 (PreEv (Dealloc l) t σ :: As)%list
.
Proof.
  intros H; inv H; unfold gsms; intros.
  destruct H0 as [Ha | [Hb Hc]].
  - unfold_before. inv Ha. inv H__before0. specialize (H l0 n m t0 t' σ0 σ'). eapply H. left.
    exists n2. exists n0. repeat split; auto; lia.
  - specialize (H l0 n m t t' σ σ'). apply H. right.
    unfold in_t in Hb; deex. inv Hb. split; trivial. exists n1; auto.
Qed.
Lemma TMSMon_step_dealloc (T0 T1 : TMSMon.AbsState) l t σ As :
  @step TMSMon.MonInstance T0 (Some (TMSMonAux.ADealloc l t)) T1 ->
  gtms T1 (As)%list ->
  gtms T0 (PreEv (Dealloc l) t σ :: As)%list
.
Proof.
  intros H [Ha [Hb Hc]]; inv H; cbn in *. unfold gtms; repeat split; intros.
  - specialize (Ha l0 n t0); cbn in *. destruct Ha as [Ha|Ha]; intros.
    + left; intros. unfold in_t in H, H0; deex; inv H.
      destruct (eq_dec (PreEv (Dealloc l0) t0 SUnlock) (PreEv (Dealloc l) t σ)).
      * inv H. contradiction.
      * inv H0; try contradiction.
        assert (in_t (PreEv (Alloc l0 n) t0 SUnlock) As) by (now exists n2).
        assert (in_t (PreEv (Dealloc l0) t0 SUnlock) As) by (now exists n1).
        specialize (Ha H0 H6). rewrite H5 in H1. apply notin_propagate in H1 as H1'.
        assert ((l,t) <> (l0,t0)) by (intros H__e; inv H__e; apply H1; clear; induction L0; cbn; eauto).
        eapply notin_cons in H4 as H4'; eauto. specialize (Ha H1' H4').
        unfold before in Ha; deex; destruct Ha as [Ha [Ha' Ha'']].
        exists (S n0); exists (S n3); repeat split; try (now constructor); try lia.
    + right; intros. rewrite H5 in *. destruct (eq_dec (l, t) (l0, t0)).
      * now inv H0.
      * apply in_propagate in H as H'; auto. specialize (Ha H').
        apply notin_unsnoc in Ha; auto.
  - admit.
  - admit.
Admitted.
Lemma TMSMon_step_alloc (T0 T1 : TMSMon.AbsState) l n t As :
  @step TMSMon.MonInstance T0 (Some (TMSMonAux.AAlloc l t)) T1 ->
  gtms T1 (As)%list ->
  gtms T0 (PreEv (Alloc l n) t SUnlock :: As)%list
.
Proof.
  intros H [Ha [Hb Hc]]; inv H. unfold gtms; repeat split; intros.
  - specialize (Ha l0 n0 t0); cbn in *. destruct Ha as [Ha|Ha]; deex; intros.
    + left; intros. unfold in_t in H, H0; deex; inv H0.
      destruct (eq_dec (PreEv (Alloc l0 n0) t0 SUnlock) (PreEv (Alloc l n) t SUnlock)).
      * inv H0. exists 0. exists (S n3). repeat split; try (now constructor); lia.
      * inv H; try contradiction.
        assert (in_t (PreEv (Alloc l0 n0) t0 SUnlock) As) by (now exists n1).
        assert (in_t (PreEv (Dealloc l0) t0 SUnlock) As) by (now exists n3).
        specialize (Ha H H5). apply UniqueAllocation in H0. (** TODO: get rid of this axiom *)
        eapply notin_cons in H1 as H1'; eauto. specialize (Ha H1' H3).
        unfold before in Ha; deex; destruct Ha as [Ha [Ha' Ha'']].
        exists (S n2); exists (S n4); repeat split; try (now constructor); lia.
    + right; intros. intros Hx. apply Ha; auto. destruct (eq_dec (l0, t0) (l, t)).
      inv H0. clear; induction (TMSMonAux.alloced T0); cbn; auto.
      apply in_unsnoc; auto.
  - admit.
  - admit.
Admitted.
Lemma tmsmon_must_step_once (S0 S2 : TMSMon.AbsState) a (As : TMSMon.tracepref) :
  @star_step TMSMon.MonInstance S0 (a :: As)%list S2 ->
  exists S1, @step TMSMon.MonInstance S0 (Some a) S1 /\ star_step S1 As S2
.
Proof.
  intros H; dependent induction H; eauto. inv H; eauto.
Qed.
Lemma smsmon_must_step_once (S0 S2 : SMSMon.AbsState) a (As : SMSMon.tracepref) :
  @star_step SMSMon.MonInstance S0 (a :: As)%list S2 ->
  exists S1, @step SMSMon.MonInstance S0 (Some a) S1 /\ star_step S1 As S2
.
Proof.
  intros H; dependent induction H; eauto. inv H; eauto.
Qed.
Lemma SMSMon_is_gSMS As T0 As0 :
  SMSMon.gsat (List.app As0 As) T0 ->
  gsms T0 (List.app As0 As)
.
Proof.
  intros [Bs [T__SMS [H0 H1]]].
  revert T0 H1; dependent induction H0; intros; try rewrite <- x; eauto using nil_gsms.
  - (* Impossible *)
    inv H.
  - (* Useless events *)
    inv H; (eapply dealloc_gsms || eapply branch_gsms || eapply binop_gsms); change (gsms T0 (nil ++ As1))%list; eauto.
  - (* Useful events *)
    inv H; eauto;
    eapply smsmon_must_step_once in H1 as [T1 [H1 H2]]; deex.
    3: (eapply aborted_gsms; change (gsms T0 (nil ++ As1))%list; eapply IHcong; trivial;
    eapply SMSMon_step_aborted in H1 as H1'; now subst).
    eapply SMSMon_step_alloc; eauto; change (gsms T1 (nil ++ As1))%list; eauto.
    apply SMSMon_step_use in H1 as H1'; subst.
    assert (As1 ~= nil ++ As1)%list by now cbn.
    specialize (IHcong As1 nil H T1 H2); clear H; cbn in IHcong. unfold gsms; intros.
    destruct H as [H__a | [H__b H__c]].
    + destruct (eq_dec (PreEv (Use l n) t σ) (PreEv (Use l0 n0) t' σ')).
      * destruct H__a as [n__x [n__y [H__a [H__a' H__a'']]]]. inv H.
        destruct n__y. inv H__a''. inv H__a'. contradiction.
      * destruct H__a as [n__x [n__y [H__a [H__a' H__a'']]]]. destruct n__x; try easy. destruct n__y; try easy.
        inv H__a. inv H__a'. eapply IHcong. left. exists n__x. exists n__y. repeat split; eauto. lia.
    + inv H__b. destruct (eq_dec (PreEv (Use l n) t σ) (PreEv (Use l0 n0) t' σ')).
      * inv H3. inv H1. enough (m = m0); subst; try assumption.
        revert H__c H5 H7; clear; intros H0 H1 H2.
        apply not_eq_None_Some in H2 as [locs Hx].
        apply NoDupList.undup_refl in Hx as Hy; subst.
        apply NoDupList.nodupinv_equiv_undup in Hx.
        induction T1; cbn in *. easy.
        destruct a as [l1 m1].
        inv Hx. destruct H0, H1.
        -- inv H; inv H0. reflexivity.
        -- inv H. exfalso; apply H3. revert H0; clear; intros H0.
           induction T1; cbn in *; try easy; destruct a as [l1 m1].
           destruct H0. inv H. now left.
           right; auto.
        -- inv H0. exfalso; apply H3. revert H; clear; intros H.
           induction T1; cbn in *; try easy; destruct a as [l1 m1].
           destruct H. inv H. now left.
           right; eauto.
        -- eauto.
      * inv H. contradiction. specialize (IHcong l0 n0 m t t' σ σ'). apply IHcong; right; split; eauto.
        exists n1. assumption.
Qed.
Lemma SMSMon_is_SMS As :
  SMSMon.sat As ->
  Props.sms As
.
Proof.
  intros H; change (SMSMon.sat (nil ++ As))%list in H; eapply SMSMon_is_gSMS in H. cbn in H. unfold gsms in H.
  unfold sms; eauto.
Qed.
Lemma TMSMon_is_gTMS As T0 As0 :
  TMSMon.gsat (List.app As0 As) T0 ->
  gtms T0 (List.app As0 As)
.
Proof.
  intros [Bs [T__SMS [H0 H1]]].
  revert T0 H1; dependent induction H0; intros; try rewrite <- x; eauto using nil_gtms.
  - (* Impossible *)
    inv H.
  - (* Useless events *)
    inv H; (eapply branch_gtms || eapply binop_gtms); change (gtms T0 (nil ++ As1))%list; eauto.
  - (* Useful events *)
    inv H; eauto; eapply tmsmon_must_step_once in H1 as [T1 [H1 H2]]; deex.
    4: (eapply aborted_gtms; change (gtms T0 (nil ++ As1))%list; eapply IHcong; trivial;
    eapply TMSMon_step_aborted in H1 as H1'; now subst).
    eapply TMSMon_step_alloc; eauto; change (gtms T1 (nil ++ As1))%list; eauto.
    eapply TMSMon_step_dealloc; eauto; change (gtms T1 (nil ++ As1))%list; eauto.
    eapply TMSMon_step_use; eauto; change (gtms T1 (nil ++ As1))%list; eauto.
Qed.
Lemma TMSMon_is_TMS As :
  TMSMon.sat As ->
  Props.tms As
.
Proof.
  (* TODO: *)
Admitted.
Lemma MSMon_step_split (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) (a : option MSMon.AbsEv) :
  @step MSMon.MonInstance (T1, T2) a (T1', T2') ->
  exists o__TMS o__SMS, a = Some (o__TMS, o__SMS) /\
       @step TMSMon.MonInstance T1 o__TMS T1' /\
       @step SMSMon.MonInstance T2 o__SMS T2'
.
Proof.
  intros H; inv H. destruct a1, a2.
  - exists (Some a); exists (Some a0); easy.
  - exists (Some a); exists None; easy.
  - exists None; exists (Some a); easy.
  - exists None; exists None; easy.
Qed.
Lemma MSMon_steps_split_nil (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) :
  @star_step MSMon.MonInstance (T1, T2) (nil)%list (T1', T2') ->
  @star_step TMSMon.MonInstance T1 nil T1' /\ @star_step SMSMon.MonInstance T2 nil T2'
.
Proof.
  intros H; dependent induction H.
  split; repeat constructor. inv H; easy.
  destruct r2 as [T1'' T2''].
  assert ((T1'', T2'') ~= (T1'', T2'') /\ ((nil : list MSMon.AbsEv) ~= (nil : list MSMon.AbsEv)) /\ (T1', T2') ~= (T1', T2')) as [H__a [H__b H__c]] by repeat split.
  specialize (IHstar_step T1'' T1' T2'' T2' H__a H__b H__c).
  split; inv H.
Qed.
Lemma TMSMon_step_none_eq (T1 T1' : TMSMon.AbsState) :
  @step TMSMon.MonInstance T1 None T1' ->
  T1 = T1'
.
Proof.
  now intros H; inv H.
Qed.
Lemma SMSMon_step_none_eq (T2 T2' : SMSMon.AbsState) :
  @step SMSMon.MonInstance T2 None T2' ->
  T2 = T2'
.
Proof.
  now intros H; inv H.
Qed.
Lemma MSMon_step_none_none_eq (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) :
  @step MSMon.MonInstance (T1, T2) (Some(None, None)) (T1', T2') ->
  T1 = T1' /\ T2 = T2'
.
Proof.
  intros H; inv H. apply TMSMon_step_none_eq in H3. apply SMSMon_step_none_eq in H7. now subst.
Qed.
Lemma MSMon_step_none_eq (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) :
  @step MSMon.MonInstance (T1, T2) None (T1', T2') ->
  T1 = T1' /\ T2 = T2'
.
Proof.
  intros H; inv H.
Qed.
Lemma MSMon_steps_nil_eq (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) :
  @star_step MSMon.MonInstance (T1, T2) (nil)%list (T1', T2') ->
  T1 = T1' /\ T2 = T2'
.
Proof.
  intros H; dependent induction H; easy.
Qed.
Lemma MSMon_steps_split_cons_nil (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) a1 a2 :
  @star_step MSMon.MonInstance (T1, T2) ((a1, a2) :: nil)%list (T1', T2') ->
  @step TMSMon.MonInstance T1 a1 T1' /\ @step SMSMon.MonInstance T2 a2 T2'
.
Proof.
  intros H; dependent induction H.
  destruct r2; apply MSMon_steps_nil_eq in H0 as [H0a H0b]; subst.
  inv H; split; assumption. destruct r2. apply MSMon_step_none_eq in H as [Ha Hb]; subst.
  now eapply IHstar_step.
Qed.
Lemma MSMon_steps_split_cons (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) a1 a2 As :
  @star_step MSMon.MonInstance (T1, T2) ((a1, a2) :: As)%list (T1', T2') ->
  exists T1'' T2'', @step TMSMon.MonInstance T1 a1 T1'' /\
       @step SMSMon.MonInstance T2 a2 T2'' /\
       @star_step MSMon.MonInstance (T1'', T2'') As (T1', T2')
.
Proof.
  intros H; dependent induction H.
  destruct r2 as [T1'' T2'']; inv H; eauto.
  destruct r2; eapply MSMon_step_none_eq in H as [H__a H__b]; subst.
  now eapply IHstar_step.
Qed.
Lemma MSMon_cong_split (As : tracepref) (As__TMS : TMSMon.tracepref) (As__SMS : SMSMon.tracepref) xs :
  Some xs = zip (opt As__TMS) (opt As__SMS) ->
  MSMon.cong As xs ->
  TMSMon.cong As As__TMS /\ SMSMon.cong As As__SMS
.
Proof.
  revert As As__TMS As__SMS; induction xs; intros.
  - assert (As__TMS = nil /\ As__SMS = nil).
    revert H; clear; intros H.
    + induction As__TMS; split; trivial.
      inv H.
      destruct As__SMS; now inv H1.
      induction As__SMS.
      inv H.
      cbn in H.
      change ((fun xs => Some nil = match xs with
             | Some x => Some ((Some a, Some a0) :: x)%list
             | None => None
             end) (zip (opt As__TMS) (opt As__SMS))) in H.
      destruct (zip(opt As__TMS) (opt As__SMS)); easy.
      induction As__SMS.
      inv H.
      cbn in H.
      change ((fun xs => Some nil = match xs with
             | Some x => Some ((Some a, Some a0) :: x)%list
             | None => None
             end) (zip (opt As__TMS) (opt As__SMS))) in H.
      destruct (zip(opt As__TMS) (opt As__SMS)); easy.
    + destruct H1 as [H1__a H1__b]; subst. clear H. dependent induction H0.
      repeat constructor 1. split; constructor; inv H; auto; now apply IHcong.
  - destruct a as [a__TMS a__SMS];
    symmetry in H; apply zip_cons in H; deex; destruct H as [H'__a [H'__b H'__c]].
    apply opt_some in H'__a, H'__b; deex; destruct H'__a as [H'a1 [H'a2 H'a3]]; destruct H'__b as [H'b1 [H'b2 H'b3]].
    subst. dependent induction H0; eauto.
    + inv H. split.
      * inv H1.
      * inv H1.
    + inv H; split; constructor 3; eauto; eapply IHcong; eauto.
    + specialize (IHxs As As'1 As'0 H'__c H0) as [IHxs1 IHxs2].
      inv H. split; now constructor 4.
Qed.
Lemma MSMon_cong_TMSMon_cong_nil (As : tracepref) :
  MSMon.cong As nil ->
  TMSMon.cong As nil
.
Proof.
  assert (Some nil = zip (opt (nil : TMSMon.tracepref)) (opt (nil : SMSMon.tracepref))) by now cbn.
  eintros H'%MSMon_cong_split; eauto; now destruct H'.
Qed.
Lemma MSMon_cong_SMSMon_cong_nil (As : tracepref) :
  MSMon.cong As nil ->
  SMSMon.cong As nil
.
Proof.
  assert (Some nil = zip (opt (nil : TMSMon.tracepref)) (opt (nil : SMSMon.tracepref))) by now cbn.
  eintros H'%MSMon_cong_split; eauto; now destruct H'.
Qed.
Lemma MSMon_steps_split (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) As :
  @star_step MSMon.MonInstance (T1, T2) (As)%list (T1', T2') ->
  exists As0 As1, @star_step TMSMon.MonInstance T1 As0 T1' /\
       @star_step SMSMon.MonInstance T2 As1 T2'
.
Proof.
  intros H; dependent induction H.
  - do 2 exists nil; repeat constructor. now inv H.
  - destruct a as [o__TMS o__SMS]; destruct r2 as [T__TMS T__SMS].
    inv H.
    assert ((T__TMS, T__SMS) ~= (T__TMS, T__SMS) /\ (T1', T2') ~= (T1', T2')) as [Ha Hb] by repeat split.
    specialize (IHstar_step T__TMS T1' T__SMS T2' Ha Hb); clear Ha Hb.
    deex; destruct IHstar_step as [IH1 IH2].
    crush_option o__TMS; crush_option o__SMS.
    + inv Hx; clear H. exists (x :: As0)%list; exists (x0 :: As1)%list. split; econstructor 2; eauto.
    + inv Hx; clear H. exists (x :: As0)%list; exists As1%list. split. econstructor 2; eauto. apply SMSMon_step_none_eq in H8; subst. assumption.
    + inv Hx; clear H. exists (As0)%list; exists (x :: As1)%list. split. apply TMSMon_step_none_eq in H4; subst. assumption. econstructor 2; eauto.
    + inv Hx; clear H. exists (As0)%list; exists (As1)%list. split; (apply TMSMon_step_none_eq in H4 + apply SMSMon_step_none_eq in H8); subst; assumption.
  - inv H.
Qed.
Lemma MSMon_cong_none_strip (As : tracepref) Bs :
  MSMon.cong As ((None, None) :: Bs)%list ->
  MSMon.cong As Bs
.
Proof.
  intros H; dependent induction H; eauto.
  econstructor 3; eauto.
  inv H; econstructor 3; trivial; constructor; eauto.
Qed.
Fixpoint noopt { A : Type } (As : list (option A)) : list A :=
  match As with
  | nil => nil
  | (Some a :: As)%list => a :: (noopt As)
  | (None :: As)%list => noopt As
  end
.
Lemma MSMon_cong_split_zip (As : tracepref) As__MS :
  MSMon.cong As As__MS ->
  exists As__TMS As__SMS, Some As__MS = zip (As__TMS) (As__SMS)
                   /\ MSMon.cong As As__MS
                   /\ TMSMon.cong As (noopt As__TMS)
                   /\ SMSMon.cong As (noopt As__SMS)
.
Proof.
  intros H; dependent induction H; eauto.
  - repeat exists nil; cbn; split; trivial; repeat constructor.
  - deex; destruct IHcong as [IH1 [IH2 [IH3 IH4]]]. destruct b as [b1 b2]; inv H. exists (b1 :: As__TMS)%list. exists (b2 :: As__SMS)%list.
    repeat split; trivial. cbn; now rewrite <- IH1. constructor 2; auto. now constructor.
    now inv H1. now inv H2.
  - deex; destruct IHcong as [IH1 [IH2 [IH3 IH4]]]. inv H. exists As__TMS. exists As__SMS. repeat split; eauto. econstructor. constructor; eauto.
    easy. econstructor 3; eauto. econstructor 3; eauto.
  - deex; destruct IHcong as [IH1 [IH2 [IH3 IH4]]]. destruct b as [b1 b2]. exists (b1 :: As__TMS)%list. exists (b2 :: As__SMS)%list.
    repeat split. cbn; now rewrite <- IH1. now econstructor 4.
    inv H. crush_option b1; cbn. inv Hx. now econstructor 4. inv Hx. now econstructor 3.
    inv H. crush_option b2; cbn. inv Hx. now econstructor 4. inv Hx. now econstructor 3.
Qed.
Lemma MSMon_cong_split_zip_cons (As : tracepref) As__MS o__TMS o__SMS :
  MSMon.cong As ((o__TMS, o__SMS) :: As__MS)%list ->
  exists As__TMS As__SMS, Some ((o__TMS, o__SMS) :: As__MS)%list = zip (As__TMS)%list (As__SMS)%list
                   /\ MSMon.cong As ((o__TMS, o__SMS) :: As__MS)%list
                   /\ TMSMon.cong As (noopt (As__TMS))%list
                   /\ SMSMon.cong As (noopt (As__SMS))%list
.
Proof.
  intros H%MSMon_cong_split_zip; deex. destruct H as [H1 [H2 [H3 H4]]].
  exists (As__TMS)%list. exists (As__SMS)%list.
  repeat split. cbn; now rewrite <- H1. easy.
  crush_option (o__TMS). inv Hx. cbn in *. symmetry in H1. apply zip_cons in H1; deex.
  destruct H1 as [H1a [H1b H1c]]; subst. easy.
  symmetry in H1. apply zip_cons in H1; deex.
  destruct H1 as [H1a [H1b H1c]]; subst. easy.
Qed.
Lemma MSMon_steps_split' (T__TMS T1' : TMSMon.AbsState) (T__SMS T2' : SMSMon.AbsState) As0 As' Bs' :
  @star_step MSMon.MonInstance (T__TMS, T__SMS) As0 (T1', T2') ->
  Some As0 = zip As' Bs' ->
  @star_step TMSMon.MonInstance T__TMS (noopt As') T1' /\
  @star_step SMSMon.MonInstance T__SMS (noopt Bs') T2'
.
Proof.
  intros H0 H; revert As' Bs' H; dependent induction H0; intros.
  - split; econstructor. 1,3: constructor. all: symmetry in H0; apply zip_empty in H0 as [H0a H0b]; subst; repeat constructor. now inv H.
  - destruct a as [o__TMS o__SMS]; destruct r2 as [T__TMS' T__SMS'].
    inv H.
    assert ((T__TMS', T__SMS') ~= (T__TMS', T__SMS') /\ (T1', T2') ~= (T1', T2')) as [Ha Hb] by repeat split.
    specialize (IHstar_step T__TMS' T1' T__SMS' T2' Ha Hb); clear Ha Hb.
    symmetry in H1; apply zip_cons in H1; deex; destruct H1 as [H1 [H2 H3]]; subst.
    specialize (IHstar_step As'0 Bs'0 H3); destruct IHstar_step as [IH1 IH2].
    crush_option o__TMS; crush_option o__SMS.
    + inv Hx; clear H. split; econstructor 2; eauto.
    + inv Hx; clear H. split. econstructor 2; eauto. apply SMSMon_step_none_eq in H9; subst. econstructor 3; eauto. constructor.
    + inv Hx; clear H. split. apply TMSMon_step_none_eq in H5; subst. econstructor 3; eauto. constructor. econstructor 2; eauto.
    + inv Hx; clear H. split; apply TMSMon_step_none_eq in H5; apply SMSMon_step_none_eq in H9; subst;
      econstructor 3; eauto; constructor.
  - inv H.
Qed.
Lemma MSMon_steps_split_cong (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) As Xs :
  MSMon.cong Xs As ->
  @star_step MSMon.MonInstance (T1, T2) (As)%list (T1', T2') ->
  exists As0 As1, @star_step TMSMon.MonInstance T1 As0 T1' /\
       @star_step SMSMon.MonInstance T2 As1 T2' /\
       TMSMon.cong Xs As0 /\
       SMSMon.cong Xs As1
.
Proof.
  intros H' H; revert Xs H'; dependent induction H; intros.
  - do 2 exists nil; repeat constructor. now inv H. now apply MSMon_cong_TMSMon_cong_nil. now apply MSMon_cong_SMSMon_cong_nil.
  - destruct a as [o__TMS o__SMS]; destruct r2 as [T__TMS T__SMS].
    apply MSMon_cong_split_zip in H'; deex; destruct H' as [H1 [H2 [H3 H4]]].
    symmetry in H1; apply zip_cons in H1; deex; destruct H1 as [H1a [H1b H1c]]; subst.
    eapply MSMon_steps_split' in H0 as [H0 H1]; eauto.
    crush_option o__TMS; crush_option o__SMS; cbn in *; inv H.
    + exists (x :: noopt As')%list. exists (x0 :: noopt Bs')%list.
      repeat split. econstructor 2. eassumption. assumption.
      econstructor 2. eassumption. assumption.
      easy. easy.
    + exists (x :: noopt As')%list. exists (noopt Bs')%list.
      repeat split. econstructor 2. eassumption. assumption. apply SMSMon_step_none_eq in H12; subst. assumption.
      easy. easy.
    + exists (noopt As')%list. exists (x :: noopt Bs')%list.
      repeat split. apply TMSMon_step_none_eq in H8; subst. assumption. econstructor 2. eassumption. assumption.
      easy. easy.
    + exists (noopt As')%list. exists (noopt Bs')%list.
      repeat split. apply TMSMon_step_none_eq in H8; subst. assumption. apply SMSMon_step_none_eq in H12; subst. assumption.
      easy. easy.
  - inv H.
Qed.
Lemma MSMon_is_MS As :
  MSMon.sat As ->
  Props.ms As
.
Proof.
  intros [Bs [T__TMS [H__a H__b]]].
  Ltac do_goal := split; (apply TMSMon_is_TMS || apply SMSMon_is_SMS).
  apply MSMon_cong_split_zip in H__a; deex; destruct H__a as [H__a1 [H__a2 [H__a3 H__a4]]].
  unfold MSMon.EmptyState in H__b; destruct T__TMS as [T__TMS T__SMS];
  eapply MSMon_steps_split' in H__b as [H__b H__c]; eauto.
  do_goal. exists (noopt As__TMS). exists T__TMS. repeat split; eauto. exists (noopt As__SMS). exists T__SMS. repeat split; eauto.
Qed.
Lemma sCCTMon_is_sCCT As :
  sCCTMon.sat As ->
  Props.sCCT As
.
Proof.
  intros [Bs [T__sCCT [H1 H2]]].
  induction H2; auto.
  - admit.
  -
Admitted.
Lemma MSSCCTMon_is_MSSCCT As :
  MSSCCTMon.sat As ->
  Props.MSSCCT As
.
Proof.
Admitted.
