Set Implicit Arguments.
Require Import Strings.String CSC.Util CSC.Sets CSC.Props Coq.Program.Equality Lia.


(** * This file defines the various monitors from the paper. *)

(** General structure of monitors. This time as module for namespacing. *)
Module Type MonitorT.
  Parameter AbsState : Type.
  Parameter EmptyState : AbsState.
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
    is_value := fun _ => True;
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
      alloced : Util.LocListSet ;
      freed : Util.LocListSet ;
    }.
  Definition AbsState := AbsState_r.
  #[export]
  Hint Unfold AbsState : core.
  Definition EmptyState : AbsState := {|
    alloced := List.nil ;
    freed := List.nil ;
  |}.
  Variant AbsEv_d : Type :=
  | AAbort
  | AAlloc (l : loc)
  | AUse (l : loc)
  | ADealloc (l : loc)
  .
  Definition AbsEv := AbsEv_d.
  #[export]
  Hint Unfold AbsEv : core.

  Inductive MonCheck_i : AbsState -> option AbsEv -> AbsState -> Prop :=
  | sms_uninteresting (T : AbsState) : MonCheck_i T None T
  | sms_abort (T : AbsState) : MonCheck_i T (Some AAbort) EmptyState
  | sms_use (T : AbsState) (l : loc) :
    LocListSets.el l T.(alloced) ->
    ~(LocListSets.el l T.(freed)) ->
    MonCheck_i T (Some(AUse l)) T
  | sms_alloc (T T' : AbsState) (l : loc) :
    ~(LocListSets.el l T.(alloced)) ->
    ~(LocListSets.el l T.(freed)) ->
    T' = {|
           alloced := LocListSets.Union T.(alloced) (List.cons l List.nil) ;
           freed := T.(freed) ;
         |} ->
    MonCheck_i T (Some(AAlloc l)) T'
  | sms_dealloc (T T' : AbsState) (l : loc) L0 L1 :
    LocListSets.el l T.(alloced) ->
    ~(LocListSets.el l T.(freed)) ->
    T.(alloced) = List.app L0 (List.cons l L1) ->
    T' = {|
           alloced := List.app L0 L1 ;
           freed := LocListSets.Union T.(freed) (List.cons l List.nil) ;
         |} ->
    MonCheck_i T (Some(ADealloc l)) T'
  .
  Definition MonCheck := MonCheck_i.
  #[export]
  Hint Unfold MonCheck : core.
  Definition string_of_absev :=
    fun a => match a with
          | AAbort => "abs↯"%string
          | AAlloc (addr _n) => "absAlloc ℓ"%string
          | ADealloc (addr _n) => "absDealloc ℓ"%string
          | AUse (addr _n) => "absUse ℓ"%string
          end
  .
  Inductive cong_i : option Props.Event -> option AbsEv -> Prop :=
  | tms_alloc_authentic : forall l n t σ,
      cong_i (Some(Props.PreEv (Props.Alloc l n) t σ))
             (Some(AAlloc l))
  | tms_dealloc_authentic : forall l t σ,
      cong_i (Some(Props.PreEv (Props.Dealloc l) t σ))
             (Some(ADealloc l))
  | tms_use_authentic : forall l n t σ,
      cong_i (Some(Props.PreEv (Props.Use l n) t σ))
             (Some(AUse l))
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
                      andb (loc_eqb l0 l1) (Nat.eqb n0 n1).
End LocNatList.
Module LocNatListSets <: Sig := SetTheoryList (LocNatList).
Definition LocNatListSet := LocNatListSets.set.
Module SMSMonAux <: MonitorT.
  Definition AbsState := LocNatListSet.
  #[export]
  Hint Unfold AbsState : core.
  Definition EmptyState : AbsState := List.nil.
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
    LocNatListSets.el (l, m) T ->
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
Lemma gTMSMon_is_TMS As As0 T0 :
  TMSMon.gsat As T0 ->
  Props.tms (List.app As0 As)
.
Proof.
  (* need to related T0 with As0 ? *)

  (*
  intros [Bs [T__TMS [H1 H2]]].
  revert As0 T__TMS H2; induction H1; auto; intros.
  - (* refl *) repeat split; intros; inv H; exfalso; revert H1; clear; intros H1; induction x; cbn in *; congruence.
  - (* trans *)
    inv H.
    + (* AAlloc *) remember (TMSMonAux.AAlloc l :: Bs)%list as BBs.
      change ((fun BBs => star_step T0 BBs T__TMS) (TMSMonAux.AAlloc l :: Bs)%list) in H2; rewrite <- HeqBBs in H2.
      induction H2.
      * (* refl *) congruence.
      * (* trans-important *) clear IHstar_step; inv HeqBBs.
        inv H.
      * (* trans-unimportant *) inv H; auto.
    + repeat split; intros. intros Ha. [x [x0 [Ha Hb]]].

    repeat split; intros.
    + inv H0; inv H3. exists x; exists x0; repeat split; auto.
      inv H. induction H1.
   *)
Admitted.
Lemma nil_tms :
  Props.tms nil
.
Proof.
  repeat split; intros; inv H; exfalso; revert H1; clear; intros H; induction x; try inv H.
Qed.
Lemma nil_sms :
  Props.sms nil
.
Proof.
  unfold sms; intros; unfold_before; inv H.
Qed.

Fixpoint allocs_from_smsmon (T : SMSMon.AbsState) : tracepref :=
  match T with
  | nil => nil
  | ((l, n)::T)%list => ((PreEv (Alloc l n) CComp SUnlock) :: allocs_from_smsmon T)%list
  end
.
Definition gsms (T__SMS : SMSMon.AbsState) : Props.prop :=
  fun As => Props.sms ((allocs_from_smsmon T__SMS) ++ As)%list
.

Lemma nil_gsms T__SMS :
  gsms T__SMS nil
.
Proof.
  induction T__SMS; unfold gsms; cbn; eauto using nil_sms.
  destruct a as [l n]. rewrite List.app_nil_r. unfold sms; intros.
  eapply IHT__SMS. rewrite List.app_nil_r. erewrite <- eat_front_before in H; eauto; try easy.
  unfold_before.
  revert H__before0; clear; intros H; exfalso.
  revert l0 n0 t' σ' l n T__SMS H; induction n2; intros.
  inv H. inv H.
  destruct T__SMS. inv H5. destruct a as [l1 n1]; cbn in *.
  eauto.
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
  - assert (PreEv (Alloc l n0) t0 σ0 <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Dealloc l) t' σ' <> PreEv (Binop n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto; erewrite eat_front_in_t in H0.
    erewrite <- eat_front_before; eauto. eauto.
  - intros H1. assert (PreEv (Use l n0) t0 σ0 <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Alloc l m) t' σ' <> PreEv (Binop n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto. erewrite eat_front_in_t in H0; eauto.
    erewrite <- eat_front_before in H1; eauto. eapply H__TMS1; eauto.
  - intros H1. assert (PreEv (Dealloc l) t0 σ0 <> PreEv (Binop n) t σ) by congruence.
    assert (PreEv (Use l n0) t' σ' <> PreEv (Binop n) t σ) by congruence.
    erewrite eat_front_in_t in H; erewrite eat_front_in_t in H0; eauto.
    erewrite <- eat_front_before in H1; eauto. eapply H__TMS2; eauto.
Qed.
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
  induction As; cbn; intros.
  - unfold gsms in *; rewrite List.app_nil_r in *.
    induction T__SMS; cbn in *.
    now apply binop_sms. destruct a as [l0 n0].
Admitted.
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
Lemma use_gsms l n t σ As T__TMS :
  gsms T__TMS As ->
  gsms T__TMS (PreEv (Use l n) t σ :: As)%list
.
Proof.
Admitted.
Lemma branch_tms n t σ As :
  tms As ->
  tms (PreEv (Branch n) t σ :: As)%list
.
Proof.
  intros [H__TMS0 [H__TMS1 H__TMS2]]; repeat split; intros.
  - assert (PreEv (Alloc l n0) t0 σ0 <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Dealloc l) t' σ' <> PreEv (Branch n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto; erewrite eat_front_in_t in H0.
    erewrite <- eat_front_before; eauto. eauto.
  - intros H1. assert (PreEv (Use l n0) t0 σ0 <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Alloc l m) t' σ' <> PreEv (Branch n) t σ) by congruence.
    erewrite eat_front_in_t in H; eauto. erewrite eat_front_in_t in H0; eauto.
    erewrite <- eat_front_before in H1; eauto. eapply H__TMS1; eauto.
  - intros H1. assert (PreEv (Dealloc l) t0 σ0 <> PreEv (Branch n) t σ) by congruence.
    assert (PreEv (Use l n0) t' σ' <> PreEv (Branch n) t σ) by congruence.
    erewrite eat_front_in_t in H; erewrite eat_front_in_t in H0; eauto.
    erewrite <- eat_front_before in H1; eauto. eapply H__TMS2; eauto.
Qed.
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
Admitted.
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
Admitted.
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
Admitted.
Lemma TMSMon_is_TMS As :
  TMSMon.sat As ->
  Props.tms As
.
Proof.
  unfold TMSMon.sat; intros H; deex; destruct H as [H0 H1].
  dependent induction H1; eauto.
  - induction As; cbn in *.
    exact nil_tms. inv H0. inv H3; eauto using branch_tms, binop_tms.
  - admit.
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
Lemma SMSMon_step_alloc (T0 T1 : SMSMon.AbsState) l n t σ As :
  @step SMSMon.MonInstance T0 (Some (SMSMonAux.AAlloc l n)) T1 ->
  gsms T1 (As)%list ->
  gsms T0 (PreEv (Alloc l n) t σ :: As)%list
.
Proof.
  intros H0 H1. inv H0; unfold gsms in *; cbn in *.
  unfold sms; intros. specialize (H1 l0 n0 m t t' σ σ').
  eapply H1. (* may need to know about t and σ, but otherwise should go through *)
Admitted.
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
    eapply @must_step_once in H1 as [T1 [H1 H2]]; deex.
    2,3: ((eapply use_gsms || eapply aborted_gsms); change (gsms T0 (nil ++ As1))%list; eapply IHcong; trivial;
    (eapply SMSMon_step_use in H1 as H1' || eapply SMSMon_step_aborted in H1 as H1'); now subst).
    eapply SMSMon_step_alloc; eauto; change (gsms T1 (nil ++ As1))%list; eauto.
Qed.
Lemma SMSMon_is_SMS As :
  SMSMon.sat As ->
  Props.sms As
.
Proof.
  intros H; change (SMSMon.sat (nil ++ As))%list in H; eapply SMSMon_is_gSMS in H; now cbn in H.
Qed.
Fixpoint opt { A : Type } (As : list A) : list(option A) :=
  match As with
  | nil => nil
  | cons a As => Some a :: opt As
  end
.
Lemma opt_nil { A : Type } (As : list A) :
  opt As = nil ->
  As = nil
.
Proof. now induction As. Qed.
Lemma opt_cons { A : Type } (As : list A) Bs (a : option A) :
  opt As = (a :: Bs)%list ->
  As <> nil
.
Proof. induction As; now cbn. Qed.
Lemma opt_some { A : Type } (As : list A) Bs (a : option A) :
  opt As = (a :: Bs)%list ->
  exists a' As', a = Some a' /\ (As = a' :: As')%list /\ Bs = opt As'
.
Proof.
  intros H; apply opt_cons in H as H'.
  revert a Bs H; induction As; try congruence; intros.
  cbn in H. inv H. exists a. exists As. repeat split; reflexivity.
Qed.
Fixpoint zip { A B : Type } (As : list A) (Bs : list B) : option (list (A * B)) :=
  match As, Bs with
  | nil, nil => Some(nil)
  | (a :: As')%list, (b :: Bs')%list =>
    let* (xs) := zip As' Bs' in
    Some ((a, b) :: xs)%list
  | _, _ => None
  end
.
Lemma zip_empty { A B : Type } (As : list A) (Bs : list B) :
  zip As Bs = Some nil ->
  As = nil /\ Bs = nil
.
Proof.
  destruct As; intros H.
  - now destruct Bs.
  - destruct Bs. inv H. cbn in H.
    change ((fun xz => match xz with
            | Some x => Some ((a, b ) :: x)%list
            | None => None
            end = Some nil) (zip As Bs)) in H.
    destruct (zip As Bs); inv H.
Qed.
Lemma zip_cons { A B : Type } (As : list A) (Bs : list B) xs (a : A) (b : B) :
  zip As Bs = Some ((a,b) :: xs)%list ->
  exists As' Bs', As = (a :: As')%list /\ Bs = (b :: Bs')%list /\ Some xs = zip As' Bs'
.
Proof.
  destruct As; intros H.
  - now destruct Bs.
  - destruct Bs. inv H. cbn in H.
    assert (H':=H);
    change ((fun xz => match xz with
            | Some x => Some((a0, b0) :: x)%list
            | None => None
            end = Some ((a, b) :: xs)%list) (zip As Bs)) in H.
    destruct (zip As Bs) in H; inv H.
    exists As. exists Bs. repeat split; eauto.
    remember (zip As Bs) as ys.
    crush_option ys. now inv H'.
Qed.
Lemma zip_singleton { A B : Type } (As : list A) (Bs : list B) (a : A) (b : B) :
  zip As Bs = Some ((a, b) :: nil)%list ->
  (As = a :: nil /\ Bs = b :: nil)%list
.
Proof.
  intros.
  apply zip_cons in H. deex; destruct H as [H1 [H2 H3]]; subst.
  symmetry in H3; apply zip_empty in H3 as [H3a H3b]; subst; easy.
Qed.
Lemma zip_opt_extend { A B : Type } (As : list A) (Bs : list B) Cs (a : A) (b : B) :
  zip (opt As) (opt Bs) = Some Cs ->
  zip (opt (a :: As)) (opt (b :: Bs)) = Some ((Some a, Some b) :: Cs)%list
.
Proof.
  revert As Bs a b; induction Cs; intros.
  - apply zip_empty in H as [Ha Hb]; cbn; subst. now rewrite Ha, Hb; cbn.
  - destruct a as [a' b']. apply zip_cons in H. deex. destruct H as [H1 [H2 H3]].
    cbn; rewrite H1, H2; cbn; now rewrite <- H3.
Qed.
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
  split; repeat constructor.
  assert ((T1, T2) ~= (T1, T2) /\ ((nil : list MSMon.AbsEv) ~= nil) /\ (T1', T2') ~= (T1', T2')) as [H__a [H__b H__c]] by repeat split;
  specialize (IHstar_step T1 T1' T2 T2' H__a H__b H__c).
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
  inv H; split; assumption. destruct r2 as [T__TMS T__SMS]; apply MSMon_step_none_eq in H as [Ha Hb]; subst.
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
  destruct r2 as [T1'' T2'']; eapply MSMon_step_none_eq in H as [H__a H__b]; subst.
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
  - do 2 exists nil; repeat constructor.
  - destruct a as [o__TMS o__SMS]; destruct r2 as [T__TMS T__SMS].
    inv H.
    assert ((T__TMS, T__SMS) ~= (T__TMS, T__SMS) /\ (T1', T2') ~= (T1', T2')) as [Ha Hb] by repeat split.
    specialize (IHstar_step T__TMS T1' T__SMS T2' Ha Hb); clear Ha Hb.
    deex; destruct IHstar_step as [IH1 IH2].
    crush_option o__TMS; crush_option o__SMS.
    + inv Hx; clear H. exists (x :: As0)%list; exists (x0 :: As1)%list. split; econstructor 2; eauto.
    + inv Hx; clear H. exists (x :: As0)%list; exists As1%list. split. econstructor 2; eauto. econstructor 3; eauto.
    + inv Hx; clear H. exists (As0)%list; exists (x :: As1)%list. split. econstructor 3; eauto. econstructor 2; eauto.
    + inv Hx; clear H. exists (As0)%list; exists (As1)%list. split; econstructor 3; eauto.
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
  - repeat constructor; symmetry in H0; apply zip_empty in H0 as [H0a H0b]; subst; repeat constructor.
  - destruct a as [o__TMS o__SMS]; destruct r2 as [T__TMS' T__SMS'].
    inv H.
    assert ((T__TMS', T__SMS') ~= (T__TMS', T__SMS') /\ (T1', T2') ~= (T1', T2')) as [Ha Hb] by repeat split.
    specialize (IHstar_step T__TMS' T1' T__SMS' T2' Ha Hb); clear Ha Hb.
    symmetry in H1; apply zip_cons in H1; deex; destruct H1 as [H1 [H2 H3]]; subst.
    specialize (IHstar_step As'0 Bs'0 H3); destruct IHstar_step as [IH1 IH2].
    crush_option o__TMS; crush_option o__SMS.
    + inv Hx; clear H. split; econstructor 2; eauto.
    + inv Hx; clear H. split. econstructor 2; eauto. econstructor 3; eauto.
    + inv Hx; clear H. split. econstructor 3; eauto. econstructor 2; eauto.
    + inv Hx; clear H. split; econstructor 3; eauto.
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
  - do 2 exists nil; repeat constructor. now apply MSMon_cong_TMSMon_cong_nil. now apply MSMon_cong_SMSMon_cong_nil.
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
