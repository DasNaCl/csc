Set Implicit Arguments.
Require Import Strings.String CSC.Util CSC.Sets CSC.Props Coq.Program.Equality.

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
  Inductive cong : Props.tracepref -> tracepref -> Prop :=
  | cong_refl : cong nil nil
(*  | cong_stutter_L : forall (b : AbsEv)
                       (Bs : tracepref)
                       (As : Props.tracepref),
      cong_e None (Some b) ->
      cong As (List.cons b Bs) ->
      cong As (List.cons b Bs) *)
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
  | sms_abort (T : AbsState) : MonCheck_i T (Some AAbort) EmptyState
  | sms_use (T : AbsState) (l : loc) (n m : nat) :
    LocNatListSets.el (l, m) T ->
    n < m ->
    MonCheck_i T (Some(AUse l n)) T
  | sms_alloc (T T' : AbsState) (l : loc) (n : nat) :
    (forall (m : nat), ~ LocNatListSets.el (l, m) T) ->
    T' = LocNatListSets.Union T (List.cons (l,n) List.nil) ->
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
Lemma TMSMon_is_TMS As :
  TMSMon.sat As ->
  Props.tms As
.
Proof.
Admitted.
Lemma SMSMon_is_SMS As :
  SMSMon.sat As ->
  Props.sms As
.
Proof.
Admitted.
Fixpoint opt { A : Type } (As : list A) : list(option A) :=
  match As with
  | nil => nil
  | cons a As => Some a :: opt As
  end
.
Fixpoint zip { A B : Type } (As : list A) (Bs : list B) : list (A * B) :=
  match As, Bs with
  | nil, nil => nil
  | (a :: As')%list, (b :: Bs')%list => ((a, b) :: zip As' Bs')%list
  | _, _ => nil
  end
.
Lemma MSMon_steps_split (T1 T1' : TMSMon.AbsState) (T2 T2' : SMSMon.AbsState) (As : list MSMon.AbsEv) :
  @star_step MSMon.MonInstance (T1, T2) As (T1', T2') ->
  exists (As__TMS : TMSMon.tracepref) (As__SMS : SMSMon.tracepref),
    As = zip (opt As__TMS) (opt As__SMS) /\
    @star_step TMSMon.MonInstance T1 As__TMS T1' /\
    @star_step SMSMon.MonInstance T2 As__SMS T2'
.
Proof. Admitted.
Lemma MSMon_cong_cons_split (As : tracepref) (a__TMS : option TMSMon.AbsEv) (a__SMS : option SMSMon.AbsEv) (As__MS : MSMon.tracepref) :
  MSMon.cong As (((a__TMS, a__SMS) :: As__MS)%list) ->
  (
  exists a As', As = (a :: As')%list /\
           TMSMon.cong_e (Some a) a__TMS /\
           SMSMon.cong_e (Some a) a__SMS /\
           MSMon.cong As' As__MS
  ) \/ (
    TMSMon.cong_e None a__TMS /\
    SMSMon.cong_e None a__SMS
  )
.
Proof. Admitted.
Lemma MSMon_cong_split (As : tracepref) (As__TMS : TMSMon.tracepref) (As__SMS : SMSMon.tracepref) :
  MSMon.cong As (zip (opt As__TMS) (opt As__SMS)) ->
  TMSMon.cong As As__TMS /\ SMSMon.cong As As__SMS
.
Proof. Admitted.
Lemma MSMon_cong_TMSMon_cong_nil (As : tracepref) :
  MSMon.cong As nil ->
  TMSMon.cong As nil
.
Proof. Admitted.
Lemma MSMon_cong_SMSMon_cong_nil (As : tracepref) :
  MSMon.cong As nil ->
  SMSMon.cong As nil
.
Proof. Admitted.
Lemma MSMon_cong_none_strip (As : tracepref) Bs :
  MSMon.cong As ((None, None) :: Bs)%list ->
  MSMon.cong As Bs
.
Proof. Admitted.
Lemma MSMon_is_MS As :
  MSMon.sat As ->
  Props.ms As
.
Proof.
  intros [Bs [T__TMS [H__a H__b]]].
  Ltac do_goal := split; (apply TMSMon_is_TMS || apply SMSMon_is_SMS).
  remember MSMon.EmptyState as T__MS; induction H__b; auto.
  - (* As cong [] *)
    remember nil as Bs; induction H__a; auto.
    + do_goal; exists List.nil; (exists TMSMon.EmptyState || exists SMSMon.EmptyState);
        split; now constructor.
    + inv H0. inv H1.
      * do_goal; exists nil; (exists TMSMon.EmptyState || exists SMSMon.EmptyState); split.
        2, 4: repeat constructor. 1,2: constructor 2; try constructor;
          now (apply MSMon_cong_TMSMon_cong_nil + apply MSMon_cong_SMSMon_cong_nil).
      * do_goal; exists nil; (exists TMSMon.EmptyState || exists SMSMon.EmptyState); split.
        2, 4: repeat constructor. 1,2: constructor 2; try constructor;
          now (apply MSMon_cong_TMSMon_cong_nil + apply MSMon_cong_SMSMon_cong_nil).
    + exfalso; revert HeqBs; clear; intros H; induction Bs; congruence.
  - (* As cong b::Bs0 *)
    destruct r2 as [T__TMS T__SMS]. destruct r3 as [T__TMS' T__SMS'].
    apply MSMon_steps_split in H__b as [As__TMS [As__SMS [H__b1 [H__b2 H__b3]]]].
    inv H.
    assert (H__a':=H__a);
    apply MSMon_cong_cons_split in H__a as [H__a | [H__a1 H__a2]].
    + destruct H__a as [a [As' [H__a1 [H__a2 [H__a3 H__a4]]]]]. subst. apply MSMon_cong_split in H__a4 as [H__a4 H__a5].
      inv H__a2.
      * exists (TMSMonAux.AAlloc l :: As__TMS)%list. exists T__TMS'. split.
          constructor 3. constructor. assumption. inv H2. econstructor 2; eauto.
      * exists (TMSMonAux.ADealloc l :: As__TMS)%list. exists T__TMS'. split.
          constructor 3. constructor. assumption. inv H2. econstructor 2; eauto.
      * exists (TMSMonAux.AUse l :: As__TMS)%list. exists T__TMS'. split.
          constructor 3. constructor. assumption. inv H2. econstructor 2; eauto.
      * exists (As__TMS)%list. exists T__TMS'. split.
          constructor 2. constructor. assumption. inv H2. econstructor 3; eauto.
      * exists (As__TMS)%list. exists T__TMS'. split.
          constructor. constructor. assumption. inv H2. econstructor 3; eauto.
      * exists (TMSMonAux.AAbort :: As__TMS)%list. exists T__TMS'. split.
          constructor 3. constructor. assumption. inv H2. econstructor 2; eauto.
    + inv H__a1. inv H__a2. inv H2. inv H4. inv H5. apply IHH__b; auto.
      now apply MSMon_cong_none_strip in H__a'.
  - (* As cong Bs *)
    apply IHH__b; auto; subst; inv H.
Admitted.
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
