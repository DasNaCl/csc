Set Implicit Arguments.
Require Import Strings.String CSC.Util CSC.Sets.

(** * This file defines the various monitors from the paper. *)

(** General structure of monitors. This time as module for namespacing. *)
Module Type MonitorT.
  Parameter AbsState : Type.
  Parameter EmptyState : AbsState.
  Parameter AbsEv : Type.
  Parameter MonCheck : AbsState -> option AbsEv -> AbsState -> Prop.
  Parameter string_of_absev : AbsEv -> string.
End MonitorT.

Module BaseMonitor (M : MonitorT).
  #[export]
  Instance MonInstance : LangParams := {
    State := M.AbsState;
    Ev := M.AbsEv;
    step := M.MonCheck;
    string_of_event := M.string_of_absev;
    is_value := fun _ => True;
  }.
End BaseMonitor.

(** Monitor Composition *)
Module CompMonitor (M1 M2 : MonitorT) : MonitorT.
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

  #[export]
  Instance MonInstance : LangParams := {
    State := AbsState;
    Ev := AbsEv;
    step := MonCheck;
    string_of_event := string_of_absev;
    is_value := fun _ => True;
  }.
End CompMonitor.

(** Temporal Memory Safety Monitor *)
Module TMSMon : MonitorT.
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
    MonCheck_i T (Some(AAlloc l)) T'
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
  #[export]
  Instance MonInstance : LangParams := {
    State := AbsState;
    Ev := AbsEv;
    step := MonCheck;
    string_of_event := string_of_absev;
    is_value := fun _ => True;
  }.
End TMSMon.

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
Module SMSMon : MonitorT.
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
  #[export]
  Instance MonInstance : LangParams := {
    State := AbsState;
    Ev := AbsEv;
    step := MonCheck;
    string_of_event := string_of_absev;
    is_value := fun _ => True;
  }.
End SMSMon.

(** Strict Cryptographic Constan Time *)
Module sCCTMon : MonitorT.
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
  #[export]
  Instance MonInstance : LangParams := {
    State := AbsState;
    Ev := AbsEv;
    step := MonCheck;
    string_of_event := string_of_absev;
    is_value := fun _ => True;
  }.
End sCCTMon.
