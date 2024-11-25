Require Import Coq.Lists.List.

Section Relations.

Definition xrelation (A B : Type) := A -> B -> Prop.

Definition left_deterministic (A B : Type)
                              (rel : xrelation A B) : Prop :=
  forall a a' b, rel a b -> rel a' b -> a = a'
.
Definition left_total (A B : Type) 
                      (rel : xrelation A B) : Prop :=
  forall a, exists b, rel a b
.
Definition right_total (A B : Type) 
                       (rel : xrelation A B) : Prop :=
  forall b, exists a, rel a b
.
Definition abstraction (A B : Type) (rel : xrelation A B) : (B -> Prop) -> (A -> Prop) :=
  fun π a => forall b, rel a b -> π b
.
Definition concretization (A B : Type) (rel : xrelation A B) : (A -> Prop) -> (B -> Prop) :=
  fun π b => exists a, rel a b /\ π a
.
Definition galois_insertion (A B : Type) (rel : xrelation A B) : Prop :=
  forall π, abstraction A B rel (concretization A B rel π) = π
.
Axiom set_exteq : forall (A : Type) (X Y : A -> Prop), 
  ((forall x, X x -> Y x) /\ (forall y, Y y -> X y)) ->
  X = Y
.
Lemma insertion (A B : Type) (rel : xrelation A B) :
  left_total A B rel ->
  left_deterministic A B rel ->
  galois_insertion A B rel
.
Proof.
  intros Htot Hdeterm π; apply set_exteq; split.
  - intros a_S Habs; specialize (Htot a_S) as [a_T Hrel];
    specialize (Habs a_T Hrel) as [a_S' [Hrel' Hsat]];
    specialize (Hdeterm a_S a_S' a_T Hrel Hrel') as ->; assumption.
  - intros a_S Hsat a_T Hrel; exists a_S; split; assumption.
Qed.

End Relations.

Axiom Loc : Set.
Axiom Val : Set.

Class Model := {
  Event : Set ;
  State : Set ;
  is_final : State -> Prop ;
  step : State -> option Event -> State -> Prop ;
}.
Inductive starstep (M : Model) : M.(State) -> list Event -> M.(State) -> Prop :=
  | starsteprefl : forall X, is_final X -> starstep M X nil X
  | starsteptransimp : forall X X' X'' a As,
    M.(step) X (Some a) X' ->
    starstep M X' As X'' ->
    starstep M X (cons a As) X''
  | starsteptransign : forall X X' X'' As,
    M.(step) X None X' ->
    starstep M X' As X'' ->
    starstep M X As X''
.
Inductive stutter_cong (M M' : Model) (rel : option M.(Event) -> option M'.(Event) -> Prop)
    : list M.(Event) -> list M'.(Event) -> Prop :=
  | stutter_cong_nil : stutter_cong _ _ _ nil nil
  | stutter_cong_cons : forall a b As Bs, 
      rel (Some a) (Some b) ->
      stutter_cong _ _ _ As Bs ->
      stutter_cong _ _ _ (cons a As) (cons b Bs)
  | stutter_cong_ignL : forall b As Bs,
      rel None (Some b) ->
      stutter_cong _ _ _ As Bs ->
      stutter_cong _ _ _ As (cons b Bs)
  | stutter_cong_ignR : forall a As Bs,
      rel (Some a) None ->
      stutter_cong _ _ _ As Bs ->
      stutter_cong _ _ _ (cons a As) Bs
.

Inductive GenericSpecOEvent (Ev : Set) : Set :=
  | GenericSpecEventAny (a : Ev)
  | GenericSpecEventSpec
  | GenericSpecEventRlb
.
Definition GenericSpecEvent (Ev : Set) := option (GenericSpecOEvent Ev).
Inductive GenericSpecStep (M : Model) : (list M.(State)) -> GenericSpecEvent (M.(Event)) -> (list M.(State)) -> Prop :=
  | GenericSpecStepSilent : forall (X X' : M.(State)) Xs, 
    GenericSpecStep M (cons X Xs) None (cons X' Xs)
  | GenericSpecStepSeq : forall (X X' : M.(State)) Xs (a : M.(Event)), 
    M.(step) X (Some a) X' ->
    GenericSpecStep M (cons X Xs) (Some (GenericSpecEventAny (M.(Event)) a)) (cons X' Xs)
  | GenericSpecStepSpecStart : forall (X : M.(State)) Xs,
    GenericSpecStep M (cons X Xs) (Some (GenericSpecEventSpec (M.(Event)))) (cons X (cons X Xs))
  | GenericSpecStepSpecRlb : forall (n : nat) (X : M.(State)) Xs,
    GenericSpecStep M (cons X Xs) (Some (GenericSpecEventRlb (M.(Event)))) (Xs)
.
Instance SpecModel (M : Model) : Model := {
  Event := GenericSpecOEvent (M.(Event)) ;
  State := list M.(State);
  is_final := (fun X => 
    match X with
    | cons X nil => is_final X
    | _ => False
    end
  ) ;
  step := GenericSpecStep M ;
}.
Axiom step_steps : forall (M : Model) X a, ~is_final X -> exists X', step X a X'.

Inductive GenericCrashedState : Set :=
  | GCSOk
  | GCSCrash
.
Inductive ModV (M : Model) : Type :=
  | modV (X : M.(State)) (o : option M.(Event)) (X' : M.(State))
.

Inductive genericspecMod (M : Model) : ModV M -> ModV (SpecModel M) -> Prop :=
  | genericspecModNone : forall X X', 
      M.(step) X None X' ->
      (SpecModel M).(step) (cons X nil) None (cons X' nil) ->
      genericspecMod M (modV M X None X')
                       (modV (SpecModel M) (cons X nil) None (cons X' nil))
  | genericspecModNoSpec : forall X X' a, 
      M.(step) X (Some a) X' ->
      (SpecModel M).(step) (cons X nil) (Some (GenericSpecEventAny _ a)) (cons X' nil) ->
      genericspecMod M (modV M X (Some a) X')
                       (modV (SpecModel M) (cons X nil) (Some (GenericSpecEventAny _ a)) (cons X' nil))
  | genericspecModSpec : forall X Xs, 
      M.(step) X None X ->
      (SpecModel M).(step) (cons X Xs) (Some (GenericSpecEventSpec _)) (cons X (cons X Xs)) ->
      genericspecMod M (modV M X None X)
                       (modV (SpecModel M) (cons X Xs) (Some (GenericSpecEventSpec _)) (cons X Xs))
  | genericspecModRlb : forall X Xs, 
      M.(step) X None X ->
      (SpecModel M).(step) (cons X Xs) (Some (GenericSpecEventRlb _)) Xs ->
      genericspecMod M (modV M X None X)
                       (modV (SpecModel M) (cons X Xs) (Some (GenericSpecEventRlb _)) Xs)
  | genericspecModSpecAny : forall X X' X'' Y Xs a, 
      M.(step) X None X ->
      (SpecModel M).(step) (cons X' (cons Y Xs)) (Some (GenericSpecEventAny _ a)) (cons X'' (cons Y Xs)) ->
      genericspecMod M (modV M X None X)
                       (modV (SpecModel M) (cons X' (cons Y Xs)) (Some (GenericSpecEventAny _ a)) (cons X'' (cons Y Xs)))
.
Local Hint Constructors genericspecMod : core.
Definition genericspecEv (M : Model) (X : M.(State)) : option M.(Event) -> option (SpecModel M).(Event) -> Prop :=
  fun a b => exists X' Y Y', genericspecMod M (modV M X a X') (modV (SpecModel M) Y b Y')
.
Lemma genericspecev_left_determ M X : 
  left_deterministic _ _ (genericspecEv M X)
.
Proof.
  intros a a' b [Xa [Ya [Za Ha]]] [Xb [Yb [Zb Hb]]];
  inversion Ha; inversion Hb; subst; eauto;
  try match goal with 
  | [H: Some _ = Some _ |- _] => now inversion H
  | [H: Some _ = None |- _] => now inversion H
  | [H: None = Some _ |- _] => now inversion H
  end.
Admitted.
Lemma genericspecev_left_total M X :
  left_total _ _ (genericspecEv M X)
.
Proof.
  intros [a|].
  - exists (Some (GenericSpecEventAny _ a)), X, (cons X nil), (cons X nil);
    apply genericspecModNoSpec.
    admit. (* concrete case analysis *)
    eapply GenericSpecStepSeq. admit. (* same as above *)
  - exists None, X, (cons X nil), (cons X nil); apply genericspecModNone.
    admit.
    eapply GenericSpecStepSilent.
Admitted.
Corollary genericspecev_insertion M X :
  galois_insertion _ _ (genericspecEv M X)
.
Proof.
  eauto using insertion, genericspecev_left_total, genericspecev_left_determ.
Qed.
Section MemModel.
Inductive MemSeqOEvent : Set :=
  | MemSeqCrash
  | MemSeqLoad (l : Loc)
  | MemSeqStore (l : Loc)
.
Definition MemSeqEvent := option MemSeqOEvent.
Instance MemSeq__Model : Model := {
  Event := MemSeqOEvent ;
  State := GenericCrashedState ;
  is_final := (fun X => True) ;
  step := (fun a o b => 
    match a, b with
    | GCSOk, GCSOk => (o <> Some MemSeqCrash)
    | GCSOk, GCSCrash => (o = Some MemSeqCrash)
    | _, _ => False
    end
  ) ;
}.
Definition MemSpecOEvent := GenericSpecOEvent MemSeqOEvent.
Definition MemSpecEvent := option MemSpecOEvent.

Instance MemSpec__Model : Model := SpecModel MemSeq__Model.

Inductive memseqspecMod : ModV MemSeq__Model -> ModV MemSpec__Model -> Prop :=
  | memseqspecModEmpty : memseqspecMod (modV MemSeq__Model GCSOk None GCSOk)
      (modV MemSpec__Model (cons GCSOk nil) None (cons GCSOk nil)) 
  | memseqspecModCrash : memseqspecMod (modV MemSeq__Model GCSOk (Some MemSeqCrash) GCSCrash)
                                     (modV MemSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ MemSeqCrash)) (cons GCSCrash nil)) 
  | memseqspecModLoad : forall l, 
      memseqspecMod (modV MemSeq__Model GCSOk (Some (MemSeqLoad l)) GCSOk)
                   (modV MemSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (MemSeqLoad l))) (cons GCSOk nil))
  | memseqspecModStore : forall l, 
      memseqspecMod (modV MemSeq__Model GCSOk (Some (MemSeqStore l)) GCSOk)
                   (modV MemSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (MemSeqStore l))) (cons GCSOk nil))
  (* Speculation Part *)
  | memseqspecModSpec : forall Xs,
      memseqspecMod (modV MemSeq__Model GCSOk None GCSOk)
                   (modV MemSpec__Model (cons GCSOk Xs) (Some (GenericSpecEventSpec _)) (cons GCSOk (cons GCSOk Xs)))
  | memseqspecModRlb : forall X Xs,
      memseqspecMod (modV MemSeq__Model GCSOk None GCSOk)
                   (modV MemSpec__Model (cons X Xs) (Some (GenericSpecEventRlb _)) (Xs))
  (* Plumbing *)
  | memseqspecModCrashIgn : forall X Xs,
      memseqspecMod (modV MemSeq__Model GCSOk None GCSOk)
                   (modV MemSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ MemSeqCrash)) (cons GCSCrash (cons X Xs))) 
  | memseqspecModLoadIgn : forall l X Xs,
      memseqspecMod (modV MemSeq__Model GCSOk None GCSOk)
                   (modV MemSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (MemSeqLoad l))) (cons GCSOk (cons X Xs))) 
  | memseqspecModStoreIgn : forall l X Xs,
      memseqspecMod (modV MemSeq__Model GCSOk None GCSOk)
                   (modV MemSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (MemSeqStore l))) (cons GCSOk (cons X Xs))) 
.
Local
Hint Constructors memseqspecMod : core.

Definition memseqspecEv (X : MemSeq__Model.(State)) (Y : MemSpec__Model.(State)) : option MemSeq__Model.(Event) -> option MemSpec__Model.(Event) -> Prop :=
  fun a b => exists X' Y', memseqspecMod (modV _ X a X') (modV _ Y b Y')
.

Lemma memseqspecev_left_determ X Y : 
  left_deterministic _ _ (memseqspecEv X Y)
.
Proof.
  intros a a' b [Xa' [Ya' Ha]] [Xb' [Yb' Hb]]; inversion Ha; inversion Hb; subst; eauto; congruence.
Qed.
(* If there is no speculation, we can always find a correspondent *)
Lemma memseqspecev_left_total :
  left_total _ _ (memseqspecEv GCSOk (cons GCSOk nil))
.
Proof.
  intros [[]|]; do 3 eexists; eauto.
Qed.
Corollary memseqspecEv_insertion :
  galois_insertion _ _ (memseqspecEv GCSOk (cons GCSOk nil))
.
Proof.
  eauto using insertion, memseqspecev_left_determ, memseqspecev_left_total.
Qed.

Lemma memseqspecev'_left_total :
  left_total _ _ (genericspecEv MemSeq__Model GCSOk).
Proof.
  intros [[]|].
  - exists (Some (GenericSpecEventAny _ (MemSeqCrash)));
    exists GCSCrash, (cons GCSOk nil), (cons GCSCrash nil); repeat constructor.
  - exists (Some (GenericSpecEventAny _ (MemSeqLoad l)));
    exists GCSOk, (cons GCSOk nil), (cons GCSOk nil); repeat constructor;
    unfold step; cbn; congruence.
  - exists (Some (GenericSpecEventAny _ (MemSeqStore l)));
    exists GCSOk, (cons GCSOk nil), (cons GCSOk nil); repeat constructor;
    unfold step; cbn; congruence.
  - exists None;
    exists GCSOk, (cons GCSOk nil), (cons GCSOk nil); repeat constructor;
    unfold step; cbn; congruence.
Qed.
Lemma memseqspecev'_insertion :
  galois_insertion _ _ (genericspecEv MemSeq__Model GCSOk).
Proof.
  eauto using insertion, memseqspecev'_left_total, genericspecev_left_determ.
Qed.

End MemModel.
Section CtModel.
Inductive CtSeqOEvent : Set :=
  | CtSeqCrash
  | CtSeqPc (n : nat)
  | CtSeqLoad (l : Loc)
  | CtSeqStore (l : Loc)
.
Definition CtSeqEvent := option CtSeqOEvent.
Instance CtSeq__Model : Model := {
  Event := CtSeqOEvent ;
  State := GenericCrashedState ;
  is_final := (fun X => True) ;
  step := (fun a o b => 
    match a, b with
    | GCSOk, GCSOk => (o <> Some CtSeqCrash)
    | GCSOk, GCSCrash => (o = Some CtSeqCrash)
    | _, _ => False
    end
  ) ;
}.
Definition CtSpecOEvent := GenericSpecOEvent CtSeqOEvent.
Definition CtSpecEvent := option CtSpecOEvent.

Instance CtSpec__Model : Model := SpecModel CtSeq__Model.

Inductive ctseqspecMod : ModV CtSeq__Model -> ModV CtSpec__Model -> Prop :=
  | ctseqspecModEmpty : ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
      (modV CtSpec__Model (cons GCSOk nil) None (cons GCSOk nil)) 
  | ctseqspecModCrash : ctseqspecMod (modV CtSeq__Model GCSOk (Some CtSeqCrash) GCSCrash)
                                     (modV CtSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ CtSeqCrash)) (cons GCSCrash nil)) 
  | ctseqspecModPc : forall n, 
      ctseqspecMod (modV CtSeq__Model GCSOk (Some (CtSeqPc n)) GCSOk)
                   (modV CtSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (CtSeqPc n))) (cons GCSOk nil))
  | ctseqspecModLoad : forall l, 
      ctseqspecMod (modV CtSeq__Model GCSOk (Some (CtSeqLoad l)) GCSOk)
                   (modV CtSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (CtSeqLoad l))) (cons GCSOk nil))
  | ctseqspecModStore : forall l, 
      ctseqspecMod (modV CtSeq__Model GCSOk (Some (CtSeqStore l)) GCSOk)
                   (modV CtSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (CtSeqStore l))) (cons GCSOk nil))
  (* Speculation Part *)
  | ctseqspecModSpec : forall Xs,
      ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
                   (modV CtSpec__Model (cons GCSOk Xs) (Some (GenericSpecEventSpec _)) (cons GCSOk (cons GCSOk Xs)))
  | ctseqspecModRlb : forall X Xs,
      ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
                   (modV CtSpec__Model (cons X Xs) (Some (GenericSpecEventRlb _)) (Xs))
  (* Plumbing *)
  | ctseqspecModCrashIgn : forall X Xs,
      ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
                   (modV CtSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ CtSeqCrash)) (cons GCSCrash (cons X Xs))) 
  | ctseqspecModPcIgn : forall n X Xs,
      ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
                   (modV CtSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (CtSeqPc n))) (cons GCSOk (cons X Xs))) 
  | ctseqspecModLoadIgn : forall l X Xs,
      ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
                   (modV CtSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (CtSeqLoad l))) (cons GCSOk (cons X Xs))) 
  | ctseqspecModStoreIgn : forall l X Xs,
      ctseqspecMod (modV CtSeq__Model GCSOk None GCSOk)
                   (modV CtSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (CtSeqStore l))) (cons GCSOk (cons X Xs))) 
.
Local
Hint Constructors ctseqspecMod : core.
Definition ctseqspecEv (X : CtSeq__Model.(State)) (Y : CtSpec__Model.(State)) : option CtSeq__Model.(Event) -> option CtSpec__Model.(Event) -> Prop :=
  fun a b => exists X' Y', ctseqspecMod (modV _ X a X') (modV _ Y b Y')
.

Lemma ctseqspecev_left_determ X Y : 
  left_deterministic _ _ (ctseqspecEv X Y)
.
Proof.
  intros a a' b [Xa' [Ya' Ha]] [Xb' [Yb' Hb]]; inversion Ha; inversion Hb; subst; eauto; congruence.
Qed.
(* If there is no speculation, we can always find a correspondent *)
Lemma ctseqspecev_left_total :
  left_total _ _ (ctseqspecEv GCSOk (cons GCSOk nil))
.
Proof.
  intros [[]|]; do 3 eexists; eauto.
Qed.
Corollary ctseqspecEv_insertion :
  galois_insertion _ _ (ctseqspecEv GCSOk (cons GCSOk nil))
.
Proof.
  eauto using insertion, ctseqspecev_left_determ, ctseqspecev_left_total.
Qed.
End CtModel.
Section ArchModel.
Inductive ArchSeqOEvent : Set :=
  | ArchSeqCrash
  | ArchSeqPc (n : nat)
  | ArchSeqLoad (l : Loc) (v : Val)
  | ArchSeqStore (l : Loc) (v : Val)
.
Definition ArchSeqEvent := option ArchSeqOEvent.
Instance ArchSeq__Model : Model := {
  Event := ArchSeqOEvent ;
  State := GenericCrashedState ;
  is_final := (fun X => True) ;
  step := (fun a o b => 
    match a, b with
    | GCSOk, GCSOk => (o <> Some ArchSeqCrash)
    | GCSOk, GCSCrash => (o = Some ArchSeqCrash)
    | _, _ => False
    end
  ) ;
}.
Definition ArchSpecOEvent := GenericSpecOEvent ArchSeqOEvent.
Definition ArchSpecEvent := option ArchSpecOEvent.

Instance ArchSpec__Model : Model := SpecModel ArchSeq__Model.

Inductive archseqspecMod : ModV ArchSeq__Model -> ModV ArchSpec__Model -> Prop :=
  | archseqspecModEmpty : archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
      (modV ArchSpec__Model (cons GCSOk nil) None (cons GCSOk nil)) 
  | archseqspecModCrash : archseqspecMod (modV ArchSeq__Model GCSOk (Some ArchSeqCrash) GCSCrash)
                                     (modV ArchSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ ArchSeqCrash)) (cons GCSCrash nil)) 
  | archseqspecModPc : forall n, 
      archseqspecMod (modV ArchSeq__Model GCSOk (Some (ArchSeqPc n)) GCSOk)
                   (modV ArchSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (ArchSeqPc n))) (cons GCSOk nil))
  | archseqspecModLoad : forall l v, 
      archseqspecMod (modV ArchSeq__Model GCSOk (Some (ArchSeqLoad l v)) GCSOk)
                   (modV ArchSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (ArchSeqLoad l v))) (cons GCSOk nil))
  | archseqspecModStore : forall l v, 
      archseqspecMod (modV ArchSeq__Model GCSOk (Some (ArchSeqStore l v)) GCSOk)
                   (modV ArchSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ (ArchSeqStore l v))) (cons GCSOk nil))
  (* Speculation Part *)
  | archseqspecModSpec : forall Xs,
      archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
                   (modV ArchSpec__Model (cons GCSOk Xs) (Some (GenericSpecEventSpec _)) (cons GCSOk (cons GCSOk Xs)))
  | archseqspecModRlb : forall X Xs,
      archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
                   (modV ArchSpec__Model (cons X Xs) (Some (GenericSpecEventRlb _)) (Xs))
  (* Plumbing *)
  | archseqspecModCrashIgn : forall X Xs,
      archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
                   (modV ArchSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ ArchSeqCrash)) (cons GCSCrash (cons X Xs))) 
  | archseqspecModPcIgn : forall n X Xs,
      archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
                   (modV ArchSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (ArchSeqPc n))) (cons GCSOk (cons X Xs))) 
  | archseqspecModLoadIgn : forall l v X Xs,
      archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
                   (modV ArchSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (ArchSeqLoad l v))) (cons GCSOk (cons X Xs))) 
  | archseqspecModStoreIgn : forall l v X Xs,
      archseqspecMod (modV ArchSeq__Model GCSOk None GCSOk)
                   (modV ArchSpec__Model (cons GCSOk (cons X Xs)) (Some (GenericSpecEventAny _ (ArchSeqStore l v))) (cons GCSOk (cons X Xs))) 
.
Local
Hint Constructors archseqspecMod : core.
Definition archseqspecEv (X : ArchSeq__Model.(State)) (Y : ArchSpec__Model.(State)) : option ArchSeq__Model.(Event) -> option ArchSpec__Model.(Event) -> Prop :=
  fun a b => exists X' Y', archseqspecMod (modV _ X a X') (modV _ Y b Y')
.

Lemma archseqspecev_left_determ X Y : 
  left_deterministic _ _ (archseqspecEv X Y)
.
Proof.
  intros a a' b [Xa' [Ya' Ha]] [Xb' [Yb' Hb]]; inversion Ha; inversion Hb; subst; eauto; congruence.
Qed.
(* If there is no speculation, we can always find a correspondent *)
Lemma archseqspecev_left_total :
  left_total _ _ (archseqspecEv GCSOk (cons GCSOk nil))
.
Proof.
  intros [[]|]; do 3 eexists; eauto.
Qed.
Corollary archseqspecEv_insertion :
  galois_insertion _ _ (archseqspecEv GCSOk (cons GCSOk nil))
.
Proof.
  eauto using insertion, archseqspecev_left_determ, archseqspecev_left_total.
Qed.
End ArchModel.

(** * Cross Language Trace Relations *)
Inductive archspecctspecMod : ModV ArchSpec__Model -> ModV CtSpec__Model -> Prop :=
  | archspecctspecModEmpty : archspecctspecMod (modV ArchSpec__Model (cons GCSOk nil) None (cons GCSOk nil))
      (modV CtSpec__Model (cons GCSOk nil) None (cons GCSOk nil)) 
  | archspecctspecModCrash : archspecctspecMod (modV ArchSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ ArchSeqCrash)) (cons GCSCrash nil))
                                     (modV CtSpec__Model (cons GCSOk nil) (Some (GenericSpecEventAny _ CtSeqCrash)) (cons GCSCrash nil)) 
                                     (* ... now what? *)
.


