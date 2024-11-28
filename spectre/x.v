
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
Definition abstraction (A B : Type) (rel : xrelation A B) : (B -> Prop) -> (A -> Prop) :=
  fun π a => forall b, rel a b -> π b
.
Definition concretization (A B : Type) (rel : xrelation A B) : (A -> Prop) -> (B -> Prop) :=
  fun π b => exists a, rel a b /\ π a
.
Definition subsets (A : Type) (X Y : A -> Prop) : Prop :=
  forall x, X x -> Y x
.
Definition galois_connection (A B : Type) (σ : (B -> Prop) -> (A -> Prop)) 
                                          (τ : (A -> Prop) -> (B -> Prop)) : Prop :=
  forall (x : A -> Prop) (y : B -> Prop), subsets _ (τ x) y <-> subsets _ x (σ y)
.
Lemma isconn (A B : Type) (rel : xrelation A B) :
  galois_connection A B (abstraction A B rel) (concretization A B rel)
.
Proof.
  intros X Y; split; intros Hsub y Hy.
  - intros x Hx; apply Hsub; exists y; now split.
  - destruct Hy as [x [Hrel HXx]]; apply Hsub with (x:=x); assumption.
Qed.
Lemma galois1 (A B : Type) (rel : xrelation A B) :
  forall (π : A -> Prop), subsets _ π (abstraction A B rel (concretization A B rel π))
.
Proof.
  intros π x Hx y Hxy; now exists x.
Qed.
Lemma galois2 (A B : Type) (rel : xrelation A B) :
  forall (π : B -> Prop), subsets _ (concretization A B rel (abstraction A B rel π)) π
.
Proof.
  intros π x [y [Hyx Habs]]; apply Habs; assumption.
Qed.
Definition galois_insertion (A B : Type) (rel : xrelation A B) : Prop :=
  forall π, abstraction A B rel (concretization A B rel π) = π
.
Axiom set_exteq : forall (A : Type) (X Y : A -> Prop), 
  (subsets A X Y /\ subsets A Y X) ->
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

Inductive SeqOEvent : Set := 
  | Any
  | Crash
.
Hint Constructors SeqOEvent : core.
Definition SeqEvent := option SeqOEvent.
Inductive SpecOEvent : Set :=
  | SAny
  | SCrash
  | SSpec
  | SRlb
.
Hint Constructors SpecOEvent : core.
Definition SpecEvent := option SpecOEvent.

Inductive seqspec : (nat * nat) -> xrelation SeqEvent SpecEvent :=
  | seqspec_empty : forall (n : nat), seqspec (n, n) None None
  | seqspec_any : forall (n : nat), seqspec (n, n) (Some Any) (Some SAny)
  | seqspec_crash : forall (n : nat), seqspec (n, n) (Some Crash) (Some SCrash)
  | seqspec_spec : forall (n : nat), seqspec (n, 1+n) (None) (Some SSpec)
  | seqspec_rlb : forall (n : nat), seqspec (1+n, n) (None) (Some SRlb)
.
Lemma seqspec_left_determ : forall n m,
  left_deterministic SeqEvent SpecEvent (seqspec (n,m))
.
Proof.
  intros n m a a' b; inversion 1; intros H'; subst; inversion H'; subst; easy.
Qed.
Lemma seqspec_m_determ : forall a a' b n m m',
  seqspec (n,m) a b ->
  seqspec (n,m') a' b ->
  m = m'
.
Proof.
  intros a a' b n m m'; inversion 1; subst; inversion 1; subst; eauto.
Qed.
Lemma seqspec_left_determ' : forall n,
  left_deterministic SeqEvent SpecEvent (fun a b => exists m, seqspec (n,m) a b)
.
Proof.
  intros n a a' b [m H] [m' H'];
  specialize (seqspec_m_determ a a' b n m m' H H') as <-.
  eapply seqspec_left_determ; eauto.
Qed.
Lemma seqspec_left_total : forall n,
  left_total SeqEvent SpecEvent (fun a b => exists m, seqspec (n,m) a b)
.
Proof.
  intros n [[]|]; do 2 eexists; now econstructor.
Qed.
Corollary seqspec_insertion : forall n,
  galois_insertion SeqEvent SpecEvent (fun a b => exists m, seqspec (n,m) a b)
.
Proof.
  intros n; eapply insertion; eauto using seqspec_left_determ', seqspec_left_total.
Qed.
