Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat Strings.String Lists.List Lia Program.Equality.
Require Import Classes.RelationClasses Morphisms Setoid.
Require Import CSC.Util CSC.Fresh.

Lemma subset_trans {T} (A B C : list T) :
  A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. intros H0 H1 x H2; apply H1; now apply H0. Qed.
#[local]
Hint Resolve subset_trans : core.

(** * MiniML *)
(** In this document, we present the formalisation of MiniML.
    It's basically simple, non-recursive let-expressions.     *)

(** ** Abstract Syntax *)
Inductive bin_op :=
  | Plus
.
Inductive val :=
  | LitV : nat -> val
.
Coercion LitV : nat >-> val.
Inductive addr :=
  | LocA : nat -> addr
.
Declare Scope val_scope.
Bind Scope val_scope with addr.
Bind Scope val_scope with val.
Lemma addr_eq_dec : forall (x y : addr), { x = y } + { x <> y }.
Proof.
  intros [] [];
  destruct (Nat.eq_dec n n0).
  - subst; now left.
  - right; intros H; apply n1; now inv H.
Qed.
Definition addr_eqb (x y : addr) :=
  match x,y with
  | LocA n, LocA m => Nat.eqb n m
  end
.
Inductive expr :=
  | Lit : nat -> expr
  | Var : string -> expr
  | BinOp : bin_op -> expr -> expr -> expr        (* e0 + e1 *)
  | Access : string -> expr -> expr              (* x[e] *)
  | Letin : string -> expr -> expr -> expr        (* let x = e0 in e1 *)
  | If : expr -> expr -> expr -> expr             (* if e0 then e1 else e2 *)
  | Assign : string -> expr -> expr -> expr       (* x[e0] <- e1 *)
  | New : string -> string -> expr -> expr -> expr (* let (y,x) = new e0 in e1 *)
  | Delete : string -> expr                     (* delete x *)
.
Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Definition of_val (v : val) : expr :=
  match v with
  | LitV z => Lit z
  end
.
Definition to_val (e : expr) : option val :=
  match e with
  | Lit z => Some (LitV z)
  | _ => None
  end
.
Coercion of_val : val >-> expr.
Definition is_val (e : expr) : Prop :=
  match e with
  | Lit _ => True
  | _ => False
  end
.
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. now induction v. Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof. revert v; induction e; cbn; intros v ?; inv H; easy. Qed.

Lemma is_val_inv e : is_val e -> { n : nat | e = Lit n }.
Proof. induction e; cbn; intros; try contradiction; now exists n. Qed.

(** ** Evaluation *)

Definition bin_op_eval_int (op : bin_op) (n1 n2 : nat) : nat :=
  match op with
  | PlusOp => n1 + n2
  end
.
Definition bin_op_eval (op : bin_op) (v1 v2 : val) : val :=
  match v1,v2 with
  | LitV z1, LitV z2 => LitV (bin_op_eval_int op z1 z2)
  end
.

Definition Heap := list nat.
Definition LocMap := list (addr * nat).

Inductive env_elem : Set :=
| EnvAddr : addr -> env_elem
| EnvVal  : val  -> env_elem
.
Definition of_env_elem (e : env_elem) : option val :=
  match e with
  | EnvVal(LitV v) => Some(LitV v)
  | _ => None
  end
.
Definition of_opt_env_elem (e : option env_elem) : option val :=
  match e with
  | Some x => of_env_elem x
  | _ => None
  end
.
Coercion EnvAddr : addr >-> env_elem.
Coercion EnvVal : val >-> env_elem.
Definition Env : Set := list (string * env_elem).

(**
  State consists of four things:
    1. A way to get unique ids
    2. A heap, modeled as a list of natural numbers
    3. Mapping of unguessable addresses to indexes to things in heap
    4. An environment containing the values of variables/identifiers
*)
Record State : Set := {
    fresh : Fresh.fresh_state ;
    H     : Heap ;
    A     : LocMap;
    Δ     : Env
  }.
Definition Conf : Set := (State * expr).

Notation "F0 ';' H0 ';' A0 ';' Δ0" := ({| fresh := F0 ; H := H0 ; A := A0 ; Δ := Δ0 |} : State)
                                  (at level 80, H0 at next level, A0 at next level, Δ0 at next level).
Notation "Ω '▷' e" := ((Ω, e) : Conf) (at level 80, e at next level).
Notation "∅" := ((Fresh.empty_fresh) ; (nil) ; (nil) ; (nil)).

Lemma state_triv_eq Ω :
  Ω = (Ω.(fresh); Ω.(H); Ω.(A); Ω.(Δ)).
Proof. destruct Ω as [F H A Δ]; cbn; easy. Qed.

Definition Δ_lookup (x : string) (Ω : State) := Util.find (String.eqb x) Ω.(Δ).
Definition A_lookup (x : addr) (Ω : State) :=
  match Util.find (addr_eqb x) Ω.(A) with
  | Some n => n
  | None => 1729
  end
.
Definition H_lookup (a : nat) (Ω : State) :=
  match List.nth_error Ω.(H) a with
  | Some n => n
  | None => 1729
  end
.
Lemma Δ_lookup_dec (x : string) (Ω : State) :
  { Δ_lookup x Ω = None } + { Δ_lookup x Ω <> None }.
Proof. unfold Δ_lookup; apply Util.find_dec. Defined.

(**
  Events occuring in traces are
    - << Internal >> is the unobservable event
    - << Alloc loc s >> a new memory region at address << loc >> of size << s >> was allocated
    - << Dealloc loc >> the memory region at address << loc >> is freed
    - << Read loc n >> value in heap at address << loc + n >> read
    - << Write loc n >> value in heap at address << loc + n >> overwritten
 *)

Variant Event : Set :=
| Internal : Event
| Alloc : addr -> nat -> Event
| Dealloc : addr -> Event
| Read : addr -> nat -> Event
| Write : addr -> nat -> Event
.
Lemma event_dec : forall a0 a1 : Event, { a0 = a1 } + { a0 <> a1 }.
Proof.
  intros.
  destruct a0, a1; try (now left + now right); destruct a, a0.
  - destruct (Nat.eq_dec n1 n2), (Nat.eq_dec n n0); subst; (now left + right; congruence).
  - destruct (Nat.eq_dec n n0); subst; (now left + right; congruence).
  - destruct (Nat.eq_dec n1 n2), (Nat.eq_dec n n0); subst; (now left + right; congruence).
  - destruct (Nat.eq_dec n1 n2), (Nat.eq_dec n n0); subst; (now left + right; congruence).
Qed.

Reserved Notation "Ω1 '-[' a ']~>' Ω2" (at level 80, a at next level, right associativity).
Inductive base_step : Conf -> Event -> Conf -> Prop :=
| VarS : forall Ω x v, Δ_lookup x Ω = Some (EnvVal(LitV v)) ->
                  (Ω ▷ Var x -[ Internal ]~> Ω ▷ Lit v)
| BinOpS : forall Ω n1 n2 o, (Ω ▷ BinOp o (Lit n1) (Lit n2) -[ Internal ]~> Ω ▷ of_val(bin_op_eval o n1 n2))
| GetS : forall Ω x n loc v nl, Δ_lookup x Ω = Some (EnvAddr loc) ->
                           A_lookup loc Ω = nl ->
                           H_lookup (nl + n) Ω = v ->
                           (Ω ▷ Access x (Lit n) -[ Read loc n ]~> Ω ▷ Lit v)
| SetS : forall Ω H' x n v loc nl, Δ_lookup x Ω = Some (EnvAddr loc) ->
                              A_lookup loc Ω = nl ->
                              H' = replace (nl + n) Ω.(H) v ->
                              (Ω ▷ Assign x (Lit n) (Lit v) -[ Write loc n ]~> Ω.(fresh);H';Ω.(A);Ω.(Δ) ▷ Lit v)
| IfBotS : forall Ω e1 e2, (Ω ▷ If (Lit 0) e1 e2 -[ Internal ]~> Ω ▷ e2)
| IfTopS : forall Ω e1 e2 v, v <> 0 -> (Ω ▷ If (Lit v) e1 e2 -[ Internal ]~> Ω ▷ e1)
| LetS : forall Ω x v e, (Ω ▷ Letin x (Lit v) e -[ Internal ]~> Ω.(fresh);Ω.(H);Ω.(A);((x,EnvVal (LitV v)) :: Ω.(Δ)) ▷ e)
| DeleteS : forall Ω x loc, Δ_lookup x Ω = Some (EnvAddr loc) ->
                       (Ω ▷ Delete x -[ Dealloc loc ]~> Ω.(fresh);Ω.(H);Ω.(A);(delete x Ω.(Δ)) ▷ Lit 0)
| NewS : forall Ω H' y x n e loc s, s = List.length Ω.(H) ->
                               H' = grow Ω.(H) n ->
                               loc = LocA(Fresh.fresh Ω.(fresh)) ->
                               (Ω ▷ New y x (Lit n) e -[ Alloc loc n ]~>
                               (Fresh.advance Ω.(fresh));H';((loc, s) :: Ω.(A));((x, EnvAddr loc) :: Ω.(Δ)) ▷ e)
where "Ω0 '-[' a ']~>' Ω1" := (base_step Ω0 a Ω1)
.
#[local]
Hint Constructors base_step : core.

(* evaluation contexts *)
Inductive ectx :=
  | HoleCtx : ectx
  | LBinOpCtx : bin_op -> ectx -> expr -> ectx
  | RBinOpCtx : bin_op -> val -> ectx -> ectx
  | AccessCtx : string -> ectx -> ectx
  | LetinCtx : string -> ectx -> expr -> ectx
  | AssignCtx : string -> ectx -> expr -> ectx
  | AssignVCtx : string -> val -> ectx -> ectx
  | NewCtx : string -> string -> ectx -> expr -> ectx
  | IfCtx : ectx -> expr -> expr -> ectx
.
Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | LBinOpCtx o K' e' => BinOp o (fill K' e) e'
  | RBinOpCtx o v K' => BinOp o v (fill K' e)
  | AccessCtx x K' => Access x (fill K' e)
  | LetinCtx x K' e' => Letin x (fill K' e) e'
  | AssignCtx x K' e' => Assign x (fill K' e) e'
  | AssignVCtx x v K' => Assign x v (fill K' e)
  | NewCtx y x K' e' => New y x (fill K' e) e'
  | IfCtx K' e1 e2 => If (fill K' e) e1 e2
  end
.
Fixpoint comp_ectx (K1 K2 : ectx) : ectx :=
  match K1 with
  | HoleCtx => K2
  | LBinOpCtx o K' e => LBinOpCtx o (comp_ectx K' K2) e
  | RBinOpCtx o v K' => RBinOpCtx o v (comp_ectx K' K2)
  | AccessCtx x K' => AccessCtx x (comp_ectx K' K2)
  | LetinCtx x K' e => LetinCtx x (comp_ectx K' K2) e
  | AssignCtx x K' e => AssignCtx x (comp_ectx K' K2) e
  | AssignVCtx x v K' => AssignVCtx x v (comp_ectx K' K2)
  | NewCtx y x K' e => NewCtx y x (comp_ectx K' K2) e
  | IfCtx K' e1 e2 => IfCtx (comp_ectx K' K2) e1 e2
  end
.
Reserved Notation "Ω1 '=[' a ']~>' Ω2" (at level 80, a at next level, right associativity).
Inductive contextual_step : Conf -> Event -> Conf -> Prop :=
| Ectx_step : forall Ω1 e1 a Ω2 e2 K e1' e2',
    e1 = fill K e1' ->
    e2 = fill K e2' ->
    (Ω1 ▷ e1' -[ a ]~> Ω2 ▷ e2') ->
    Ω1 ▷ e1 =[ a ]~> Ω2 ▷ e2
where "Ω1 '=[' a ']~>' Ω2" := (contextual_step Ω1 a Ω2)
.
Reserved Notation "Ω1 '=[' a ']~>*' Ω2" (at level 80, a at next level, right associativity).
Unset Elimination Schemes.
Inductive steps : Conf -> list Event -> Conf -> Prop :=
| stepsRefl : forall Ω e, steps (Ω ▷ e) nil (Ω ▷ e)
| stepsTrans : forall Ω e a as0 Ω' e' Ω'' e'',
    (Ω ▷ e =[ a ]~> Ω' ▷ e') ->
    (Ω' ▷ e' =[ as0 ]~>* Ω'' ▷ e'') ->
    (Ω ▷ e =[ a :: as0 ]~>* Ω'' ▷ e'')
where "Ω1 '=[' a ']~>*' Ω2" := (steps Ω1 a Ω2)
.
Set Elimination Schemes.
Scheme steps_ind := Induction for steps Sort Prop.
#[local]
Hint Constructors steps contextual_step : core.

Lemma fill_empty e : fill HoleCtx e = e.
Proof. now cbn. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; cbn; congruence. Qed.

Lemma base_contextual_step Ω e a Ω' e' :
  Ω ▷ e -[ a ]~> Ω' ▷ e' -> Ω ▷ e =[ a ]~> Ω' ▷ e'.
Proof. apply Ectx_step with HoleCtx; try rewrite fill_empty; trivial. Qed.

Lemma fill_contextual_step Ω e1 a e2 Ω' K :
  Ω ▷ e1 =[ a ]~> Ω' ▷ e2 -> Ω ▷ (fill K e1) =[ a ]~> Ω' ▷ (fill K e2).
Proof. intros H; inv H; rewrite !fill_comp; econstructor; try reflexivity; assumption. Qed.

Lemma fill_steps Ω e1 As Ω' e2 K :
  Ω ▷ e1 =[ As ]~>* Ω' ▷ e2 -> Ω ▷ (fill K e1) =[ As ]~>* Ω' ▷ (fill K e2).
Proof.
  intros H.
  pose (project := fun a : Conf => match a with | (Ω, e) => Ω ▷ fill K e end).
  change ((fun a b => (project a) =[ As ]~>* (project b)) (Ω ▷ e1) (Ω' ▷ e2)).
  induction H; try eapply stepsRefl.
  eapply stepsTrans. eapply fill_contextual_step. eassumption.
  eapply IHsteps; trivial.
Qed.

Ltac get_values := repeat match goal with
                   | [H: is_val ?e |- _] => apply is_val_inv in H as []
                   end.
Ltac context_intro := (
                       intros;
                       get_values; subst
                      ).
Ltac context_solver C := (
                        match goal with
                        | [ H : _ =[ _ ]~>* _ |- _ =[ _ ]~>* _ ] =>
                             eapply fill_steps with (K:=C) in H; eauto
                        | [ H : _ =[ _ ]~> _ |- _ =[ _ ]~> _ ] =>
                            (eapply fill_contextual_step with (K:=C) in H; cbn in H; eauto)
                        | [ |- _ =[ _ ]~> _ ] =>
                            eapply Ectx_step with (K:=C); try now cbn; constructor
                        end
                        ).


Lemma contextual_step_bin_l Ω e1 o a e1' e2 Ω' :
  Ω ▷ e1 =[ a ]~> Ω' ▷ e1' ->
  Ω ▷ BinOp o e1 e2 =[ a ]~> Ω' ▷ BinOp o e1' e2.
Proof. context_intro; context_solver (LBinOpCtx o HoleCtx e2). Qed.

Lemma contextual_step_bin_r Ω e1 o a e2 e2' Ω' :
  is_val e1 ->
  Ω ▷ e2 =[ a ]~> Ω' ▷ e2' ->
  Ω ▷ BinOp o e1 e2 =[ a ]~> Ω' ▷ BinOp o e1 e2'.
Proof. context_intro; context_solver (RBinOpCtx o (LitV x) HoleCtx). Qed.

Lemma contextual_step_bin_v Ω e1 o e2 :
  is_val e1 ->
  is_val e2 ->
  { v : expr | Ω ▷ BinOp o e1 e2 =[ Internal ]~> Ω ▷ v }.
Proof. context_intro; exists (Lit (x0 + x)); context_solver (HoleCtx). Qed.

Lemma contextual_step_access Ω e e' a x Ω' :
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ Access x e =[ a ]~> Ω' ▷ Access x e'.
Proof. context_intro; context_solver (AccessCtx x HoleCtx). Qed.

Lemma contextual_step_letin Ω e e' e0 a x Ω' :
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ Letin x e e0 =[ a ]~> Ω' ▷ Letin x e' e0.
Proof. context_intro; context_solver (LetinCtx x HoleCtx e0). Qed.

Lemma contextual_step_assign Ω e e' e0 x a Ω' :
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ Assign x e e0 =[ a ]~> Ω' ▷ Assign x e' e0.
Proof. context_intro; context_solver (AssignCtx x HoleCtx e0). Qed.

Lemma contextual_step_assignv Ω e e' v x a Ω' :
  is_val v ->
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ Assign x v e =[ a ]~> Ω' ▷ Assign x v e'.
Proof. context_intro; context_solver (AssignVCtx x (LitV x0) HoleCtx). Qed.

Lemma contextual_step_newctx Ω y x e0 e e' a Ω' :
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ New y x e e0 =[ a ]~> Ω' ▷ New y x e' e0.
Proof. context_intro; context_solver (NewCtx y x HoleCtx e0). Qed.

Lemma contextual_step_ifctx Ω e e' e1 e2 a Ω' :
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ If e e1 e2 =[ a ]~> Ω' ▷ If e' e1 e2.
Proof. context_intro; context_solver (IfCtx HoleCtx e1 e2). Qed.


Lemma ctx_steps_bin_l Ω e1 o a e1' e2 Ω' :
  Ω ▷ e1 =[ a ]~>* Ω' ▷ e1' ->
  Ω ▷ BinOp o e1 e2 =[ a ]~>* Ω' ▷ BinOp o e1' e2.
Proof. context_intro; context_solver (LBinOpCtx o HoleCtx e2). Qed.

Lemma ctx_steps_bin_r Ω e1 o a e2 e2' Ω' :
  is_val e1 ->
  Ω ▷ e2 =[ a ]~>* Ω' ▷ e2' ->
  Ω ▷ BinOp o e1 e2 =[ a ]~>* Ω' ▷ BinOp o e1 e2'.
Proof. context_intro; context_solver (RBinOpCtx o (LitV x) HoleCtx). Qed.

Lemma ctx_steps_access Ω e e' a x Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ Access x e =[ a ]~>* Ω' ▷ Access x e'.
Proof. context_intro; context_solver (AccessCtx x HoleCtx). Qed.

Lemma ctx_steps_letin Ω e e' e0 a x Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ Letin x e e0 =[ a ]~>* Ω' ▷ Letin x e' e0.
Proof. context_intro; context_solver (LetinCtx x HoleCtx e0). Qed.

Lemma ctx_steps_assign Ω e e' e0 x a Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ Assign x e e0 =[ a ]~>* Ω' ▷ Assign x e' e0.
Proof. context_intro; context_solver (AssignCtx x HoleCtx e0). Qed.

Lemma ctx_steps_assignv Ω e e' v x a Ω' :
  is_val v ->
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ Assign x v e =[ a ]~>* Ω' ▷ Assign x v e'.
Proof. context_intro; context_solver (AssignVCtx x (LitV x0) HoleCtx). Qed.

Lemma ctx_steps_newctx Ω y x e0 e e' a Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ New y x e e0 =[ a ]~>* Ω' ▷ New y x e' e0.
Proof. context_intro; context_solver (NewCtx y x HoleCtx e0). Qed.

Lemma ctx_steps_ifctx Ω e e' e1 e2 a Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ If e e1 e2 =[ a ]~>* Ω' ▷ If e' e1 e2.
Proof. context_intro; context_solver (IfCtx HoleCtx e1 e2). Qed.

Lemma contextual_step_steps σ a σ' :
  σ =[ a ]~> σ' -> σ =[ a :: nil ]~>* σ'.
Proof. intros; destruct σ, σ'; eapply stepsTrans; (eapply stepsRefl + eassumption). Qed.

#[local]
Hint Resolve
  base_contextual_step
  contextual_step_bin_l contextual_step_bin_r contextual_step_bin_v contextual_step_access contextual_step_letin
  contextual_step_assign contextual_step_assignv contextual_step_newctx contextual_step_ifctx
  contextual_step_steps
  ctx_steps_bin_l ctx_steps_bin_r ctx_steps_access ctx_steps_letin
  ctx_steps_assign ctx_steps_assignv ctx_steps_newctx ctx_steps_ifctx
  : core
.
Lemma trans_steps σ σ' σ'' As1 As2 :
  σ =[ As1 ]~>* σ' -> σ' =[ As2 ]~>* σ'' -> σ =[ As1 ++ As2 ]~>* σ''
.
Proof.
  induction 1; cbn; intros H; try easy;
  destruct σ''; eapply stepsTrans; try eassumption; apply IHsteps; eassumption.
Qed.

Lemma inv_lit_ctx_step Ω n E Ω' e :
  Ω ▷ Lit n =[ E ]~> Ω' ▷ e -> False.
Proof. intros; inv H0; induction K; cbn in *; try congruence; subst; inv H8. Qed.

Lemma inv_lit_steps Ω n Tr e Ω' :
  Ω ▷ Lit n =[ Tr ]~>* Ω' ▷ e -> e = Lit n /\ Ω = Ω' /\ Tr = nil.
Proof.
  intros H.
  change ((fun σ σ' : Conf => fun Tr =>
          let (Ω, e0) := σ in
          let (Ω', e) := σ' in
          e = e0 /\ Ω = Ω' /\ Tr = nil) (Ω ▷ Lit n) (Ω' ▷ e) Tr).
  remember (Ω ▷ Lit n) as σ.
  remember (Ω' ▷ e) as σ'.
  induction H; inv Heqσ; inv Heqσ'; eauto; now apply inv_lit_ctx_step in c.
Qed.

Lemma inv_var_ctx_step Ω Ω' E s e :
  (Ω, Var s) =[ E ]~> (Ω', e) -> exists v, e = Lit v /\ Δ_lookup s Ω = Some(EnvVal v) /\ Ω = Ω'.
Proof. intros; inv H0; induction K; cbn in *; try congruence; subst; inv H8; eauto. Qed.

Lemma inv_var_steps Ω Ω' Tr s e :
  (Ω, Var s) =[ Tr ]~>* (Ω', e) -> e = Var s \/ exists v, e = Lit v /\ Δ_lookup s Ω = Some(EnvVal v) /\ Ω = Ω' /\ Tr = Internal :: nil.
Proof.
  intros H0; inv H0.
  - now left.
  - inv H5; induction K; cbn in *; try congruence; subst; inv H9; try easy;
    right; exists v; eapply inv_lit_steps in H7 as [H0 [H1 H2]];
    subst; eauto.
Qed.

Definition reducible (Ω : State) (e : expr) :=
  exists a Ω' e', Ω ▷ e =[ a ]~> Ω' ▷ e'
.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ => true
  | Var x => bool_In X x
  | BinOp _ e0 e1 => andb (is_closed X e0) (is_closed X e1)
  | Access x e0 => if bool_In X x then is_closed X e0 else false
  | Letin x e0 e1 => andb (is_closed X e0) (is_closed (x :: X) e1)
  | If e0 e1 e2 => andb (andb (is_closed X e0) (is_closed X e1)) (is_closed X e2)
  | Assign x e0 e1 => if bool_In X x then andb (is_closed X e0) (is_closed X e1) else false
  | New y x e0 e1 => andb (is_closed X e0) (is_closed (y :: x :: X) e1)
  | Delete x => bool_In X x
  end
.
Definition closed (X : list string) (e : expr) : Prop := if is_closed X e then True else False.

Lemma closed_equiv_is_closed X e : is_closed X e = true <-> closed X e.
Proof. unfold closed; now rewrite bool_eq_equiv_if. Qed.

Lemma closed_weaken X Y e : closed X e -> X ⊆ Y -> closed Y e.
Proof.
  revert X Y; induction e; unfold closed; cbn; intros; eauto;
  try (rewrite bool_In_equiv_In; rewrite bool_In_equiv_In in H; now apply H0).
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0.
    eapply subset_equiv_bool_in_subset; eassumption.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite bool_and_equiv_prop in H0; rewrite bool_and_equiv_prop;
    destruct H0; split; rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H0, H2;
    (eapply IHe1 + eapply IHe2); unfold closed; eassumption.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    apply nested_bool_pred; rewrite bool_and_equiv_prop;
    rewrite nested_bool_pred in H0; rewrite bool_and_equiv_prop in H0;
    split; destruct H0; try eapply subset_equiv_bool_in_subset; try eassumption;
    rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H2;
    eapply IHe; eassumption.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H0;
    destruct H0; split.
    + rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H0; eapply IHe1; eassumption.
    + rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H2; eapply IHe2; try eassumption; now apply cons_subset.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite !bool_and_equiv_prop in H0; rewrite !bool_and_equiv_prop;
    destruct H0 as [[H2 H3] H4]; repeat split;
    rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H2, H3, H4;
    (eapply IHe1 + eapply IHe2 + eapply IHe3); eauto.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0.
    rewrite nested_bool_pred; rewrite nested_bool_pred in H0.
    rewrite !bool_and_equiv_prop; rewrite !bool_and_equiv_prop in H0.
    destruct H0 as [H2 [H3 H4]]; repeat split;
    try (eapply subset_equiv_bool_in_subset; eauto);
    rewrite <- bool_eq_equiv_if in H3, H4;
    rewrite <- bool_eq_equiv_if; (eapply IHe1 + eapply IHe2); eauto.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H0;
    destruct H0; split;
    rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H0, H2;
    (eapply IHe1 + eapply IHe2); eauto using cons_subset.
  - erewrite bool_In_equiv_In; apply H1; apply bool_In_equiv_In in H0; assumption.
Qed.
Lemma closed_weaken_nil X e : closed nil e -> closed X e.
Proof. intros; eapply closed_weaken; try exact H0; intros ? ?; inv H1. Qed.

Inductive ty :=
| tyNat : ty
| tyRefnat : ty
| tyCap : string -> ty
.
Definition Gamma := list (string * ty).
Reserved Notation "Γa '||-' e ':' τ" (at level 99, right associativity, e at next level, τ at level 200).
Inductive check : Gamma -> expr -> ty -> Prop :=
| Texchange : forall Γ0 Γ1 e ty, (Γ1 ++ Γ0 ||- e : ty) -> (Γ0 ++ Γ1 ||- e : ty)
| Tweaken : forall Γ e ty ty' x, ty = tyNat \/ ty = tyRefnat ->
                            (Γ ||- e : ty') ->
                            ((x,ty)::Γ ||- e : ty')
| TcontractNat : forall Γ e ty x, ((x,tyNat)::(x,tyNat)::Γ ||- e : ty) ->
                             ((x,tyNat)::Γ ||- e : ty)
| TcontractRefnat : forall Γ e ty x y, ((y,tyCap x)::(x,tyRefnat)::Γ ||- e : ty) ->
                                  ((y,tyCap x)::Γ ||- e : ty)
| Tvar : forall x, ((x, tyNat)::nil ||- (Var x) : tyNat)
| Tnat : forall Γ n, (Γ ||- Lit n : tyNat)
| Tbinop : forall Γ1 Γ2 e1 e2 o, (forall x y, ~ In (y, tyCap x) (Γ1 ++ Γ2)) ->
                            (Γ1 ||- e1 : tyNat) ->
                            (Γ2 ||- e2 : tyNat) ->
                            (Γ1 ++ Γ2 ||- BinOp o e1 e2 : tyNat)
| Tget : forall Γ x e, (Γ ||- e : tyNat) ->
                  ((x,tyRefnat)::Γ ||- Access x e : tyNat)
| Tset : forall Γ1 Γ2 x e1 e2, (forall x y, ~ In (y, tyCap x) (Γ1 ++ Γ2)) ->
                          (Γ1 ||- e1 : tyNat) ->
                          (Γ2 ||- e2 : tyNat) ->
                          ((x,tyRefnat)::Γ1++Γ2 ||- Assign x e1 e2 : tyNat)
| Tlet : forall Γ1 Γ2 x e1 e2, (forall x y, ~ In (y, tyCap x) Γ1) ->
                          (Γ1 ||- e1 : tyNat) ->
                          ((x,tyNat)::Γ2 ||- e2 : tyNat) ->
                          (Γ1++Γ2 ||- Letin x e1 e2 : tyNat)
| Tletnew : forall Γ1 Γ2 y x e1 e2, (forall x' y', ~ In (y', tyCap x') Γ1) ->
                               (Γ1 ||- e1 : tyNat) ->
                               ((x,tyRefnat)::(y,tyCap x) :: Γ2 ||- e2 : tyNat) ->
                               (Γ1++Γ2 ||- New y x e1 e2 : tyNat)
| Tdelete : forall Γ y x, ((y,tyCap x)::Γ ||- Delete y : tyNat)
| Tif : forall Γ1 Γ2 e1 e2 e3, (forall x y, ~ In (y, tyCap x) Γ1) ->
                          (Γ1 ||- e1 : tyNat) ->
                          (Γ2 ||- e2 : tyNat) ->
                          (Γ2 ||- e3 : tyNat) ->
                          (Γ1++Γ2 ||- If e1 e2 e3 : tyNat)
where "Γa '||-' e ':' τ" := (check Γa e τ)
.
#[local]
Hint Constructors check : core.

(* This is easier to work with to get traces. TODO: make it cofix when adding loops *)
Fixpoint exec (Ω : State) (e : expr) : option (State * val * list Event) :=
  match e with
  | Var x => match Δ_lookup x Ω with
            | Some(EnvVal(LitV v)) => Some (Ω, LitV v, Internal :: nil)
            | _ => None
            end
  | Lit n => Some (Ω, LitV n, nil)
  | BinOp o e1 e2 =>
      match exec Ω e1 with
      | Some(Ω1, LitV v1, Tr1) =>
          match exec Ω1 e2 with
          | Some(Ω2, LitV v2, Tr2) => Some (Ω2, LitV (v1 + v2), Tr1 ++ Tr2 ++ (Internal :: nil))
          | None => None
          end
      | None => None
      end
  | Access x e => match exec Ω e with
                 | Some(Ω', LitV v, Tr) =>
                   match Δ_lookup x Ω' with
                   | Some(EnvAddr loc) =>
                       let nl := A_lookup loc Ω' in
                       Some (Ω', LitV (H_lookup (nl + v) Ω'), Tr ++ ((Read loc v) :: nil))
                   | _ => None
                   end
                 | None => None
                 end
  | Assign x e1 e2 => match exec Ω e1 with
                     | Some(Ω1, LitV n, Tr1) =>
                         match exec Ω1 e2 with
                         | Some(Ω2, LitV v, Tr2) =>
                           match Δ_lookup x Ω2 with
                           | Some(EnvAddr loc) =>
                               let nl := A_lookup loc Ω2 in
                               Some ((Ω2.(fresh); replace (nl + n) Ω2.(H) v; Ω2.(A); Ω2.(Δ)),
                                     LitV v, Tr1 ++ Tr2 ++ ((Write loc n)::nil))
                           | _ => None
                           end
                         | None => None
                         end
                     | None => None
                     end
  | If e1 e2 e3 => match exec Ω e1 with
                  | Some(Ω1, LitV v, Tr1) =>
                      match v with
                      | 0 => match exec Ω1 e3 with
                            | Some(Ω3, v3, Tr3) => Some(Ω3, v3, Tr1 ++ (Internal :: nil) ++ Tr3)
                            | None => None
                            end
                      | S _ => match exec Ω1 e2 with
                              | Some(Ω2, v2, Tr2) => Some(Ω2, v2, Tr1 ++ (Internal :: nil) ++ Tr2)
                              | None => None
                              end
                      end
                  | None => None
                  end
  | Letin x e1 e2 => match exec Ω e1 with
                    | Some(Ω1, LitV v1, Tr1) =>
                        match exec (Ω1.(fresh); Ω1.(H); Ω1.(A); (x, EnvVal v1) :: Ω1.(Δ)) e2 with
                        | Some(Ω2, v2, Tr2) => Some(Ω2, v2, Tr1 ++ (Internal :: nil) ++ Tr2)
                        | None => None
                        end
                    | None => None
                    end
  | Delete x => match Δ_lookup x Ω with
               | Some (EnvAddr loc) => Some ((Ω.(fresh); Ω.(H); Ω.(A); delete x Ω.(Δ)), LitV 0, (Dealloc loc)::nil)
               | _ => None
               end
  | New _ x e1 e2 => match exec Ω e1 with
                  | Some(Ω1, LitV m, Tr1) =>
                      let loc := LocA(Fresh.fresh (Ω1.(fresh))) in
                      let s := List.length (Ω1.(H)) in
                      match exec (Fresh.advance Ω1.(fresh); grow Ω1.(H) m; (loc,s)::(Ω1.(A)); (x,EnvAddr loc) :: Ω1.(Δ)) e2 with
                      | Some(Ω2, v2, Tr2) => Some(Ω2, v2, Tr1 ++ ((Alloc loc m)::nil) ++ Tr2)
                      | _ => None
                      end
                  | None => None
                  end
  end
.
Definition compute_trace_prefix (e : expr) : list Event :=
  match exec ∅ e with
  | Some(Ω, v, Tr) => Tr
  | None => nil
  end
.
Lemma split_prod {A : Type} (a b c d e a' b' c' d' e' : Type) :
  (a,b,c,d,e) = (a',b',c',d',e') -> a = a' /\ b = b' /\ c = c' /\ d = d' /\ e = e'.
Proof. intros H; inv H; now repeat split. Qed.

Ltac exec_reduce_handle_eq_none := (
  match goal with
  | [ H1: match exec ?Ω ?e with | Some _ => _ | None => None end = _,
     H: exec ?Ω ?e <> None |- _ ] =>
      let Ωa1 := fresh "Ωa" in
      let v1 := fresh "v" in
      let Tr1 := fresh "Tr" in
    apply Util.not_eq_None_Some in H as [x]; destruct x as [[Ωa1 [v1]] Tr1];
    rewrite H in H1; cbn in H1
  end;
  match goal with
  | [Ha: (exec ?Ωa ?e = Some (?Ωa', LitV ?v', ?Tr')),
      IH: forall (Ω : State) (v : nat) (Tr : list Event) (Ω' : State),
          exec Ω ?e = Some (Ω', LitV v, Tr) ->
          (Ω, ?e) =[ Tr ]~>* (Ω', Lit v) |- _ ] =>
      specialize (IH Ωa v' Tr' Ωa' Ha)
  end
).

Ltac exec_reduce := (
  try match goal with
  | [ H: match exec ?Ω ?e with | Some _ => _ | None => None end = _ |- _ ] =>
      assert (exec Ω e <> None) by (
      let Ωa1 := fresh "Ωa" in
      let v1 := fresh "v" in
      let Tr1 := fresh "Tr" in
      destruct (exec Ω e) as [[[Ωa1 [v1]]]|]; congruence);
      exec_reduce_handle_eq_none
  | [ H: match Δ_lookup ?s ?Ω with | Some _ => _ | None => None end = _ |- _ ] =>
    let H2 := fresh "H" in
    destruct (Δ_lookup_dec s Ω) as [H2|H2]; try (rewrite H2 in H; congruence);
    apply Util.not_eq_None_Some in H2 as [x H2];
    rewrite H2 in H; cbn in H
  | [ H: Some _ = Some _ |- _ ] => inv H
  | [ H : match ?x with | EnvAddr _ => _ | EnvVal _ => _ end = _ |- _] => destruct x; try congruence
  | [ H : match ?v with | 0 => _ | S _ => _ end = _ |- _ ] => destruct v
  end
).

Lemma exec_is_steps Ω Ω' e v Tr :
  exec Ω e = Some (Ω', LitV v, Tr) ->
  Ω ▷ e =[ Tr ]~>* Ω' ▷ Lit v
.
Proof.
  revert Ω v Tr Ω'; induction e; intros; cbn in H0; inv H0; eauto.
  - repeat exec_reduce; destruct v0; inv H2; eauto.
  - repeat exec_reduce;
    eapply fill_steps with (K:=LBinOpCtx b HoleCtx e2) in IHe1; cbn in IHe1;
    eapply fill_steps with (K:=RBinOpCtx b (LitV v0) HoleCtx) in IHe2; cbn in IHe2;
    eauto using trans_steps.
  - repeat exec_reduce;
    eapply fill_steps with (K:=AccessCtx s HoleCtx) in IHe; cbn in IHe;
    eapply trans_steps; try exact IHe; eapply stepsTrans; try eapply stepsRefl;
    context_solver HoleCtx; econstructor; trivial.
  - repeat exec_reduce;
    eapply fill_steps with (K:=LetinCtx s HoleCtx e2) in IHe1; cbn in IHe1;
    eauto using trans_steps.
  - repeat exec_reduce;
    eapply fill_steps with (K:=IfCtx HoleCtx e2 e3) in IHe1; cbn in IHe1;
    eauto using trans_steps.
  - repeat exec_reduce;
    eapply fill_steps with (K:=AssignCtx s HoleCtx e2) in IHe1; cbn in IHe1;
    eapply fill_steps with (K:=AssignVCtx s (LitV v0) HoleCtx) in IHe2; cbn in IHe2;
    eapply trans_steps; try exact IHe1; eapply trans_steps; eauto.
  - repeat exec_reduce;
    eapply fill_steps with (K:=NewCtx s s0 HoleCtx e2) in IHe1; cbn in IHe1.
    eapply trans_steps; try exact IHe1.
    eapply stepsTrans; try exact IHe2.
    context_solver HoleCtx.
  - repeat exec_reduce; eauto.
Qed.

Fixpoint drop {A} (Γ : list (string * A)) : list string :=
  match Γ with
  | nil => nil
  | (x,_) :: Γ' => x :: (drop Γ')
  end
.
Lemma closed_typing Γ e τ :
  (Γ ||- e : τ) -> closed (drop Γ) e.
Proof.
  induction 1; subst; apply closed_equiv_is_closed; cbn.
  - (* exchange *) admit.
  - (* weaken *) admit.
  - (* contract ℕ *) admit.
  - (* contract refℕ *) admit.
  - (* var *) destruct (string_dec x x); now cbn.
  - (* lit *) easy.
  - (* binop *) apply bool_and_equiv_prop; split; apply closed_equiv_is_closed;
    admit.
  - (* access *) destruct (string_dec x x); try now cbn. admit.
  - (* assign *) destruct (string_dec x x); try now cbn.
    rewrite !bool_and_equiv_prop; repeat split.
    + admit.
    + admit.
  - (* letin *) apply bool_and_equiv_prop; split.
    + admit.
    + admit.
  - (* new *) apply bool_and_equiv_prop; split.
    + admit.
    + admit.
  - (* delete *) destruct (string_dec y y); now cbn.
  - (* if *) rewrite !bool_and_equiv_prop; repeat split.
    + admit.
    + admit.
    + admit.
Admitted.

Lemma cons_read_same x v Ω :
  H_lookup x (Ω.(fresh); v :: (Ω.(H)); Ω.(A); Ω.(Δ)) = v -> H_lookup (S x) (Ω.(fresh); v :: v :: (Ω.(H)); Ω.(A); Ω.(Δ)) = v.
Proof. revert v Ω; induction x; intros; cbn in *; trivial. Qed.

Lemma gprogress e τ Γ :
  (Γ ||- e : τ) -> is_val e \/ exists Ω, reducible Ω e.
Proof.
  induction 1; subst.
  - (* exchange *) easy.
  - (* weaken *) easy.
  - (* contract ℕ *) easy.
  - (* contract refℕ *) easy.
  - (* var *) right; exists (empty_fresh; nil; nil; (x, EnvVal(LitV 0)) :: nil); do 3 eexists; context_solver HoleCtx;
    eapply VarS; cbn; now rewrite String.eqb_refl.
  - (* lit *) now left.
  - (* binop *) right; destruct (IHcheck1), (IHcheck2); get_values; subst.
    + exists ∅; do 3 eexists; context_solver HoleCtx.
    + do 4 destruct H2 as [? H2]; do 4 eexists;
      eapply fill_contextual_step with (K:=RBinOpCtx o (LitV x) HoleCtx) in H2; eauto.
    + do 4 destruct H1 as [? H1]; exists x0; exists x1; exists x2;
      exists (BinOp o x3 (Lit x)); now eapply fill_contextual_step with (K:=LBinOpCtx o HoleCtx (Lit x)) in H1.
    + do 4 destruct H1 as [? H1]; exists x; exists x0; exists x1;
      exists (BinOp o x2 e2); now eapply fill_contextual_step with (K:=LBinOpCtx o HoleCtx e2) in H1.
  - (* access *) right; destruct (IHcheck); get_values; subst.
    + do 4 eexists; context_solver HoleCtx; econstructor.
      instantiate (1:=LocA 0). instantiate (1:=(empty_fresh; grow nil (1+x0); (LocA 0, 0)::nil; (x,EnvAddr(LocA 0))::nil)); cbn; now rewrite String.eqb_refl.
      instantiate (1:=0); now cbn.
      instantiate (1:=0); cbn; clear IHcheck H0; induction x0; cbn; trivial; now apply cons_read_same.
    + do 4 destruct H1 as [? H1]; do 4 eexists;
      eapply fill_contextual_step with (K:=AccessCtx x HoleCtx) in H1; cbn in H1; eassumption.
  - (* assign *) right; destruct (IHcheck1), (IHcheck2); get_values; subst.
    + do 4 eexists; context_solver HoleCtx; econstructor.
      instantiate (1:=LocA 0). instantiate (1:=(empty_fresh; nil; (LocA 0, 0)::nil; (x, EnvAddr(LocA 0))::nil)); cbn; now rewrite String.eqb_refl.
      instantiate (1:=0); now cbn.
      instantiate (1:=nil); now destruct x1; cbn.
    + do 4 destruct H2 as [? H2]; do 4 eexists; eapply fill_contextual_step with (K:=AssignVCtx x (LitV x0) HoleCtx) in H2; eauto.
    + do 4 destruct H1 as [? H1]; do 4 eexists; eapply fill_contextual_step with (K:=AssignCtx x HoleCtx (Lit x0)) in H1; eauto.
    + do 4 destruct H1 as [? H1]; do 4 eexists; eapply fill_contextual_step with (K:=AssignCtx x HoleCtx e2) in H1; eauto.
  - (* letin *) right; destruct (IHcheck1); get_values; subst.
    + exists ∅; do 3 eexists; eauto.
    + do 4 destruct H1 as [? H1]; do 4 eexists; eapply fill_contextual_step with (K:=LetinCtx x HoleCtx e2) in H1; eauto.
  - (* new *) right; destruct (IHcheck1); get_values; subst.
    + exists ∅; do 3 eexists; context_solver HoleCtx; econstructor; reflexivity.
    + do 4 destruct H1 as [? H1]; do 4 eexists; eapply fill_contextual_step with (K:=NewCtx y x HoleCtx e2) in H1; eauto.
  - (* delete *) right; exists (empty_fresh; nil; nil; (y,EnvAddr(LocA 0))::nil); do 3 eexists; context_solver HoleCtx;
    econstructor; cbn; now rewrite String.eqb_refl.
  - (* if *) right; destruct (IHcheck1); get_values; subst.
    + exists ∅; exists Internal; exists ∅; destruct (Nat.eq_dec x 0); subst.
      * exists e3; context_solver HoleCtx.
      * exists e2; context_solver HoleCtx.
    + do 4 destruct H1 as [? H1]; eapply fill_contextual_step with (K:=IfCtx HoleCtx e2 e3) in H1; do 4 eexists; eassumption.
Qed.

Lemma gprogress_steps e τ Γ :
  (Γ ||- e : τ) -> exists Ω Ω' Tr v, (Ω ▷ e =[ Tr ]~>* Ω' ▷ v) \/ is_val v.
Proof.
  intros; apply gprogress in H0 as [].
  - do 2 exists ∅; exists nil; apply is_val_inv in H0 as []; exists (Lit x); subst; repeat constructor.
  - destruct H0 as [Ω [E [Ω' [e' H0]]]]; exists Ω; exists Ω'; exists (E :: nil); exists e'; left; eapply stepsTrans; try eassumption; eapply stepsRefl.
Qed.

Lemma binop_ctx_step_inv Ω1 b e1 e2 Ω3 v E :
  Ω1 ▷ BinOp b e1 e2 =[ E ]~> Ω3 ▷ Lit v ->
  exists v1 v2, (e1 = Lit v1 /\ e2 = Lit v2 /\ E = Internal /\ v = bin_op_eval_int b v1 v2)
.
Proof.
  intros; inv H0; induction K; cbn in *; try congruence; subst;
  inv H8; exists n1; exists n2; easy.
Qed.

Lemma binop_ctx_step_inv_extra Ω1 b e1 e2 Ω3 Tr e :
  Ω1 ▷ BinOp b e1 e2 =[ Tr ]~> Ω3 ▷ e ->
  (exists v, e = Lit v) \/
  (exists Ω1' Tr1 e1', (Ω1 ▷ e1 =[ Tr1 ]~> Ω1' ▷ e1') /\ e = BinOp b e1' e2) \/
  (exists Ω2' Tr2 e2', (Ω1 ▷ e2 =[ Tr2 ]~> Ω2' ▷ e2') /\ e = BinOp b e1 e2')
.
Proof.
Admitted.

Lemma lit_steps_inv Ω1 v1 Ω2 v2 Tr :
  Ω1 ▷ (Lit v1) =[ Tr ]~>* Ω2 ▷ Lit v2 ->
  Ω1 = Ω2 /\ v1 = v2 /\ Tr = nil.
Proof.
  intros H; inv H; repeat split; trivial;
  inv H4; induction K; cbn in *; try congruence; subst; inv H9.
Qed.

Lemma binop_steps_lits_inv Ω1 b Ω3 v1 v2 v Tr :
  Ω1 ▷ BinOp b (Lit v1) (Lit v2) =[ Tr ]~>* Ω3 ▷ Lit v ->
  Ω1 = Ω3 /\ v = v1 + v2 /\ Tr = Internal :: nil.
Proof.
  intros; inv H0; inv H5; destruct K; cbn in *; try congruence; subst.
  - inv H9; apply inv_lit_steps in H7 as [H [H0 H1]]; subst; inv H; easy.
  - inv H6; destruct K; cbn in *; try congruence; subst; inv H9.
  - inv H6; destruct K; cbn in *; try congruence; subst; inv H9.
Qed.

Lemma binop_steps_inv Ω1 b e1 e2 Ω3 v Tr :
  Ω1 ▷ BinOp b e1 e2 =[ Tr ]~>* Ω3 ▷ Lit v ->
  exists Ω2 Tr1 Tr2 v1 v2, ((Ω1 ▷ e1 =[ Tr1 ]~>* Ω2 ▷ Lit v1) /\ (Ω2 ▷ e2 =[ Tr2 ]~>* Ω3 ▷ Lit v2)
/\ Tr = Tr1 ++ Tr2 ++ Internal :: nil /\ v = bin_op_eval_int b v1 v2)
.
Proof.
Admitted.

Lemma access_steps_inv Ω1 Ω3 s e v Tr :
  Ω1 ▷ Access s e =[ Tr ]~>* Ω3 ▷ Lit v ->
  exists Ω' Tr' loc v1, ((Ω1 ▷ e =[ Tr' ]~>* Ω' ▷ Lit v1)
/\ (Ω3 = Ω' /\ v = H_lookup (A_lookup loc Ω' + v1) Ω')
/\ Δ_lookup s Ω' = Some(EnvAddr loc) /\ Tr = Tr' ++ Read loc v1 :: nil)
.
Proof.
Admitted.

Lemma letin_steps_inv Ω1 Ω3 s e1 e2 v Tr :
  Ω1 ▷ Letin s e1 e2 =[ Tr ]~>* Ω3 ▷ Lit v ->
  exists Ω2 Tr1 Tr2 v1 v2, (Ω1 ▷ e1 =[ Tr1 ]~>* Ω2 ▷ Lit v1)
/\ ((Ω2.(fresh); Ω2.(H); Ω2.(A); (s,EnvVal v1) :: Ω2.(Δ)) ▷ e2 =[ Tr2 ]~>* Ω3 ▷ Lit v2) /\ v = v2 /\ Tr = Tr1 ++ Internal :: Tr2
.
Proof.
Admitted.

Lemma if_steps_inv Ω Ω' e1 e2 e3 v Tr :
  Ω ▷ If e1 e2 e3 =[ Tr ]~>* Ω' ▷ Lit v ->
  exists v1 Tr1 Ω1, ((Ω ▷ e1 =[ Tr1 ]~>* Ω1 ▷ Lit v1) /\ (
    (v1 <> 0 /\ exists v2 Tr2 Ω2, (Ω1 ▷ e2 =[ Tr2 ]~>* Ω2 ▷ Lit v2) /\ v = v2 /\ Tr = Tr1 ++ Internal :: Tr2 /\ Ω' = Ω2)
  \/ (v1 = 0 /\ exists v3 Tr3 Ω3, (Ω1 ▷ e3 =[ Tr3 ]~>* Ω3 ▷ Lit v3) /\ v = v3 /\ Tr = Tr1 ++ Internal :: Tr3 /\ Ω' = Ω3)
  ))
.
Proof.
Admitted.

Lemma assign_steps_inv Ω Ω' s e1 e2 v Tr :
  Ω ▷ Assign s e1 e2 =[ Tr ]~>* Ω' ▷ Lit v ->
  exists v1 Tr1 Ω1 v2 Tr2 Ω2 loc, (Ω ▷ e1 =[ Tr1 ]~>* Ω1 ▷ Lit v1) /\ (Ω1 ▷ e2 =[ Tr2 ]~>* Ω2 ▷ Lit v2)
/\ ((Δ_lookup s Ω2 = Some(EnvAddr loc)
                             /\ Tr = Tr1 ++ Tr2 ++ Write loc v1 :: nil /\ v = v2 /\ Ω'.(fresh) = Ω2.(fresh)
                             /\ Ω'.(H) = replace (A_lookup loc Ω2 + v1) Ω2.(H) v2 /\ Ω'.(A) = Ω2.(A) /\ Ω'.(Δ) = Ω2.(Δ)))
.
Proof.
Admitted.

Lemma new_steps_inv Ω Ω' s s0 e1 e2 v Tr :
  Ω ▷ New s0 s e1 e2 =[ Tr ]~>* Ω' ▷ Lit v ->
  exists v1 Tr1 Ω1 v2 Tr2 Ω2, (Ω ▷ e1 =[ Tr1 ]~>* Ω1 ▷ Lit v1)
/\ (((Fresh.advance (Ω1.(fresh)); grow Ω1.(H) v1;
     (LocA(Fresh.fresh Ω1.(fresh)), List.length Ω1.(H)) :: (Ω1.(A)); (s,EnvAddr(LocA(Fresh.fresh (Ω1.(fresh))))) :: (Ω1.(Δ))
                                ▷ e2 =[ Tr2 ]~>* Ω2 ▷ Lit v2)
/\  Ω' = Ω2 /\ v = v2 /\ Tr = Tr1 ++ Alloc (LocA(Fresh.fresh(Ω1.(fresh)))) v1 :: Tr2))
.
Proof.
Admitted.

Lemma delete_steps_inv Ω Ω' s Tr v :
  Ω ▷ Delete s =[ Tr ]~>* Ω' ▷ Lit v ->
  exists loc, (Δ_lookup s Ω = Some(EnvAddr loc)
      /\ Ω' = (Ω.(fresh); Ω.(H); Ω.(A); delete s Ω.(Δ)) /\ v = 0 /\ Tr = Dealloc loc :: nil
  ).
Proof.
  intros; destruct Ω; inv H0.
  inv H6; induction K; cbn in *; try congruence; subst; inv H10;
  exists loc; repeat split; apply inv_lit_steps in H8 as [Hx0 [Hx1 Hx2]]; try easy;
  now (inv Hx0 + rewrite Hx2).
Qed.

(*
Inductive ectx_check : Gamma -> ectx -> ty -> ty -> Prop :=
| Ctx_check_swap : forall Γ0 Γ1 K ty0 ty1, ectx_check (Γ0 ++ Γ1) K ty0 ty1 ->
                                      ectx_check (Γ1 ++ Γ0) K ty0 ty1
| Ctx_check_weak : forall Γ x t K ty0 ty1, ectx_check Γ K ty0 ty1 ->
                                      ectx_check ((x,t)::Γ) K ty0 ty1
| Ctx_check_contrnat : forall Γ x K ty0 ty1, ectx_check ((x,tyNat)::(x,tyNat)::Γ) K ty0 ty1 ->
                                        ectx_check ((x,tyNat)::Γ) K ty0 ty1
| Ctx_check_contrrefnat : forall Γ y x K ty0 ty1,
                             ectx_check ((y,tyCap x)::(x,tyRefnat)::Γ) K ty0 ty1 ->
                             ectx_check ((y,tyCap x)::Γ) K ty0 ty1
| HoleCtx_check : forall Γ A, ectx_check Γ HoleCtx A A
| LBinOpCtx_check : forall Γ0 Γ1 o K e A, (Γ1 ||- e : tyNat) ->
                                 (ectx_check Γ0 K A tyNat) ->
                                  ectx_check (Γ0 ++ Γ1) (LBinOpCtx o K e) A tyNat
| RBinOpCtx_check : forall Γ o K v A, (ectx_check Γ K A tyNat) ->
                                  ectx_check Γ (RBinOpCtx o v K) A tyNat
| AccessCtx_check : forall Γ x K A, (ectx_check Γ K A tyNat) ->
                                Util.find (String.eqb x) Γ = Some tyRefnat ->
                                ectx_check Γ (AccessCtx x K) A tyNat
| LetinCtx_check : forall Γ0 Γ1 x e K A, (ectx_check Γ0 K A tyNat) ->
                                    ((x, tyNat) :: Γ1 ||- e : tyNat) ->
                                    (ectx_check (Γ0 ++ Γ1) (LetinCtx x K e) A tyNat)
| AssignCtx_check : forall Γ0 Γ1 x e K A, (ectx_check Γ0 K A tyNat) ->
                                     (Γ1 ||- e : tyNat) ->
                                     (ectx_check (Γ0 ++ Γ1) (AssignCtx x K e) A tyNat)
| AssignVCtx_check : forall Γ0 x v K A, (ectx_check Γ0 K A tyNat) ->
                                   (ectx_check Γ0 (AssignVCtx x v K) A tyNat)
| NewCtx_check : forall Γ0 Γ1 y x e K A, (ectx_check Γ0 K A tyNat) ->
                                    ((y, tyCap x) :: (x, tyRefnat) :: Γ1 ||- e : tyNat) ->
                                    (ectx_check (Γ0 ++ Γ1) (NewCtx y x K e) A tyNat)
| IfCtx_check : forall Γ0 Γ1 e1 e2 K A, (ectx_check Γ0 K A tyNat) ->
                                   (Γ1 ||- e1 : tyNat) ->
                                   (Γ1 ||- e2 : tyNat) ->
                                   (ectx_check (Γ0 ++ Γ1) (IfCtx K e1 e2) A tyNat)
.
#[local]
Hint Constructors ectx_check : core.
*)
Lemma delete_is_subset (Γ : Gamma) x :
  delete x Γ ⊆ Γ.
Proof.
  induction Γ; trivial; destruct a; intros [s0 t0] H;
  cbn in *; destruct (string_dec x s).
  - subst; now right.
  - specialize (IHΓ (s0, t0)); cbn in H; destruct H.
    + now left.
    + right; auto.
Qed.
#[local]
Hint Resolve delete_is_subset : core.

Lemma subset_swap_nil (Γ1 Γ3 : Gamma) :
  Γ1 ++ nil ⊆ Γ3 -> nil ++ Γ1 ⊆ Γ3.
Proof. intros H; cbn; now rewrite app_nil_r in H. Qed.
Lemma subset_swap_cons a (Γ1 Γ3 : Gamma) :
  Γ1 ++ a :: nil ⊆ Γ3 -> a :: Γ1 ⊆ Γ3.
Proof.
  intros H0 x H1; apply H0; destruct H1; subst; induction Γ1; cbn; firstorder.
Qed.
Lemma subset_swap (Γ1 Γ2 Γ3 : Gamma) :
  Γ1 ++ Γ2 ⊆ Γ3 -> Γ2 ++ Γ1 ⊆ Γ3.
Proof.
  intros H0 x H1; apply H0. induction Γ2; cbn in *.
  now rewrite app_nil_r. destruct H1; subst.
  clear IHΓ2; induction Γ1; cbn; firstorder.
  clear IHΓ2 H0. induction Γ2; cbn in *; firstorder.
  eapply subset_swap_nil in H1. exact H1. clear H1; rewrite app_nil_r.
  induction Γ1; cbn; firstorder eauto.
  subst; clear IHΓ2; induction Γ1; firstorder eauto.
  clear H0; induction Γ1; firstorder eauto.
Qed.
Lemma subset_cons_swap a b (Γ1 Γ2 : Gamma) :
  a :: b :: Γ1 ⊆ Γ2 -> b :: a :: Γ1 ⊆ Γ2.
Proof. firstorder eauto. Qed.
Lemma subset_weak a (Γ1 Γ2 : Gamma) :
  a :: Γ1 ⊆ Γ2 -> Γ1 ⊆ Γ2.
Proof. firstorder eauto. Qed.
Lemma cons_subset a (Γ1 Γ2 : Gamma) :
  Γ1 ⊆ Γ2 -> a :: Γ1 ⊆ a :: Γ2.
Proof. firstorder eauto. Qed.

Lemma preservation_base e e' Γ0 Ω Ω' a ty :
  (Γ0 ||- e : ty) ->
  (Ω ▷ e -[ a ]~> Ω' ▷ e') ->
  exists Γ1, (Γ1 ||- e' : ty) /\ (Γ0 ⊆ Γ1)
.
Proof.
  intros H0 H1; dependent induction H0; eauto.
  - specialize (IHcheck H1); destruct IHcheck as [Γ2 [IHchecka IHcheckb]];
    eauto using subset_swap.
  - specialize (IHcheck H2); destruct IHcheck as [Γ2 [IHchecka IHcheckb]];
    exists ((x,ty0)::Γ2); split; trivial.
    eapply Tweaken; trivial.
    now apply cons_subset.
  - specialize (IHcheck H1); destruct IHcheck as [Γ2 [IHchecka IHcheckb]].
    exists Γ2; split; trivial. eapply subset_weak; eassumption.
  - specialize (IHcheck H1); destruct IHcheck as [Γ2 [IHchecka IHcheckb]].
    exists Γ2; split; trivial. eapply subset_weak, subset_cons_swap; eassumption.
  - inv H1; exists ((x,tyNat)::nil); split; eauto.
  - inv H1; eauto.
  - inv H1. remember (Γ1++Γ2) as Γ3; exists Γ3.
    clear Ω' Γ1 Γ2 HeqΓ3 H0_ H0_0 IHcheck2 IHcheck1; induction Γ3; split; eauto.
  - inv H1; exists ((x,tyRefnat)::Γ); split; eauto.
  - inv H1; eauto.
  - inv H1; exists (Γ1 ++ (x,tyNat) :: Γ2); split; clear Ω v H0_ IHcheck1 IHcheck2.
    induction Γ1; cbn; eauto.
    + destruct a; eapply Tweaken.
      destruct t; eauto; edestruct H0; now left.
      apply IHΓ1; intros x0 y0 H1; eapply H0; right; eassumption.
    + clear e' H0 H0_0. induction Γ1; firstorder eauto.
  - inv H1. exists (Γ1 ++ (x, tyRefnat) :: (y, tyCap x) :: Γ2); split; clear Ω n H0_ IHcheck1 IHcheck2.
    induction Γ1; cbn; eauto.
    + destruct a; eapply Tweaken.
      destruct t; eauto; edestruct H0; now left.
      apply IHΓ1; intros x0 y0 H1; eapply H0; right; eassumption.
    + clear e' H0 H0_0. induction Γ1; firstorder eauto.
  - inv H1; eauto.
  - inv H1; eauto; exists (Γ1 ++ Γ2); split; trivial.
    + clear Ω' H0_ H0_0 IHcheck1 IHcheck2 IHcheck3; induction Γ1; cbn; eauto.
      * destruct a; eapply Tweaken.
        destruct t; eauto; edestruct H0; now left.
        apply IHΓ1; intros x0 y0 H1; eapply H0; right; eassumption.
    + clear Ω' H0_ H0_1 IHcheck1 IHcheck2 IHcheck3; induction Γ1; cbn; eauto.
      * destruct a; eapply Tweaken.
        destruct t; eauto; edestruct H0; now left.
        apply IHΓ1; intros x0 y0 H1; eapply H0; right; eassumption.
Qed.

Lemma inv_check_binop Γ b e1 e2 ty :
  (Γ ||- BinOp b e1 e2 : ty) ->
  exists Γ0 Γ1, ty = tyNat /\ (Γ ⊆ Γ0 ++ Γ1) /\ (Γ0 ||- e1 : tyNat) /\ (Γ1 ||- e2 : tyNat).
Proof.
  intros H; assert (H':=H); remember (BinOp b e1 e2) as e3; dependent induction H;
  try congruence.
  - destruct IHcheck as [Γ2 [Γ3 [IHchecka [IHcheckb [IHcheckc IHcheckd]]]]]; trivial.
    exists Γ2; exists Γ3; repeat split; eauto.
    clear b e1 e2 e Heqe3 ty0 H0 H' IHchecka IHcheckc IHcheckd.
    now apply subset_swap.
  - destruct IHcheck as [Γ2 [Γ3 [IHchecka [IHcheckb [IHcheckc IHcheckd]]]]]; trivial.
    exists ((x,ty0)::Γ2); exists Γ3; repeat split; firstorder.
  - destruct IHcheck as [Γ2 [Γ3 [IHchecka [IHcheckb [IHcheckc IHcheckd]]]]]; trivial.
    exists ((x,ty0)::Γ2); exists Γ3; repeat split; eauto; firstorder.
  - destruct IHcheck as [Γ2 [Γ3 [IHchecka [IHcheckb [IHcheckc IHcheckd]]]]]; trivial.
    exists Γ2; exists Γ3; repeat split; eauto; firstorder.
  - inv Heqe3; clear IHcheck1 H' IHcheck2; do 2 eexists; repeat split; eauto.
Qed.
#[local]
Hint Resolve inv_check_binop : core.

Lemma weaken_check (Γ1 Γ2 : Gamma) e (A : ty) :
  (forall x y, ~ In (y, tyCap x) Γ2) ->
  (Γ1 ||- e : A) -> Γ1 ⊆ Γ2 -> (Γ2 ||- e : A)
.
Proof.
Admitted.

Definition ectx_check (Γ : Gamma) (K : ectx) (A B : ty) :=
  forall e Γ', (forall x y, ~ In (y, tyCap x) Γ') ->
          (Γ' ||- e : A) ->
          (Γ ⊆ Γ') ->
          (Γ ||- (fill K e) : B).
Lemma weaken_ctx_check Γ0 Γ1 K ty ty' :
  (ectx_check Γ0 K ty ty') ->
  (Γ0 ⊆ Γ1) ->
  (ectx_check Γ1 K ty ty').
Proof.
  intros H0 H1 e Γ' H2 H3 H4.
  assert (Γ0 ⊆ Γ') by firstorder.
  specialize (H0 e Γ' H2 H3 H5).
  eapply weaken_check; eauto.
  intros x0 y0 H6. edestruct H2. eapply H4. exact H6.
Qed.

Lemma preservation_decomposition e K Γ0 ty :
  (Γ0 ||- fill K e : ty) ->
  exists ty' Γ1, (Γ1 ||- e : ty') /\ (ectx_check Γ0 K ty' ty) /\ (Γ0 ⊆ Γ1).
Proof.
Admitted.

Lemma preservation_composition e K Γ Γ' ty ty' :
  (ectx_check Γ K ty ty') ->
  (Γ' ||- e : ty) ->
  (Γ ||- fill K e : ty').
Proof. intros H0 H1; eapply H0; eauto. Qed.

Lemma preservation e e' Γ0 Ω Ω' a ty :
  (Γ0 ||- e : ty) ->
  (Ω ▷ e =[ a ]~> Ω' ▷ e') ->
  exists Γ1, (Γ1 ||- e' : ty) /\ (Γ0 ⊆ Γ1)
.
Proof.
  intros H0 H1; inv H1.
  eapply preservation_decomposition in H0 as [ty' [Γ1 [H0a [H0b H0c]]]].
  eapply preservation_base in H9 as [Γ2 [H9a H9b]]; eauto.
  eexists; repeat split; eauto.
  eapply weaken_ctx_check in H0b; eauto.
  eapply H0b; exact H9a.
Qed.

Lemma preservation_star e e' Γ0 Ω Ω' a ty :
  (Γ0 ||- e : ty) ->
  (Ω ▷ e =[ a ]~>* Ω' ▷ e') ->
  exists Γ1, (Γ1 ||- e' : ty) /\ (Γ0 ⊆ Γ1)
.
Proof.
  intros H0 H1; assert (H1' := H1); pattern e in H0;
  change ((fun x : Conf =>
             let (_, e) := x in
             (Γ0 ||- e : ty)
          ) (Ω ▷ e)) in H0;
  remember (Ω ▷ e) as σ;
  pattern e';
  change ((fun x : Conf =>
            let (_, e0) := x in
            exists Γ1 : Gamma, (Γ1 ||- e0 : ty) /\
                          (Γ0 ⊆ Γ1)
         ) (Ω' ▷ e'));
  remember (Ω' ▷ e') as σ';
  clear Heqσ Heqσ' e e' Ω Ω'.
  revert Γ0 ty H0; induction H1; intros Γ0 ty H2; eauto;
  specialize (IHsteps H1).
  eapply preservation in H2.
  destruct H2 as [Γ1 [H0a H0b]].
  edestruct IHsteps as [Γ2 [IHsteps0 IHsteps1]]; eauto.
  eassumption.
Qed.


Inductive WhileProgram :=
| WProg : forall e, closed nil e -> WhileProgram
.
Inductive WhileComponent :=
| WComp : forall e, closed ("x"%string :: nil) e -> WhileComponent
.
Inductive WhileContext :=
| WCtx : forall e0 e1, closed nil e0 -> closed ("y"%string :: nil) e1 -> WhileContext
.
Definition wprog2tracepref (p : WhileProgram) : list Event :=
  match p with
  | WProg e _ => compute_trace_prefix e
  end
.

Lemma contexts_closed e0 ep e1 :
  closed nil e0 ->
  closed ("y"%string :: nil) e1 ->
  closed ("x"%string :: nil) ep ->
  closed nil (Letin "y"%string (Letin "x"%string e0 ep) e1).
Proof.
  intros; unfold closed; cbn; rewrite bool_eq_equiv_if, !bool_and_equiv_prop;
  repeat split; rewrite closed_equiv_is_closed; trivial.
Defined.
Definition plug (c : WhileContext) (p : WhileComponent) : WhileProgram :=
  match c with
  | WCtx e0 e1 H0 H1 => match p with
                       | WComp ep Hp => WProg (Letin ("y"%string) (Letin ("x"%string) e0 ep) e1)
                                             (contexts_closed e0 ep e1 H0 H1 Hp)
                       end
  end
.
Inductive whole_program_check : WhileProgram -> Type :=
| WProgCheck : forall e t (H : nil ||- e : tyNat), whole_program_check (WProg e t)
.
Inductive component_check : WhileComponent -> Type :=
| WCompCheck : forall e (H : ((("x"%string, tyNat)::nil) ||- e : tyNat)),
               component_check (WComp e (closed_typing H))
.
Inductive context_check : WhileContext -> Type :=
| WCtxCheck : forall e0 e1 (H0 : (nil ||- e0 : tyNat)) (H1 : ((("y"%string, tyNat) :: nil) ||- e1 : tyNat)),
                            context_check (WCtx e0 e1 (closed_typing H0) (closed_typing H1))
.

(** We are only interested in safety properties.
    Thus, it is fine to ignore infinite program executions and just look at prefixes. *)
Definition Trace := list Event.
Definition occ (e : Event) (t : Trace) := List.In e t.

Definition one_event (e : Event) (t : Trace) :=
  forall n, List.nth_error t n = Some e -> ~exists m, n <> m /\ List.nth_error t m = Some e
.
Definition after_another_event (e0 e1 : Event) (t : Trace) :=
  forall n, List.nth_error t n = Some e0 -> exists m, List.nth_error t m = Some e1 /\ n < m
.
Definition temp_memsafe (t : Trace) :=
  forall v s, after_another_event (Alloc v s) (Dealloc v) t /\
         (~(forall x, after_another_event (Read v x) (Alloc v s) t)) /\
         (~(forall x, after_another_event (Write v x) (Alloc v s) t)) /\
         (~(forall x, after_another_event (Dealloc v) (Read v x) t)) /\
         (~(forall x, after_another_event (Dealloc v) (Write v x) t))
.
Definition spat_memsafe (t : Trace) :=
  forall loc s, occ (Alloc loc s) t ->
           (forall n, occ (Read loc n) t -> n < s) /\
           (forall n, occ (Write loc n) t -> n < s)
.

Lemma plug_checks_propagate (c : WhileContext) (p : WhileComponent) :
  context_check c ->
  component_check p ->
  whole_program_check (plug c p).
Proof.
  intros H H0; destruct c, H, H0; cbn; repeat (econstructor; trivial).
  change (nil ++ nil ||- Letin "y" (Letin "x" e2 e) e3 : tyNat).
  eapply Tlet.
  - eauto.
  - change (nil ++ nil ||- Letin "x" e2 e : tyNat); eauto.
  - assumption.
Defined.
Definition prog2trace (p : WhileProgram) : Trace := wprog2tracepref p.

Definition wsat (p : WhileProgram) (H : whole_program_check p) (π : Trace -> Prop) : Prop := π (prog2trace p).
Definition wrsat (p : WhileComponent) (H0 : component_check p) (π : Trace -> Prop) : Prop :=
  forall (c : WhileContext) (H1 : context_check c), @wsat (plug c p) (@plug_checks_propagate c p H1 H0) π
.

(** Returns the suffix starting at the nth position in the given trace t. *)
Fixpoint sufftr (n : nat) (t : list Event) :=
  match n,t with
  | 0,t' => t'
  | _,nil => nil
  | S n',_ :: t' => sufftr n' t'
  end
.
Ltac boring := (
  repeat match goal with
  | [H: nth_error nil ?n = Some _ |- _] =>
      induction n; cbn in *; congruence
  | [H: (?Ω, Lit ?n) =[ ?TR ]~>* (?Ω'', Lit ?n') |- _] =>
      apply lit_steps_inv in H as [Ha [Hb Hc]]; subst
  | [H: Lit ?v = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: Var ?v = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  end
).
Lemma base_alloc_yields_new e e' Ω Ω' loc s :
  Ω ▷ e -[ Alloc loc s ]~> Ω' ▷ e' ->
  exists y x e2, e = New y x (Lit s) e2 /\ Δ_lookup x Ω' = Some (EnvAddr loc) /\ e' = e2.
Proof.
  intros H; inv H; boring.
  exists y; exists x; exists e'; cbn; split; trivial.
  rewrite eqb_refl; now cbn.
Qed.
Lemma ctx_alloc_yields_new e e' Ω Ω' loc s :
  Ω ▷ e =[ Alloc loc s ]~> Ω' ▷ e' ->
  exists K y x e2, e = fill K (New y x (Lit s) e2) /\ Δ_lookup x Ω' = Some (EnvAddr loc) /\
              e' = fill K e2.
Proof.
  intros H; inv H; boring; apply base_alloc_yields_new in H7 as [y [x [e2 [H0a [H0b H0c]]]]];
  exists K; subst; eauto. do 3 eexists; repeat split; easy.
Qed.
Lemma steps_alloc_yields_new e e' Ω Ω' Tr loc s :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ e' ->
  List.nth_error Tr 0 = Some (Alloc loc s) ->
  exists Ω'' K y x e2, e = fill K (New y x (Lit s) e2) /\ Δ_lookup x Ω'' = Some (EnvAddr loc)
   /\ (Ω ▷ e =[ Alloc loc s ]~> Ω'' ▷ fill K e2)
   /\ Ω'' ▷ fill K e2 =[ List.tail Tr ]~>* Ω' ▷ e'.
Proof.
  intros H0 H1; inv H0; boring;
  cbn in H1; inv H1;
  exists Ω'0;
  edestruct ctx_alloc_yields_new as [K [y [x [e2 [H0a [H0b H0c]]]]]]; cbn; subst; eauto;
  exists K; exists y; exists x; exists e2; repeat split; subst; eauto.
Qed.
Lemma steps_alloc_yields_new_inbetween e e' Ω Ω' Tr loc s n :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ e' ->
  List.nth_error Tr n = Some (Alloc loc s) ->
  exists Ω1 Ω2 Tr' K y x e2, (Ω ▷ e =[ Tr' ]~>* Ω1 ▷ (fill K (New y x (Lit s) e2)))
          /\ (Ω1 ▷ fill K (New y x (Lit s) e2) =[ Alloc loc s ]~> Ω2 ▷ fill K e2)
          /\ Δ_lookup x Ω2 = Some (EnvAddr loc)
          /\ Ω2 ▷ fill K e2 =[ sufftr (S n) Tr ]~>* Ω' ▷ e'.
Proof.
  intros H0 H1.
  revert Tr Ω Ω' e e' H0 H1; induction n; intros Tr Ω Ω' e e' H0 H1.
  - edestruct steps_alloc_yields_new as [Ω'' [K [y [x [e2 [H2a [H2b [H2c H2d]]]]]]]]; eauto;
    do 7 eexists; subst; repeat split; eauto.
  - inv H0; boring; cbn in *;
    specialize (IHn as0 Ω'0 Ω' e'0 e' H8 H1);
    destruct IHn as [Ω1 [Ω2 [Tr' [K [y [x [e2 [IHa [IHb [IHc IHd]]]]]]]]]];
    do 7 eexists; eauto.
Qed.

Lemma base_dealloc_yields_delete e e' Ω Ω' loc :
  Ω ▷ e -[ Dealloc loc ]~> Ω' ▷ e' ->
  exists x, e = Delete x /\ Δ_lookup x Ω = Some (EnvAddr loc) /\ e' = (Lit 0).
Proof.
  intros H; inv H; boring.
  exists x; cbn; repeat split; trivial.
Qed.
Lemma ctx_dealloc_yields_delete e e' Ω Ω' loc :
  Ω ▷ e =[ Dealloc loc ]~> Ω' ▷ e' ->
  exists K x, e = fill K (Delete x) /\ Δ_lookup x Ω = Some (EnvAddr loc) /\
         e' = fill K (Lit 0).
Proof.
  intros H; inv H; boring; apply base_dealloc_yields_delete in H7 as [x [H0a [H0b H0c]]];
  exists K; subst; eauto.
Qed.
Lemma steps_dealloc_yields_delete e e' Ω Ω' Tr loc :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ e' ->
  List.nth_error Tr 0 = Some (Dealloc loc) ->
  exists Ω'' K x, e = fill K (Delete x) /\ Δ_lookup x Ω = Some (EnvAddr loc)
   /\ (Ω ▷ e =[ Dealloc loc ]~> Ω'' ▷ fill K (Lit 0))
   /\ Ω'' ▷ fill K (Lit 0) =[ List.tail Tr ]~>* Ω' ▷ e'.
Proof.
  intros H0 H1. inv H0; boring.
  cbn in H1; inv H1.
  exists Ω'0.
  edestruct ctx_dealloc_yields_delete as [K [x [H0a [H0b H0c]]]]; cbn; subst; eauto.
  exists K; exists x; repeat split; subst; eauto.
Qed.
Lemma steps_dealloc_yields_delete_inbetween e e' Ω Ω' Tr loc n :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ e' ->
  List.nth_error Tr n = Some (Dealloc loc) ->
  exists Ω1 Ω2 Tr' K x, (Ω ▷ e =[ Tr' ]~>* Ω1 ▷ (fill K (Delete x)))
          /\ (Ω1 ▷ fill K (Delete x) =[ Dealloc loc ]~> Ω2 ▷ fill K (Lit 0))
          /\ Δ_lookup x Ω1 = Some (EnvAddr loc)
          /\ Ω2 ▷ fill K (Lit 0) =[ sufftr (S n) Tr ]~>* Ω' ▷ e'.
Proof.
  intros H0 H1.
  revert Tr Ω Ω' e e' H0 H1; induction n; intros Tr Ω Ω' e e' H0 H1.
  - edestruct steps_dealloc_yields_delete as [Ω'' [K [x [H2a [H2b [H2c H2d]]]]]]; eauto;
    do 6 eexists; subst; repeat split; eauto.
  - inv H0; boring; cbn in *.
    specialize (IHn as0 Ω'0 Ω' e'0 e' H8 H1).
    destruct IHn as [Ω1 [Ω2 [Tr' [K [x [IHa [IHb [IHc IHd]]]]]]]].
    do 6 eexists; eauto.
Qed.

Lemma trace_split (Tr : list Event) n ev :
  List.nth_error Tr n = Some ev ->
  exists Tr0 Tr1, Tr = Tr0 ++ ev :: Tr1 /\ List.length Tr0 = n.
Proof.
  intros H; apply nth_error_split in H as [Tr0 [Tr1 []]];
  do 2 eexists; eauto.
Qed.
Lemma refnat_in_type_means_dealloc_is_in_there x Γ e τ Ω loc:
  ((x, tyRefnat) :: Γ ||- e : τ) ->
  Δ_lookup x Ω = Some loc ->
  exists Ω' K Tr, (Ω ▷ e =[ Tr ]~>* Ω' ▷ (fill K (Delete x))).
Proof.
Admitted.

Lemma combine_steps Ω0 Ω1 e Tr Tr' Ω0' Ω1' e'' K K' v ev e''' :
  (Ω0 ▷ fill K e =[ Tr ]~>* Ω0' ▷ Lit v) ->
  (Ω0 ▷ e =[ Tr' ]~>* Ω1 ▷ fill K' e'') ->
  (Ω1 ▷ fill K' e'' =[ ev ]~> Ω1' ▷ fill K' e''') ->
  exists Tr'', Ω0 ▷ fill K e =[ Tr' ++ ev :: Tr'']~>* Ω0' ▷ Lit v.
Proof.
Admitted.

Lemma Δ_lookup_carries Ω Ω' x loc e Tr K :
  Δ_lookup x Ω = Some loc ->
  (Ω ▷ e =[ Tr ]~>* Ω' ▷ fill K (Delete x)) ->
  Δ_lookup x Ω' = Some loc.
Proof.
Admitted.

Lemma nth_error_simpl (Tr Tr' : Trace) n :
  List.nth_error (Tr ++ Tr') (List.length Tr + n) = List.nth_error Tr' n.
Proof. induction Tr; now cbn. Qed.

Lemma nth_error_cons_simpl (Tr : Trace) ev n :
  List.nth_error (ev :: Tr) (1 + n) = List.nth_error Tr n.
Proof. now cbn. Qed.

Lemma sufftr_skip Tr Tr' x :
  sufftr (List.length Tr + 1) (Tr ++ x :: Tr') = Tr'.
Proof. induction Tr; cbn in *; trivial. Qed.

Lemma deterministic_events Ω e Tr Ω' e' Tr' :
  Ω ▷ e -[ Tr ]~> Ω' ▷ e' ->
  Ω ▷ e -[ Tr' ]~> Ω' ▷ e' ->
  Tr = Tr'.
Proof.
  revert Ω Ω' e' Tr Tr'; induction e; intros; inv H0; inv H1; boring; trivial.
  - rewrite H7 in H6; inv H6; easy.
  - rewrite H7 in H6; inv H6; easy.
  - rewrite H5 in H4; inv H4; easy.
Qed.
Lemma deterministic_ctx_events Ω e Tr Ω' e' Tr' :
  Ω ▷ e =[ Tr ]~> Ω' ▷ e' ->
  Ω ▷ e =[ Tr' ]~> Ω' ▷ e' ->
  Tr = Tr'.
Proof.
  revert Ω Ω' e' Tr Tr'; induction e; intros.
  - inv H0; inv H1; boring; eapply deterministic_events; try exact H9; exact H10.
  - inv H0; inv H1; boring; eapply deterministic_events; try exact H9; exact H10.
Admitted.
Lemma deterministic_traces Ω e Tr Ω' e' Tr' :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ e' ->
  Ω ▷ e =[ Tr' ]~>* Ω' ▷ e' ->
  Tr = Tr'.
Proof.
Admitted.

Lemma nth_error_list_skip (Tr1 Tr2 : Trace) :
  List.nth_error (Tr1 ++ Tr2) (List.length Tr1) = List.nth_error Tr2 0.
Proof. induction Tr1; cbn; trivial. Qed.

Lemma while_alloc_before_dealloc Γ τ Ω Ω' Tr e v loc s :
  (Γ ||- e : τ) ->
  (Ω ▷ e =[ Tr ]~>* Ω' ▷ (Lit v)) ->
  after_another_event (Alloc loc s) (Dealloc loc) Tr.
Proof.
  intros H0 H1; unfold after_another_event.
  intros n H2; assert (H2' := H2); eapply trace_split in H2 as [Tr1 [Tr2 [H2a H2b]]]; subst.
  assert (H1' := H1);
  eapply steps_alloc_yields_new_inbetween in H1 as [Ω'' [Ω''' [Tr [K [y [x [e2 [H1a [H1b [H1c H1d]]]]]]]]]];
  try eapply H2'.
  eapply preservation_star in H1a as [Γ0 [H2a H2b]]; try exact H0.
  eapply preservation_decomposition in H2a as [ty' [Γ1 [H3a [H3b H3c]]]].
  (* inversion lemma of Tnew *)
  eapply refnat_in_type_means_dealloc_is_in_there in H8 as H8'; try exact H1c.
  destruct H8' as [Ω2' [K2 [Tr2' H9']]].
  remember (Ω2'.(fresh);Ω2'.(H);Ω2'.(A);(delete x Ω2'.(Δ))) as Ω2''.
  assert (Ω2' ▷ fill K2 (Delete x) =[ Dealloc loc ]~> Ω2'' ▷ fill K2 (Lit 0)) by
  (econstructor; eauto; subst; econstructor; eapply Δ_lookup_carries; eauto).
  assert (H1d' := H1d).
  eapply combine_steps in H1d; subst; eauto.
  destruct H1d as [Tr3 H1d].
  rewrite <- Nat.add_1_r, sufftr_skip in H1d'.
  eapply deterministic_traces in H1d'; try exact H1d.
  subst.
  exists (List.length Tr1 + 1 + List.length Tr2'); cbn; split; try lia.
  repeat rewrite <- Nat.add_assoc;
  rewrite nth_error_simpl, nth_error_cons_simpl, nth_error_list_skip.
  easy.
Qed.

Definition out_of_bounds_program :=
  New "y"%string "x0"%string (Lit 42)
    (Letin "_"%string (Access "x0"%string (Lit 1337))
      (Delete "y"%string)).
Lemma oob_prog_typechecks :
  (("x"%string, tyNat)::nil ||- out_of_bounds_program : tyNat).
Proof.
  econstructor; try now left.
  replace nil with ((nil ++ nil) : Gamma) by easy.
  eapply Tletnew; eauto.
  replace (("x0"%string, tyRefnat) :: ("y"%string, tyCap "x0") :: nil)
          with ((("x0"%string,tyRefnat)::nil) ++ (("y"%string, tyCap "x0") :: nil)) by easy.
  eapply Tlet; eauto.
  intros x y H0; cbn in H0; destruct H0 as [H0|H0]; easy.
Qed.

Lemma while_is_not_spat_memsafe :
  ~ (forall (p : WhileComponent) (H : component_check p), wrsat H spat_memsafe).
Proof.
  intros H.
  remember out_of_bounds_program as p.
  assert (H0 := oob_prog_typechecks); rewrite <- Heqp in H0.
  assert (component_check (WComp p (closed_typing H0))) by econstructor.
  specialize (H (WComp p (closed_typing H0)) H1).

  unfold wrsat in H.
  assert (nil ||- Lit 0 : tyNat =| nil) by repeat econstructor.
  assert ((("y"%string, tyNat) :: nil) ||- Lit 0 : tyNat =| (("y"%string, tyNat)::nil)) by repeat econstructor.
  assert (context_check (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3))) by repeat econstructor.
  specialize (H (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3)) H4).

  unfold wsat in H; unfold spat_memsafe in H.
  remember (plug (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3))
                  (WComp p (closed_typing H0))) as fp.
  assert (occ (Alloc (LocA 0) 42) (prog2trace fp)).
  rewrite Heqfp; unfold compute_trace_prefix; cbn;
  rewrite Heqp; cbn; right; now left.

  assert (occ (Read (LocA 0) 1337) (prog2trace fp)).
  cbn; rewrite Heqfp; cbn; rewrite Heqp; unfold compute_trace_prefix; cbn;
  destruct (addr_eq_dec (LocA 0) (LocA 0)); try contradiction; cbn.
  do 2 right; now left.
  specialize (H (LocA 0) 42 H5) as [Ha Hb].
  specialize (Ha 1337 H6).
  lia.
Qed.


Lemma while_is_temp_memsafe (p : WhileComponent) (H : component_check p) :
  wrsat H temp_memsafe.
Proof.
  destruct p; destruct H as [e' HΓ].
Admitted.
