Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat Strings.String Lists.List Lia Program.Equality.
Require Import CSC.Util.

Inductive bin_op :=
  | Plus
.
Inductive val :=
  | LitV : nat -> val
.
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
  | BinOp : bin_op -> expr -> expr -> expr  (* e0 + e1 *)
  | Access : string -> expr -> expr        (* x[e] *)
  | Letin : string -> expr -> expr -> expr  (* let x = e0 in e1 *)
  | If : expr -> expr -> expr -> expr       (* if e0 then e1 else e2 *)
  | Assign : string -> expr -> expr -> expr (* x[e0] <- e1 *)
  | New : string -> expr -> expr -> expr    (* let x = new e0 in e1 *)
  | Delete : string -> expr               (* delete x *)
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
Definition is_val (e : expr) : Type :=
  match e with
  | Lit _ => True
  | _ => False
  end
.
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  now induction v.
Qed.
Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  revert v; induction e; cbn; intros v ?; inv H; easy.
Qed.
Lemma is_val_inv e : is_val e -> { n : nat | e = Lit n }.
Proof.
  induction e; cbn; intros; try contradiction.
  now exists n.
Qed.


(* Not sure if necessary, let's see... *)
Fixpoint esubst (x : string) (fore : expr) (ine : expr) : expr :=
  match ine with
  | Lit _ => ine
  | Var y => if string_dec x y then fore else Var x
  | BinOp o e1 e2 => BinOp o (esubst x fore e1) (esubst x fore e2)
  | Access y e => Access y (esubst x fore e)
  | Letin y e1 e2 => Letin y (esubst x fore e1) (if string_dec x y then e2 else esubst x fore e2)
  | If e1 e2 e3 => If (esubst x fore e1) (esubst x fore e2) (esubst x fore e3)
  | Assign x e1 e2 => Assign x (esubst x fore e1) (esubst x fore e2)
  | New x eat e => New x (esubst x fore eat) (esubst x fore e)
  | Delete x => Delete x
  end
.
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
Definition of_env_elem (e : env_elem) : option expr :=
  match e with
  | EnvVal(LitV v) => Some(Lit v)
  | _ => None
  end
.
Definition of_opt_env_elem (e : option env_elem) : option expr :=
  match e with
  | Some x => of_env_elem x
  | _ => None
  end
.
Coercion EnvAddr : addr >-> env_elem.
Coercion EnvVal : val >-> env_elem.
Definition Env : Set := list (string * env_elem).
Definition State : Set := (Heap * LocMap * Env).
Definition Conf : Set := (State * expr).

Notation "H ';' A ';' Δ" := ((H, A, Δ) : State) (at level 80, A at next level, Δ at next level).
Notation "Ω '▷' e" := ((Ω, e) : Conf) (at level 80, e at next level).

Definition lookup {A : Type} (x : string) (Δ : list (string * A)) := Util.find (String.eqb x) Δ.
Definition fetch {A : Type} (x : addr) (A : list (addr * A)) := Util.find (addr_eqb x) A.

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
Inductive base_tstep : Conf -> Event -> Conf -> Prop :=
| VarS : forall H A (Δ : Env) (x : string) v, lookup x Δ = Some(EnvVal(LitV v)) ->
                                         (H;A;Δ ▷ Var x -[ Internal ]~> H;A;Δ ▷ Lit v)
where "Ω '-[' a ']~>' Ω2" := (base_tstep Ω a Ω2)
.

Definition pack (Ω : State) (eo : option expr) (a : Event) : option (State * expr * Event) :=
  match eo with
  | None => None
  | Some x => Some(Ω, x, a)
  end
.

Definition one_tstep (Ω : State) (e : expr) : option (State * expr * Event)  :=
  let '(H, A, Δ) := Ω in
  match e with
  | Var x => pack Ω (of_opt_env_elem(lookup x Δ)) Internal
  | _ => None
  end
.

Lemma base_tstep_and_one_tstep Ω Ω' e a e' :
  one_tstep Ω e = Some (Ω', e', a) -> base_tstep (Ω ▷ e) a (Ω' ▷ e').
Proof.
  revert Ω Ω' a e'; induction e; intros [[Ha Aa] Δa] [[Hb Ab] Δb] a e' H; cbn in *.
  - inv H.
  -
    Search (List.find).
    edestruct ((lookup s Δa) = Some ?_). . ) as [env0 | H0]; cbn in *; try congruence.
    destruct env0 as [v | ?]; cbn in *; try congruence.
    destruct v; inv H.
    constructor. econstructor.
Qed.



Reserved Notation "H ';' A ';' Δ '▷' e '--' a '-->' Ha ';' Aa ';' Δa '▷' ea" (at level 80, A at next level, Δ at next level,
                                                                            e at next level, a at next level, Ha at next level,
                                                                            Aa at next level, Δa at next level).
Inductive base_step : Heap -> LocMap -> Env -> expr -> Event -> Heap -> LocMap -> Env -> expr -> Prop :=
| VarS : forall H A Δ x v, lookup x Δ = Some (EnvVal v) -> (H;A;Δ ▷ Var x -- Internal --> H;A;Δ ▷ v)
| AddS : forall H A Δ n1 n2 o, (H;A;Δ ▷ BinOp o (Lit n1) (Lit n2) -- Internal --> H;A;Δ ▷ Lit (n1 + n2))
| GetS : forall H A Δ x n loc v nl, lookup x Δ = Some (EnvAddr loc) ->
                            fetch loc A = Some nl ->
                            List.nth_error H (nl + n) = Some v ->
                            (H;A;Δ ▷ Access x (Lit n) -- Read loc n --> H;A;Δ ▷ Lit v)
| SetS : forall H H' A Δ x n v loc nl, lookup x Δ = Some (EnvAddr loc) ->
                                  fetch loc A = Some nl ->
                                  H' = replace (nl + n) H v ->
                                  (H;A;Δ ▷ Assign x (Lit n) (Lit v) -- Write loc n --> H';A;Δ ▷ Lit v)
| IfBotS : forall H A Δ e1 e2, (H;A;Δ ▷ If (Lit 0) e1 e2 -- Internal --> H;A;Δ ▷ e2)
| IfTopS : forall H A Δ v e1 e2, v <> 0 -> (H;A;Δ ▷ If (Lit v) e1 e2 -- Internal --> H;A;Δ ▷ e1)
| LetS : forall H A Δ x v e, (H;A;Δ ▷ Letin x (Lit v) e -- Internal --> H;A;((x,EnvVal (LitV v)) :: Δ) ▷ e)
| DeleteS : forall H A Δ x loc, lookup x Δ = Some (EnvAddr loc) ->
                           (H;A;Δ ▷ Delete x -- Dealloc loc --> H;A;(delete x Δ) ▷ Lit 0)
| NewS : forall H H' A Δ x n e loc s, s = List.length H ->
                                 H' = grow H n ->
                                 loc = LocA (List.length A) ->  (* <- using the length of A allows us to not need an axiom *)
                                 (H;A;Δ ▷ New x (Lit n) e -- Alloc loc n --> H';((loc, s) :: A);((x, EnvAddr loc) :: Δ) ▷ e)
where "H ';' A ';' Δ '▷' e '--' a '-->' Ha ';' Aa ';' Δa '▷' ea" := (base_step H A Δ e a Ha Aa Δa ea)
.
#[global]
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
  | NewCtx : string -> ectx -> expr -> ectx
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
  | NewCtx x K' e' => New x (fill K' e) e'
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
  | NewCtx x K' e => NewCtx x (comp_ectx K' K2) e
  | IfCtx K' e1 e2 => IfCtx (comp_ectx K' K2) e1 e2
  end
.
Inductive contextual_step (H : Heap) (A : LocMap) (Δ : Env) (e1 : expr)
                          (a : Event)
                          (H' : Heap) (A' : LocMap) (Δ' : Env) (e2 : expr) : Prop :=
| Ectx_step : forall K e1' e2',
    e1 = fill K e1' -> e2 = fill K e2' ->
    (H;A;Δ ▷ e1' -- a --> H';A';Δ' ▷ e2') ->
    contextual_step H A Δ e1 a H' A' Δ' e2
.
Inductive steps (H: Heap) (A : LocMap) (Δ : Env) (e : expr) : list Event -> Heap -> LocMap -> Env -> expr -> Prop :=
| stepsRefl : steps H A Δ e nil H A Δ e
| stepsTrans : forall H' A' Δ' e' a As H'' A'' Δ'' e'', contextual_step H A Δ e a H' A' Δ' e' ->
                                                   steps H' A' Δ' e' As H'' A'' Δ'' e'' ->
                                                   steps H A Δ e (a :: As) H'' A'' Δ'' e''
.
#[global]
Hint Constructors steps contextual_step.
Lemma fill_empty e : fill HoleCtx e = e.
Proof. now cbn. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; cbn; congruence. Qed.

Lemma base_contextual_step H A Δ e1 a e2 H' A' Δ' :
  base_step H A Δ e1 a e2 H' A' Δ' -> contextual_step H A Δ e1 a e2 H' A' Δ'.
Proof. apply Ectx_step with HoleCtx; try rewrite fill_empty; trivial. Qed.

Lemma fill_contextual_step H A Δ e1 a e2 H' A' Δ' K :
  contextual_step H A Δ e1 a H' A' Δ' e2 -> contextual_step H A Δ (fill K e1) a H' A' Δ' (fill K e2).
Proof. destruct 1; subst. rewrite !fill_comp. econstructor; try reflexivity; assumption. Qed.

Lemma fill_steps H A Δ e1 As e2 H' A' Δ' K :
  steps H A Δ e1 As H' A' Δ' e2 -> steps H A Δ (fill K e1) As H' A' Δ' (fill K e2).
Proof.
  induction 1; subst; try eapply stepsRefl.
  eapply stepsTrans. eapply fill_contextual_step. exact H0. exact IHsteps.
Qed.

Ltac get_values := repeat match goal with
                   | [H: is_val ?e |- _] => apply is_val_inv in H as []
                   end.
Ltac context_intro := (
                       (match goal with
                        | [ H: _ |- steps _ _ _ _ _ _ _ _ _ -> _ ] => induction 1; try apply stepsRefl
                        end) || (
                       intros;
                       repeat match goal with
                       | [ H : contextual_step _ _ _ _ _ _ _ _ _ |- _ ] => destruct H
                       end; get_values)
                      ).
Ltac context_solver C := (
                        match goal with
                        | [ H0 : contextual_step ?H ?A ?Δ ?e ?a ?H' ?A' ?Δ' ?e',
                            H1 : steps _ _ _ ?e' ?As ?H'' ?A'' ?Δ'' _ |- steps ?H ?A ?Δ _ (?a :: ?As) ?H'' ?A'' ?Δ'' _ ] =>
                             eapply stepsTrans; eapply fill_contextual_step with (K:=C) in H0; eauto
                        | [ H0 : steps _ _ _ ?e' _ ?H'' ?A'' ?Δ'' _ |- steps ?H ?A ?Δ _ _ ?H'' ?A'' ?Δ'' _ ] =>
                             eapply fill_steps with (K:=C) in H0; subst; cbn in *; assumption
                        | [ H : _ |- contextual_step _ _ _ _ _ _ _ _ _ ] =>
                            (subst; eapply Ectx_step with (K:=C); try now cbn; eauto)
                        end
                        ).


Lemma contextual_step_bin_l H A Δ e1 o a e1' e2 H' A' Δ' :
  contextual_step H A Δ e1 a H' A' Δ' e1' ->
  contextual_step H A Δ (BinOp o e1 e2) a H' A' Δ' (BinOp o e1' e2).
Proof. context_intro; context_solver (LBinOpCtx o K e2). Qed.

Lemma contextual_step_bin_r H A Δ e1 o a e2 e2' H' A' Δ' :
  is_val e1 ->
  contextual_step H A Δ e2 a H' A' Δ' e2' ->
  contextual_step H A Δ (BinOp o e1 e2) a H' A' Δ' (BinOp o e1 e2').
Proof. context_intro; context_solver (RBinOpCtx o (LitV x) K). Qed.

Lemma contextual_step_bin_v H A Δ e1 o e2 :
  is_val e1 ->
  is_val e2 ->
  { v : expr | contextual_step H A Δ (BinOp o e1 e2) Internal H A Δ v }.
Proof. context_intro; exists (Lit (x0 + x)); context_solver (HoleCtx). Qed.

Lemma contextual_step_access H A Δ e e' a x H' A' Δ' :
  contextual_step H A Δ e a H' A' Δ' e' ->
  contextual_step H A Δ (Access x e) a H' A' Δ' (Access x e').
Proof. context_intro; context_solver (AccessCtx x K). Qed.

Lemma contextual_step_letin H A Δ e e' e0 a x H' A' Δ' :
  contextual_step H A Δ e a H' A' Δ' e' ->
  contextual_step H A Δ (Letin x e e0) a H' A' Δ' (Letin x e' e0).
Proof. context_intro; context_solver (LetinCtx x K e0). Qed.

Lemma contextual_step_assign H A Δ e e' e0 x a H' A' Δ' :
  contextual_step H A Δ e a H' A' Δ' e' ->
  contextual_step H A Δ (Assign x e e0) a H' A' Δ' (Assign x e' e0).
Proof. context_intro; context_solver (AssignCtx x K e0). Qed.

Lemma contextual_step_assignv H A Δ e e' v x a H' A' Δ' :
  is_val v ->
  contextual_step H A Δ e a H' A' Δ' e' ->
  contextual_step H A Δ (Assign x v e) a H' A' Δ' (Assign x v e').
Proof. context_intro; context_solver (AssignVCtx x (LitV x0) K). Qed.

Lemma contextual_step_newctx H A Δ x e0 e e' a H' A' Δ' :
  contextual_step H A Δ e a H' A' Δ' e' ->
  contextual_step H A Δ (New x e e0) a H' A' Δ' (New x e' e0).
Proof. context_intro; context_solver (NewCtx x K e0). Qed.

Lemma contextual_step_ifctx H A Δ e e' e1 e2 a H' A' Δ' :
  contextual_step H A Δ e a H' A' Δ' e' ->
  contextual_step H A Δ (If e e1 e2) a H' A' Δ' (If e' e1 e2).
Proof. context_intro; context_solver (IfCtx K e1 e2). Qed.

Lemma ctx_steps_bin_l H A Δ e1 o a e1' e2 H' A' Δ' :
  steps H A Δ e1 a H' A' Δ' e1' ->
  steps H A Δ (BinOp o e1 e2) a H' A' Δ' (BinOp o e1' e2).
Proof. context_intro; context_solver (LBinOpCtx o HoleCtx e2). Qed.

Lemma ctx_steps_bin_r H A Δ e1 o As e2 e2' H' A' Δ' :
  is_val e1 ->
  steps H A Δ e2 As H' A' Δ' e2' ->
  steps H A Δ (BinOp o e1 e2) (As) H' A' Δ' (BinOp o e1 e2').
Proof. context_intro; context_solver (RBinOpCtx o (LitV x) HoleCtx). Qed.

Lemma ctx_steps_access H A Δ e e' a x H' A' Δ' :
  steps H A Δ e a H' A' Δ' e' ->
  steps H A Δ (Access x e) a H' A' Δ' (Access x e').
Proof. context_intro; context_solver (AccessCtx x HoleCtx). Qed.

Lemma ctx_steps_letin H A Δ e e' e0 a x H' A' Δ' :
  steps H A Δ e a H' A' Δ' e' ->
  steps H A Δ (Letin x e e0) a H' A' Δ' (Letin x e' e0).
Proof. context_intro; context_solver (LetinCtx x HoleCtx e0). Qed.

Lemma ctx_steps_assign H A Δ e e' e0 x a H' A' Δ' :
  steps H A Δ e a H' A' Δ' e' ->
  steps H A Δ (Assign x e e0) a H' A' Δ' (Assign x e' e0).
Proof. context_intro; context_solver (AssignCtx x HoleCtx e0). Qed.

Lemma ctx_steps_assignv H A Δ e e' v x a H' A' Δ' :
  is_val v ->
  steps H A Δ e a H' A' Δ' e' ->
  steps H A Δ (Assign x v e) a H' A' Δ' (Assign x v e').
Proof. context_intro; context_solver (AssignVCtx x (LitV x0) HoleCtx). Qed.

Lemma ctx_steps_newctx H A Δ x e0 e e' a H' A' Δ' :
  steps H A Δ e a H' A' Δ' e' ->
  steps H A Δ (New x e e0) a H' A' Δ' (New x e' e0).
Proof. context_intro; context_solver (NewCtx x HoleCtx e0). Qed.

Lemma ctx_steps_ifctx H A Δ e e' e1 e2 a H' A' Δ' :
  steps H A Δ e a H' A' Δ' e' ->
  steps H A Δ (If e e1 e2) a H' A' Δ' (If e' e1 e2).
Proof. context_intro; context_solver (IfCtx HoleCtx e1 e2). Qed.

Lemma contextual_step_steps H A Δ e1 a e2 H' A' Δ' :
  contextual_step H A Δ e1 a e2 H' A' Δ' -> steps H A Δ e1 (a :: nil) e2 H' A' Δ'.
Proof. intros; eapply stepsTrans; (exact H0 || eapply stepsRefl). Qed.

#[global]
Hint Resolve
  base_contextual_step
  contextual_step_bin_l contextual_step_bin_r contextual_step_bin_v contextual_step_access contextual_step_letin
  contextual_step_assign contextual_step_assignv contextual_step_newctx contextual_step_ifctx
  contextual_step_steps
  ctx_steps_bin_l ctx_steps_bin_r ctx_steps_access ctx_steps_letin
  ctx_steps_assign ctx_steps_assignv ctx_steps_newctx ctx_steps_ifctx
  : core
.

Lemma steps_bin_l H A Δ e1 o a e1' e2 H' A' Δ' :
  steps H A Δ e1 a H' A' Δ' e1' ->
  steps H A Δ (BinOp o e1 e2) a H' A' Δ' (BinOp o e1' e2).
Proof. context_intro; context_solver (LBinOpCtx o HoleCtx e2). Qed.

Definition reducible (H : Heap) (A : LocMap) (Δ : Env) (e : expr) :=
  exists a H' A' Δ', exists e', contextual_step H A Δ e a H' A' Δ' e'
.

Fixpoint bool_In (X : list string) (x : string) : bool :=
  match X with
  | nil => false
  | y :: Y => if string_dec x y then true else bool_In Y x
  end
.
Notation "X '⊆' Y" := (forall x, In x X -> In x Y) (at level 81, left associativity).
Lemma cons_subset {A} (X Y : list A) (x : A) : X ⊆ Y -> ((x :: X) ⊆ (x :: Y)).
Proof. intros. destruct H0; try ((now left) + (right; now apply H)). Qed.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ => true
  | Var x => bool_In X x
  | BinOp _ e0 e1 => andb (is_closed X e0) (is_closed X e1)
  | Access x e0 => if bool_In X x then is_closed X e0 else false
  | Letin x e0 e1 => andb (is_closed X e0) (is_closed (x :: X) e1)
  | If e0 e1 e2 => andb (andb (is_closed X e0) (is_closed X e1)) (is_closed X e2)
  | Assign x e0 e1 => if bool_In X x then andb (is_closed X e0) (is_closed X e1) else false
  | New x e0 e1 => andb (is_closed X e0) (is_closed (x :: X) e1)
  | Delete x => bool_In X x
  end
.
Definition closed (X : list string) (e : expr) : Prop := if is_closed X e then True else False.
Lemma bool_In_equiv_In X x : (if bool_In X x then True else False) <-> In x X.
Proof.
  induction X; split; cbn; intros; try congruence || contradiction.
  - destruct (string_dec x a); subst.
    + now left.
    + right; now apply IHX.
  - destruct H; destruct (string_dec x a); subst; trivial.
    congruence. now apply IHX.
Qed.
Lemma bool_eq_equiv_if (x : bool) : (if x then True else False) <-> x = true.
Proof. now destruct x. Qed.
Lemma bool_and_equiv_prop (x y : bool) : (x && y)%bool = true <-> (x = true) /\ (y = true).
Proof. now destruct x,y. Qed.

Lemma subset_equiv_bool_in_subset X Y : X ⊆ Y <-> (forall x, bool_In X x = true -> bool_In Y x = true).
Proof.
  split; intros.
  - apply bool_eq_equiv_if in H0; apply bool_In_equiv_In in H0;
    apply bool_eq_equiv_if; apply bool_In_equiv_In; now apply H.
  - apply bool_In_equiv_In in H0; apply bool_eq_equiv_if in H0.
    apply bool_In_equiv_In; apply bool_eq_equiv_if; now apply H.
Qed.
Lemma closed_equiv_is_closed X e : is_closed X e = true <-> closed X e.
Proof. unfold closed; now rewrite bool_eq_equiv_if. Qed.

Lemma nested_bool_pred (x y : bool) : ((if x then y else false) = true) <-> (andb x y = true).
Proof. now destruct x,y. Qed.

Lemma closed_weaken X Y e : closed X e -> X ⊆ Y -> closed Y e.
Proof.
  revert X Y; induction e; unfold closed; cbn; intros; eauto;
  try (rewrite bool_In_equiv_In; rewrite bool_In_equiv_In in H; now apply H0).
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H;
    apply bool_and_equiv_prop; apply bool_and_equiv_prop in H;
    destruct H; apply closed_equiv_is_closed in H, H1;
    split; apply closed_equiv_is_closed; (eapply IHe1 + eapply IHe2); eauto.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H.
    rewrite nested_bool_pred in H; rewrite nested_bool_pred.
    rewrite bool_and_equiv_prop in H; rewrite bool_and_equiv_prop.
    destruct H; split.
    + rewrite <- bool_eq_equiv_if; rewrite bool_In_equiv_In;
      apply H0;
      apply bool_In_equiv_In; now rewrite bool_eq_equiv_if.
    + rewrite closed_equiv_is_closed; eapply IHe; eauto; now rewrite <- closed_equiv_is_closed.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H.
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H.
    destruct H; split.
    + rewrite closed_equiv_is_closed; eapply IHe1; eauto;
      now rewrite <- closed_equiv_is_closed.
    + rewrite closed_equiv_is_closed; eapply IHe2. instantiate (1:=s :: X).
      now rewrite <- closed_equiv_is_closed. now apply cons_subset.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H.
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H.
    destruct H; split.
    + rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H.
      destruct H; split.
      * rewrite closed_equiv_is_closed; eapply IHe1; eauto; now rewrite <- closed_equiv_is_closed.
      * rewrite closed_equiv_is_closed; eapply IHe2; eauto; now rewrite <- closed_equiv_is_closed.
    + rewrite closed_equiv_is_closed; eapply IHe3; eauto; now rewrite <- closed_equiv_is_closed.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H;
    rewrite nested_bool_pred; rewrite nested_bool_pred in H.
    rewrite !bool_and_equiv_prop; rewrite !bool_and_equiv_prop in H.
    destruct H as [H []]; repeat split.
    + rewrite <- bool_eq_equiv_if; rewrite bool_In_equiv_In;
      apply H0;
      apply bool_In_equiv_In; now rewrite bool_eq_equiv_if.
    + rewrite closed_equiv_is_closed; eapply IHe1; eauto; now rewrite <- closed_equiv_is_closed.
    + rewrite closed_equiv_is_closed; eapply IHe2; eauto; now rewrite <- closed_equiv_is_closed.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H.
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H.
    destruct H; split.
    + rewrite closed_equiv_is_closed; eapply IHe1; eauto;
      now rewrite <- closed_equiv_is_closed.
    + rewrite closed_equiv_is_closed; eapply IHe2. instantiate (1:=s :: X).
      now rewrite <- closed_equiv_is_closed. now apply cons_subset.
Qed.
Lemma closed_weaken_nil X e : closed nil e -> closed X e.
Proof. intros; eapply closed_weaken; try exact H; intros ? ?; inv H0. Qed.

Inductive ty :=
| tyNat : ty
| tyRefnat : ty
.
Definition Gamma := list (string * ty).
Reserved Notation "Γa '||-' e ':' τ '=|' Γb" (at level 99, right associativity, e at next level, τ at level 200).
Inductive check : Gamma -> expr -> ty -> Gamma -> Type :=
| Tvar : forall Γ x τ, lookup x Γ = Some τ -> (Γ ||- (Var x) : τ =| Γ)
| Tnat : forall Γ n, (Γ ||- Lit n : tyNat =| Γ)
| Tbinop : forall Γ e1 e2 o, (Γ ||- e1 : tyNat =| Γ) ->
                        (Γ ||- e2 : tyNat =| Γ) ->
                        (Γ ||- BinOp o e1 e2 : tyNat =| Γ)
| Tget : forall Γ x e, (Γ ||- Var x : tyRefnat =| Γ) ->
                  (Γ ||- e : tyNat =| Γ) ->
                  (Γ ||- Access x e : tyNat =| Γ)
| Tset : forall Γ x e1 e2, (Γ ||- Var x : tyRefnat =| Γ) ->
                      (Γ ||- e1 : tyNat =| Γ) ->
                      (Γ ||- e2 : tyNat =| Γ) ->
                      (Γ ||- Assign x e1 e2 : tyNat =| Γ)
| Tlet : forall Γ Γ'' Γ''' x e1 e2, (Γ ||- e1 : tyNat =| Γ) ->
                               ((x,tyNat) :: Γ ||- e2 : tyNat =| Γ'') ->
                               lookup x Γ'' = Some tyNat ->
                               Γ''' = delete x Γ'' ->
                               (Γ ||- Letin x e1 e2 : tyNat =| Γ''')
| Tletnew : forall Γ Γ'' x e1 e2, (Γ ||- e1 : tyNat =| Γ) ->
                             ((x,tyRefnat) :: Γ ||- e2 : tyNat =| Γ'') ->
                             lookup x Γ'' = None ->
                             (Γ ||- New x e1 e2 : tyNat =| Γ'')
| Tdelete : forall Γ Γ' x, lookup x Γ = Some tyRefnat ->
                   Γ' = delete x Γ ->
                   (Γ ||- Delete x : tyNat =| Γ')
| Tif : forall Γ e1 e2 e3, (Γ ||- e1 : tyNat =| Γ) ->
                      (Γ ||- e2 : tyNat =| Γ) ->
                      (Γ ||- e3 : tyNat =| Γ) ->
                      (Γ ||- If e1 e2 e3 : tyNat =| Γ)
where "Γa '||-' e ':' τ '=|' Γb" := (check Γa e τ Γb)
.
#[global]
Hint Constructors check : core.

(*
Fixpoint exec (*n*) (H : Heap) (A : LocMap) (Δ : Env) (e : expr) : (Heap * LocMap * Env * option val * list Event) :=
  (*
  match n with
  | 0 => (nil, nil, nil, None, nil)
  | S n' =>*) match e with
           | Var x => (H, A, Δ, match lookup x Δ with
                               | Some(EnvVal(LitV v)) => Some (LitV v)
                               | _ => None
                               end, Internal :: nil)
           | Lit n => (H, A, Δ, Some (LitV n), nil)
           | BinOp _ e1 e2 => let '(H', A', Δ', sv1, evs1) := exec (*n'*) H A Δ e1 in
                             let '(H'', A'', Δ'', sv2, evs2) := exec (*n'*) H' A' Δ' e2 in
                             (H'', A'', Δ'', match sv1, sv2 with
                                             | Some(LitV v1), Some(LitV v2) => Some (LitV (v1 + v2))
                                             | _, _ => None
                                             end, evs1 ++ evs2)
           | Access x e => let '(H', A', Δ', sv, evs) := exec (*n'*) H A Δ e in
                          match lookup x Δ, sv with
                          | Some(EnvAddr(loc)), Some(LitV v) =>
                              match fetch loc A' with
                              | Some nl => (H', A', Δ', match (List.nth_error H' (nl + v)) with
                                                       | Some x => Some (LitV x)
                                                       | None => Some (LitV 0)
                                                       end,
                                                      evs ++ ((Read loc v)::nil))
                              | _ => (H', A', Δ', None, nil)
                              end
                          | _, _ => (H', A', Δ', None, nil)
                          end
           | Assign x e1 e2 => let '(H', A', Δ', sv1, evs1) := exec (*n'*) H A Δ e1 in
                              let '(H'', A'', Δ'', sv2, evs2) := exec (*n'*) H' A' Δ' e2 in
                              match lookup x Δ, sv1, sv2 with
                              | Some(EnvAddr(loc)), Some(LitV n), Some(LitV v) =>
                                  match fetch loc A'' with
                                  | Some nl => (replace (nl + n) H'' v, A'', Δ'', Some (LitV v), evs1 ++ evs2 ++ ((Write loc n)::nil))
                                  | _ => (H'', A'', Δ'', None, nil)
                                  end
                              | _,_,_ => (H'', A'', Δ'', None, nil)
                              end
           | If e1 e2 e3 => let '(H0, A0, Δ0, sv0, evs0) := exec (*n'*) H A Δ e1 in
                           match sv0 with
                           | Some(LitV 0) => let '(H1, A1, Δ1, sv1, evs1) := exec (*n'*) H0 A0 Δ0 e2 in
                                            (H1, A1, Δ1, sv1, evs0 ++ evs1)
                           | Some(LitV _) => let '(H1, A1, Δ1, sv1, evs1) := exec (*n'*) H0 A0 Δ0 e3 in
                                            (H1, A1, Δ1, sv1, evs0 ++ evs1)

                           | _ => (nil, nil, nil, None, nil)
                           end
           | Letin x e1 e2 => let '(H0, A0, Δ0, sv0, evs0) := exec (*n'*) H A Δ e1 in
                             match sv0 with
                             | Some v0 => let '(H1, A1, Δ1, sv1, evs1) := exec (*n'*) H A ((x,EnvVal v0) :: Δ0) e2 in
                                         (H1, A1, Δ1, sv1, evs0 ++ evs1)
                             | None => (nil, nil, nil, None, nil)
                             end
           | Delete x => match lookup x Δ with
                        | Some (EnvAddr loc) => (H, A, delete x Δ, Some(LitV 0), (Dealloc loc)::nil)
                        | _ => (nil, nil, nil, None, nil)
                        end
           | New x e1 e2 => let '(H0, A0, Δ0, sv0, evs0) := exec (*n'*) H A Δ e1 in
                           match sv0 with
                           | Some(LitV m) => let loc := LocA(List.length A) in
                                            let s := List.length H in
                                            let '(H1, A1, Δ1, sv1, evs1) :=
                                              exec (*n'*) (grow H m) ((loc,s)::A) ((x,EnvAddr loc) :: Δ0) e2 in
                                            (H1, A1, Δ1, sv1, evs0 ++ ((Alloc loc m)::nil) ++ evs1)
                           | None => (nil, nil, nil, None, nil)
                           end
           end
  (*end*)
.
Definition compute_trace_prefix (e : expr) : list Event := let '(H, A, Δ, v, es) := exec nil nil nil e in es.
Lemma split_prod {A : Type} (a b c d e a' b' c' d' e' : Type) :
  (a,b,c,d,e) = (a',b',c',d',e') -> a = a' /\ b = b' /\ c = c' /\ d = d' /\ e = e'.
Proof. intros H; inv H; now repeat split. Qed.

Lemma exec_equiv_steps H A Δ e v Es H' A' Δ' :
  exec H A Δ e = (H', A', Δ', Some(LitV v), Es) ->
  steps H A Δ e Es H' A' Δ' (Lit v)
.
Proof.
  revert H A Δ v Es H' A' Δ'; induction e; intros; cbn in H0; inv H0; eauto.
  - eapply stepsTrans. context_solver HoleCtx; econstructor; destruct (lookup s Δ'); try congruence;
    destruct e; try congruence. destruct v0; inv H5; reflexivity.
    eapply stepsRefl.
  - remember (exec H A Δ e1) as X; destruct X as [[[[He1 A1] Δ1] v1] Es1].
    remember (exec He1 A1 Δ1 e2) as X; destruct X as [[[[He2 A2] Δ2] v2] Es2].
    destruct v1; try congruence; destruct v0 as [n0].
    destruct v2; try congruence; destruct v0 as [n1].
    symmetry in HeqX, HeqX0.
    specialize (IHe1 H A Δ n0 Es1 He1 A1 Δ1 HeqX); specialize (IHe2 He1 A1 Δ1 n1 Es2 He2 A2 Δ2 HeqX0).
    inv H2.
    induction Es1; cbn.
    eapply ctx_steps_bin_l in IHe1; eapply ctx_steps_bin_r in IHe2.

    inv H2. eapply stepsTrans. context_solver HoleCtx.
    inv H2. inv IHe1; inv IHe2.
      * econstructor. context_solver HoleCtx. econstructor.
      * econstructor. eapply fill_contextual_step with (K:=RBinOpCtx b (LitV n0) HoleCtx) in H. cbn in H.
        eauto. eapply fill_destruct a. exact H. inv H. inv H0. inv H4.
        context_solver (RBinOpCtx b (LitV n0) HoleCtx). eapp0
      instantiate (1:=Lit (n0 + n1)). econstructor.
      admit. admit.
  admit.
  - induction e; intros; cbn.
    +
Qed.
*)

Ltac reducible_in_ctx := repeat match goal with
                         | [ H: reducible ?a ?b ?c ?e |- _] => do 5 destruct H
                         end.

Definition treducible (H : Heap) (A : LocMap) (Δ : Env) (e : expr) : Set :=
  { a : Event & { H' : Heap & { A' : LocMap & { Δ' : Env & { e' : expr | contextual_step H A Δ e a H' A' Δ' e' }}}}}
.

Lemma progress e τ Γ' :
  (nil ||- e : τ =| Γ') -> is_val e + treducible nil nil nil e.
Proof.
  remember nil as Γ;
  induction 1; subst.
  - (* var *) cbn in e; congruence.
  - (* lit *) now left.
  - (* binop *) right; destruct (IHcheck1 eq_refl), (IHcheck2 eq_refl); get_values; subst.
    + do 5 eexists; context_solver HoleCtx.
    + rename t into s; do 5 destruct s; do 5 eexists; apply fill_contextual_step with (K:=RBinOpCtx o (LitV x) HoleCtx) in c;
      exact c.
    + rename t into s; do 5 destruct s; do 5 eexists; apply fill_contextual_step with (K:=LBinOpCtx o HoleCtx (Lit x)) in c;
      exact c.
    + rename t into s; do 5 destruct s; do 5 eexists; apply fill_contextual_step with (K:=LBinOpCtx o HoleCtx e2) in c;
      exact c.
  - (* access *) inv H; cbn in H3; congruence.
  - (* assign *) inv H; cbn in H4; congruence.
  - (* letin *) right; destruct (IHcheck1 eq_refl); get_values; subst; reducible_in_ctx.
    + do 5 eexists; context_solver HoleCtx.
    + rename t into s; do 5 destruct s; do 5 eexists; apply fill_contextual_step with (K:=LetinCtx x HoleCtx e2) in c;
      exact c.
  - (* new *) right; destruct (IHcheck1 eq_refl); get_values; subst.
    + do 5 eexists; context_solver HoleCtx; econstructor; reflexivity.
    + rename t into s; do 5 destruct s; do 5 eexists; eauto.
  - (* delete *) inv e.
  - (* if *) right; destruct (IHcheck1 eq_refl); get_values; subst.
    + destruct (Nat.eq_dec x 0).
      * do 5 eexists; context_solver HoleCtx.
      * do 5 eexists; context_solver HoleCtx.
    + rename t into s; do 5 destruct s; do 5 eexists; apply fill_contextual_step with (K:=IfCtx HoleCtx e2 e3) in c;
      exact c.
Qed.

Fixpoint drop {A} (Γ : list (string * A)) : list string :=
  match Γ with
  | nil => nil
  | (x,_) :: Γ' => x :: (drop Γ')
  end
.

Lemma closed_typing Γ e τ Γ' :
  (Γ ||- e : τ =| Γ') -> closed (drop Γ) e.
Proof.
  induction 1; subst; apply closed_equiv_is_closed; cbn.
  - (* var *) rewrite <- bool_eq_equiv_if; erewrite bool_In_equiv_In. induction Γ; cbn. inv e.
    destruct a. cbn in e. destruct (string_dec x s); subst.
    + cbn; now left.
    + right; now apply IHΓ.
  - (* lit *) easy.
  - (* binop *) apply bool_and_equiv_prop; split; apply closed_equiv_is_closed; easy.
  - (* access *) apply nested_bool_pred; apply bool_and_equiv_prop; split.
    + unfold closed in IHcheck1; cbn in IHcheck1; rewrite <- bool_eq_equiv_if; easy.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck2; now apply closed_equiv_is_closed.
  - (* assign *) apply bool_and_equiv_prop; apply bool_and_equiv_prop. rewrite !bool_and_equiv_prop; repeat split.
    + unfold closed in IHcheck1; cbn in IHcheck1; rewrite <- bool_eq_equiv_if; easy.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck2; now apply closed_equiv_is_closed.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck3; now apply closed_equiv_is_closed.
  - (* letin *) apply bool_and_equiv_prop; split.
    + rewrite <- bool_eq_equiv_if; easy.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck2; now apply closed_equiv_is_closed.
  - (* new *) apply bool_and_equiv_prop; split.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck1; now apply closed_equiv_is_closed.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck2; now apply closed_equiv_is_closed.
  - (* delete *) induction Γ; cbn. inv e. destruct a. cbn in e. destruct (string_dec x s); subst.
    + cbn; destruct (string_dec s s); try contradiction; reflexivity.
    + cbn; destruct (string_dec x s); try contradiction; now apply IHΓ.
  - (* if *) rewrite !bool_and_equiv_prop; repeat split.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck1; now apply closed_equiv_is_closed.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck2; now apply closed_equiv_is_closed.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck3; now apply closed_equiv_is_closed.
Qed.

Lemma gprogress e τ Γ Γ' :
  (Γ ||- e : τ =| Γ') -> is_val e + { H : Heap & { A : LocMap & { Δ : Env & treducible H A Δ e } } }.
Proof.
  induction 1; subst.
  - (* var *) right; do 2 exists nil; do 6 eexists; context_solver HoleCtx.
    eapply VarS;
    instantiate (1:=LitV 42); instantiate (1:=(x,EnvVal(LitV 42))::nil); cbn;
    destruct (string_dec x x); try contradiction; reflexivity.
  - (* lit *) now left.
  - (* binop *) right; destruct (IHcheck1), (IHcheck2); reducible_in_ctx; get_values; subst.
    + do 3 exists nil; do 5 eexists; context_solver HoleCtx.
    + do 8 destruct s as [? s]; do 8 eexists. eapply fill_contextual_step with (K:=RBinOpCtx o (LitV x) HoleCtx) in s; eauto.
    + do 8 destruct s as [? s]; rename x7 into e1'. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
      exists (BinOp o e1' (Lit x)). eapply fill_contextual_step with (K:=LBinOpCtx o HoleCtx (Lit x)) in s; cbn in s; exact s.
    + do 8 destruct s as [? s]; rename x6 into e1'. exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
      exists (BinOp o e1' e2). eapply fill_contextual_step with (K:=LBinOpCtx o HoleCtx e2) in s; cbn in s; exact s.
  - (* access *) right; destruct (IHcheck2); get_values; reducible_in_ctx; subst.
    + do 8 eexists. context_solver HoleCtx. econstructor. instantiate (1:=LocA 0). instantiate (1:=(x,EnvAddr(LocA 0))::nil).
      cbn. destruct (string_dec x x); try contradiction; trivial.
      instantiate (1:=0). instantiate (1:=(LocA 0, 0)::nil); cbn.
      destruct (addr_eq_dec (LocA 0) (LocA 0)); try contradiction; trivial.
      instantiate (1:=0). instantiate (1:=grow nil (1+x0)); cbn.
      clear IHcheck1 IHcheck2 H0.
      induction x0; cbn; trivial.
    + do 8 destruct s as [? s]; rename x7 into e'; do 8 eexists;
      eapply fill_contextual_step with (K:=AccessCtx x HoleCtx) in s; cbn in s; exact s.
  - (* assign *) right; destruct (IHcheck2), (IHcheck3); reducible_in_ctx; get_values; subst.
    + do 8 eexists. context_solver HoleCtx. econstructor.
      instantiate (1:=LocA 0). instantiate (1:=(x,EnvAddr(LocA 0))::nil); cbn.
      destruct (string_dec x x); try contradiction; trivial.
      instantiate (1:=0). instantiate (1:=(LocA 0, 0)::nil); cbn.
      destruct (addr_eq_dec (LocA 0) (LocA 0)); try contradiction; trivial.
      instantiate (1:=nil). instantiate (1:=nil). now destruct x1; cbn.
    + do 8 destruct s as [? s]; do 8 eexists; eapply fill_contextual_step with (K:=AssignVCtx x (LitV x0) HoleCtx) in s; eauto.
    + do 8 destruct s as [? s]; do 8 eexists; eapply fill_contextual_step with (K:=AssignCtx x HoleCtx (Lit x0)) in s; eauto.
    + do 8 destruct s as [? s]; do 8 eexists; eapply fill_contextual_step with (K:=AssignCtx x HoleCtx e2) in s; eauto.
  - (* letin *) right; destruct (IHcheck1); get_values; subst; reducible_in_ctx.
    + do 3 exists nil; do 5 eexists; context_solver HoleCtx.
    + do 8 destruct s as [? s]; do 8 eexists; eapply fill_contextual_step with (K:=LetinCtx x HoleCtx e2) in s; eauto.
  - (* new *) right; destruct (IHcheck1); get_values; subst; reducible_in_ctx.
    + do 3 exists nil. do 5 eexists. context_solver HoleCtx; econstructor; reflexivity.
    + do 8 destruct s as [? s]; do 8 eexists; eapply fill_contextual_step with (K:=NewCtx x HoleCtx e2) in s; eauto.
  - (* delete *) right. exists nil. exists nil. do 6 eexists. context_solver HoleCtx. econstructor.
    instantiate (1:=LocA 0). instantiate (1:=(x,EnvAddr(LocA 0))::nil); cbn.
    destruct (string_dec x x); try contradiction; trivial.
  - (* if *) right; destruct (IHcheck1); get_values; subst.
    + do 3 exists nil. exists Internal. do 3 exists nil. destruct (Nat.eq_dec x 0); subst.
      * exists e3; context_solver HoleCtx.
      * exists e2; context_solver HoleCtx.
    + do 8 destruct s as [? s]; eapply fill_contextual_step with (K:=IfCtx HoleCtx e2 e3) in s; do 8 eexists; exact s.
Qed.

Lemma preservation e e' Γ Γ' H A Δ H' A' Δ' a :
  (Γ ||- e : tyNat =| Γ') ->
  (contextual_step H A Δ e a H' A' Δ' e') ->
  { Γ0 : Gamma & { Γ1 : Gamma & (Γ0 ||- e' : tyNat =| Γ1) }}
.
Proof.
Admitted.


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
  intros. unfold closed. cbn. rewrite bool_eq_equiv_if. rewrite !bool_and_equiv_prop.
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
| WProgCheck : forall Γ' e t (H : nil ||- e : tyNat =| Γ'), whole_program_check (WProg e t)
.
Inductive component_check : WhileComponent -> Type :=
| WCompCheck : forall e (H : ((("x"%string, tyNat)::nil) ||- e : tyNat =| (("x"%string, tyNat)::nil))),
               component_check (WComp e (closed_typing H))
.
Inductive context_check : WhileContext -> Type :=
| WCtxCheck : forall e0 e1 (H0 : (nil ||- e0 : tyNat =| nil)) (H1 : ((("y"%string, tyNat) :: nil) ||- e1 : tyNat =| (("y"%string, tyNat)::nil))),
                            context_check (WCtx e0 e1 (closed_typing H0) (closed_typing H1))
.
CoInductive infinite_steps (p : expr) : Type :=
| more : forall H H' A A' Δ Δ' b p', contextual_step H A Δ p b H' A' Δ' p' -> infinite_steps p' -> infinite_steps p
| term : infinite_steps p
.

CoInductive CTrace : Type :=
| SCons : Event -> CTrace -> CTrace
.
Definition termtrace : CTrace.
Proof.
  cofix H; econstructor; exact Internal || exact H.
Defined.
CoFixpoint mk_trace p (H : infinite_steps p) : CTrace.
Proof.
  inv H. econstructor.
  - exact b.
  - eapply mk_trace; exact (more H1 H2).
  - exact termtrace.
Defined.

CoFixpoint mk_steps p Γ Γ' (H : Γ ||- p : tyNat =| Γ') : infinite_steps p.
Proof.
  eapply gprogress in H as H0.
  destruct H0.
  - eapply term.
  - do 8 destruct s as [? s]. eapply more.
    + exact s.
    + eapply preservation in s as H0.
      do 2 destruct H0 as [? H0].
      eapply mk_steps. exact H0.
      exact H.
Defined.
Definition execute_expr (e : expr) Γ Γ' (H : Γ ||- e : tyNat =| Γ') := mk_trace (mk_steps H).
Definition execute (p : WhileProgram) (H : whole_program_check p) : CTrace.
Proof. destruct H; now apply execute_expr in H. Defined.

Fixpoint trace_at (t : CTrace) (n : nat) :=
  match t with
  | SCons e0 xs =>
      match n with
      | 0 => e0
      | S n' => trace_at xs n'
      end
  end
.
Fixpoint is_prefix (m : list Event) (t : CTrace) :=
  match m,t with
  | nil, _ => True
  | a :: m', SCons a' t' => if event_dec a a' then is_prefix m' t' else False
  end
.
Definition safety (π : CTrace -> Prop) : Prop :=
  forall (t : CTrace), π t -> exists (m : list Event), is_prefix m t /\ forall (t' : CTrace), is_prefix m t' -> ~(π t')
.
Definition occ (e : Event) (t : CTrace) :=
  exists n, trace_at t n = e
.
Definition one_event (e : Event) (t : CTrace) :=
  exists n, trace_at t n = e /\ ~exists m, n <> m /\ trace_at t m = e
.
Definition after_another_event (e0 e1 : Event) (t : CTrace) :=
  exists n, trace_at t n = e0 -> exists m, trace_at t m = e1 /\ n < m
.
Definition temp_memsafe (t : CTrace) :=
  forall v s, one_event (Alloc v s) t ->
         one_event (Dealloc v) t /\
         after_another_event (Alloc v s) (Dealloc v) t
.
Definition spat_memsafe (t : CTrace) :=
  forall loc s, occ (Alloc loc s) t ->
           (forall n, occ (Read loc n) t -> n < s) /\
           (forall n, occ (Write loc n) t -> n < s)
.
Lemma temp_memsafe_is_safety : safety temp_memsafe.
Proof.
Admitted.
Lemma spat_memsafe_is_safety : safety spat_memsafe.
Proof.
Admitted.

Lemma plug_checks_propagate (c : WhileContext) (p : WhileComponent) :
  context_check c ->
  component_check p ->
  whole_program_check (plug c p).
Proof. intros; destruct c, H, H0; cbn; repeat (econstructor; trivial); (eassumption || now cbn). Defined.

Fixpoint mk_full_trace_from_pref (m : list Event) : CTrace :=
  match m with
  | nil => termtrace
  | e :: m' => SCons e (mk_full_trace_from_pref m')
  end
.
Definition prog2trace (p : WhileProgram) : CTrace := mk_full_trace_from_pref(wprog2tracepref p).

Definition wsat (p : WhileProgram) (H : whole_program_check p) (π : CTrace -> Prop) : Prop := π (prog2trace p).
Definition wrsat (p : WhileComponent) (H0 : component_check p) (π : CTrace -> Prop) : Prop :=
  forall (c : WhileContext) (H1 : context_check c), @wsat (plug c p) (@plug_checks_propagate c p H1 H0) π
.

Lemma while_is_not_spat_memsafe :
  ~ (forall (p : WhileComponent) (H : component_check p), wrsat H spat_memsafe).
Proof.
  intros H.
  remember (New "x0"%string (Lit 42) (Letin "_"%string (Access "x0"%string (Lit 1337)) (Delete "x0"%string))) as p.
  assert ((("x"%string, tyNat)::nil) ||- p : tyNat =| (("x"%string, tyNat)::nil)) by (rewrite Heqp; repeat econstructor; eauto).
  assert (component_check (WComp p (closed_typing H0))) by econstructor.
  specialize (H (WComp p (closed_typing H0)) H1).

  unfold wrsat in H.
  assert (nil ||- Lit 0 : tyNat =| nil) by repeat econstructor.
  assert ((("y"%string, tyNat) :: nil) ||- Lit 0 : tyNat =| (("y"%string, tyNat)::nil)) by repeat econstructor.
  assert (context_check (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3))) by repeat econstructor.
  specialize (H (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3)) H4).

  unfold wsat in H.
  specialize (H (LocA 0) 42). destruct H.


  unfold compute_trace_prefix. rewrite Heqp. cbn.
  destruct (addr_eq_dec (LocA 0) (LocA 0)); try contradiction; cbn.
  exists 0; now cbn.
  assert (occ (Read (LocA 0) 1337)
        (prog2trace
           (plug (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3))
              (WComp p (closed_typing H0))))).
  cbn. rewrite Heqp. unfold compute_trace_prefix. cbn. destruct (addr_eq_dec (LocA 0) (LocA 0)); try contradiction; cbn.
  exists 1; now cbn.
  (*unfold execute. destruct H4, H1; cbn. unfold execute_expr. cbn.*)
  (*unfold one_event. exists 1. cbn. admit.*)
  specialize (H 1337 H6).
  lia.
Qed.

Lemma while_is_temp_memsafe (p : WhileComponent) (H : component_check p) :
  wrsat H temp_memsafe.
Proof.
  destruct p. destruct H as [Γ' e' H].
  intros ? ?. unfold wsat. cbn.
Admitted.
