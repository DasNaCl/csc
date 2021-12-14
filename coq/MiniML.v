Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat Strings.String Lists.List Lia Program.Equality.
Require Import Classes.RelationClasses Morphisms Setoid.
Require Import CSC.Util.

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
Definition is_val (e : expr) : Prop :=
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
Definition State : Set := (Heap * LocMap * Env).
Definition Conf : Set := (State * expr).

Notation "H ';' A ';' Δ" := ((H, A, Δ) : State) (at level 80, A at next level, Δ at next level).
Notation "Ω '▷' e" := ((Ω, e) : Conf) (at level 80, e at next level).

Notation "∅" := ((nil, nil, nil) : State).

Definition lookup {A : Type} (x : string) (Δ : list (string * A)) := Util.find (String.eqb x) Δ.
Definition fetch (x : addr) (A : list (addr * nat)) :=
  match Util.find (addr_eqb x) A with
  | Some n => n
  | None => 1729
  end
.
Definition read (a : nat) (H : list nat) :=
  match List.nth_error H a with
  | Some n => n
  | None => 1729
  end
.
Lemma lookup_dec {A : Type} (x : string) (Δ : list (string * A)) :
  { lookup x Δ = None } + { lookup x Δ <> None }.
Proof. unfold lookup; apply Util.find_dec. Defined.

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
| VarS : forall H A Δ x v, lookup x Δ = Some (EnvVal(LitV v)) ->
                      (H;A;Δ ▷ Var x -[ Internal ]~> H;A;Δ ▷ Lit v)
| BinOpS : forall Ω n1 n2 o, (Ω ▷ BinOp o (Lit n1) (Lit n2) -[ Internal ]~> Ω ▷ of_val(bin_op_eval o n1 n2))
| GetS : forall H A Δ x n loc v nl, lookup x Δ = Some (EnvAddr loc) ->
                               fetch loc A = nl ->
                               read (nl + n) H = v ->
                               (H;A;Δ ▷ Access x (Lit n) -[ Read loc n ]~> H;A;Δ ▷ Lit v)
| SetS : forall H H' A Δ x n v loc nl, lookup x Δ = Some (EnvAddr loc) ->
                                  fetch loc A = nl ->
                                  H' = replace (nl + n) H v ->
                                  (H;A;Δ ▷ Assign x (Lit n) (Lit v) -[ Write loc n ]~> H';A;Δ ▷ Lit v)
| IfBotS : forall Ω e1 e2, (Ω ▷ If (Lit 0) e1 e2 -[ Internal ]~> Ω ▷ e2)
| IfTopS : forall Ω e1 e2 v, v <> 0 -> (Ω ▷ If (Lit v) e1 e2 -[ Internal ]~> Ω ▷ e1)
| LetS : forall H A Δ x v e, (H;A;Δ ▷ Letin x (Lit v) e -[ Internal ]~> H;A;((x,EnvVal (LitV v)) :: Δ) ▷ e)
| DeleteS : forall H A Δ x loc, lookup x Δ = Some (EnvAddr loc) ->
                           (H;A;Δ ▷ Delete x -[ Dealloc loc ]~> H;A;(delete x Δ) ▷ Lit 0)
| NewS : forall H H' A Δ x n e loc s, s = List.length H ->
                                 H' = grow H n ->
                                 loc = LocA (List.length A) ->  (* <- using the length of A allows us to not need an axiom *)
                                 (H;A;Δ ▷ New x (Lit n) e -[ Alloc loc n ]~> H';((loc, s) :: A);((x, EnvAddr loc) :: Δ) ▷ e)
where "Ω0 '-[' a ']~>' Ω1" := (base_step Ω0 a Ω1)
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
Inductive steps : Conf -> list Event -> Conf -> Prop :=
| stepsRefl : forall Ω e, steps (Ω ▷ e) nil (Ω ▷ e)
| stepsTrans : forall Ω e a as0 Ω' e' Ω'' e'',
    (Ω ▷ e =[ a ]~> Ω' ▷ e') ->
    (Ω' ▷ e' =[ as0 ]~>* Ω'' ▷ e'') ->
    (Ω ▷ e =[ a :: as0 ]~>* Ω'' ▷ e'')
where "Ω1 '=[' a ']~>*' Ω2" := (steps Ω1 a Ω2)
.

#[global]
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
  (*Ω ▷ e1 =[ As ]~>* Ω' ▷ e2 -> Ω ▷ (fill K e1) =[ As ]~>* Ω' ▷ (fill K e2).*)
  steps (Ω ▷ e1) As (Ω' ▷ e2) -> steps (Ω ▷ (fill K e1)) As (Ω' ▷ (fill K e2)).
Proof.
  intros H; dependent induction H; subst; try eapply stepsRefl.
  eapply stepsTrans. eapply fill_contextual_step. exact H.
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

Lemma contextual_step_newctx Ω x e0 e e' a Ω' :
  Ω ▷ e =[ a ]~> Ω' ▷ e' ->
  Ω ▷ New x e e0 =[ a ]~> Ω' ▷ New x e' e0.
Proof. context_intro; context_solver (NewCtx x HoleCtx e0). Qed.

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

Lemma ctx_steps_newctx Ω x e0 e e' a Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ New x e e0 =[ a ]~>* Ω' ▷ New x e' e0.
Proof. context_intro; context_solver (NewCtx x HoleCtx e0). Qed.

Lemma ctx_steps_ifctx Ω e e' e1 e2 a Ω' :
  Ω ▷ e =[ a ]~>* Ω' ▷ e' ->
  Ω ▷ If e e1 e2 =[ a ]~>* Ω' ▷ If e' e1 e2.
Proof. context_intro; context_solver (IfCtx HoleCtx e1 e2). Qed.

Lemma contextual_step_steps σ a σ' :
  σ =[ a ]~> σ' -> σ =[ a :: nil ]~>* σ'.
Proof. intros; destruct σ, σ'; eapply stepsTrans; (eapply stepsRefl + exact H). Qed.

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
Lemma trans_steps σ σ' σ'' As1 As2 :
  σ =[ As1 ]~>* σ' -> σ' =[ As2 ]~>* σ'' -> σ =[ As1 ++ As2 ]~>* σ''
.
Proof.
  intros H; dependent induction H; cbn; intros; try easy;
  destruct σ''; eapply stepsTrans; try exact H; apply IHsteps; exact H1.
Qed.

Lemma inv_lit_ctx_step Ω n E v Ω' :
  Ω ▷ Lit n =[ E ]~> Ω' ▷ Lit v -> Lit n = Lit v /\ Ω = Ω'.
Proof. intros; inv H; induction K; cbn in *; try congruence; subst; inv H7. Qed.

Lemma inv_lit_steps Ω n Tr v Ω' :
  Ω ▷ Lit n =[ Tr ]~>* Ω' ▷ Lit v -> Lit n = Lit v /\ Ω = Ω' /\ Tr = nil.
Proof.
  intros; dependent induction H; try easy.
  inv H; induction K; cbn in *; try congruence; subst; inv H8.
Qed.

Lemma inv_var_ctx_step A H Δ Ω' E v s :
  (A; H; Δ, Var s) =[ E ]~> (Ω', Lit v) -> lookup s Δ = Some(EnvVal v) /\ (A; H; Δ) = Ω'.
Proof. intros; inv H0; induction K; cbn in *; try congruence; subst; now inv H8. Qed.

Lemma inv_var_steps A H Δ Ω' Tr v s :
  (A; H; Δ, Var s) =[ Tr ]~>* (Ω', Lit v) -> lookup s Δ = Some(EnvVal v) /\ (A; H; Δ) = Ω' /\ Tr = Internal :: nil.
Proof.
  intros; dependent induction H0; try easy;
  inv H1; induction K; cbn in *; try congruence; subst; inv H9; try easy;
  apply inv_lit_steps in H0 as []; inv H0; now inv H1.
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
  | New x e0 e1 => andb (is_closed X e0) (is_closed (x :: X) e1)
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
Inductive check : Gamma -> expr -> ty -> Gamma -> Prop :=
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

(* This is easier to work with to get traces. TODO: make it cofix when adding loops *)
Fixpoint exec (Ω : State) (e : expr) : option (State * val * list Event) :=
  let '(H, A, Δ) := Ω in
  match e with
  | Var x => match lookup x Δ with
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
                   let '(H', A', Δ') := Ω' in
                   match lookup x Δ' with
                   | Some(EnvAddr loc) =>
                       let nl := fetch loc A' in
                       Some (Ω', LitV (read (nl + v) H'), Tr ++ ((Read loc v) :: nil))
                   | _ => None
                   end
                 | None => None
                 end
  | Assign x e1 e2 => match exec Ω e1 with
                     | Some(Ω1, LitV n, Tr1) =>
                         match exec Ω1 e2 with
                         | Some(Ω2, LitV v, Tr2) =>
                           let '(H', A', Δ') := Ω2 in
                           match lookup x Δ' with
                           | Some(EnvAddr loc) =>
                               let nl := fetch loc A' in
                               Some ((replace (nl + n) H' v, A', Δ'), LitV v, Tr1 ++ Tr2 ++ ((Write loc n)::nil))
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
                        let '(H1, A1, Δ1) := Ω1 in
                        match exec (H1, A1, (x, EnvVal v1) :: Δ1) e2 with
                        | Some(Ω2, v2, Tr2) => Some(Ω2, v2, Tr1 ++ (Internal :: nil) ++ Tr2)
                        | None => None
                        end
                    | None => None
                    end
  | Delete x => match lookup x Δ with
               | Some (EnvAddr loc) => Some ((H, A, delete x Δ), LitV 0, (Dealloc loc)::nil)
               | _ => None
               end
  | New x e1 e2 => match exec Ω e1 with
                  | Some(Ω1, LitV m, Tr1) =>
                      let '(H1, A1, Δ1) := Ω1 in
                      let loc := LocA(List.length A1) in
                      let s := List.length H1 in
                      match exec (grow H1 m, (loc,s)::A1, (x,EnvAddr loc) :: Δ1) e2 with
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
  | [ H1: match exec (?Aa, ?Ha, ?Δa) ?e with | Some _ => _ | None => None end = _,
     H: exec (?Aa, ?Ha, ?Δa) ?e <> None |- _ ] =>
      let Aa1 := fresh "Aa" in
      let Ha1 := fresh "Ha" in
      let Δa1 := fresh "Δa" in
      let v1 := fresh "v" in
      let Tr1 := fresh "Tr" in
    apply Util.not_eq_None_Some in H as [x]; destruct x as [[[[Aa1 Ha1] Δa1] [v1]] Tr1];
    rewrite H in H1; cbn in H1
  end;
  match goal with
  | [Ha: (exec (?A, ?H, ?Δ) ?e = Some (?A', ?H', ?Δ', LitV ?v', ?Tr')),
      IH: forall (Ω : State) (v : nat) (Tr : list Event) (Ω' : State),
          exec Ω ?e = Some (Ω', LitV v, Tr) ->
          (Ω, ?e) =[ Tr ]~>* (Ω', Lit v) |- _ ] =>
      specialize (IH (A, H, Δ) v' Tr' (A', H', Δ') Ha)
  end
).

Ltac exec_reduce := (
  try match goal with
  | [ H: match exec (?Aa, ?Ha, ?Δa) ?e with | Some _ => _ | None => None end = _ |- _ ] =>
      assert (exec (Aa, Ha, Δa) e <> None) by (
      let Aa1 := fresh "Aa" in
      let Ha1 := fresh "Ha" in
      let Δa1 := fresh "Δa" in
      let v1 := fresh "v" in
      let Tr1 := fresh "Tr" in
      destruct (exec (Aa, Ha, Δa) e) as [[[[[Aa1 Ha1] Δa1] [v1]]]|]; congruence);
      exec_reduce_handle_eq_none
  | [ H: match lookup ?s ?Δa with | Some _ => _ | None => None end = _ |- _ ] =>
    let H2 := fresh "H" in
    destruct (lookup_dec s Δa) as [H2|H2]; try (rewrite H2 in H; congruence);
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
  revert Ω v Tr Ω'; induction e; intros; destruct Ω as [[Aa Ha] Δa]; cbn in H; inv H; eauto.
  - repeat exec_reduce; destruct v0; inv H1; eauto.
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
    eapply fill_steps with (K:=NewCtx s HoleCtx e2) in IHe1; cbn in IHe1.
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
Lemma closed_typing Γ e τ Γ' :
  (Γ ||- e : τ =| Γ') -> closed (drop Γ) e.
Proof.
  induction 1; subst; apply closed_equiv_is_closed; cbn.
  - (* var *) rewrite <- bool_eq_equiv_if; erewrite bool_In_equiv_In. induction Γ; cbn. inv H.
    destruct a. cbn in H. destruct (string_dec x s); subst.
    + cbn; now left.
    + right; apply IHΓ; apply String.eqb_neq in n; now rewrite n in H.
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
  - (* delete *) induction Γ; cbn. inv H. destruct a. cbn in H. destruct (string_dec x s); subst.
    + cbn; destruct (string_dec s s); try contradiction; reflexivity.
    + cbn; destruct (string_dec x s); try contradiction; apply IHΓ; apply String.eqb_neq in n; now rewrite n in H.
  - (* if *) rewrite !bool_and_equiv_prop; repeat split.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck1; now apply closed_equiv_is_closed.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck2; now apply closed_equiv_is_closed.
    + rewrite <- bool_eq_equiv_if; apply closed_equiv_is_closed in IHcheck3; now apply closed_equiv_is_closed.
Qed.

Lemma cons_read_same x v H :
  read x (v :: H) = v -> read (S x) (v :: v :: H) = v.
Proof. revert v H; induction x; intros; cbn in *; trivial. Qed.

Lemma gprogress e τ Γ Γ' :
  (Γ ||- e : τ =| Γ') -> is_val e \/ exists Ω, reducible Ω e.
Proof.
  induction 1; subst.
  - (* var *) right; exists (nil, nil, (x, EnvVal(LitV 0)) :: nil); do 3 eexists; context_solver HoleCtx;
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
  - (* access *) right; destruct (IHcheck2); get_values; subst.
    + do 4 eexists; context_solver HoleCtx; econstructor.
      instantiate (1:=LocA 0); instantiate (1:=(x,EnvAddr(LocA 0))::nil); cbn; now rewrite String.eqb_refl.
      instantiate (1:=0); instantiate (1:=(LocA 0, 0)::nil); now cbn.
      instantiate (1:=0); instantiate (1:=grow nil (1+x0)); cbn;
      clear IHcheck1 IHcheck2 H0. induction x0; cbn; trivial; now apply cons_read_same.
    + do 4 destruct H1 as [? H1]; do 4 eexists;
      eapply fill_contextual_step with (K:=AccessCtx x HoleCtx) in H1; cbn in H1; exact H1.
  - (* assign *) right; destruct (IHcheck2), (IHcheck3); get_values; subst.
    + do 4 eexists; context_solver HoleCtx; econstructor.
      instantiate (1:=LocA 0); instantiate (1:=(x,EnvAddr(LocA 0))::nil); cbn; now rewrite String.eqb_refl.
      instantiate (1:=0); instantiate (1:=(LocA 0, 0)::nil); now cbn.
      instantiate (1:=nil); instantiate (1:=nil); now destruct x1; cbn.
    + do 4 destruct H3 as [? H3]; do 4 eexists; eapply fill_contextual_step with (K:=AssignVCtx x (LitV x0) HoleCtx) in H3; eauto.
    + do 4 destruct H2 as [? H2]; do 4 eexists; eapply fill_contextual_step with (K:=AssignCtx x HoleCtx (Lit x0)) in H2; eauto.
    + do 4 destruct H2 as [? H2]; do 4 eexists; eapply fill_contextual_step with (K:=AssignCtx x HoleCtx e2) in H2; eauto.
  - (* letin *) right; destruct (IHcheck1); get_values; subst.
    + exists (nil, nil, nil); do 3 eexists; eauto.
    + do 4 destruct H2 as [? H2]; do 4 eexists; eapply fill_contextual_step with (K:=LetinCtx x HoleCtx e2) in H2; eauto.
  - (* new *) right; destruct (IHcheck1); get_values; subst.
    + exists (nil, nil, nil); do 3 eexists; context_solver HoleCtx; econstructor; reflexivity.
    + do 4 destruct H2 as [? H2]; do 4 eexists; eapply fill_contextual_step with (K:=NewCtx x HoleCtx e2) in H2; eauto.
  - (* delete *) right; exists (nil, nil, (x,EnvAddr(LocA 0))::nil); do 3 eexists; context_solver HoleCtx;
    econstructor; cbn; now rewrite String.eqb_refl.
  - (* if *) right; destruct (IHcheck1); get_values; subst.
    + exists (nil, nil, nil); exists Internal; exists (nil, nil, nil); destruct (Nat.eq_dec x 0); subst.
      * exists e3; context_solver HoleCtx.
      * exists e2; context_solver HoleCtx.
    + do 4 destruct H2 as [? H2]; eapply fill_contextual_step with (K:=IfCtx HoleCtx e2 e3) in H2; do 4 eexists; exact H2.
Qed.

Lemma gprogress_steps e τ Γ Γ' :
  (Γ ||- e : τ =| Γ') -> exists Ω Ω' Tr v, (Ω ▷ e =[ Tr ]~>* Ω' ▷ v) /\ is_val v.
Proof.
  intros; apply gprogress in H as [].
  - do 2 exists ∅. exists nil. apply is_val_inv in H as []. exists (Lit x). subst. repeat constructor.
  - destruct H as [Ω [E [Ω' [e' H]]]]. exists Ω. exists Ω'. exists (E :: nil). exists e'. split. eapply stepsTrans. exact H. eapply stepsRefl.
    (* Logical Relations .... *)
Admitted.

Lemma preservation e e' Γ Γ' Ω Ω' a :
  (Γ ||- e : tyNat =| Γ') ->
  (Ω ▷ e -[ a ]~> Ω' ▷ e') ->
  exists Γ'', Γ' ||- e' : tyNat =| Γ''
.
Proof.
Admitted.

Axiom zap : forall e : expr, exists Ω E Ω' v, Ω ▷ e =[ E ]~> Ω' ▷ Lit v.

Lemma binop_ctx_step_inv Ω1 b e1 e2 Ω3 v E :
  Ω1 ▷ BinOp b e1 e2 =[ E ]~> Ω3 ▷ Lit v ->
  exists v1 v2, (e1 = Lit v1 /\ e2 = Lit v2 /\ E = Internal /\ v = bin_op_eval_int b v1 v2)
.
Proof.
  intros. inv H. induction K; cbn in *; try congruence. subst.
  inv H7. exists n1; exists n2; easy.
Qed.

Lemma binop_steps_lits_inv Ω1 b Ω3 v1 v2 v Tr :
  Ω1 ▷ BinOp b (Lit v1) (Lit v2) =[ Tr ]~>* Ω3 ▷ Lit v ->
  Ω1 = Ω3 /\ v = v1 + v2 /\ Tr = Internal :: nil.
Proof.
  intros; inv H; inv H4; destruct K; cbn in *; try congruence; subst.
  - inv H8; apply inv_lit_steps in H6 as [H [H0 H1]]; subst; inv H; easy.
  - inv H5; destruct K; cbn in *; try congruence; subst; inv H8.
  - inv H5; destruct K; cbn in *; try congruence; subst; inv H8.
Qed.

Lemma binop_steps_inv Ω1 b e1 e2 Ω3 v Tr :
  Ω1 ▷ BinOp b e1 e2 =[ Tr ]~>* Ω3 ▷ Lit v ->
  exists Ω2 Tr1 Tr2 v1 v2, ((Ω1 ▷ e1 =[ Tr1 ]~>* Ω2 ▷ Lit v1) /\ (Ω2 ▷ e2 =[ Tr2 ]~>* Ω3 ▷ Lit v2)
/\ Tr = Tr1 ++ Tr2 ++ Internal :: nil /\ v = bin_op_eval_int b v1 v2)
.
Proof.
Admitted.

Lemma access_steps_inv Ω1 A3 H3 Δ3 s e v Tr :
  Ω1 ▷ Access s e =[ Tr ]~>* (H3; A3; Δ3) ▷ Lit v ->
  exists Ω' Tr' loc v1, ((Ω1 ▷ e =[ Tr' ]~>* Ω' ▷ Lit v1)
/\ (let '(H', A', Δ') := Ω' in (A3 = A' /\ H3 = H' /\ Δ3 = Δ' /\ v = read (fetch loc A' + v1) H')
/\ lookup s Δ' = Some(EnvAddr loc) /\ Tr = Tr' ++ Read loc v1 :: nil))
.
Proof.
  intros. dependent induction H.
Admitted.

Lemma letin_steps_inv Ω1 Ω3 s e1 e2 v Tr :
  Ω1 ▷ Letin s e1 e2 =[ Tr ]~>* Ω3 ▷ Lit v ->
  exists H1 A1 Δ1 Tr1 Tr2 v1 v2, (Ω1 ▷ e1 =[ Tr1 ]~>* (H1; A1; Δ1) ▷ Lit v1)
/\ ((H1; A1; (s,EnvVal v1) :: Δ1) ▷ e2 =[ Tr2 ]~>* Ω3 ▷ Lit v2) /\ v = v2 /\ Tr = Tr1 ++ Internal :: Tr2
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

Lemma assign_steps_inv Ω H' A' Δ' s e1 e2 v Tr :
  Ω ▷ Assign s e1 e2 =[ Tr ]~>* (H'; A'; Δ') ▷ Lit v ->
  exists v1 Tr1 Ω1 v2 Tr2 Ω2 loc, (Ω ▷ e1 =[ Tr1 ]~>* Ω1 ▷ Lit v1) /\ (Ω1 ▷ e2 =[ Tr2 ]~>* Ω2 ▷ Lit v2)
/\ (let '(H2, A2, Δ2) := Ω2 in (lookup s Δ2 = Some(EnvAddr loc)
                             /\ Tr = Tr1 ++ Tr2 ++ Write loc v1 :: nil /\ v = v2
                             /\ H' = replace (fetch loc A' + v1) H2 v2 /\ A' = A2 /\ Δ' = Δ2))
.
Proof.
Admitted.

Lemma new_steps_inv Ω Ω' s e1 e2 v Tr :
  Ω ▷ New s e1 e2 =[ Tr ]~>* Ω' ▷ Lit v ->
  exists v1 Tr1 Ω1 v2 Tr2 Ω2, (Ω ▷ e1 =[ Tr1 ]~>* Ω1 ▷ Lit v1)
/\ (let '(H1, A1, Δ1) := Ω1 in (((grow H1 v1; (LocA(List.length A1), List.length H1) :: A1; (s,EnvAddr(LocA(List.length A1))) :: Δ1)
                                ▷ e2 =[ Tr2 ]~>* Ω2 ▷ Lit v2)
/\  Ω' = Ω2 /\ v = v2 /\ Tr = Tr1 ++ Alloc (LocA(List.length A1)) v1 :: Tr2))
.
Proof.
Admitted.

Lemma delete_steps_inv Ω Ω' s Tr v :
  Ω ▷ Delete s =[ Tr ]~>* Ω' ▷ Lit v ->
  exists loc, (let '(Ha, Aa, Δa) := Ω in (lookup s Δa = Some(EnvAddr loc)
      /\ Ω' = (Ha, Aa, delete s Δa) /\ v = 0 /\ Tr = Dealloc loc :: nil
  )).
Proof.
  intros; destruct Ω; inv H;
  inv H4; induction K; cbn in *; try congruence; subst; inv H8;
  exists loc; repeat split; apply inv_lit_steps in H6 as [H0 [H1 H2]]; try easy;
  now (inv H0 + rewrite H2).
Qed.

(* this depends on the above inversion lemmas... *)
Lemma steps_is_exec Ω Ω' e v Tr :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ Lit v ->
  exec Ω e = Some (Ω', LitV v, Tr)
.
Proof.
  revert Ω v Tr Ω'; induction e; intros; destruct Ω as [[Ha Aa] Δa], Ω' as [[Ha' Aa'] Δa']; cbn.
  - apply inv_lit_steps in H as []; subst; inv H0; inv H; inv H1; easy.
  - apply inv_var_steps in H as [H []]; rewrite H, H1; inv H0; easy.
  - eapply binop_steps_inv in H as [Ω2 [Tr1 [Tr2 [v1 [v2 [H1 [H2 [H3 H4]]]]]]]];
    specialize (IHe1 (Ha; Aa; Δa) v1 Tr1 Ω2 H1); specialize (IHe2 Ω2 v2 Tr2 (Ha'; Aa'; Δa') H2);
    now rewrite IHe1, IHe2, H3, H4.
  - eapply access_steps_inv in H as [[[H' A'] Δ'] [Tr' [loc [v1 [H1 [[H2 [H3 [H4 H5]]] [H6 H7]]]]]]];
    specialize (IHe (Ha; Aa; Δa) v1 Tr' (H'; A'; Δ') H1);
    now rewrite IHe, H6, H5, H7, H2, H3, H4.
  - eapply letin_steps_inv in H as [H1 [A1 [Δ1 [Tr1 [Tr2 [v1 [v2 [H2 [H3 [H4 H5]]]]]]]]]];
    specialize (IHe1 (Ha; Aa; Δa) v1 Tr1 (H1; A1; Δ1) H2);
    specialize (IHe2 (H1; A1; (s, EnvVal v1) :: Δ1) v2 Tr2 (Ha'; Aa'; Δa') H3);
    now rewrite IHe1, IHe2, H4, H5.
  - eapply if_steps_inv in H as [v1 [Tr1 [Ω1 [H1 [[H2 [v2 [Tr2 [Ω2 [H3 [H4 [H5 H6]]]]]]]
                                                | [H2 [v3 [Tr3 [Ω3 [H3 [H4 [H5 H6]]]]]]]]]]]];
    specialize (IHe1 (Ha; Aa; Δa) v1 Tr1 Ω1 H1).
    + specialize (IHe2 Ω1 v2 Tr2 Ω2 H3);
      destruct v1; try contradiction; now rewrite IHe1, IHe2, H4, H5, H6.
    + specialize (IHe3 Ω1 v3 Tr3 Ω3 H3);
      now rewrite IHe1, IHe3, H4, H2, H5, H6.
  - eapply assign_steps_inv in H as [v1 [Tr1 [Ω1 [v2 [Tr2 [[[H2 A2] Δ2] [loc [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]]]]]]];
    specialize (IHe1 (Ha; Aa; Δa) v1 Tr1 Ω1 H3); specialize (IHe2 Ω1 v2 Tr2 (H2; A2; Δ2) H4);
    now rewrite IHe1, IHe2, H5, H6, H7, H8, H9, H10.
  - eapply new_steps_inv in H as [v1 [Tr1 [[[H1 A1] Δ1] [v2 [Tr2 [Ω2 [H2 [H3 [H4 [H5 H6]]]]]]]]]];
    specialize (IHe1 (Ha; Aa; Δa) v1 Tr1 (H1; A1; Δ1) H2);
    specialize (IHe2 (grow H1 v1; (LocA(List.length A1), List.length H1) :: A1; (s, EnvAddr(LocA(List.length A1))) :: Δ1) v2 Tr2 Ω2 H3);
    now rewrite IHe1, IHe2, H4, H5, H6.
  - eapply delete_steps_inv in H as [loc [H1 [H2 [H3 H4]]]];
    now rewrite H1, H2, H3, H4.
Qed.

Theorem steps_equiv_exec Ω Ω' e v Tr :
  Ω ▷ e =[ Tr ]~>* Ω' ▷ Lit v <-> exec Ω e = Some (Ω', LitV v, Tr).
Proof. split; (apply steps_is_exec + apply exec_is_steps). Qed.

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

CoInductive CTrace : Type :=
| SCons : Event -> CTrace -> CTrace
.
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
  forall (t : CTrace), ~(π t) -> exists (m : list Event), (is_prefix m t -> forall (t' : CTrace), is_prefix m t' -> ~(π t'))
.
Definition occ (e : Event) (t : CTrace) :=
  exists n, trace_at t n = e
.
Lemma prefix_implies_occ t m e :
  is_prefix m t -> List.In e m -> occ e t.
Proof.
Admitted.

Definition one_event (e : Event) (t : CTrace) :=
  exists n, trace_at t n = e /\ ~exists m, n <> m /\ trace_at t m = e
.
Definition after_another_event (e0 e1 : Event) (t : CTrace) :=
  exists n, trace_at t n = e0 -> exists m, trace_at t m = e1 /\ n < m
.
Definition temp_memsafe (t : CTrace) :=
  forall v s, after_another_event (Alloc v s) (Dealloc v) t /\
         (~(forall x, after_another_event (Read v x) (Alloc v s) t)) /\
         (~(forall x, after_another_event (Write v x) (Alloc v s) t)) /\
         (~(forall x, after_another_event (Dealloc v) (Read v x) t)) /\
         (~(forall x, after_another_event (Dealloc v) (Write v x) t))
.
Definition spat_memsafe (t : CTrace) :=
  forall loc s, occ (Alloc loc s) t ->
           (forall n, occ (Read loc n) t -> n < s) /\
           (forall n, occ (Write loc n) t -> n < s)
.
Lemma temp_memsafe_is_safety : safety temp_memsafe.
Proof.
  intros ? ?.
  exists (Dealloc (LocA 0) :: Read (LocA 0) 42 :: nil); intros ? ? ? ?.
  unfold temp_memsafe in H, H2.
  eapply H2. exact 5.  (* <- this makes it seem like something is off of the definition *)
  intros ?. exists 0. intros. exists 1. split; try lia.
  (* by prefix *)
Admitted.
Lemma spat_memsafe_is_safety : safety spat_memsafe.
Proof.
  intros ? ?.
  exists (Alloc (LocA 0) 42 :: Read (LocA 0) 1337 :: nil); intros ? ? ? ?.
  eapply prefix_implies_occ with (e:=Alloc (LocA 0) 42) in H1 as Halloc1; cbn; try now left.
  eapply prefix_implies_occ with (e:=Read (LocA 0) 1337) in H1 as Hread1; cbn; try (right; now left).
  specialize (H2 (LocA 0) 42 Halloc1) as [].
  assert (occ (Read (LocA 0) 1337) t') by assumption.
  destruct Hread1 as [n1 Hread1'].
  specialize (H2 1337 H4).
  lia.
Qed.

Lemma plug_checks_propagate (c : WhileContext) (p : WhileComponent) :
  context_check c ->
  component_check p ->
  whole_program_check (plug c p).
Proof. intros; destruct c, H, H0; cbn; repeat (econstructor; trivial); (eassumption || now cbn). Defined.

Definition termtrace : CTrace.
Proof.
  cofix H; econstructor; try exact Internal; apply H.
Defined.
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

  unfold wsat in H; unfold spat_memsafe in H.
  remember (plug (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3))
                  (WComp p (closed_typing H0))) as fp.
  assert (occ (Alloc (LocA 0) 42) (prog2trace fp)).
  rewrite Heqfp; unfold compute_trace_prefix; cbn;
  rewrite Heqp; cbn; exists 1; now cbn.

  assert (occ (Read (LocA 0) 1337) (prog2trace fp)).
  cbn; rewrite Heqfp; cbn; rewrite Heqp; unfold compute_trace_prefix; cbn;
  destruct (addr_eq_dec (LocA 0) (LocA 0)); try contradiction; cbn.
  exists 2; now cbn.
  specialize (H (LocA 0) 42 H5) as [Ha Hb].
  specialize (Ha 1337 H6).
  lia.
Qed.

Lemma alloc_not_in_termtrace v n s :
  trace_at termtrace n <> Alloc v s.
Proof. induction n; cbn; intros ?; congruence. Qed.

Lemma while_is_temp_memsafe (p : WhileComponent) (H : component_check p) :
  wrsat H temp_memsafe.
Proof.
  destruct p; destruct H as [e' HΓ].
  intros ? ? ? ? ?; split; remember (plug c0 (WComp e' (closed_typing HΓ))) as fp; destruct fp.
  - destruct H as [n [Ha Hb]].

    induction e0; cbn in *; try now apply alloc_not_in_termtrace in Ha.
Admitted.
