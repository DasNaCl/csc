Set Implicit Arguments.
Require Import Coq.Arith.PeanoNat Strings.String Lists.List Lia Program.Equality.
Require Import Classes.RelationClasses Morphisms Setoid.
Require Import CSC.Util CSC.Fresh CSC.Sets.


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
(** * Syntax *)
(** We define two languages, one just for statics, the other just for dynamics. *)
(** Reason we do this is to disallow programmers, and, thus, contexts from guessing locations. *)
Inductive sexpr {R : Type} :=
  | CLit : nat -> sexpr
  | CVar : string -> sexpr
  | CBinOp : bin_op -> R -> R -> sexpr    (* e0 + e1 *)
  | CAccess : R -> R -> sexpr             (* x[e] *)
  | CLetin : string -> R -> R -> sexpr    (* let x = e0 in e1 *)
  | CIf : R -> R -> R -> sexpr            (* if e0 then e1 else e2 *)
  | CAssign : R -> R -> R -> sexpr        (* x[e0] <- e1 *)
  | CNew : R -> sexpr                     (* new e0 *)
  | CDelete : R -> sexpr                  (* delete x *)
.
Inductive lexpr {R : Type} :=
  | CLoc : addr -> lexpr
.
Inductive interface := Interface :> @sexpr interface -> interface.
(** "constructors" *)
Definition ILit n := Interface(CLit n).
Definition IVar x := Interface(CVar x).
Definition IBinOp b e1 e2 := Interface(CBinOp b e1 e2).
Definition IAccess x e := Interface(CAccess x e).
Definition ILetin x e1 e2 := Interface(CLetin x e1 e2).
Definition IIf e0 e1 e2 := Interface(CIf e0 e1 e2).
Definition IAssign x e0 e1 := Interface(CAssign x e0 e1).
Definition INew x := Interface(CNew x).
Definition IDelete x := Interface(CDelete x).
(** Language where the actual statics & dynamics happen *)
Inductive expr :=
  | L : @sexpr expr -> expr
  | R : @lexpr expr -> expr
.
(** "constructors" *)
Definition Lit n := L(CLit n).
Definition Var x := L(CVar x).
Definition BinOp b e1 e2 := L(CBinOp b e1 e2).
Definition Access x e := L(CAccess x e).
Definition Letin x e1 e2 := L(CLetin x e1 e2).
Definition If e0 e1 e2 := L(CIf e0 e1 e2).
Definition Assign x e0 e1 := L(CAssign x e0 e1).
Definition New x := L(CNew x).
Definition Delete x := L(CDelete x).
Definition Loc n := R(CLoc n).

Fixpoint i2d (e : interface) : expr :=
  match e with
  | Interface e' => match e' with
                | CLit x => Lit x
                | CVar x => Var x
                | CBinOp b e1 e2 => BinOp b (i2d e1) (i2d e2)
                | CAccess x e0 => Access (i2d x) (i2d e0)
                | CLetin x e1 e2 => Letin x (i2d e1) (i2d e2)
                | CIf e0 e1 e2 => If (i2d e0) (i2d e1) (i2d e2)
                | CAssign x e1 e2 => Assign (i2d x) (i2d e1) (i2d e2)
                | CNew x => New (i2d x)
                | CDelete x => Delete (i2d x)
                end
  end
.
Coercion i2d : interface >-> expr.
Definition of_val (v : val) : expr :=
  match v with
  | LitV z => Lit z
  end
.
Definition to_val (e : expr) : option val :=
  match e with
  | L(CLit z) => Some (LitV z)
  | _ => None
  end
.
Coercion of_val : val >-> expr.
Definition is_val (e : expr) : Prop :=
  match e with
  | L(CLit _) => True
  | _ => False
  end
.
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. now induction v. Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  revert v; induction e; cbn; intros v H; inv H;
  destruct s; try congruence; now inv H1.
Qed.

Lemma is_val_inv e : is_val e -> { n : nat | e = Lit n }.
Proof.
  induction e; cbn; intro H; try contradiction; destruct s; try contradiction; now exists n.
Qed.

(** ** Evaluation *)
Definition bin_op_eval_int (op : bin_op) (n1 n2 : nat) : nat :=
  match op with
  | PlusOp => n1 + n2
  end
.

Definition Heap := list nat.
Definition LocMap := list (addr * nat).

(**
  State consists of four things:
    1. A way to get unique ids
    2. A heap, modeled as a list of natural numbers
    3. Mapping of unguessable addresses to indexes to things in heap
*)
Record State : Set := {
    fresh : Fresh.fresh_state ;
    H     : Heap ;
    A     : LocMap;
  }.
Definition Conf : Set := (State * expr).

Notation "F0 ';' H0 ';' A0" := ({| fresh := F0 ; H := H0 ; A := A0 |} : State)
                               (at level 80, H0 at next level, A0 at next level).
Notation "?? '???' e" := ((??, e) : Conf) (at level 80, e at next level).
Notation "???" := ((Fresh.empty_fresh) ; (nil) ; (nil) ).

Lemma state_triv_eq ?? :
  ?? = (??.(fresh); ??.(H); ??.(A)).
Proof. destruct ?? as [F H A]; cbn; easy. Qed.

Definition A_lookup (x : addr) (?? : State) :=
  match Util.find (addr_eqb x) ??.(A) with
  | Some n => n
  | None => 1729
  end
.
Definition H_lookup (a : nat) (?? : State) :=
  match List.nth_error ??.(H) a with
  | Some n => n
  | None => 1729
  end
.
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
Fixpoint esubst (x : string) (fore : expr) (ine : expr) : expr :=
  match ine with
  | L ine' =>
    match ine' with
    | CLit _ => ine
    | CVar y => if string_dec x y then fore else Var y
    | CBinOp o e1 e2 => BinOp o (esubst x fore e1) (esubst x fore e2)
    | CAccess y e => Access (esubst x fore y) (esubst x fore e)
    | CLetin y e1 e2 => Letin y (esubst x fore e1) (if string_dec x y then e2 else esubst x fore e2)
    | CIf e1 e2 e3 => If (esubst x fore e1) (esubst x fore e2) (esubst x fore e3)
    | CAssign y e1 e2 => Assign (esubst x fore y) (esubst x fore e1) (esubst x fore e2)
    | CNew y => New (esubst x fore y)
    | CDelete y => Delete (esubst x fore y)
    end
  | R _ => ine (* this is just a location *)
  end
.
Definition deleteLoc {A' : Type} (x : addr) (A : list (addr * A')) :=
  match A with
  | nil => nil
  | (y, v) :: ??' => if addr_eq_dec x y then ??' else (y,v) :: ??' (* delete x ??' *)
  end
.
Reserved Notation "??1 '-[' a ']~>' ??2" (at level 80, a at next level, right associativity).
Inductive base_step : Conf -> Event -> Conf -> Prop :=
| BinOpS : forall ?? n1 n2 o, (?? ??? BinOp o (Lit n1) (Lit n2) -[ Internal ]~> ?? ??? of_val(bin_op_eval_int o n1 n2))
| GetS : forall ?? n loc v nl, A_lookup loc ?? = nl ->
                         H_lookup (nl + n) ?? = v ->
                         (?? ??? Access (Loc loc) (Lit n) -[ Read loc n ]~> ?? ??? Lit v)
| SetS : forall ?? H' n v loc nl, A_lookup loc ?? = nl ->
                            H' = replace (nl + n) ??.(H) v ->
                            (?? ??? Assign (Loc loc) (Lit n) (Lit v) -[ Write loc n ]~> ??.(fresh);H';??.(A) ??? Lit v)
| IfBotS : forall ?? e1 e2, (?? ??? If (Lit 0) e1 e2 -[ Internal ]~> ?? ??? e2)
| IfTopS : forall ?? e1 e2 v, v <> 0 -> (?? ??? If (Lit v) e1 e2 -[ Internal ]~> ?? ??? e1)
| LetSLit : forall ?? x v e, (?? ??? Letin x (Lit v) e -[ Internal ]~> ?? ??? esubst x (Lit v) e)
| LetSLoc : forall ?? x v e, (?? ??? Letin x (Loc v) e -[ Internal ]~> ?? ??? esubst x (Loc v) e)
| DeleteS : forall ?? x loc, (?? ??? Delete x -[ Dealloc loc ]~> ??.(fresh);??.(H);deleteLoc loc ??.(A) ??? Lit 0)
| NewS : forall ?? H' n loc s, s = List.length ??.(H) ->
                         H' = grow ??.(H) n ->
                         loc = LocA(Fresh.fresh ??.(fresh)) ->
                         (?? ??? New (Lit n) -[ Alloc loc n ]~>
                         (Fresh.advance ??.(fresh));H';((loc, s) :: ??.(A)) ??? Loc loc)
where "??0 '-[' a ']~>' ??1" := (base_step ??0 a ??1)
.
#[local]
Hint Constructors base_step : core.

(* evaluation contexts *)
Inductive ectx :=
  | HoleCtx : ectx
  | LBinOpCtx : bin_op -> ectx -> expr -> ectx
  | RBinOpCtx : bin_op -> val -> ectx -> ectx
  | LAccessCtx : ectx -> expr -> ectx
  | RAccessCtx : addr -> ectx -> ectx
  | LetinCtx : string -> ectx -> expr -> ectx
  | LAssignCtx : ectx -> expr -> expr -> ectx
  | RAssignCtx : addr -> ectx -> expr -> ectx
  | AssignVCtx : addr -> val -> ectx -> ectx
  | NewCtx : ectx -> ectx
  | IfCtx : ectx -> expr -> expr -> ectx
.
Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | LBinOpCtx o K' e' => BinOp o (fill K' e) e'
  | RBinOpCtx o v K' => BinOp o v (fill K' e)
  | LAccessCtx K' e' => Access (fill K' e) e'
  | RAccessCtx x K' => Access (Loc x) (fill K' e)
  | LetinCtx x K' e' => Letin x (fill K' e) e'
  | LAssignCtx K' e0 e' => Assign (fill K' e) e0 e'
  | RAssignCtx x K' e' => Assign (Loc x) (fill K' e) e'
  | AssignVCtx x v K' => Assign (Loc x) v (fill K' e)
  | NewCtx K' => New (fill K' e)
  | IfCtx K' e1 e2 => If (fill K' e) e1 e2
  end
.
Fixpoint comp_ectx (K1 K2 : ectx) : ectx :=
  match K1 with
  | HoleCtx => K2
  | LBinOpCtx o K' e => LBinOpCtx o (comp_ectx K' K2) e
  | RBinOpCtx o v K' => RBinOpCtx o v (comp_ectx K' K2)
  | LAccessCtx K' e => LAccessCtx (comp_ectx K' K2) e
  | RAccessCtx x K' => RAccessCtx x (comp_ectx K' K2)
  | LetinCtx x K' e => LetinCtx x (comp_ectx K' K2) e
  | LAssignCtx K' e0 e => LAssignCtx (comp_ectx K' K2) e0 e
  | RAssignCtx x K' e => RAssignCtx x (comp_ectx K' K2) e
  | AssignVCtx x v K' => AssignVCtx x v (comp_ectx K' K2)
  | NewCtx K' => NewCtx (comp_ectx K' K2)
  | IfCtx K' e1 e2 => IfCtx (comp_ectx K' K2) e1 e2
  end
.
Reserved Notation "??1 '=[' a ']~>' ??2" (at level 80, a at next level, right associativity).
Inductive contextual_step : Conf -> Event -> Conf -> Prop :=
| Ectx_step : forall ??1 e1 a ??2 e2 K e1' e2',
    e1 = fill K e1' ->
    e2 = fill K e2' ->
    (??1 ??? e1' -[ a ]~> ??2 ??? e2') ->
    ??1 ??? e1 =[ a ]~> ??2 ??? e2
where "??1 '=[' a ']~>' ??2" := (contextual_step ??1 a ??2)
.
Reserved Notation "??1 '=[' a ']~>*' ??2" (at level 80, a at next level, right associativity).
Inductive steps : Conf -> list Event -> Conf -> Prop :=
| stepsRefl : forall ?? e, steps (?? ??? e) nil (?? ??? e)
| stepsTrans : forall ?? e a as0 ??' e' ??'' e'',
    (?? ??? e =[ a ]~> ??' ??? e') ->
    (??' ??? e' =[ as0 ]~>* ??'' ??? e'') ->
    (?? ??? e =[ a :: as0 ]~>* ??'' ??? e'')
where "??1 '=[' a ']~>*' ??2" := (steps ??1 a ??2)
.
#[local]
Hint Constructors steps contextual_step : core.

Lemma fill_empty e : fill HoleCtx e = e.
Proof. now cbn. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; cbn; congruence. Qed.

Lemma base_contextual_step ?? e a ??' e' :
  ?? ??? e -[ a ]~> ??' ??? e' -> ?? ??? e =[ a ]~> ??' ??? e'.
Proof. apply Ectx_step with HoleCtx; try rewrite fill_empty; trivial. Qed.

Lemma fill_contextual_step ?? e1 a e2 ??' K :
  ?? ??? e1 =[ a ]~> ??' ??? e2 -> ?? ??? (fill K e1) =[ a ]~> ??' ??? (fill K e2).
Proof. intros H; inv H; rewrite !fill_comp; econstructor; try reflexivity; assumption. Qed.

Lemma fill_steps ?? e1 As ??' e2 K :
  ?? ??? e1 =[ As ]~>* ??' ??? e2 -> ?? ??? (fill K e1) =[ As ]~>* ??' ??? (fill K e2).
Proof.
  intros H;
  pose (project := fun a : Conf => match a with | (??, e) => ?? ??? fill K e end);
  change ((fun a b => (project a) =[ As ]~>* (project b)) (?? ??? e1) (??' ??? e2));
  induction H; try eapply stepsRefl;
  eapply stepsTrans; try eapply fill_contextual_step; eassumption.
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


Lemma contextual_step_bin_l ?? e1 o a e1' e2 ??' :
  ?? ??? e1 =[ a ]~> ??' ??? e1' ->
  ?? ??? BinOp o e1 e2 =[ a ]~> ??' ??? BinOp o e1' e2.
Proof. context_intro; context_solver (LBinOpCtx o HoleCtx e2). Qed.

Lemma contextual_step_bin_r ?? e1 o a e2 e2' ??' :
  is_val e1 ->
  ?? ??? e2 =[ a ]~> ??' ??? e2' ->
  ?? ??? BinOp o e1 e2 =[ a ]~> ??' ??? BinOp o e1 e2'.
Proof. context_intro; context_solver (RBinOpCtx o (LitV x) HoleCtx). Qed.

Lemma contextual_step_bin_v ?? e1 o e2 :
  is_val e1 ->
  is_val e2 ->
  { v : expr | ?? ??? BinOp o e1 e2 =[ Internal ]~> ?? ??? v }.
Proof. context_intro; exists (Lit (x0 + x)); context_solver (HoleCtx). Qed.

(*
Lemma contextual_step_access ?? e e' a x ??' :
  ?? ??? e =[ a ]~> ??' ??? e' ->
  ?? ??? Access x e =[ a ]~> ??' ??? Access x e'.
Proof. context_intro; context_solver (AccessCtx x HoleCtx). Qed.
 *)

Lemma contextual_step_letin ?? e e' e0 a x ??' :
  ?? ??? e =[ a ]~> ??' ??? e' ->
  ?? ??? Letin x e e0 =[ a ]~> ??' ??? Letin x e' e0.
Proof. context_intro; context_solver (LetinCtx x HoleCtx e0). Qed.

(*
Lemma contextual_step_assign ?? e e' e0 x a ??' :
  ?? ??? e =[ a ]~> ??' ??? e' ->
  ?? ??? Assign x e e0 =[ a ]~> ??' ??? Assign x e' e0.
Proof. context_intro; context_solver (AssignCtx x HoleCtx e0). Qed.
*)

Lemma contextual_step_assignv ?? e e' v x a ??' :
  is_val v ->
  ?? ??? e =[ a ]~> ??' ??? e' ->
  ?? ??? Assign (Loc x) v e =[ a ]~> ??' ??? Assign (Loc x) v e'.
Proof. context_intro; context_solver (AssignVCtx x (LitV x0) HoleCtx). Qed.

Lemma contextual_step_newctx ?? e e' a ??' :
  ?? ??? e =[ a ]~> ??' ??? e' ->
  ?? ??? New e =[ a ]~> ??' ??? New e'.
Proof. context_intro; context_solver (NewCtx HoleCtx). Qed.

Lemma contextual_step_ifctx ?? e e' e1 e2 a ??' :
  ?? ??? e =[ a ]~> ??' ??? e' ->
  ?? ??? If e e1 e2 =[ a ]~> ??' ??? If e' e1 e2.
Proof. context_intro; context_solver (IfCtx HoleCtx e1 e2). Qed.


Lemma ctx_steps_bin_l ?? e1 o a e1' e2 ??' :
  ?? ??? e1 =[ a ]~>* ??' ??? e1' ->
  ?? ??? BinOp o e1 e2 =[ a ]~>* ??' ??? BinOp o e1' e2.
Proof. context_intro; context_solver (LBinOpCtx o HoleCtx e2). Qed.

Lemma ctx_steps_bin_r ?? e1 o a e2 e2' ??' :
  is_val e1 ->
  ?? ??? e2 =[ a ]~>* ??' ??? e2' ->
  ?? ??? BinOp o e1 e2 =[ a ]~>* ??' ??? BinOp o e1 e2'.
Proof. context_intro; context_solver (RBinOpCtx o (LitV x) HoleCtx). Qed.

(*
Lemma ctx_steps_access ?? e e' a x ??' :
  ?? ??? e =[ a ]~>* ??' ??? e' ->
  ?? ??? Access x e =[ a ]~>* ??' ??? Access x e'.
Proof. context_intro; context_solver (AccessCtx x HoleCtx). Qed.
*)

Lemma ctx_steps_letin ?? e e' e0 a x ??' :
  ?? ??? e =[ a ]~>* ??' ??? e' ->
  ?? ??? Letin x e e0 =[ a ]~>* ??' ??? Letin x e' e0.
Proof. context_intro; context_solver (LetinCtx x HoleCtx e0). Qed.

(*
Lemma ctx_steps_assign ?? e e' e0 x a ??' :
  ?? ??? e =[ a ]~>* ??' ??? e' ->
  ?? ??? Assign x e e0 =[ a ]~>* ??' ??? Assign x e' e0.
Proof. context_intro; context_solver (AssignCtx x HoleCtx e0). Qed.
*)

Lemma ctx_steps_assignv ?? e e' v x a ??' :
  is_val v ->
  ?? ??? e =[ a ]~>* ??' ??? e' ->
  ?? ??? Assign (Loc x) v e =[ a ]~>* ??' ??? Assign (Loc x) v e'.
Proof. context_intro; context_solver (AssignVCtx x (LitV x0) HoleCtx). Qed.

Lemma ctx_steps_newctx ?? e e' a ??' :
  ?? ??? e =[ a ]~>* ??' ??? e' ->
  ?? ??? New e =[ a ]~>* ??' ??? New e'.
Proof. context_intro; context_solver (NewCtx HoleCtx). Qed.

Lemma ctx_steps_ifctx ?? e e' e1 e2 a ??' :
  ?? ??? e =[ a ]~>* ??' ??? e' ->
  ?? ??? If e e1 e2 =[ a ]~>* ??' ??? If e' e1 e2.
Proof. context_intro; context_solver (IfCtx HoleCtx e1 e2). Qed.

Lemma contextual_step_steps ?? a ??' :
  ?? =[ a ]~> ??' -> ?? =[ a :: nil ]~>* ??'.
Proof. intros; destruct ??, ??'; eapply stepsTrans; (eapply stepsRefl + eassumption). Qed.

Lemma lit_steps_inv ??1 v1 ??2 v2 Tr :
  ??1 ??? (Lit v1) =[ Tr ]~>* ??2 ??? Lit v2 ->
  ??1 = ??2 /\ v1 = v2 /\ Tr = nil.
Proof.
  intros H; inv H; repeat split; trivial; inv H4;
  induction K; cbn in *; try inv H7; subst; inv H9.
Qed.

#[local]
Hint Resolve
  base_contextual_step
  contextual_step_bin_l contextual_step_bin_r contextual_step_bin_v (*contextual_step_access*)
  contextual_step_letin
  (*contextual_step_assign*) contextual_step_assignv contextual_step_newctx contextual_step_ifctx
  contextual_step_steps
  ctx_steps_bin_l ctx_steps_bin_r (*ctx_steps_access*) ctx_steps_letin
  (*ctx_steps_assign*) ctx_steps_assignv ctx_steps_newctx ctx_steps_ifctx
  : core
.
Lemma trans_steps ?? ??' ??'' As1 As2 :
  ?? =[ As1 ]~>* ??' -> ??' =[ As2 ]~>* ??'' -> ?? =[ As1 ++ As2 ]~>* ??''
.
Proof.
  induction 1; cbn; intros H; try easy;
  destruct ??''; eapply stepsTrans; try eassumption; apply IHsteps; eassumption.
Qed.

Lemma inv_lit_ctx_step ?? n E ??' e :
  ?? ??? Lit n =[ E ]~> ??' ??? e -> False.
Proof. intros; inv H0; induction K; cbn in *; try inv H6; subst; inv H8. Qed.

Lemma inv_lit_steps ?? n Tr e ??' :
  ?? ??? Lit n =[ Tr ]~>* ??' ??? e -> e = Lit n /\ ?? = ??' /\ Tr = nil.
Proof.
  intros H.
  change ((fun ?? ??' : Conf => fun Tr =>
          let (??, e0) := ?? in
          let (??', e) := ??' in
          e = e0 /\ ?? = ??' /\ Tr = nil) (?? ??? Lit n) (??' ??? e) Tr).
  remember (?? ??? Lit n) as ??.
  remember (??' ??? e) as ??'.
  induction H; inv Heq??; inv Heq??'; eauto; now apply inv_lit_ctx_step in H0.
Qed.

Definition reducible (?? : State) (e : expr) :=
  exists a ??' e', ?? ??? e =[ a ]~> ??' ??? e'
.

(*
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | R _ => true (* locations *)
  | L(CLit _) => true
  | L(CVar x) => bool_In X x
  | L(CBinOp _ e0 e1) => andb (is_closed X e0) (is_closed X e1)
  | L(CAccess e0 e1) => andb (is_closed X e0) (is_closed X e1)
  | L(CLetin x e0 e1) => andb (is_closed X e0) (is_closed (x :: X) e1)
  | L(CIf e0 e1 e2) => andb (andb (is_closed X e0) (is_closed X e1)) (is_closed X e2)
  | L(CAssign e0 e1 e2) => if bool_In X x then (andb (is_closed X e0) (is_closed X e1)) else false
  | L(CNew e0) => (is_closed X e0)
  | L(CDelete x) => bool_In X x
  end
.
Definition closed (X : list string) (e : expr) : Prop := if is_closed X e then True else False.

Lemma closed_equiv_is_closed X e : is_closed X e = true <-> closed X e.
Proof. unfold closed; now rewrite bool_eq_equiv_if. Qed.

Section Closedness.
Import StrListSets StrListSets.Notations.

Lemma closed_weaken X Y e : closed X e -> X ??? Y -> closed Y e.
Proof.
  revert X Y; pattern e; destruct e; try constructor; induction s; unfold closed; cbn; intros; eauto;
  try (rewrite bool_In_equiv_In; rewrite bool_In_equiv_In in H; now apply H0).
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0.
    eapply subset_equiv_bool_in_subset; eassumption.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite bool_and_equiv_prop in H0; rewrite bool_and_equiv_prop;
    destruct H0; split; rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H0, H2; admit.
    (*(eapply IHe1 + eapply IHe2); unfold closed; eassumption.*)
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    apply nested_bool_pred; rewrite bool_and_equiv_prop; split;
    assert (bool_In X s = true \/ bool_In X s = false) as [H2|H2] by (destruct (bool_In X s); auto);
    try (rewrite H2 in H0; eapply subset_equiv_bool_in_subset; try eassumption).
    inv H0.
    rewrite H2 in H0. eapply closed_equiv_is_closed. eapply closed_equiv_is_closed in H0.
    (*eapply IHe; eauto.*) admit.
    rewrite H2 in H0; inv H0.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H0;
    destruct H0; split.
    + rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H0; admit. (*eapply IHe1; eassumption.*)
    + rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H2; admit. (*eapply IHe2; try eassumption; now apply cons_subset.*)
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite !bool_and_equiv_prop in H0; rewrite !bool_and_equiv_prop;
    destruct H0 as [[H2 H3] H4]; repeat split;
    rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H2, H3, H4; admit.
    (* (eapply IHe1 + eapply IHe2 + eapply IHe3); eauto. *)
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    assert (bool_In X s = true \/ bool_In X s = false) as [H2|H2] by (destruct (bool_In X s); auto);
    rewrite H2 in H0. eapply subset_equiv_bool_in_subset in H2; eauto.
    rewrite H2. rewrite bool_and_equiv_prop; split; rewrite bool_and_equiv_prop in H0;
    destruct H0 as [H0a H0b].
    rewrite closed_equiv_is_closed; admit. (* eapply IHe1; rewrite closed_equiv_is_closed in H0a; eauto. *)
    rewrite closed_equiv_is_closed; admit. (* eapply IHe2; rewrite closed_equiv_is_closed in H0b; eauto. *)
    inv H0.
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0;
    rewrite bool_and_equiv_prop; rewrite bool_and_equiv_prop in H0;
    destruct H0; split;
    rewrite <- bool_eq_equiv_if; rewrite <- bool_eq_equiv_if in H0, H2; admit.
    (* (eapply IHe1 + eapply IHe2); eauto using cons_subset. *)
  - rewrite bool_eq_equiv_if; rewrite bool_eq_equiv_if in H0.
    eapply subset_equiv_bool_in_subset; eauto.
Admitted.
Lemma closed_weaken_nil X e : closed nil e -> closed X e.
Proof. intros; eapply closed_weaken; try exact H0; intros ? ?; inv H1. Qed.

End Closedness. *)

(* This is easier to work with to get traces. TODO: make it cofix when adding loops *)
Fixpoint exec (?? : State) (e : expr) : option (State * val * list Event) :=
  None
  (*
  match e with
  | Lit n => Some (??, LitV n, nil)
  | BinOp o e1 e2 =>
      match exec ?? e1 with
      | Some(??1, LitV v1, Tr1) =>
          match exec ??1 e2 with
          | Some(??2, LitV v2, Tr2) => Some (??2, LitV (v1 + v2), Tr1 ++ Tr2 ++ (Internal :: nil))
          | None => None
          end
      | None => None
      end
  | Access x e => match exec ?? e with
                 | Some(??', LitV v, Tr) =>
                   match ??_lookup x ??' with
                   | Some(loc) =>
                       let nl := A_lookup loc ??' in
                       Some (??', LitV (H_lookup (nl + v) ??'), Tr ++ ((Read loc v) :: nil))
                   | _ => None
                   end
                 | None => None
                 end
  | Assign x e1 e2 => match exec ?? e1 with
                     | Some(??1, LitV n, Tr1) =>
                         match exec ??1 e2 with
                         | Some(??2, LitV v, Tr2) =>
                           match ??_lookup x ??2 with
                           | Some(loc) =>
                               let nl := A_lookup loc ??2 in
                               Some ((??2.(fresh); replace (nl + n) ??2.(H) v; ??2.(A); ??2.(??)),
                                     LitV v, Tr1 ++ Tr2 ++ ((Write loc n)::nil))
                           | _ => None
                           end
                         | None => None
                         end
                     | None => None
                     end
  | If e1 e2 e3 => match exec ?? e1 with
                  | Some(??1, LitV v, Tr1) =>
                      match v with
                      | 0 => match exec ??1 e3 with
                            | Some(??3, v3, Tr3) => Some(??3, v3, Tr1 ++ (Internal :: nil) ++ Tr3)
                            | None => None
                            end
                      | S _ => match exec ??1 e2 with
                              | Some(??2, v2, Tr2) => Some(??2, v2, Tr1 ++ (Internal :: nil) ++ Tr2)
                              | None => None
                              end
                      end
                  | None => None
                  end
  | Letin x e1 e2 => match exec ?? e1 with
                    | Some(??1, LitV v1, Tr1) =>
                        match exec (??1.(fresh); ??1.(H); ??1.(A); (x, v1) :: ??1.(??)) e2 with
                        | Some(??2, v2, Tr2) => Some(??2, v2, Tr1 ++ (Internal :: nil) ++ Tr2)
                        | None => None
                        end
                    | None => None
                    end
  | Delete x => match ??_lookup x ?? with
               | Some (loc) => Some ((??.(fresh); ??.(H); ??.(A); delete x ??.(??)), LitV 0, (Dealloc loc)::nil)
               | _ => None
               end
  | New x e1 e2 => match exec ?? e1 with
                  | Some(??1, LitV m, Tr1) =>
                      let loc := LocA(Fresh.fresh (??1.(fresh))) in
                      let s := List.length (??1.(H)) in
                      match exec (Fresh.advance ??1.(fresh); grow ??1.(H) m; (loc,s)::(??1.(A)); (x,loc) :: ??1.(??)) e2 with
                      | Some(??2, v2, Tr2) => Some(??2, v2, Tr1 ++ ((Alloc loc m)::nil) ++ Tr2)
                      | _ => None
                      end
                  | None => None
                  end
  end
  *)
.
Definition compute_trace_prefix (e : expr) : list Event :=
  match exec ??? e with
  | Some(??, v, Tr) => Tr
  | None => nil
  end
.

Ltac exec_reduce_handle_eq_none := (
  match goal with
  | [ H1: match exec ??? ?e with | Some _ => _ | None => None end = _,
     H: exec ??? ?e <> None |- _ ] =>
      let ??a1 := fresh "??a" in
      let v1 := fresh "v" in
      let Tr1 := fresh "Tr" in
    apply Util.not_eq_None_Some in H as [x]; destruct x as [[??a1 [v1]] Tr1];
    rewrite H in H1; cbn in H1
  end;
  match goal with
  | [Ha: (exec ???a ?e = Some (???a', LitV ?v', ?Tr')),
      IH: forall (?? : State) (v : nat) (Tr : list Event) (??' : State),
          exec ?? ?e = Some (??', LitV v, Tr) ->
          (??, ?e) =[ Tr ]~>* (??', Lit v) |- _ ] =>
      specialize (IH ??a v' Tr' ??a' Ha)
  end
).

Ltac exec_reduce := (
  try match goal with
  | [ H: match exec ??? ?e with | Some _ => _ | None => None end = _ |- _ ] =>
      assert (exec ?? e <> None) by (
      let ??a1 := fresh "??a" in
      let v1 := fresh "v" in
      let Tr1 := fresh "Tr" in
      destruct (exec ?? e) as [[[??a1 [v1]]]|]; congruence);
      exec_reduce_handle_eq_none
  | [ H: Some _ = Some _ |- _ ] => inv H
  | [ H : match ?v with | 0 => _ | S _ => _ end = _ |- _ ] => destruct v
  end
).

Lemma exec_is_steps ?? ??' e v Tr :
  exec ?? e = Some (??', LitV v, Tr) ->
  ?? ??? e =[ Tr ]~>* ??' ??? Lit v
.
Proof.
  (*
  revert ?? v Tr ??'; induction e; intros; cbn in H0; inv H0; eauto.
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
    eapply fill_steps with (K:=NewCtx s HoleCtx e2) in IHe1; cbn in IHe1.
    eapply trans_steps; try exact IHe1.
    eapply stepsTrans; try exact IHe2.
    context_solver HoleCtx.
  - repeat exec_reduce; eauto.
  *)
Admitted.

Inductive ty :=
| tyNat : ty
| tyRefnat : ty
.
Lemma ty_eq_dec : forall (x y : ty), { x = y } + { x <> y }.
Proof. intros [] []; firstorder eauto; now right. Qed.
Definition ty_eqb t0 t1 :=
  match t0, t1 with
  | tyNat, tyNat => true
  | tyRefnat, tyRefnat => true
  | _, _ => false
  end
.
Definition Gamma := list (string * ty).

Module GammaSetM <: ListBase.
  Definition A : Type := (string * ty).
  Definition eqb : A -> A -> bool := fun p0 p1 => let (s0,t0) := p0 in
                                              let (s1,t1) := p1 in
                                              andb (String.eqb s0 s1) (ty_eqb t0 t1).
End GammaSetM.
Module GammaSet <: Sets.Sig := Sets.SetTheoryList GammaSetM.


Section Typing.
Import GammaSet GammaSet.Notations.
Lemma find_split (?? : Gamma) x ty :
  find (eqb x) ?? = Some ty -> exists ??', ?? ??? (x,ty)::??'.
Proof.
Admitted.

Lemma delete_is_subset (?? : list (string * ty)) x :
  delete x ?? ??? ??.
Proof.
  induction ??; unfold delete; cbn. try firstorder; cbn. destruct a; intros [s0 t0] H;
  cbn in *; destruct (string_dec x s).
  - subst; now right.
  - specialize (IH?? (s0, t0)); cbn in H; destruct H.
    + now left.
    + right; auto.
Qed.
#[local]
Hint Resolve delete_is_subset : core.

Definition HasPtr x ?? := (Util.find (String.eqb x) ?? = Some tyRefnat).
Definition same_ptrs (??1 ??2 : Gamma) := (??1 ??? ??2). (*/\ (forall x, HasPtr x ??2 -> HasPtr x ??1). *)
#[local]
Instance same_ptrs_refl : Reflexive (same_ptrs).
Proof. intros ?; trivial; easy. Qed.
#[local]
Instance same_ptrs_trans : Transitive (same_ptrs).
Proof. intros ??0 ??1 ??2 H0 H1; firstorder eauto. Qed.
Infix "???" := (same_ptrs) (at level 81).
Reserved Notation "??a '||-' e ':' ?? '=|' ??b" (at level 99, right associativity, e at next level, ?? at level 200).
Inductive check : Gamma -> expr -> ty -> Gamma -> Prop :=
| Tvar : forall x ??, (Util.find (String.eqb x) ?? = Some tyNat) ->
                (?? ||- (Var x) : tyNat =| ??)
| Tnat : forall ?? n, (?? ||- Lit n : tyNat =| ??)
| Tbinop : forall ??1 ??2 ??3 e1 e2 o, (??2 ??? ??1) -> (??2 ??? ??3) ->
                               (??1 ||- e1 : tyNat =| ??2) ->
                               (??2 ||- e2 : tyNat =| ??3) ->
                               (??1 ||- BinOp o e1 e2 : tyNat =| ??3)
| Tget : forall ??1 ??2 e0 e1, (??1 ||- e0 : tyRefnat =| ??2) ->
                         (??1 ||- e1 : tyRefnat =| ??2) ->
                         (??1 ||- Access e0 e1 : tyNat =| ??2)
| Tset : forall ??1 ??2 ??3 e0 e1 e2, (??1 ||- e0 : tyRefnat =| ??2) ->
                               (??1 ||- e1 : tyNat =| ??2) ->
                               (??2 ||- e2 : tyNat =| ??3) ->
                               (??1 ||- Assign e0 e1 e2 : tyNat =| ??3)
| Tlet : forall ??1 ??2 ??3 x e1 e2, (??2 ??? ??1) ->
                   (??1 ||- e1 : tyNat =| ??2) ->
                   ((x,tyNat)::??2 ||- e2 : tyNat =| (x,tyNat)::??3) ->
                   (??1 ||- Letin x e1 e2 : tyNat =| ??3)
| Tletnew : forall ??1 ??2 ??3 e0, (??1 ||- e0 : tyNat =| ??2) ->
                            (??1 ||- New e0 : tyNat =| ??3)
| Tdelete : forall ?? x, (?? ||- Delete x : tyNat =| ??)
| Tif : forall ??1 ??2 ??3 e1 e2 e3, (??2 ??? ??1) ->
                             (??1 ||- e1 : tyNat =| ??2) ->
                             (??2 ||- e2 : tyNat =| ??3) ->
                             (??2 ||- e3 : tyNat =| ??3) ->
                             (??1 ||- If e1 e2 e3 : tyNat =| ??3)
where "??a '||-' e ':' ?? '=|' ??b" := (check ??a e ?? ??b)
.
#[local]
Hint Constructors check : core.

Lemma Texchange ??1 ??1' ??2 ??2' e ty :
  ??1 ??? ??2 -> ??1' ??? ??2' -> (??1 ||- e : ty =| ??1') -> ??2 ||- e : ty =| ??2'.
Proof.
Admitted.

Definition mult_free :=
  New "x"%string (Lit 0)
      (New "y"%string
           (Delete "x"%string)
           (Delete "y"%string)).
Goal (("x"%string, tyNat)::nil ||- mult_free : tyNat =| ("x"%string, tyNat)::nil).
Proof.
  eapply Tletnew. easy. eapply Tnat.
  eapply Tletnew. instantiate (1:=("x"%string, tyNat)::nil); firstorder.
  eapply Tdelete.
  eapply Tdelete.
Qed.

Definition out_of_bounds_program :=
  New "y"%string (Lit 42)
    (Letin "_"%string (Access "y"%string (Lit 1337))
                      (Delete "y"%string)).
Lemma oob_prog_typechecks :
  (("x"%string, tyNat)::nil ||- out_of_bounds_program : tyNat =| ("x"%string, tyNat)::nil).
Proof.
  eapply Tletnew. easy. apply Tnat.
  eapply Tlet. easy.
  apply Tget; try apply Tnat. easy.
  replace (("_"%string, tyNat) :: ("y"%string, tyRefnat) :: ("x"%string, tyNat) :: nil)
     with ((("_"%string, tyNat)::nil) ++ (("y"%string, tyRefnat) :: ("x"%string, tyNat) :: nil)) by now cbn.
  replace (("_"%string, tyNat)::("x"%string, tyNat) :: nil) with
         ((("_"%string,tyNat)::("x"%string, tyNat)::nil) ++ nil) by now cbn.
  eapply Texchange; cbn.
  instantiate (1:=("y"%string,tyRefnat)::("_"%string,tyNat)::("x"%string,tyNat)::nil); firstorder.
  reflexivity.
  apply Tdelete.
Qed.

End Typing.

Module CheckNotation.
  Notation "??a '||-' e ':' ?? '=|' ??b" := (check ??a e ?? ??b) (at level 99, right associativity,
                                                             e at next level,
                                                             ?? at level 200).
  Infix "???" := (same_ptrs) (at level 81).
End CheckNotation.
Section Drop.
  Import CheckNotation StrListSets StrListSets.Notations.
Fixpoint drop {A} (?? : list (string * A)) : list string :=
  match ?? with
  | nil => nil
  | (x,_) :: ??' => x :: (drop ??')
  end
.
(* Relation of typing environment ?? to operational state ?? *)
Definition transmogrifies (?? : Gamma) (?? : State) :=
  drop ?? ??? drop ??.(??) (* add more if necessary *)
.
Infix "~" := (transmogrifies) (at level 78, left associativity).

Instance gamma_trans_flip ?? : Proper (GammaSet.equiv ==> Basics.flip Basics.impl)
                                     (fun ?? : list (string * ty) => ?? ~ ??).
Proof.
Admitted.

Instance equiv_closed_proper e : Proper (GammaSet.equiv ==> Basics.flip Basics.impl)
                                      (fun (?? : Gamma) => closed (drop ??) e).
Proof.
Admitted.
Instance equiv_is_closed_proper e : Proper (GammaSet.equiv ==> Basics.flip Basics.impl)
                                           (fun (?? : Gamma) => is_closed (drop ??) e = true).
Proof.
  intros ??0 ??1 H0 H1; apply closed_equiv_is_closed; pattern ??0; rewrite H0;
  apply closed_equiv_is_closed; easy.
Qed.

Instance equiv_type_judg e ??2 : Proper (GammaSet.equiv ==> Basics.flip Basics.impl)
                                       (fun g : Gamma => g ||- e : tyNat =| ??2).
Proof.
Admitted.

Lemma subset_implies_drop_subset (??1 ??2 : Gamma) :
  (GammaSet.subset ??1 ??2) -> (drop ??1 ??? drop ??2).
Proof.
  induction ??1; cbn; intros H.
  easy.
  destruct a. eapply GammaSet.subset_weak in H as H'. specialize (IH??1 H').
  intros x H1.
  specialize (IH??1 x). apply IH??1.
Admitted.
Lemma drop_subset (??1 ??2 : Gamma) :
  (drop ??1 ??? drop (??1 ++ ??2)) /\ (drop ??2 ??? drop (??1 ++ ??2)).
Proof. induction ??1; try firstorder; destruct a; firstorder. Qed.
Lemma drop_subset_cons a (??1 ??2 : Gamma) :
  (drop ??1 ??? a :: drop (??1 ++ ??2)) /\
  (drop ??2 ??? a :: drop (??1 ++ ??2))
.
Proof. split; induction ??1; try firstorder; destruct a0; firstorder. Qed.


Lemma bool_In_equiv_find_none x (?? : Gamma) :
  (bool_In (drop ??) x = false) <-> (find (eqb x) ?? = None).
Proof.
Admitted.
Lemma bool_In_equiv_find_some x ty (?? : Gamma) :
  (bool_In (drop ??) x = true) <-> (find (eqb x) ?? = Some ty).
Proof.
Admitted.

Lemma closed_typing ?? ??' e ?? :
  (?? ||- e : ?? =| ??') -> closed (drop ??) e.
Proof.
  (*
  intros H; assert (H':=H); dependent induction H; subst; apply closed_equiv_is_closed; cbn.
  - (* var *) eapply bool_In_equiv_find_some; eassumption.
  - (* lit *) easy.
  - (* binop *) apply bool_and_equiv_prop; split; apply closed_equiv_is_closed; destruct e1, e2.
    + eapply closed_weaken. now eapply IHcheck1. intuition.
    + eapply closed_weaken. now eapply IHcheck2. intuition.
      eapply subset_implies_drop_subset, H0.
  - (* access *)
    assert ((bool_In (drop ??1) x = true) \/ (bool_In (drop ??1) x = false)) as [H|H] by
    (destruct (bool_In (drop ??1) x); eauto).
    rewrite H. destruct e; eapply closed_equiv_is_closed, closed_weaken.
    eapply IHcheck; eauto. firstorder.
    apply bool_In_equiv_find_none in H; congruence.
  - (* assign *)
    assert ((bool_In (drop ??1) x = true) \/ (bool_In (drop ??1) x = false)) as [H|H] by
    (destruct (bool_In (drop ??1) x); eauto).
    rewrite H.
    rewrite !bool_and_equiv_prop; repeat split; apply closed_equiv_is_closed.
    destruct e1; eapply closed_weaken.
    now eapply IHcheck1. eapply subset_implies_drop_subset. easy.
    destruct e2; eapply closed_weaken.
    now eapply IHcheck2. eapply subset_implies_drop_subset. eapply H1.
    unfold HasPtr in H0. apply bool_In_equiv_find_none in H; congruence.
  - (* letin *) apply bool_and_equiv_prop; split.
    + rewrite closed_equiv_is_closed. destruct e1; eapply closed_weaken. now eapply IHcheck1.
      intuition.
    + rewrite closed_equiv_is_closed. destruct e2; eapply closed_weaken. now eapply IHcheck2.
      eapply cons_subset. now apply subset_implies_drop_subset.
  - (* new *) apply bool_and_equiv_prop; split.
    + rewrite closed_equiv_is_closed. destruct e1; eapply closed_weaken. now eapply IHcheck1.
      firstorder.
    + rewrite closed_equiv_is_closed. destruct e2; eapply closed_weaken. now eapply IHcheck2.
      eapply cons_subset. now apply subset_implies_drop_subset.
  - (* delete *) destruct (string_dec x x); try congruence.
  - (* if *) rewrite !bool_and_equiv_prop; repeat split; destruct e1, e2, e3.
    + rewrite closed_equiv_is_closed. eapply closed_weaken. now eapply IHcheck1. reflexivity.
    + rewrite closed_equiv_is_closed. eapply closed_weaken. now eapply IHcheck2. now apply subset_implies_drop_subset.
    + rewrite closed_equiv_is_closed. eapply closed_weaken. now eapply IHcheck3. now apply subset_implies_drop_subset.
  *)
Admitted.

Lemma subset_delete (?? : Gamma) (?? : State) (x : string) :
  drop ?? ??? drop (??.(??)) -> drop (delete x ??) ??? drop(delete x (??.(??))).
Proof.
Admitted.

End Drop.

Lemma cons_read_same x v ?? :
  H_lookup x (??.(fresh); v :: (??.(H)); ??.(A); ??.(??)) = v -> H_lookup (S x) (??.(fresh); v :: v :: (??.(H)); ??.(A); ??.(??)) = v.
Proof. revert v ??; induction x; intros; cbn in *; trivial. Qed.

Section TypeSafety.
  Import CheckNotation GammaSet GammaSet.Notations.
Ltac inv_check_intro := (intros H; match goal with
                        | [H: (_ ||- ?e : _ =| _) |- _] =>
                            let e3 := fresh "e" in
                            assert (H':=H); remember (e) as e3; dependent induction H;
                            try congruence
                        end).
Ltac boring := (
  repeat match goal with
  | [H: exists ?? : State, reducible ?? ?e |- exists ??' : State, reducible ??' _] =>
      let x0 := fresh "??" in
      let x1 := fresh "a" in
      let x2 := fresh "??" in
      let x3 := fresh "e" in
      destruct H as [x0 [x1 [x2 [x3 H]]]]
  end;
  repeat match goal with
  | [H: nth_error nil ?n = Some _ |- _] =>
      induction n; cbn in *; congruence
  | [H: (???, Lit ?n) =[ ?TR ]~>* (???'', Lit ?n') |- _] =>
      apply lit_steps_inv in H as [Ha [Hb Hc]]; subst
  | [H: Lit ?v = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: Var ?v = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: BinOp _ _ _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: Access _ _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: Letin _ _ _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: If _ _ _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: Assign _ _ _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: New _ _ _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: Delete _ = fill ?K ?e |- _] => induction K; cbn in *; try congruence; subst
  | [H: ???0 ??? ???1 |- _] => apply GammaSet.equiv_is_equal in H
  | [H: _ |- ???0 ??? ???1] => apply GammaSet.equiv_is_equal
  | [H: ??? ??? nil |- _] => eapply subset_nil in H; inv H
  | [H: ??? ??? nil |- _] => eapply subset_nil in H; inv H
  | [H: _ ||- Lit _ : _ =| _ |- _] => inv H
  end
).

Ltac solve_progress_case Ctx := (
  match goal with
  | [H: exists ?? : State, reducible ?? ?e |- exists ??' : State, reducible ??' _] =>
      let x0 := fresh "??" in
      let x1 := fresh "a" in
      let x2 := fresh "??" in
      let x3 := fresh "e" in
      destruct H as [x0 [x1 [x2 [x3 H]]]];
      do 4 eexists;
      eapply fill_contextual_step with (K:=Ctx) in H;
      eauto
  end
).

Lemma progress e ?? :
  (nil ||- e : ?? =| nil) -> is_val e \/ exists ??, reducible ?? e.
Proof.
  intros H; assert (H':=H);
  remember nil as ??;
  induction H; subst.
  - (* var *) now cbn in H0.
  - (* lit *) now left.
  - (* binop *)
    inv H'; apply GammaSet.subset_nil in H1, H7; subst; clear H9.
    specialize (IHcheck1 eq_refl H10); specialize (IHcheck2 eq_refl H12); clear H3 H2 H0;
    right; destruct (IHcheck1), (IHcheck2); get_values; subst.
    + exists ???; do 3 eexists; context_solver HoleCtx.
    + solve_progress_case (RBinOpCtx o (LitV x) HoleCtx).
    + solve_progress_case (LBinOpCtx o HoleCtx (Lit x)).
    + boring; exists ??2; exists a0; exists ??3; exists (BinOp o e0 e2).
      clear H1; context_solver (LBinOpCtx o HoleCtx e2).
  - (* access *)
    inv H'; clear H1; specialize (IHcheck eq_refl H6);
    right; destruct (IHcheck); get_values; subst.
    + inv H5. (* TODO: This should not be trivial! I guess the string position needs to be replaced by a location *)
    + solve_progress_case (AccessCtx x HoleCtx).
  - (* assign *)
    inv H'; inv H7.
  - (* letin *)
    inv H'; clear H1; apply GammaSet.subset_nil in H7; subst. admit.
  - (* new *)
    inv H'; clear H1; apply GammaSet.subset_nil in H7; subst. admit.
  - (* delete *) right; exists (empty_fresh; nil; nil; (x,(LocA 0))::nil); do 3 eexists; context_solver HoleCtx;
    econstructor; cbn; now rewrite String.eqb_refl. Unshelve. exact (LocA 0).
  - (* if *)
    inv H'; clear H1. apply GammaSet.subset_nil in H7; subst. admit.
Admitted.

Lemma progress_steps e ?? :
  (nil ||- e : ?? =| nil) -> exists ?? ??' Tr v, (?? ??? e =[ Tr ]~>* ??' ??? v) \/ is_val v.
Proof.
  intros; apply progress in H0 as [H0|H0].
  - do 2 exists ???; exists nil; get_values; boring; subst; exists (Lit x); repeat constructor.
  - destruct H0 as [?? [E [??' [e' H0]]]]; exists ??; exists ??'; exists (E :: nil); exists e'; left; eapply stepsTrans; try eassumption; eapply stepsRefl.
Qed.

End TypeSafety.

Section Inversions.
  Import CheckNotation.
Lemma closed_implies_typing e :
  closed nil e -> exists ?? : ty, nil ||- e : ?? =| nil.
Proof.
Admitted.

Lemma binop_ctx_step_inv ??1 b e1 e2 ??3 v E :
  ??1 ??? BinOp b e1 e2 =[ E ]~> ??3 ??? Lit v ->
  exists v1 v2, (e1 = Lit v1 /\ e2 = Lit v2 /\ E = Internal /\ v = bin_op_eval_int b v1 v2)
.
Proof.
Admitted.

Lemma binop_ctx_step_inv_extra ??1 b e1 e2 ??3 Tr e :
  ??1 ??? BinOp b e1 e2 =[ Tr ]~> ??3 ??? e ->
  (exists v, e = Lit v) \/
  (exists ??1' Tr1 e1', (??1 ??? e1 =[ Tr1 ]~> ??1' ??? e1') /\ e = BinOp b e1' e2) \/
  (exists ??2' Tr2 e2', (??1 ??? e2 =[ Tr2 ]~> ??2' ??? e2') /\ e = BinOp b e1 e2')
.
Proof.
Admitted.

Lemma binop_steps_lits_inv ??1 b ??3 v1 v2 v Tr :
  ??1 ??? BinOp b (Lit v1) (Lit v2) =[ Tr ]~>* ??3 ??? Lit v ->
  ??1 = ??3 /\ v = v1 + v2 /\ Tr = Internal :: nil.
Proof.
Admitted.

Lemma binop_steps_inv ??1 b e1 e2 ??3 v Tr :
  ??1 ??? BinOp b e1 e2 =[ Tr ]~>* ??3 ??? Lit v ->
  exists ??2 Tr1 Tr2 v1 v2, ((??1 ??? e1 =[ Tr1 ]~>* ??2 ??? Lit v1) /\ (??2 ??? e2 =[ Tr2 ]~>* ??3 ??? Lit v2)
/\ Tr = Tr1 ++ Tr2 ++ Internal :: nil /\ v = bin_op_eval_int b v1 v2)
.
Proof.
Admitted.

Lemma access_steps_inv ??1 ??3 es e v Tr :
  ??1 ??? Access es e =[ Tr ]~>* ??3 ??? Lit v ->
  exists s ??' Tr' loc v1, ((??1 ??? e =[ Tr' ]~>* ??' ??? Lit v1) /\ (es = s)
/\ (??3 = ??' /\ v = H_lookup (A_lookup loc ??' + v1) ??')
/\ ??_lookup s ??' = Some(loc) /\ Tr = Tr' ++ Read loc v1 :: nil)
.
Proof.
Admitted.

Lemma letin_steps_inv ??1 ??3 s e1 e2 v Tr :
  ??1 ??? Letin s e1 e2 =[ Tr ]~>* ??3 ??? Lit v ->
  exists ??2 Tr1 Tr2 v1 v2, (??1 ??? e1 =[ Tr1 ]~>* ??2 ??? Lit v1)
/\ ((??2.(fresh); ??2.(H); ??2.(A); ??2.(??)) ??? e2 =[ Tr2 ]~>* ??3 ??? Lit v2) /\ v = v2 /\ Tr = Tr1 ++ Internal :: Tr2
.
Proof.
Admitted.

Lemma if_steps_inv ?? ??' e1 e2 e3 v Tr :
  ?? ??? If e1 e2 e3 =[ Tr ]~>* ??' ??? Lit v ->
  exists v1 Tr1 ??1, ((?? ??? e1 =[ Tr1 ]~>* ??1 ??? Lit v1) /\ (
    (v1 <> 0 /\ exists v2 Tr2 ??2, (??1 ??? e2 =[ Tr2 ]~>* ??2 ??? Lit v2) /\ v = v2 /\ Tr = Tr1 ++ Internal :: Tr2 /\ ??' = ??2)
  \/ (v1 = 0 /\ exists v3 Tr3 ??3, (??1 ??? e3 =[ Tr3 ]~>* ??3 ??? Lit v3) /\ v = v3 /\ Tr = Tr1 ++ Internal :: Tr3 /\ ??' = ??3)
  ))
.
Proof.
Admitted.

Lemma assign_steps_inv ?? ??' es e1 e2 v Tr :
  ?? ??? Assign es e1 e2 =[ Tr ]~>* ??' ??? Lit v ->
  exists s v1 Tr1 ??1 v2 Tr2 ??2 loc, (?? ??? e1 =[ Tr1 ]~>* ??1 ??? Lit v1) /\ (??1 ??? e2 =[ Tr2 ]~>* ??2 ??? Lit v2)
/\ (es = s) /\ ((??_lookup s ??2 = Some(loc)
                             /\ Tr = Tr1 ++ Tr2 ++ Write loc v1 :: nil /\ v = v2 /\ ??'.(fresh) = ??2.(fresh)
                             /\ ??'.(H) = replace (A_lookup loc ??2 + v1) ??2.(H) v2 /\ ??'.(A) = ??2.(A) /\ ??'.(??) = ??2.(??)))
.
Proof.
Admitted.

Lemma new_steps_inv ?? ??' s e1 e2 v Tr :
  ?? ??? New s e1 e2 =[ Tr ]~>* ??' ??? Lit v ->
  exists v1 Tr1 ??1 v2 Tr2 ??2, (?? ??? e1 =[ Tr1 ]~>* ??1 ??? Lit v1)
/\ (((Fresh.advance (??1.(fresh)); grow ??1.(H) v1;
     (LocA(Fresh.fresh ??1.(fresh)), List.length ??1.(H)) :: (??1.(A)); (s,(LocA(Fresh.fresh (??1.(fresh))))) :: (??1.(??))
                                ??? e2 =[ Tr2 ]~>* ??2 ??? Lit v2)
/\  ??' = ??2 /\ v = v2 /\ Tr = Tr1 ++ Alloc (LocA(Fresh.fresh(??1.(fresh)))) v1 :: Tr2))
.
Proof.
Admitted.

Lemma delete_steps_inv ?? ??' x Tr v :
  ?? ??? Delete x =[ Tr ]~>* ??' ??? Lit v ->
  exists loc, (??_lookup x ?? = Some(loc)
      /\ ??' = (??.(fresh); ??.(H); ??.(A); delete x ??.(??)) /\ v = 0 /\ Tr = Dealloc loc :: nil
  ).
Proof.
Admitted.

Lemma preservation_base e e' ?? ??' a ty :
  (nil ||- e : ty =| nil) ->
  (?? ??? e -[ a ]~> ??' ??? e') ->
  (nil ||- e' : ty =| nil)
.
Proof.
  (*
  intros H2 H0 H1; assert (H1' := H1); assert (H0' := H0).
  change ((fun (?? : Conf) =>  let (??, _)   := ??  in ??0 ~ ??) (?? ??? e)) in H2.
  change ((fun (?? : Conf) =>  let (_, e)   := ??  in ??0 ||- e : ty =| ??2) (?? ??? e)) in H0, H0'.
  change ((fun (??' : Conf) => let (??1, e') := ??' in exists ??1 ??2' : Gamma, (??1 ||- e' : ty =| ??2') /\ ??1 ~ ??1 /\ (??2 ??? ??2')) (??' ??? e')).
  induction H1.
  - (* var *) inv H0'. apply find_split in H5 as [??2' H5].
    do 2 exists ((x,tyNat)::??2'); repeat split; eauto; try firstorder.
    pattern ((x,tyNat)::??2'); now rewrite <- H5.
  - (* binop *) inv H0; boring.
    exists ??2; eauto using Tnat.
  - (* access *) inv H0; boring.
    do 2 exists ??2; repeat split; eauto using Tnat; reflexivity.
  - (* assign *) inv H0; boring.
    do 2 exists ??2; eauto using Tnat.
  - (* ifF *) inv H0; boring.
    exists ??3; exists ??2; eauto using Tnat; firstorder.
  - (* ifT *) inv H0; boring.
    exists ??3; exists ??2; eauto using Tnat; firstorder.
  - (* let *) inv H0; boring.
    exists ((x,tyNat)::??3); exists ((x,tyNat) :: ??2); repeat split; eauto.
    now eapply cons_subset. firstorder.
  - (* delete *) inv H0'. do 2 exists ??2; repeat split. now constructor.
    unfold "_ ~ _"; cbn.
    replace (drop ??2) with (drop (delete x ((x,tyRefnat)::??2))) by (cbn; destruct (string_dec x x); congruence).
    now eapply subset_delete. reflexivity.
  - (* new *) inv H0; boring.
    exists ((x,tyRefnat)::??3); exists ??2; repeat split; eauto.
    now eapply cons_subset. reflexivity.
Qed.*)
Admitted.

Definition ectx_check (K : ectx) A B :=
  forall e, (nil ||- e : A =| nil) ->
       (nil ||- (fill K e) : B =| nil).

Lemma preservation_composition e K A B:
  (ectx_check K A B) ->
  (nil ||- e : A =| nil) ->
  (nil ||- fill K e : B =| nil).
Proof. intros H0 H1; eauto. Qed.

Lemma preservation_decomposition e K B :
  (nil ||- fill K e : B =| nil) ->
  exists A, (ectx_check K A B) /\ (nil ||- e : A =| nil).
Proof.
  (*
  unfold ectx_check; induction K in e |-*; simpl; eauto.
  all: inversion 1; subst; boring; edestruct IHK as [? [Hit Hty]]; eauto;
       eexists; split; intros; try eassumption; econstructor; try easy; now eapply Hit.
  Unshelve.
  all: try exact ""%string.
  *)
Admitted.
Lemma preservation e e' ?? ??' a ty :
  (nil ||- e : ty =| nil) ->
  (?? ??? e =[ a ]~> ??' ??? e') ->
  (nil ||- e' : ty =| nil)
.
Proof.
  intros H0 H1; inv H1.
  eapply preservation_decomposition in H0 as [ty' [H0a H0b]].
  eapply preservation_base in H0b; try eassumption.
  eapply preservation_composition; eauto.
Qed.

Lemma preservation_star e e' ?? ??' a ty :
  (nil ||- e : ty =| nil) ->
  (?? ??? e =[ a ]~>* ??' ??? e') ->
  (nil ||- e' : ty =| nil)
.
Proof.
  intros H0 H1; assert (H1' := H1); pattern e in H0;
  change ((fun x : Conf =>
             let (_, e) := x in
             (nil ||- e : ty =| nil)
          ) (?? ??? e)) in H0.
  remember (?? ??? e) as ??;
  pattern e';
  change ((fun x : Conf =>
            let (??', e0) := x in
            (nil ||- e0 : ty =| nil)
         ) (??' ??? e'));
  remember (??' ??? e') as ??'.
  clear Heq?? Heq??'; revert ty H0; dependent induction H1; intros ty H0'; trivial.
  - eapply preservation in H0; eauto.
Qed.


Inductive WhileProgram :=
| WProg : forall e, closed nil (i2d e) -> WhileProgram
.
Inductive WhileComponent :=
| WComp : forall e, closed ("x"%string :: nil) (i2d e) -> WhileComponent
.
Inductive WhileContext :=
| WCtx : forall e0 e1, closed nil (i2d e0) -> closed ("y"%string :: nil) (i2d e1) -> WhileContext
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
                       | WComp ep Hp => WProg (ILetin ("y"%string) (ILetin ("x"%string) e0 ep) e1)
                                             (contexts_closed e0 ep e1 H0 H1 Hp)
                       end
  end
.
Inductive whole_program_check : WhileProgram -> Type :=
| WProgCheck : forall e t (H : nil ||- i2d e : tyNat =| nil), whole_program_check (WProg e t)
.
Inductive component_check : WhileComponent -> Type :=
| WCompCheck : forall e (H : ((("x"%string, tyNat)::nil) ||- i2d e : tyNat =| ("x"%string, tyNat)::nil)),
               component_check (WComp e (closed_typing H))
.
Inductive context_check : WhileContext -> Type :=
| WCtxCheck : forall e0 e1 (H0 : (nil ||- i2d e0 : tyNat =| nil))
                      (H1 : ((("y"%string, tyNat) :: nil) ||- i2d e1 : tyNat =| ("y"%string, tyNat) :: nil)),
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
  intros H H0; destruct c, H, H0; cbn. econstructor; trivial.
  change (nil ++ nil ||- Letin "y" (Letin "x" e2 e) e3 : tyNat =| nil ++ nil).
  eapply Tlet.
  - eapply Tlet; now cbn.
  - assumption.
  - reflexivity.
Defined.
Definition prog2trace (p : WhileProgram) : Trace := wprog2tracepref p.

Definition wsat (p : WhileProgram) (H : whole_program_check p) (?? : Trace -> Prop) : Prop := ?? (prog2trace p).
Definition wrsat (p : WhileComponent) (H0 : component_check p) (?? : Trace -> Prop) : Prop :=
  forall (c : WhileContext) (H1 : context_check c), @wsat (plug c p) (@plug_checks_propagate c p H1 H0) ??
.

(** Returns the suffix starting at the nth position in the given trace t. *)
Fixpoint sufftr (n : nat) (t : list Event) :=
  match n,t with
  | 0,t' => t'
  | _,nil => nil
  | S n',_ :: t' => sufftr n' t'
  end
.
Lemma base_alloc_yields_new e e' ?? ??' loc s :
  ?? ??? e -[ Alloc loc s ]~> ??' ??? e' ->
  exists x e2, e = New x (Lit s) e2 /\ ??_lookup x ??' = Some (loc) /\ e' = e2.
Proof.
  intros H; inv H; boring.
  exists x; exists e'; cbn; split; trivial.
  rewrite eqb_refl; now cbn.
Qed.
Lemma ctx_alloc_yields_new e e' ?? ??' loc s :
  ?? ??? e =[ Alloc loc s ]~> ??' ??? e' ->
  exists K x e2, e = fill K (New x (Lit s) e2) /\ ??_lookup x ??' = Some (loc) /\
            e' = fill K e2.
Proof.
  intros H; inv H; boring; apply base_alloc_yields_new in H7 as [x [e2 [H0a [H0b H0c]]]];
  exists K; subst; eauto.
Qed.
Lemma steps_alloc_yields_new e e' ?? ??' Tr loc s :
  ?? ??? e =[ Tr ]~>* ??' ??? e' ->
  List.nth_error Tr 0 = Some (Alloc loc s) ->
  exists ??'' K x e2, e = fill K (New x (Lit s) e2) /\ ??_lookup x ??'' = Some (loc)
   /\ (?? ??? e =[ Alloc loc s ]~> ??'' ??? fill K e2)
   /\ ??'' ??? fill K e2 =[ List.tail Tr ]~>* ??' ??? e'.
Proof.
  intros H0 H1; inv H0; boring;
  cbn in H1; inv H1;
  exists ??'0;
  edestruct ctx_alloc_yields_new as [K [x [e2 [H0a [H0b H0c]]]]]; cbn; subst; eauto;
  exists K; exists x; exists e2; repeat split; subst; eauto.
Qed.
Lemma steps_alloc_yields_new_inbetween e e' ?? ??' Tr loc s n :
  ?? ??? e =[ Tr ]~>* ??' ??? e' ->
  List.nth_error Tr n = Some (Alloc loc s) ->
  exists ??1 ??2 Tr' K x e2, (?? ??? e =[ Tr' ]~>* ??1 ??? (fill K (New x (Lit s) e2)))
          /\ (??1 ??? fill K (New x (Lit s) e2) =[ Alloc loc s ]~> ??2 ??? fill K e2)
          /\ ??_lookup x ??2 = Some (loc)
          /\ ??2 ??? fill K e2 =[ sufftr (S n) Tr ]~>* ??' ??? e'.
Proof.
  intros H0 H1.
  revert Tr ?? ??' e e' H0 H1; induction n; intros Tr ?? ??' e e' H0 H1.
  - edestruct steps_alloc_yields_new as [??'' [K [x [e2 [H2a [H2b [H2c H2d]]]]]]]; eauto;
    do 7 eexists; subst; repeat split; eauto.
  - inv H0; boring; cbn in *;
    specialize (IHn as0 ??'0 ??' e'0 e' H8 H1);
    destruct IHn as [??1 [??2 [Tr' [K [x [e2 [IHa [IHb [IHc IHd]]]]]]]]];
    do 7 eexists; eauto.
Qed.

Lemma base_dealloc_yields_delete e e' ?? ??' loc :
  ?? ??? e -[ Dealloc loc ]~> ??' ??? e' ->
  exists x, e = Delete x /\ ??_lookup x ?? = Some (loc) /\ e' = (Lit 0).
Proof.
  intros H; inv H; boring.
  exists x; cbn; repeat split; trivial.
Qed.
Lemma ctx_dealloc_yields_delete e e' ?? ??' loc :
  ?? ??? e =[ Dealloc loc ]~> ??' ??? e' ->
  exists K x, e = fill K (Delete x) /\ ??_lookup x ?? = Some (loc) /\
         e' = fill K (Lit 0).
Proof.
  intros H; inv H; boring; apply base_dealloc_yields_delete in H7 as [x [H0a [H0b H0c]]];
  exists K; subst; eauto.
Qed.
Lemma steps_dealloc_yields_delete e e' ?? ??' Tr loc :
  ?? ??? e =[ Tr ]~>* ??' ??? e' ->
  List.nth_error Tr 0 = Some (Dealloc loc) ->
  exists ??'' K x, e = fill K (Delete x) /\ ??_lookup x ?? = Some (loc)
   /\ (?? ??? e =[ Dealloc loc ]~> ??'' ??? fill K (Lit 0))
   /\ ??'' ??? fill K (Lit 0) =[ List.tail Tr ]~>* ??' ??? e'.
Proof.
  intros H0 H1. inv H0; boring.
  cbn in H1; inv H1.
  exists ??'0.
  edestruct ctx_dealloc_yields_delete as [K [x [H0a [H0b H0c]]]]; cbn; subst; eauto.
  exists K; exists x; repeat split; subst; eauto.
Qed.
Lemma steps_dealloc_yields_delete_inbetween e e' ?? ??' Tr loc n :
  ?? ??? e =[ Tr ]~>* ??' ??? e' ->
  List.nth_error Tr n = Some (Dealloc loc) ->
  exists ??1 ??2 Tr' K x, (?? ??? e =[ Tr' ]~>* ??1 ??? (fill K (Delete x)))
          /\ (??1 ??? fill K (Delete x) =[ Dealloc loc ]~> ??2 ??? fill K (Lit 0))
          /\ ??_lookup x ??1 = Some (loc)
          /\ ??2 ??? fill K (Lit 0) =[ sufftr (S n) Tr ]~>* ??' ??? e'.
Proof.
  intros H0 H1.
  revert Tr ?? ??' e e' H0 H1; induction n; intros Tr ?? ??' e e' H0 H1.
  - edestruct steps_dealloc_yields_delete as [??'' [K [x [H2a [H2b [H2c H2d]]]]]]; eauto;
    do 6 eexists; subst; repeat split; eauto.
  - inv H0; boring; cbn in *.
    specialize (IHn as0 ??'0 ??' e'0 e' H8 H1).
    destruct IHn as [??1 [??2 [Tr' [K [x [IHa [IHb [IHc IHd]]]]]]]].
    do 6 eexists; eauto.
Qed.

Lemma trace_split (Tr : list Event) n ev :
  List.nth_error Tr n = Some ev ->
  exists Tr0 Tr1, Tr = Tr0 ++ ev :: Tr1 /\ List.length Tr0 = n.
Proof.
  intros H; apply nth_error_split in H as [Tr0 [Tr1 []]];
  do 2 eexists; eauto.
Qed.
Lemma refnat_in_type_means_dealloc_is_in_there x ?? e ?? ?? loc:
  ((x, tyRefnat) :: ?? ||- e : ?? =| ??) ->
  ??_lookup x ?? = Some loc ->
  exists ??' K Tr, (?? ??? e =[ Tr ]~>* ??' ??? (fill K (Delete x))).
Proof.
Admitted.

Lemma combine_steps ??0 ??1 e Tr Tr' ??0' ??1' e'' K K' v ev e''' :
  (??0 ??? fill K e =[ Tr ]~>* ??0' ??? Lit v) ->
  (??0 ??? e =[ Tr' ]~>* ??1 ??? fill K' e'') ->
  (??1 ??? fill K' e'' =[ ev ]~> ??1' ??? fill K' e''') ->
  exists Tr'', ??0 ??? fill K e =[ Tr' ++ ev :: Tr'']~>* ??0' ??? Lit v.
Proof.
Admitted.

Lemma ??_lookup_carries ?? ??' x loc e Tr K :
  ??_lookup x ?? = Some loc ->
  (?? ??? e =[ Tr ]~>* ??' ??? fill K (Delete x)) ->
  ??_lookup x ??' = Some loc.
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

Lemma deterministic_events ?? e Tr ??' e' Tr' :
  ?? ??? e -[ Tr ]~> ??' ??? e' ->
  ?? ??? e -[ Tr' ]~> ??' ??? e' ->
  Tr = Tr'.
Proof.
  revert ?? ??' e' Tr Tr'; induction e; intros; inv H0; inv H1; boring; trivial.
  - rewrite H7 in H6; inv H6; easy.
  - rewrite H7 in H6; inv H6; easy.
  - rewrite H5 in H4; inv H4; easy.
Qed.
Lemma deterministic_ctx_events ?? e Tr ??' e' Tr' :
  ?? ??? e =[ Tr ]~> ??' ??? e' ->
  ?? ??? e =[ Tr' ]~> ??' ??? e' ->
  Tr = Tr'.
Proof.
  revert ?? ??' e' Tr Tr'; induction e; intros.
  - inv H0; inv H1; boring; eapply deterministic_events; try exact H9; exact H10.
  - inv H0; inv H1; boring; eapply deterministic_events; try exact H9; exact H10.
Admitted.
Lemma deterministic_traces ?? e Tr ??' e' Tr' :
  ?? ??? e =[ Tr ]~>* ??' ??? e' ->
  ?? ??? e =[ Tr' ]~>* ??' ??? e' ->
  Tr = Tr'.
Proof.
Admitted.

Lemma nth_error_list_skip (Tr1 Tr2 : Trace) :
  List.nth_error (Tr1 ++ Tr2) (List.length Tr1) = List.nth_error Tr2 0.
Proof. induction Tr1; cbn; trivial. Qed.

Lemma while_is_not_spat_memsafe :
  ~ (forall (p : WhileComponent) (H : component_check p), wrsat H spat_memsafe).
Proof.
  intros H.
  remember out_of_bounds_program as p.
  assert (H0 := oob_prog_typechecks); rewrite <- Heqp in H0.
  assert (component_check (WComp p (closed_typing H0))) by econstructor.
  specialize (H (WComp p (closed_typing H0)) H1).

  unfold wrsat in H.
  assert (nil ||- Lit 0 : tyNat =| nil) by econstructor.
  assert ((("y"%string, tyNat) :: nil) ||- Lit 0 : tyNat =| (("y"%string, tyNat)::nil)) by econstructor.
  assert (context_check (WCtx (Lit 0) (Lit 0) (closed_typing H2) (closed_typing H3))) by econstructor.
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

Lemma while_alloc_before_dealloc ?? ??' ?? ?? ??' Tr e v loc s :
  (?? ||- e : ?? =| ??') ->
  (?? ??? e =[ Tr ]~>* ??' ??? (Lit v)) ->
  after_another_event (Alloc loc s) (Dealloc loc) Tr.
Proof.
  intros H0 H1; unfold after_another_event.
  intros n H2; assert (H2' := H2); eapply trace_split in H2 as [Tr1 [Tr2 [H2a H2b]]]; subst.
  assert (H1' := H1);
  eapply steps_alloc_yields_new_inbetween in H1 as [??'' [??''' [Tr [K [y [x [e2 [H1a [H1b [H1c H1d]]]]]]]]]];
  try eapply H2'.
  eapply preservation_star in H1a as [??0 [H2a H2b]]; try exact H0.
  eapply preservation_decomposition in H2a as [ty' [??1 [H3a [H3b H3c]]]].
  (* inversion lemma of Tnew *)
  eapply refnat_in_type_means_dealloc_is_in_there in H8 as H8'; try exact H1c.
  destruct H8' as [??2' [K2 [Tr2' H9']]].
  remember (??2'.(fresh);??2'.(H);??2'.(A);(delete x ??2'.(??))) as ??2''.
  assert (??2' ??? fill K2 (Delete x) =[ Dealloc loc ]~> ??2'' ??? fill K2 (Lit 0)) by
  (econstructor; eauto; subst; econstructor; eapply ??_lookup_carries; eauto).
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


Lemma while_is_temp_memsafe (p : WhileComponent) (H : component_check p) :
  wrsat H temp_memsafe.
Proof.
  destruct p; destruct H as [e' H??].
Admitted.
