Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef Lia.
Require Import CSC.Shared.Fresh CSC.Shared.Sema CSC.Util.Sets CSC.Shared.Props CSC.Util.HasEquality.
Require Import CSC.Util.Convenience CSC.Util.NoDupInv CSC.Shared.Trace.

From RecordUpdate Require Import RecordSet.

Require Import CSC.Lirl.syntax.

(** Type for list of relevant functions, i.e. those that are part of the component. *)
Definition commlib := list vart.
(** Fill hole in evaluation context. *)
Fixpoint insert (K : evalctx) (withh : expr) : expr :=
  let R := fun k => insert k withh in
  match K with
  | Khole => withh
  | KbinopL b K' e => Xbinop b (R K') e
  | KbinopR b v K' => Xbinop b (Xval v) (R K')
  | KgetL K' e0 e1 => Xget (R K') e0 e1
  | KgetM v K' e => Xget (Xval v) (R K') e
  | KgetR v0 v1 K' => Xget (Xval v0) (Xval v1) (R K')
  | KsetL K' e0 e1 e2 => Xset (R K') e0 e1 e2
  | KsetM0 v K' e0 e1 => Xset (Xval v) (R K') e0 e1
  | KsetM1 v0 v1 K' e => Xset (Xval v0) (Xval v1) (R K') e
  | KsetR v0 v1 v2 K' => Xset (Xval v0) (Xval v1) (Xval v2) (R K')
  | Klet x K' e => Xlet x (R K') e
  | KnewL γ K' e => Xnew γ (R K') e
  | KnewR γ v K' => Xnew γ (Xval v) (R K')
  | Kdel K' => Xdel (R K')
  | Kunpack γ x K' e => Xunpack γ x (R K') e
  | KpackL K' e => Xpack (R K') e
  | KpackR ℓ K' => Xpack (Xval ℓ) (R K')
  | KpairL K' e => Xpair (R K') e
  | KpairR v K' => Xpair (Xval v) (R K')
  | Kunpair x1 x2 K' e => Xunpair x1 x2 (R K') e
  | Kifz K' e0 e1 => Xifz (R K') e0 e1
  | Kreturn K' => Xreturn (R K')
  | Kcall foo K' => Xcall foo (R K')
  | Khas K' t => Xhas (R K') t
  | Kispoisoned K' => Xispoisoned (R K')
  end
.
(* A "dynamic" location contains the location and its poison *)
Record dynloc : Type := mkdL {
  dρ : poison ;     (* wether the location is already deallocated *)
  dn : nat ;          (* allocation size *)
  dx : vart ;       (* static information *)
}.
#[export]
Instance etaDynloc : Settable _ := settable! mkdL < dρ; dn; dx>.
Definition dynloc_eqb :=
  fun (dℓ1 dℓ2 : dynloc) =>
    (andb (andb (dℓ1.(dρ) == dℓ2.(dρ))
                (Nat.eqb dℓ1.(dn) dℓ2.(dn)))
          (dℓ1.(dx) == dℓ2.(dx)))
.
Lemma dynloc_eqb_eq dℓ0 dℓ1 :
  dynloc_eqb dℓ0 dℓ1 = true <-> dℓ0 = dℓ1.
Proof.
  unfold dynloc_eqb; split; intros.
  - eq_to_defeq Nat.eqb. cbv in *; destruct dℓ0, dℓ1; inv H; trivial.
  - inv H; eq_to_defeq Nat.eqb; try apply Nat.eqb_eq.
Qed.
#[export]
Instance dynloceq__Instance : HasEquality dynloc := {
  eq := dynloc_eqb ;
  eqb_eq := dynloc_eqb_eq ;
}.
#[global]
Notation "'dL(' bρ ';' bn ';' bx ')'" := (({| dρ := bρ ;
                                              dn := bn ;
                                              dx := bx |}) : dynloc) (at level 80).

Record ptr_key : Type := mkdPtr {
  dL : loc ;         (* the concrete location *)
  dt : ControlTag ;  (* wether the location is on the heap of the component or context *)
}.
#[export]
Instance etaPtrkey : Settable _ := settable! mkdPtr < dL; dt>.
Definition ptr_key_eqb :=
  fun (kℓ0 kℓ1 : ptr_key) =>
    (andb (kℓ0.(dL) == kℓ1.(dL))
          (kℓ0.(dt) == kℓ1.(dt)))
.
Lemma ptr_key_eqb_eq kℓ0 kℓ1 :
  ptr_key_eqb kℓ0 kℓ1 = true <-> kℓ0 = kℓ1.
Proof.
  unfold ptr_key_eqb; split; intros.
  eq_to_defeq x. cbv in *; destruct kℓ0, kℓ1; inv H. easy.
  eq_to_defeq x; inv H; split; apply eq_refl.
Qed.
#[export]
Instance ptrkeyeq__Instance : HasEquality ptr_key := {
  eq := ptr_key_eqb ;
  eqb_eq := ptr_key_eqb_eq ;
}.
#[global]
Notation "'dK(' bl ';' bt ')'" := (({| dL := bl ; dt := bt |}) : ptr_key) (at level 80).

(** Stores pointers and their respective metadata. *)
Definition ptrstore := mapind ptrkeyeq__Instance dynloc.
Definition snil : ptrstore := mapNil ptrkeyeq__Instance dynloc.

(** Continuation Stacks *)
Definition active_ectx := list (evalctx * vart).

#[local]
Existing Instance varteq__Instance | 0.
Record CfState : Type := mkΨ {
  CΞ : symbols ;
  Cξ : commlib ;
  CKs : active_ectx ;
}.
#[export]
Instance etaCfState : Settable _ := settable! mkΨ <CΞ; Cξ; CKs>.

Definition heap := @Sema.heap value.

Record MemState : Type := mkΦ {
  MH__ctx : heap ;
  MH__comp : heap ;
  MΔ : ptrstore ;
}.
#[export]
Instance etaMemState : Settable _ := settable! mkΦ <MH__ctx; MH__comp; MΔ>.
Definition EmptyΦ : MemState := mkΦ hNil hNil snil.
Record state : Type := mkΩ {
  SF : CSC.Shared.Fresh.fresh_state ;
  SΨ : CfState ;
  St : ControlTag ;
  SΦ : MemState ;
}.
#[export]
Instance etaState : Settable _ := settable! mkΩ <SF; SΨ; St; SΦ>.

Import RecordSetNotations.

Definition Htgrow (Φ : MemState) (s : nat) (t : ControlTag) (default : value) : MemState :=
  match t with
  | CCtx => let H := Hgrow Φ.(MH__ctx) s default in (Φ <| MH__ctx := H |>)
  | CComp => let H := Hgrow Φ.(MH__comp) s default in (Φ <| MH__comp := H |>)
  end
.
Definition getH (Φ : MemState) (t : ControlTag) : heap :=
  match t with
  | CCtx => Φ.(MH__ctx)
  | CComp => Φ.(MH__comp)
  end
.
Definition setH (Φ : MemState) (t : ControlTag) (H : heap) : MemState :=
  match t with
  | CCtx => Φ <| MH__ctx := H |>
  | CComp => Φ <| MH__comp := H |>
  end
.

#[global]
Notation "'Ψ(' Ξ ';' ξ ';' Ks ')'" := ({| CΞ := Ξ ; Cξ := ξ ; CKs := Ks |}) (at level 81, ξ at next level, Ks at next level).
#[global]
Notation "'Φ(' H__ctx ';' H__comp ';' Δ ')'" := ({| MH__ctx := H__ctx ; MH__comp := H__comp ; MΔ := Δ |}) (at level 81, H__comp at next level, Δ at next level).
#[global]
Notation "'Ωa(' F ';' Ψ ';' t ';' Φ ')'" := ({| SF := F ; SΨ := Ψ ; St := t ; SΦ := Φ |}) (at level 81, Ψ at next level, t at next level, Φ at next level).
#[global]
Notation "'Ω(' F ';' Ξ ';' ξ ';' Ks ';' t ';' H__ctx ';' H__comp ';' Δ ')'" :=
  (Ωa(F ; (Ψ(Ξ ; ξ ; Ks) : CfState) ; t ; (Φ(H__ctx ; H__comp ; Δ) : MemState))) (at level 81, Δ at next level).
Definition nodupinv (Ω : state) : Prop :=
  nodupinv (Ω.(SΨ).(CΞ)) /\ nodupinv (Ω.(SΦ).(MΔ))
.
Lemma nodupinv_empty (Ξ : symbols) (ξ : commlib) :
  Util.NoDupInv.nodupinv Ξ ->
  nodupinv (Ω(Fresh.empty_fresh; Ξ; ξ; List.nil; CComp; hNil; hNil; snil)).
Proof. intros H; cbn; repeat split; eauto; constructor. Qed.

(** Types of events that may occur in a trace. *)
Variant preevent : Type :=
| Sstart : preevent
| Send (v : value) : preevent
| Salloc (ℓ : loc) (n : nat) : preevent
| Sdealloc (ℓ : loc) : preevent
| Sget (ℓ : loc) (n : nat) : preevent
| Sset (ℓ : loc) (n : nat) (v : value) : preevent
| Scall (q : comms) (foo : vart) (arg : value) : preevent
| Sret (q : comms) (v : value) : preevent
.
Definition preevent_eqb (e1 e2 : preevent) : bool :=
  match e1, e2 with
  | Sstart, Sstart => true
  | Send n1, Send n2 => n1 == n2
  | Salloc ℓ0 n0, Salloc ℓ1 n1 => andb (ℓ0 == ℓ1) (Nat.eqb n0 n1)
  | Sdealloc ℓ0, Sdealloc ℓ1 => ℓ0 == ℓ1
  | Sget ℓ0 n0, Sget ℓ1 n1 => andb (ℓ0 == ℓ1) (Nat.eqb n0 n1)
  | Sset ℓ0 n0 v0, Sset ℓ1 n1 v1 => andb (andb (ℓ0 == ℓ1) (n0 == n1))
                                              (v0 == v1)
  | Scall q1 foo v0, Scall q2 bar v1 => andb (andb (String.eqb foo bar) (v0 == v1)) (q1 == q2)
  | Sret q1 v0, Sret q2 v1 => andb (v0 == v1) (q1 == q2)
  | _, _ => false
  end
.
Lemma preevent_eqb_eq e1 e2 :
  preevent_eqb e1 e2 = true <-> e1 = e2.
Proof.
  destruct e1, e2; cbn; split; intros; try easy; eq_to_defeq value_eqb; eq_to_defeq loc_eqb; eq_to_defeq comms_eqb.
  - now inv H.
  - apply Nat.eqb_eq in H0; inv H0. reflexivity.
  - inv H; split; try easy. apply Nat.eqb_refl.
  - now inv H.
  - apply Nat.eqb_eq in H0; inv H0; reflexivity.
  - inv H; split; try easy. apply Nat.eqb_refl.
  - apply Nat.eqb_eq in H0; inv H0; reflexivity.
  - inv H; repeat split; try easy. apply Nat.eqb_refl.
  - apply String.eqb_eq in H; inv H; reflexivity.
  - inv H; repeat split; eq_to_defeq a; apply String.eqb_refl.
  - inv H; split; easy.
Qed.
#[export]
Instance preeventeq__Instance : HasEquality preevent := {
  eq := preevent_eqb ;
  eqb_eq := preevent_eqb_eq ;
}.
Variant event : Type :=
| SCrash : event
| Sev (e__b : preevent) (t : ControlTag) : event
.
Definition event_eqb (e1 e2 : event) : bool :=
  match e1, e2 with
  | SCrash, SCrash => true
  | Sev e1 t1, Sev e2 t2 => andb (e1 == e2) (t1 == t2)
  | _, _ => false
  end
.
Lemma event_eqb_eq (e1 e2 : event) :
  event_eqb e1 e2 = true <-> e1 = e2.
Proof.
  destruct e1, e2; cbn; split; intros; try easy; eq_to_defeq event_eqb.
  eq_to_defeq preevent_eqb; eq_to_defeq control_tag_eq.
  inv H; eq_to_defeq preevent_eqb; eq_to_defeq control_tag_eq.
Qed.
#[export]
Instance eventeq__Instance : HasEquality event := {
  eq := event_eqb ;
  eqb_eq := event_eqb_eq ;
}.
#[global]
Notation "'ev(' e ';' t ')'" := (Sev e t) (at level 81, t at next level).
(** Pretty-printing function for better debuggability *)
Definition string_of_preevent (e : preevent) :=
  match e with
  | (Sstart) => "Start"%string
  | (Send v) => String.append ("End "%string) ("v"%string)
  | (Salloc (addr ℓ) n) => String.append
                      (String.append ("Alloc ℓ"%string) (string_of_nat ℓ))
                      (String.append (" "%string) (string_of_nat n))
  | (Sdealloc (addr ℓ)) => String.append ("Dealloc ℓ"%string) (string_of_nat ℓ)
  | (Sget (addr ℓ) n) => String.append
                    (String.append ("Get ℓ"%string) (string_of_nat ℓ))
                    (String.append (" "%string) (string_of_nat n))
  | (Sset (addr ℓ) n m) => String.append
                             (String.append
                               (String.append ("Set ℓ"%string) (string_of_nat ℓ))
                               (String.append (" "%string) ("n"%string)))
                             (String.append (" "%string) ("m"%string))
  | (Scall q foo v) => String.append (String.append
                                     (String.append ("Call "%string)
                                      (String.append (string_of_comms q)
                                       (String.append " "%string foo))) " "%string)
                      ("v"%string)
  | (Sret q v) => String.append ("Ret "%string)
                 (String.append (string_of_comms q)
                  (String.append " "%string "v"%string))
  end
.
Definition string_of_event (e : event) :=
  match e with
  | SCrash => "↯"%string
  | Sev e__b t => String.append (string_of_preevent e__b) (string_of_controltag t)
  end
.

(** A runtime program is a state plus an expression. *)
Inductive rtexpr : Type :=
| RTerm (Ω : state) (e : expr)
| RCrash
.
(* '▷' is `\triangleright and '↯' is `\lightning`` *)
#[global]
Notation "Ω '▷' e" := ((RTerm Ω e) : rtexpr) (at level 81, e at next level).
#[global]
Notation "'↯' '▷' 'stuck'" := (RCrash).

(** Substitution, which assumes that the given expression is closed. *)
Definition subst (what : vart) (inn forr : expr) : expr :=
  let fix R e :=
    match e with
    | Xval _ => e
    | Xabort => Xabort
    | Xlet x e0 e1 => if vareq what x then Xlet x (R e0) e1 else Xlet x (R e0) (R e1)
    | Xnew γ e0 e1 => Xnew γ (R e0) (R e1) (*we don't want people to be able to subst γ here*)
    | Xdel e => Xdel (R e)
    | Xget e0 e1 e2 => Xget (R e0) (R e1) (R e2)
    | Xset e0 e1 e2 e3 => Xset (R e0) (R e1) (R e2) (R e3)
    | Xvar x => if vareq what x then forr else e
    | Xbinop b e1 e2 => Xbinop b (R e1) (R e2)
    | Xifz c e1 e2 => Xifz (R c) (R e1) (R e2)
    | Xreturn e => Xreturn (R e)
    | Xcall foo e => Xcall foo (R e)
    | Xunpack γ x e0 e1 => if vareq what x then Xunpack γ x (R e0) e1 else Xunpack γ x (R e0) (R e1)
    | Xpack ℓ e => Xpack (R ℓ) (R e)
    | Xpair e0 e1 => Xpair (R e0) (R e1)
    | Xunpair x1 x2 e0 e1 => if orb (vareq what x1) (vareq what x2) then
                              Xunpair x1 x2 (R e0) e1
                            else
                              Xunpair x1 x2 (R e0) (R e1)
    | Xhas e t => Xhas (R e) t
    | Xispoisoned e => Xispoisoned (R e)
    end
  in
  R inn
.
Inductive pstep : PrimStep rtexpr event :=
| e_binop : forall (Ω : state) (n1 n2 n3 : nat) (b : binopsymb),
    Some(n3) = eval_binop b n1 n2 ->
    Ω ▷ Xbinop b (Xval n1) (Xval n2) --[]--> Ω ▷ (Xval(Vnat n3))
| e_ifz_true : forall (Ω : state) (e1 e2 : expr),
    Ω ▷ Xifz (Xval 0) e1 e2 --[]--> Ω ▷ e1
| e_ifz_false : forall (Ω : state) (e1 e2 : expr) (n : nat),
    n <> 0 ->
    Ω ▷ Xifz (Xval n) e1 e2 --[]--> Ω ▷ e2
| e_pair : forall (Ω : state) (v1 v2 : value),
    Ω ▷ Xpair (Xval v1) (Xval v2) --[]--> Ω ▷ Xval(Vpair v1 v2)
| e_abort : forall (Ω : state),
    Ω ▷ Xabort --[ (SCrash) ]--> ↯ ▷ stuck
| e_let : forall (Ω : state) (x : vart) (v : value) (e e' : expr),
    e' = subst x e (Xval v) ->
    Ω ▷ Xlet x (Xval v) e --[]--> Ω ▷ e'
| e_unpair : forall (Ω : state) (v1 v2 : value) (x1 x2 : vart) (e e' : expr),
    e' = subst x1 (subst x2 e (Xval v2)) (Xval v1) ->
    Ω ▷ Xunpair x1 x2 (Xval(Vpair v1 v2)) e --[]--> Ω ▷ e'
| e_alloc : forall (F : CSC.Shared.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
              (Φ Φ' : MemState) (v : value) (n : nat) (ℓ : loc) (Δ' : ptrstore) (γ : vart),
    ℓ = addr(List.length (getH Φ t)) ->
    Util.NoDupInv.nodupinv Φ.(MΔ) ->
    push (dK(ℓ ; t)) (dL(◻ ; n ; γ)) Φ.(MΔ) = Some Δ' ->
    Φ' = Htgrow (Φ <| MΔ := Δ' |>) n t v ->
    (Ωa(F ; Ψ ; t ; Φ)) ▷ Xnew γ (Xval v) (Xval n) --[ ev( Salloc ℓ n ; t ) ]--> (Ωa(F ; Ψ ; t ; Φ')) ▷ Xval (Vpack (LConst ℓ γ) (Vpair Vcap (Vptr ℓ γ)))
| e_delete : forall (F : CSC.Shared.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
               (Φ Φ' : MemState) (n : nat) (ℓ : loc) (ρ : poison) (Δ1 Δ2 : ptrstore) (γ : vart),
    Util.NoDupInv.nodupinv (Δ1 ◘ (dK(ℓ ; t)) ↦ (dL(ρ ; n ; γ)) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK(ℓ ; t)) ↦ dL(ρ ; n ; γ) ◘ Δ2) ->
    Φ' = Φ <| MΔ := Δ1 ◘ (dK(ℓ ; t)) ↦ (dL(☣ ; n ; γ)) ◘ Δ2 |> ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xdel (Xval (Vpack (LConst ℓ γ) (Vpair Vcap (Vptr ℓ γ)))) --[ ev( Sdealloc ℓ ; t ) ]--> Ωa(F ; Ψ ; t ; Φ') ▷ Xval 0
| e_get : forall (F : CSC.Shared.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
            (Φ : MemState) (n m ℓ : nat) (v : value)  (ρ : poison) (Δ1 Δ2 : ptrstore) (γ : vart),
    Util.NoDupInv.nodupinv (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(ρ ; m ; γ) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(ρ ; m ; γ) ◘ Δ2) ->
    (List.nth_error (getH Φ t) (ℓ + n) = (Some v) \/ (v = Vnat 1729 /\ List.nth_error (getH Φ t) (ℓ + n) = None)) ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xget (Xval Vcap) (Xval(Vptr (addr ℓ) γ)) (Xval n) --[ ev( Sget (addr ℓ) n ; t ) ]--> Ωa(F ; Ψ ; t ; Φ) ▷ Xval (Vpair Vcap v)
| e_set : forall (F : CSC.Shared.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag) (H' : heap)
            (Φ Φ' : MemState) (n m ℓ : nat) (w : value) (ρ : poison) (Δ1 Δ2 : ptrstore) (γ : vart),
    Util.NoDupInv.nodupinv (Δ1 ◘ (dK((addr ℓ); t)) ↦ dL(ρ ; m ; γ) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK((addr ℓ); t)) ↦ dL(ρ ; m ; γ) ◘ Δ2) ->
    (NoDupList.swap_nth_aux (getH Φ t) (ℓ + n) (w) = Some H' \/ (H' = getH Φ t /\ NoDupList.swap_nth_aux (getH Φ t) (ℓ + n) (w) = None)) ->
    Φ' = setH Φ t H' ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xset (Xval Vcap) (Xval(Vptr (addr ℓ) γ)) (Xval n) (Xval w) --[ ev( Sset (addr ℓ) n w ; t ) ]--> Ωa(F ; Ψ ; t ; Φ') ▷ Xval (Vpair Vcap w)
| e_unpack : forall (Ω : state) (γ γ' x : vart) (ℓ : loc) (v : value) (e e' : expr),
    e' = subst γ (subst x e (Xval v)) (Xval (Vptr ℓ γ')) ->
    Ω ▷ Xunpack γ x (Xval (Vpack (LConst ℓ γ') v)) e --[]--> Ω ▷ e'
| e_pack : forall (Ω : state) (ℓ : loc) (v : value) (γ : vart),
    Ω ▷ Xpack (Xval (Vptr ℓ γ)) (Xval v) --[]--> Ω ▷ Xval(Vpack (LConst ℓ γ) v)
| e_poison_yes : forall (F : CSC.Shared.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
            (Φ : MemState) (m ℓ : nat) (v : value)  (Δ1 Δ2 : ptrstore) (γ : vart),
    Util.NoDupInv.nodupinv (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(☣ ; m ; γ) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(☣ ; m ; γ) ◘ Δ2) ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xispoisoned (Xval(Vptr (addr ℓ) γ)) --[]--> Ωa(F ; Ψ ; t ; Φ) ▷ Xval(Vnat 0)
| e_poison_no : forall (F : CSC.Shared.Fresh.fresh_state) (Ψ : CfState) (t : ControlTag)
            (Φ : MemState) (m ℓ : nat) (v : value)  (Δ1 Δ2 : ptrstore) (γ : vart),
    Util.NoDupInv.nodupinv (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(◻ ; m ; γ) ◘ Δ2) ->
    Φ.(MΔ) = (Δ1 ◘ (dK((addr ℓ) ; t)) ↦ dL(◻ ; m ; γ) ◘ Δ2) ->
    Ωa(F ; Ψ ; t ; Φ) ▷ Xispoisoned (Xval(Vptr (addr ℓ) γ)) --[]--> Ωa(F ; Ψ ; t ; Φ) ▷ Xval(Vnat 1)
| e_has_nat_yes : forall (Ω : state) (n : nat),
    Ω ▷ Xhas (Xval(Vnat n)) Tℕ --[]--> Ω ▷ Xval(Vnat 0)
| e_has_nat_no : forall (Ω : state) (v : value),
    (forall n, v <> Vnat n) ->
    Ω ▷ Xhas (Xval v) Tℕ --[]--> Ω ▷ Xval(Vnat 1)
| e_has_pair_yes : forall (Ω : state) (v1 v2 : nat),
    Ω ▷ Xhas (Xval(Vpair (Vnat v1) (Vnat v2))) (Tpair Tℕ Tℕ) --[]--> Ω ▷ Xval(Vnat 0)
| e_has_pair_no : forall (Ω : state) (v : value),
    (forall v1 v2, v <> Vpair v1 v2) ->
    Ω ▷ Xhas (Xval v) (Tpair Tℕ Tℕ) --[]--> Ω ▷ Xval(Vnat 1)
(*more rules*)
.
#[global]
Existing Instance pstep.
#[global]
Hint Constructors pstep : core.

Lemma Htgrow_Δ_passthrough Φ Δ n t v :
  MΔ (Htgrow (Φ <| MΔ := Δ |>) n t v) = Δ
.
Proof. now destruct t; cbn. Qed.

Lemma setH_Δ_passthrough Φ Δ t H' :
  MΔ (setH (Φ <| MΔ := Δ |>) t H') = Δ
.
Proof. now destruct t; cbn. Qed.

Lemma pstep_is_nodupinv_invariant Ω e Ω' e' a :
  Ω ▷ e --[, a ]--> Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  intros H; cbv in H; dependent induction H; try easy; intros.
  - (* e_alloc *)
    inv H3; cbn in *; eapply push_ok in H1 as H1'; unfold push in H1;
    crush_undup ({| dL := addr(List.length (getH Φ t)); dt := t |} ↦ {| dρ := ◻; dn := n; dx := γ |} ◘ MΔ Φ);
    inv H1; clear Hx; constructor; eauto; cbn; rewrite Htgrow_Δ_passthrough;
    inv H1'; now constructor.
  - (* e_del *) inv H1; inv H2; cbn in *; clear H3; rewrite H0 in *; constructor; cbn in *; auto;
    revert H4; clear; intros; induction Δ1; cbn in *; inv H4.
    + now constructor.
    + specialize (IHΔ1 H3); constructor; try easy;
      revert H1; clear; intros H1; induction Δ1; cbn in *; try easy;
      destruct (eq_dec a0 a).
      * subst; exfalso; apply H1; now left.
      * intros [H2|H2]; try contradiction;
        apply IHΔ1; auto.
  - (* e_set *) inv H3; cbn in *; rewrite H0 in *; constructor; auto;
    cbn; change (Util.NoDupInv.nodupinv (MΔ (setH (Φ <| MΔ := MΔ Φ |>) t H')));
    rewrite setH_Δ_passthrough, H0; easy.
Qed.

(** functional version of the above *)
Definition pstepf (r : rtexpr) : option (option event * rtexpr) :=
  match r with
  | RCrash => None
  | RTerm Ω e =>
    match e with
    | Xbinop b (Xval v1) (Xval v2) =>
      match v1, v2 with
      | Vnat v1, Vnat v2 =>
        let* v3 := eval_binop b v1 v2 in
        Some(None, Ω ▷ Xval(Vnat v3))
      | _, _ => None
      end
    | Xifz (Xval(Vnat n)) e1 e2 =>
      match n with
      | 0 => Some(None, Ω ▷ e1)
      | _ => Some(None, Ω ▷ e2)
      end
    | Xpair (Xval v1) (Xval v2) =>
      Some(None, Ω ▷ Xval(Vpair v1 v2))
    | Xabort => Some(Some SCrash, ↯ ▷ stuck)
    | Xlet x (Xval v) e =>
      Some(None, Ω ▷ subst x e (Xval v))
    | Xunpair x1 x2 (Xval(Vpair v1 v2)) e =>
      Some(None, Ω ▷ subst x1 (subst x2 e (Xval v2)) (Xval v1))
    | Xnew γ (Xval v) (Xval(Vnat n)) =>
      let ℓ := addr(List.length (getH Ω.(SΦ) Ω.(St))) in
      let* _ := undup Ω.(SΦ).(MΔ) in
      let* Δ' := push (dK(ℓ ; Ω.(St))) (dL(◻ ; n ; γ)) Ω.(SΦ).(MΔ) in
      let Φ' := Htgrow (Ω.(SΦ) <| MΔ := Δ' |>) n Ω.(St) v in
      let Ω' := Ω <| SΦ := Φ' |> in
      Some(Some(ev(Salloc ℓ n ; Ω.(St))), Ω' ▷ Xval(Vpack (LConst ℓ γ) (Vpair Vcap (Vptr ℓ γ))))
    | Xdel (Xval(Vpack (LConst ℓ γ) (Vpair Vcap (Vptr ℓ' γ')))) =>
      if ℓ == ℓ' then
        if γ == γ' then
          let* Δ := undup Ω.(SΦ).(MΔ) in
          let* (Δ1, dK, dl, Δ2) := splitat Δ (dK(ℓ ; Ω.(St))) in
          if ℓ == dK.(dL) then
            let dl' := dl <| dρ := ☣ |> in
            let Φ' := Ω.(SΦ) <| MΔ := Δ1 ◘ dK ↦ dl' ◘ Δ2 |> in
            let Ω' := Ω <| SΦ := Φ' |> in
            if Ω.(St) == dK.(dt) then
              if γ == dl.(dx) then
                Some(Some(ev(Sdealloc ℓ ; Ω.(St))), Ω' ▷ Xval 0)
              else
                None
            else
              None
          else
            None
        else
          None
      else
        None
    | Xget (Xval Vcap) (Xval(Vptr(addr ℓ) γ)) (Xval(Vnat n)) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, dk, dl, Δ2) := splitat Δ (dK((addr ℓ) ; Ω.(St))) in
      let '(addr ln) := dk.(dL) in
      if ℓ == ln then
        let v := match List.nth_error (getH Ω.(SΦ) Ω.(St)) (ℓ+n) with
                 | Some(v) => v
                 | _ => Vnat 1729
                 end
        in
        if Ω.(St) == dk.(dt) then
          if γ == dl.(dx) then
            Some(Some(ev(Sget (addr ℓ) n ; Ω.(St))), Ω ▷ Xval(Vpair Vcap v))
          else
            None
        else
          None
      else
        None
    | Xispoisoned (Xval(Vptr(addr ℓ) γ)) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, dk, dl, Δ2) := splitat Δ (dK((addr ℓ) ; Ω.(St))) in
      let '(addr ln) := dk.(dL) in
      if ℓ == ln then
        if Ω.(St) == dk.(dt) then
          if γ == dl.(dx) then
            Some(None, Ω ▷ Xval(Vnat(if dl.(dρ) == ☣ then 0 else 1)))
          else
            None
        else
          None
      else
        None
    | Xset (Xval Vcap) (Xval(Vptr(addr ℓ) γ)) (Xval(Vnat n)) (Xval w) =>
      let* Δ := undup Ω.(SΦ).(MΔ) in
      let* (Δ1, dk, dl, Δ2) := splitat Δ (dK((addr ℓ) ; Ω.(St))) in
      let '(addr ln) := dk.(dL) in
      if ℓ == ln then
        let H' := match NoDupList.swap_nth_aux (getH Ω.(SΦ) Ω.(St)) (ℓ+n) (w) with
                  | Some(H') => H'
                  | _ => getH Ω.(SΦ) Ω.(St)
                  end
        in
        let Φ' := setH Ω.(SΦ) Ω.(St) H' in
        let Ω' := Ω <| SΦ := Φ' |> in
        if Ω.(St) == dk.(dt) then
          if γ == dl.(dx) then
            Some(Some(ev(Sset (addr ℓ) n w ; Ω.(St))), Ω' ▷ Xval(Vpair Vcap w))
          else
            None
        else
          None
      else
        None
    | Xunpack γ x (Xval(Vpack (LConst ℓ γ') v)) e =>
      let e' := subst γ (subst x e (Xval v)) (Xval(Vptr ℓ γ')) in
      Some(None, Ω ▷ e')
    | Xpack (Xval(Vptr ℓ γ)) (Xval v) =>
      Some(None, Ω ▷ Xval(Vpack (LConst ℓ γ) v))
    | Xhas (Xval(Vnat n)) Tℕ =>
      Some(None, Ω ▷ Xval(Vnat 0))
    | Xhas (Xval(Vpair(Vnat n1) (Vnat n2))) (Tpair Tℕ Tℕ) =>
      Some(None, Ω ▷ Xval(Vnat 0))
    | Xhas _ Tℕ =>
      Some(None, Ω ▷ Xval(Vnat 1))
    | Xhas (Xval _) (Tpair Tℕ Tℕ) =>
      Some(None, Ω ▷ Xval(Vnat 1))
    | _ => None
    end
  end
.
Ltac grab_value e :=
  let n := fresh "n" in
  let v0 := fresh "v0" in
  let v1 := fresh "v1" in
  let l := fresh "ℓ" in
  let v := fresh "v" in
  (destruct e as [[n | v0 v1 | (* Vcap *) | l | l v]| | | | | | | | | | | | | | |]; try congruence)
.
Ltac grab_value2 e1 e2 := (grab_value e1; grab_value e2).
Ltac grab_value3 e1 e2 e3 := (grab_value e1; grab_value e2; grab_value e3).
Ltac grab_value4 e1 e2 e3 e4 := (grab_value e1; grab_value e2; grab_value e3; grab_value e4).

(** We use an alternative notation of pstep here that does not constrain a to be *either* Some/None *)
Lemma equiv_pstep (r0 : rtexpr) (a : option event) (r1 : rtexpr) :
  r0 --[, a ]--> r1 <-> pstepf r0 = Some(a, r1).
Proof.
  split.
  - intros H; cbv in H; dependent induction H; cbn.
    + (* binop *) destruct b; inv H; easy.
    + (* ifz-true *) easy.
    + (* ifz-false *) destruct n; easy.
    + (* pair *) easy.
    + (* crash *) easy.
    + (* let *) now inv H.
    + (* unpair *) now inv H.
    + (* alloc *) crush_undup (MΔ Φ); inv H; cbn in H1; rewrite H1; easy.
    + (* del *) eq_to_defeq loc_eqb; rewrite eq_refl; apply nodupinv_equiv_undup in H as H'. inv H0. rewrite H3, H'.
      apply splitat_elim in H as ->. eq_to_defeq loc_eqb; rewrite eq_refl. eq_to_defeq control_tag_eq; rewrite eq_refl. cbn. eq_to_defeq vareq; rewrite eq_refl. easy.
    + (* get *) apply nodupinv_equiv_undup in H as H'. inv H0. rewrite H3, H'.
      apply splitat_elim in H as ->. cbn. rewrite Nat.eqb_refl. cbn; eq_to_defeq control_tag_eq; rewrite eq_refl. cbn; destruct H1 as [-> | [-> ->]]; eq_to_defeq vareq; rewrite eq_refl; easy.
    + (* set *) apply nodupinv_equiv_undup in H as H'0. rewrite H0, H'0.
      apply splitat_elim in H as ->. cbn. rewrite Nat.eqb_refl. inv H2. eq_to_defeq control_tag_eq; rewrite eq_refl. eq_to_defeq vareq; rewrite eq_refl. destruct H1 as [-> | [-> ->]]; try easy.
    + (* unpack *) now inv H.
    + (* pack *) easy.
    + (* ispoisoned-yes *) apply nodupinv_equiv_undup in H as H'. inv H0. rewrite H2, H'.
      apply splitat_elim in H as ->. cbn. rewrite Nat.eqb_refl. eq_to_defeq control_tag_eq; rewrite eq_refl.
      eq_to_defeq vareq; rewrite eq_refl. easy.
    + (* ispoisoned-no *) apply nodupinv_equiv_undup in H as H'. inv H0. rewrite H2, H'.
      apply splitat_elim in H as ->. cbn. rewrite Nat.eqb_refl. eq_to_defeq control_tag_eq; rewrite eq_refl.
      eq_to_defeq vareq; rewrite eq_refl. easy.
    + (* has ℕ yes *) easy.
    + (* has ℕ no *) destruct v; try easy. specialize (H n); congruence.
      destruct v1, v2; easy.
    + (* has Tpair yes *) easy.
    + (* has Tpair no *) destruct v; try easy. destruct v1, v2; try easy.
      specialize (H (Vnat n) (Vnat n0)); congruence.
  - destruct r0 as [Ω e|]; try now cbn.
    (*])
    revert Ω a r1; induction e; intros; cbn in H.
    + (* value *) inv H.
    + (* variable *) inv H.
    + (* binop *) grab_value2 e1 e2; destruct symb; inv H; now constructor.
    + (* get *) grab_value3 e1 e2 e3; destruct ℓ; try now inv H. crush_undup (MΔ (SΦ Ω)).
      apply nodupinv_equiv_undup in Hx as Hy; recognize_split; elim_split. cbn in H.
      rewrite Nat.eqb_refl in H. destruct v; cbn in H; eq_to_defeq control_tag_eq. rewrite eq_refl in H.
      eq_to_defeq vareq. destruct (eq_dec v2 dx0); try (apply neqb_neq in H1; rewrite H1 in H; congruence); subst.
      rewrite eq_refl in H.
      crush_option (List.nth_error (getH (SΦ Ω) (St Ω)) (n0 + n)).
      * inv H. cbn in *. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; econstructor; try eassumption. now left.
      * rewrite Hx0 in H. inv H. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; econstructor; try eassumption. right; now split.
    + (* set *) grab_value3 e1 e2 e3; destruct ℓ; try now inv H. destruct e4; try now inv H. crush_undup (MΔ (SΦ Ω)).
      apply nodupinv_equiv_undup in Hx as Hy; recognize_split; elim_split. destruct v0. cbn in H.
      rewrite Nat.eqb_refl in H.
      cbn in H; eq_to_defeq control_tag_eq. rewrite eq_refl in H.
      eq_to_defeq vareq. destruct (eq_dec v2 dx0); try (apply neqb_neq in H1; rewrite H1 in H; congruence); subst.
      rewrite eq_refl in H.
      crush_option (NoDupList.swap_nth_aux (getH (SΦ Ω) (St Ω)) (n0 + n) v).
      * inv H. cbn in *. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; cbn in *; econstructor; cbn; try eassumption. left; eassumption. reflexivity.
      * rewrite Hx0 in H. inv H. cbn in *. rewrite H0 in Hx. apply nodupinv_equiv_undup in Hx.
        destruct Ω; cbn in *; econstructor; cbn; try eassumption. now right. reflexivity.
    + (* let *) grab_value e1; inv H; now constructor.
    + (* new *) destruct e1; try now inv H. grab_value e2.
      crush_undup (MΔ (SΦ Ω)).
      crush_option (push (dK(addr (List.length (getH (SΦ Ω) (St Ω))) ; Ω.(St))) {| dρ := ◻; dn := n; dx := γ |} (MΔ (SΦ Ω))).
      inv H. destruct Ω; econstructor; try eassumption. now cbn. now apply nodupinv_equiv_undup in Hx. now symmetry.
    + (* del *) grab_value e. destruct ℓ; try now inv H. destruct v; try now inv H. destruct v1, v2; try now inv H.
      eq_to_defeq loc_eqb. destruct (eq_dec l l0); try (apply neqb_neq in H0; now rewrite H0 in H).
      rewrite H0 in H; rewrite eq_refl in H.
      eq_to_defeq vareq;
      destruct (eq_dec v0 v); try (apply neqb_neq in H1; now rewrite H1 in H).
      subst; rewrite eq_refl in H.
      crush_undup (MΔ (SΦ Ω)).
      apply nodupinv_equiv_undup in Hx as Hy; recognize_split; elim_split.
      subst. eq_to_defeq loc_eqb; rewrite eq_refl in H. eq_to_defeq control_tag_eq. rewrite eq_refl in H.
      eq_to_defeq vareq; destruct (eq_dec v (dx v0)); try (apply neqb_neq in H1; rewrite H1 in H; congruence);
      subst; rewrite eq_refl in H.
      inv H. rewrite H0 in *. destruct v0; destruct Ω; cbn in *; econstructor; try eassumption.
      reflexivity.
    + (* unpack *) grab_value e1; inv H; destruct ℓ; try now inv H1; destruct Ω; cbn in *; econstructor.
    + (* pack *) grab_value2 e1 e2; inv H; easy.
    + (* pair *) grab_value2 e1 e2; inv H; constructor.
    + (* unpair *) grab_value e1; inv H; constructor; reflexivity.
    + (* return *) inv H.
    + (* call *) inv H.
    + (* ifz *) grab_value e1; destruct n; inv H; constructor; easy.
    + (* crash *) inv H; constructor. *)
Admitted.
Lemma pstepf_is_nodupinv_invariant Ω e Ω' e' a :
  pstepf (Ω ▷ e) = Some(a, Ω' ▷ e') ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof. intros H0 H1; apply equiv_pstep in H0; apply pstep_is_nodupinv_invariant in H0; eauto. Qed.

(** convert an expression to evalctx in order to execute it functionally + "contextually" *)
(** this function returns an eval context K and an expr e' such that K[e'] = e given some e *)
Fixpoint evalctx_of_expr (e : expr) : option (evalctx * expr) :=
  match e with
  | Xval _ => None
  | Xvar _ => None
  | Xabort => Some(Khole, Xabort)
  | Xhas e t =>
    match e with
    | Xval v =>
      Some (Khole, Xhas (Xval v) t)
    | _ =>
      let* (K, e') := evalctx_of_expr e in
      Some(Khas K t, e')
    end
  | Xispoisoned e =>
    match e with
    | Xval v =>
      Some (Khole, Xispoisoned (Xval v))
    | _ =>
      let* (K, e') := evalctx_of_expr e in
      Some(Kispoisoned K, e')
    end
  | Xbinop b e1 e2 =>
    match e1, e2 with
    | Xval(n1), Xval(n2) =>
      Some(Khole, Xbinop b (Xval n1) (Xval n2))
    | Xval(n1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KbinopR b n1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KbinopL b K e2, e1')
    end
  | Xget e0 e1 e2 =>
    match e0, e1, e2 with
    | Xval(v0), Xval(v1), Xval(v2) =>
      Some(Khole, Xget (Xval v0) (Xval v1) (Xval v2))
    | Xval(v0), Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KgetR v0 v1 K, e2')
    | Xval(v), en1, e2 =>
      let* (K, e1') := evalctx_of_expr en1 in
      Some(KgetM v K e2, e1')
    | _, _, _ =>
      let* (K, e0') := evalctx_of_expr e0 in
      Some(KgetL K e1 e2, e0')
    end
  | Xset e0 e1 e2 e3 =>
    match e0, e1, e2, e3 with
    | Xval(v0), Xval(v1), Xval(v2), Xval(v3) =>
      Some (Khole, Xset (Xval v0) (Xval v1) (Xval v2) (Xval v3))
    | Xval(v0), Xval(v1), Xval(v2), en3 =>
      let* (K, e3') := evalctx_of_expr en3 in
      Some (KsetR v0 v1 v2 K, e3')
    | Xval(v0), Xval(v1), en2, en3 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some (KsetM1 v0 v1 K en3, e2')
    | Xval(v0), en1, en2, en3 =>
      let* (K, e1') := evalctx_of_expr en1 in
      Some (KsetM0 v0 K en2 en3, e1')
    | _, _, _, _ =>
      let* (K, e0') := evalctx_of_expr e0 in
      Some (KsetL K e1 e2 e3, e0')
    end
  | Xlet x e1 e2 =>
    match e1 with
    | Xval(v) =>
      Some(Khole, Xlet x (Xval v) e2)
    | _ => let* (K, e1') := evalctx_of_expr e1 in
          Some(Klet x K e2, e1')
    end
  | Xunpair x1 x2 e1 e2 =>
    match e1 with
    | Xval(v) =>
      Some(Khole, Xunpair x1 x2 (Xval v) e2)
    | _ => let* (K, e1') := evalctx_of_expr e1 in
          Some(Kunpair x1 x2 K e2, e1')
    end
  | Xnew γ e1 e2 =>
    match e1, e2 with
    | Xval(v1), Xval(v2) =>
      Some(Khole, Xnew γ (Xval v1) (Xval v2))
    | Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KnewR γ v1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KnewL γ K e2, e1')
    end
  | Xdel e =>
    match e  with
    | Xval(v) =>
      Some(Khole, Xdel (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kdel K, e')
    end
  | Xunpack γ x e0 e1 =>
    match e0 with
    | Xval(v0) =>
      Some(Khole, Xunpack γ x (Xval v0) e1)
    | en0 =>
      let* (K, e0') := evalctx_of_expr en0 in
      Some(Kunpack γ x K e1, e0')
    end
  | Xpack e1 e2 =>
    match e1, e2 with
    | Xval(v1), Xval(v2) =>
      Some(Khole, Xpack (Xval v1) (Xval v2))
    | Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KpackR v1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KpackL K e2, e1')
    end
  | Xpair e1 e2 =>
    match e1, e2 with
    | Xval(v1), Xval(v2) =>
      Some(Khole, Xpair (Xval v1) (Xval v2))
    | Xval(v1), en2 =>
      let* (K, e2') := evalctx_of_expr en2 in
      Some(KpairR v1 K, e2')
    | _, _ =>
      let* (K, e1') := evalctx_of_expr e1 in
      Some(KpairL K e2, e1')
    end
  | Xreturn e =>
    match e with
    | Xval v =>
      Some(Khole, Xreturn (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kreturn K, e')
    end
  | Xcall foo e =>
    match e with
    | Xval v =>
      Some(Khole, Xcall foo (Xval v))
    | _ => let* (K, e') := evalctx_of_expr e in
          Some(Kcall foo K, e')
    end
  | Xifz c e0 e1 =>
    match c with
    | Xval(v) =>
      Some(Khole, Xifz (Xval v) e0 e1)
    | _ => let* (K, c') := evalctx_of_expr c in
          Some(Kifz K e0 e1, c')
    end
  end
.
(** Checks wether the thing that is filled into the hole is somehow structurually compatible with pstep *)
(** This check does not apply to contextual steps *)
Definition pstep_compatible (e : expr) : option expr :=
  match e with
  | Xifz (Xval v) e0 e1 => Some (Xifz (Xval v) e0 e1)
  | Xabort => Some (Xabort)
  | Xbinop b (Xval(Vnat v1)) (Xval(Vnat v2)) => Some(Xbinop b (Xval v1) (Xval v2))
  | Xlet x (Xval v) e => Some(Xlet x (Xval v) e)
  | Xpair (Xval v1) (Xval v2) => Some(Xpair (Xval v1) (Xval v2))
  | Xunpair x1 x2 (Xval v) e => Some(Xunpair x1 x2 (Xval v) e)
  | Xnew γ (Xval(Vnat v1)) (Xval v2) => Some(Xnew γ (Xval(Vnat v1)) (Xval v2))
  | Xdel (Xval v) => Some(Xdel (Xval v))
  | Xget (Xval(Vcap)) (Xval(Vptr ℓ γ)) (Xval(Vnat v)) => Some(Xget (Xval Vcap) (Xval(Vptr ℓ γ)) (Xval(Vnat v)))
  | Xset (Xval(Vcap)) (Xval(Vptr ℓ γ)) (Xval(Vnat n)) (Xval v3) => Some(Xset (Xval(Vcap)) (Xval(Vptr ℓ γ)) (Xval(Vnat n)) (Xval v3))
  | Xpack (Xval v1) (Xval v2) => Some(Xpack (Xval v1) (Xval v2))
  | Xunpack γ x (Xval v) e => Some(Xunpack γ x (Xval v) e)
  | _ => None
  end
.
(** This function subsumes `pstep_compatible`, but it also includes the contextual steps. *)
Definition pestep_compatible (e : expr) : option expr :=
  match e with
  | Xifz (Xval v) e0 e1 => Some (Xifz (Xval v) e0 e1)
  | Xabort => Some (Xabort)
  | Xbinop b (Xval(Vnat v1)) (Xval(Vnat v2)) => Some(Xbinop b (Xval(Vnat v1)) (Xval(Vnat v2)))
  | Xlet x (Xval v) e => Some(Xlet x (Xval v) e)
  | Xpair (Xval v1) (Xval v2) => Some(Xpair (Xval v1) (Xval v2))
  | Xunpair x1 x2 (Xval v) e => Some(Xunpair x1 x2 (Xval v) e)
  | Xnew γ (Xval(Vnat v1)) (Xval v2) => Some(Xnew γ (Xval(Vnat v1)) (Xval v2))
  | Xdel (Xval v) => Some(Xdel (Xval v))
  | Xget (Xval(Vcap)) (Xval(Vptr ℓ γ)) (Xval(Vnat v)) => Some(Xget (Xval Vcap) (Xval(Vptr ℓ γ)) (Xval(Vnat v)))
  | Xset (Xval(Vcap)) (Xval(Vptr ℓ γ)) (Xval(Vnat n)) (Xval v3) => Some(Xset (Xval(Vcap)) (Xval(Vptr ℓ γ)) (Xval(Vnat n)) (Xval v3))
  | Xpack (Xval v1) (Xval v2) => Some(Xpack (Xval v1) (Xval v2))
  | Xunpack γ x (Xval v) e => Some(Xunpack γ x (Xval v) e)
  | Xcall foo (Xval v) => Some(Xcall foo (Xval v))
  | Xreturn (Xval v) => Some(Xreturn (Xval v))
  | _ => None
  end
.
Lemma return_pestep_compat (v : value) :
  Some(Xreturn (Xval v)) = pestep_compatible (Xreturn (Xval v)).
Proof. now cbn. Qed.
Lemma call_pestep_compat foo (v : value) :
  Some(Xcall foo (Xval v)) = pestep_compatible (Xcall foo (Xval v)).
Proof. now cbn. Qed.
Lemma pstep_compat_weaken e :
  Some e = pstep_compatible e ->
  Some e = pestep_compatible e.
Proof. induction e; now cbn. Qed.
#[global]
Hint Resolve pstep_compat_weaken call_pestep_compat return_pestep_compat : core.

(** ** Environment Semantics  *)
Ltac In_find_resolve_contr_hook Hx Hy := fail.
Ltac In_find_resolve_contr := (
      match goal with
      | [Hx : List.find (fun x : string => vareq _ ?bar) ?ξ = None,
         Hy : In ?bar ?ξ |- _] =>
        apply (List.find_none _ _ Hx) in Hy; apply String.eqb_neq in Hy; contradiction
      | [Hx : List.find (fun x : string => vareq _ ?bar) ?ξ = Some _,
         Hy : ~In ?bar ?ξ |- _] =>
        let Hxf := fresh "Hx'" in
        let Hx1 := fresh "Hx1" in
        let Hx2 := fresh "Hx2" in
        assert (Hx':=Hx); apply List.find_some in Hxf as [Hx1 Hx2];
        apply String.eqb_eq in Hx2; subst; contradiction
      | [Hx : List.find (fun x : string => vareq _ ?foo) _ = None,
         Hy : List.find (fun x : string => vareq _ ?bar) _ = None |- _] =>
        In_find_resolve_contr_hook Hx Hy
      | [Hx : List.find (fun x : string => vareq _ ?foo) _ = Some _,
         Hy : List.find (fun x : string => vareq _ ?bar) _ = Some _ |- _] =>
        In_find_resolve_contr_hook Hx Hy
      end)
.
Inductive context_switched : commlib -> vart -> ControlTag -> comms -> ControlTag -> Prop :=
| SwitchCtxToComp : forall (ξ : commlib) (foo : vart),
    (* foo is called, foo is part of component, so for switch the call must've been CCtx *)
    List.In foo ξ ->
    context_switched ξ foo CCtx Qctxtocomp CComp
| SwitchCompToCtx : forall (ξ : commlib) (foo : vart),
    (* foo is called, foo is not part of component, so for switch the call must've been CComp *)
    ~(List.In foo ξ) ->
    context_switched ξ foo CComp Qcomptoctx CCtx
| NoSwitchComp : forall (ξ : commlib) (foo : vart),
    (* component calling foo, which is in component, is an internal fn call *)
    List.In foo ξ ->
    context_switched ξ foo CComp Qinternal CComp
| NoSwitchCtx : forall (ξ : commlib) (foo : vart),
    (* context calling foo, which is in context, is an internal fn call *)
    ~(List.In foo ξ) ->
    context_switched ξ foo CCtx Qinternal CCtx
.
Definition context_switchedf (ξ : commlib) (foo : vart) (t : ControlTag) : (comms * ControlTag) :=
  match List.find (fun x => foo == x) ξ with
  | Some _ =>
    match t with
    | CCtx => (* SwitchCtxToComp *)
      (Qctxtocomp, CComp)
    | CComp => (* NoSwitchComp *)
      (Qinternal, CComp)
    end
  | None =>
    match t with
    | CCtx => (* NoSwitchCtx *)
      (Qinternal, CCtx)
    | CComp => (* SwitchCompToCtx *)
      (Qcomptoctx, CCtx)
    end
  end
.
Lemma context_switched_equiv (ξ : commlib) (foo : vart) (t t' : ControlTag) (q : comms) :
  context_switched ξ foo t q t' <-> context_switchedf ξ foo t = (q, t').
Proof.
  split; intros H.
  - inv H; unfold context_switchedf.
    + crush_option (List.find (fun x => foo == x) ξ). easy. eapply List.find_none in H0; eauto.
      cbn in H0; eq_to_defeq vareq; apply neqb_neq in H0. contradiction.
    + crush_option (List.find (fun x => foo == x) ξ).
      apply List.find_some in Hx as [Hx Hy]. apply eqb_eq in Hy; subst. contradiction.
    + crush_option (List.find (fun x => foo == x) ξ). easy. eapply List.find_none in Hx; eauto.
      apply neqb_neq in Hx. contradiction.
    + crush_option (List.find (fun x => foo == x) ξ). eapply List.find_some in Hx as [Hx Hy]; eauto.
      apply eqb_eq in Hy; subst; contradiction.
  - unfold context_switchedf in H.
    crush_option (List.find (fun x => foo == x) ξ); destruct t; inv H.
    + constructor. apply List.find_some in Hx as [Hx Hy].
      apply eqb_eq in Hy; subst; assumption.
    + constructor. apply List.find_some in Hx as [Hx Hy].
      apply eqb_eq in Hy; subst; assumption.
    + cbn in Hx. rewrite Hx in H1. inv H1. constructor. intros H. eapply List.find_none in Hx; eauto.
      eq_to_defeq vareq. apply neqb_neq in Hx; contradiction.
    + cbn in Hx. rewrite Hx in H1. inv H1. constructor. intros H. eapply List.find_none in Hx; eauto.
      eq_to_defeq vareq. apply neqb_neq in Hx; contradiction.
Qed.

Inductive estep : EctxStep rtexpr event :=
| E_ectx : forall (Ω Ω' : state) (e e' e0 e0' : expr) (o : option event) (K : evalctx),
    (*Some(K,e) = evalctx_of_expr e0 ->*)
    Some e = pstep_compatible e ->
    e0 = insert K e ->
    e0' = insert K e' ->
    Ω ▷ e --[, o ]--> Ω' ▷ e' ->
    Ω ▷ e0 ==[, o ]==> Ω' ▷ e0'
| E_stuck : forall (Ω : state) (e e0 : expr) (K : evalctx),
    (*Some(K,e) = evalctx_of_expr e0 ->*)
    Some e = pstep_compatible e ->
    e0 = insert K e ->
    Ω ▷ e --[ SCrash ]--> ↯ ▷ stuck ->
    Ω ▷ e0 ==[ SCrash ]==> ↯ ▷ stuck
| E_start : forall (Ω Ω' : state) (Ξ1 Ξ2 : symbols) (main : symbol) (Ψ' : CfState) (e : expr),
    Ω.(SΨ).(CKs) = nil ->
    Ω.(St) = CComp ->
    Ω.(SΦ) = EmptyΦ ->
    ((Ω.(SΨ).(CΞ)) = (Ξ1 ◘ "main"%string ↦ main ◘ Ξ2)) ->
    e = subst (vart_of_symbol main) (expr_of_symbol main) (Xval 0) ->
    Ψ' = Ω.(SΨ) <| CKs := ((Khole, "main"%string) :: nil)%list |> ->
    Ω' = Ω <| St := CCtx |> <| SΨ := Ψ' |> ->
    Ω ▷ Xcall "main"%string (Xval 0) ==[ ev(Sstart ; CComp) ]==> Ω' ▷ e
| E_call : forall (Ω Ω' : state) (Ξ1 Ξ2 : symbols) (foov : vart) (foo : symbol) (Ψ' : CfState)
             (x : vart) (v : value) (K : evalctx) (e0 e0' : expr) (q : comms) (t' : ControlTag),
    Ω.(SΨ).(CΞ) = (Ξ1 ◘ foov ↦ foo ◘ Ξ2) ->
    context_switched Ω.(SΨ).(Cξ) foov Ω.(St) q t' ->
    e0' = subst (vart_of_symbol foo) (expr_of_symbol foo) (Xval v) ->
    Ψ' = Ω.(SΨ) <| CKs := ((K, foov) :: Ω.(SΨ).(CKs)) |> ->
    Ω' = Ω <| St := t' |> <| SΨ := Ψ' |> ->
    e0 = insert K (Xcall foov (Xval v)) ->
    Ω ▷ e0 ==[ ev(Scall q foov v ; Ω.(St)) ]==> Ω' ▷ e0'
| E_ret : forall (Ω Ω' : state) (foov : vart) (K K__foo : evalctx) (Ψ' : CfState)
            (e0 e0' : expr) (v : value) (q : comms) (Ks : active_ectx) (t' : ControlTag),
    context_switched Ω.(SΨ).(Cξ) foov Ω.(St) q t' ->
    Ω.(SΨ).(CKs) = ((K__foo, foov) :: Ks)%list ->
    Ks <> nil -> (* <- prevent E_end from firing *)
    Ψ' = Ω.(SΨ) <| CKs := Ks |> ->
    Ω' = Ω <| St := t' |> <| SΨ := Ψ' |> ->
    e0 = insert K (Xreturn (Xval v)) ->
    e0' = insert K__foo (Xval v) ->
    Ω ▷ e0 ==[ ev(Sret q v ; Ω.(St)) ]==> Ω' ▷ e0'
| E_end : forall (Ω Ω' : state) (K : evalctx) (Ψ' : CfState)
            (e0 : expr) (v : value),
    Ω.(SΨ).(CKs) = ((Khole, "main"%string) :: nil)%list ->
    Ψ' = Ω.(SΨ) <| CKs := nil |> ->
    Ω' = Ω <| St := CComp |> <| SΨ := Ψ' |> ->
    e0 = insert K (Xreturn (Xval v)) ->
    Ω ▷ e0 ==[ ev(Send v ; CCtx) ]==> Ω' ▷ (Xval v)
.
#[global]
Existing Instance estep.
#[global]
Hint Constructors estep : core.

Lemma estep_is_nodupinv_invariant Ω e Ω' e' a :
  Ω ▷ e ==[, a ]==> Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  remember (Ω ▷ e) as r0; remember (Ω' ▷ e') as r1.
  induction 1; inv Heqr0; inv Heqr1; try easy.
  intros H0; apply pstep_is_nodupinv_invariant in H2; eauto.
Qed.
Local Set Warnings "-cast-in-pattern".

Definition estepf (r : rtexpr) : option (option event * rtexpr) :=
  match r with
  | RCrash => None
  | RTerm Ω e =>
    let* (K, e0) := evalctx_of_expr e in
    match e0 with
    | Xcall foo (Xval v) =>
      let* (Ξ1, foof, foo, Ξ2) := splitat Ω.(SΨ).(CΞ) (foo) in
      let e := subst (vart_of_symbol foo) (expr_of_symbol foo) (Xval v) in
      let Ψ' := Ω.(SΨ) <| CKs := ((K, foof) :: Ω.(SΨ).(CKs))%list |> in
      let (q, t') := context_switchedf Ω.(SΨ).(Cξ) foof Ω.(St) in
      let Ω' := Ω <| St := t' |> <| SΨ := Ψ' |> in
      if String.eqb foof "main"%string then
        if andb (Nat.eqb (List.length Ω.(SΨ).(CKs)) 0)
           (andb (Ω.(St) == CComp)
           (andb (Nat.eqb (List.length Ω.(SΦ).(MH__ctx)) 0)
           (andb (Nat.eqb (List.length Ω.(SΦ).(MH__comp)) 0)
                 (Nat.eqb (Util.NoDupInv.length Ω.(SΦ).(MΔ)) 0)))) then
          match v, K, Ω.(SΨ).(CKs), Ω.(St) with
          | Vnat 0, Khole, nil, CComp =>
            Some(Some(ev(Sstart ; CComp)), Ω' ▷ e)
          | _, _, _, _ => None
          end
        else
          (* just a recursive function call to "main", not the initial call, though *)
          Some(Some(ev(Scall q foof v ; Ω.(St))), Ω' ▷ e)
      else
        Some(Some(ev(Scall q foof v ; Ω.(St))), Ω' ▷ e)
    | Xreturn(Xval v) =>
      match Ω.(SΨ).(CKs) with
      | nil => None
      | ((Khole, main)::nil)%list =>
        if String.eqb main "main"%string then
          let Ψ' := Ω.(SΨ) <| CKs := nil |> in
          let Ω' := Ω <| St := CComp |> <| SΨ := Ψ' |> in
          Some(Some(ev(Send v ; CCtx)), Ω' ▷ Xval v)
        else
          None
      | ((K__foo, foo)::Ks)%list =>
        let (q, t') := context_switchedf Ω.(SΨ).(Cξ) foo Ω.(St) in
        let Ψ' := Ω.(SΨ) <| CKs := Ks |> in
        let Ω' := Ω <| St := t' |> <| SΨ := Ψ' |> in
        let e0' := insert K__foo (Xval v) in
        Some(Some(ev(Sret q v ; Ω.(St))), Ω' ▷ e0')
      end
    | _ =>
      let* _ := pstep_compatible e0 in
      let* (a, r') := pstepf (Ω ▷ e0) in
      match r' with
      | RCrash => Some(Some SCrash, ↯ ▷ stuck)
      | RTerm Ω' e0' =>
        let e' := insert K e0' in
        Some(a, Ω' ▷ e')
      end
    end
  end
.

Ltac crush_insert :=
  match goal with
  | [H: insert ?K ?e = ?f |- _] => symmetry in H
  | _ => trivial
  end;
  (match goal with
   | [H: ?f = insert ?K ?e |- _] =>
     let H' := fresh "H" in
     assert (H':=H); generalize dependent e; induction K; intros; cbn in H; try congruence; inv H
   end)
.

Inductive is_val : expr -> Prop :=
| Cval : forall (e : expr) (v : value), e = Xval v -> is_val e
.
(** A runtime expression is classified as value if the associated state is also freed completely. *)
Inductive rtexpr_is_val : rtexpr -> Prop :=
| CRTval : forall (Ω : state) (e : expr) (v : value),
    (forall l t dl, mget Ω.(SΦ).(MΔ) (dK(l ; t)) = Some dl -> dl.(dρ) = ☣) ->
    nodupinv Ω ->
    e = Xval v ->
    rtexpr_is_val (Ω ▷ e)
| CRTfail : rtexpr_is_val (↯ ▷ stuck) (* this will let star_step terminate with a crash *)
.
Lemma expr_val_dec e :
  { is_val e } + { ~is_val e }.
Proof.
  induction e.
  1: destruct v; left; eauto using Cval.
  all: right; intros H; inv H; inv H0.
Qed.
(* unfortunately, this is a rather compute-intense lemma *)
Lemma grab_ectx e K e0 :
  Some e0 = pestep_compatible e0 ->
  e = insert K e0 ->
  evalctx_of_expr e = Some(K, e0)
.
Proof.
  admit.
Admitted.

Lemma easy_ectx e0 :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e0 = Some(Khole, e0).
Proof.
  admit. (*
  induction e0; cbn; try congruence; intros.
  grab_value2 e0_1 e0_2; inv H.
  grab_value3 e0_1 e0_2 e0_3; inv H.
  grab_value4 e0_1 e0_2 e0_3 e0_4; inv H.
  grab_value e0_1.
  grab_value2 e0_1 e0_2.
  grab_value e0.
  grab_value e0_1.
  grab_value2 e0_1 e0_2.
  grab_value2 e0_1 e0_2.
  grab_value e0_1.
  grab_value e0.
  grab_value e0.
  grab_value e0_1.*)
Admitted.

Lemma injective_ectx e0 K e e' :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e = Some(K, e0) ->
  evalctx_of_expr e' = Some(K, e0) ->
  e = e'.
Proof.
Admitted.

Lemma ungrab_ectx e K e0 :
  Some e0 = pestep_compatible e0 ->
  evalctx_of_expr e = Some(K, e0) ->
  e = insert K e0.
Proof.
  intros H H1; remember (insert K e0) as e1;
  eapply grab_ectx in Heqe1 as H2; eauto;
  eapply injective_ectx; eauto.
Qed.
Lemma pstep_compatible_some e e' :
  pstep_compatible e = Some e' -> e = e'.
Proof.
  admit.
Admitted.

Lemma pestep_compatible_some e e' :
  pestep_compatible e = Some e' -> e = e'.
Proof.
Admitted.
Lemma elim_ectx_ret K (v : value) :
  evalctx_of_expr (insert K (Xreturn (Xval v))) = Some(K, Xreturn (Xval v)).
Proof. remember (insert K (Xreturn (Xval v))); eapply grab_ectx in Heqe; eauto. Qed.
Lemma elim_ectx_call K foo (v : value) :
  evalctx_of_expr (insert K (Xcall foo (Xval v))) = Some(K, Xcall foo (Xval v)).
Proof. remember (insert K (Xcall foo (Xval v))); eapply grab_ectx in Heqe; eauto. Qed.

Lemma equiv_estep r0 a r1 :
  r0 ==[, a ]==> r1 <-> estepf r0 = Some(a, r1).
Proof.
Admitted.

Lemma estepf_is_nodupinv_invariant Ω e Ω' e' a :
  estepf (Ω ▷ e) = Some(a, Ω' ▷ e') ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof. intros H0 H1; apply equiv_estep in H0; apply estep_is_nodupinv_invariant in H0; eauto. Qed.

#[export]
Instance TMS__TraceParams : TraceParams := {
  Ev := event ;
  string_of_event := string_of_event;
}.
#[export]
Instance TMS__LangParams : LangParams := {
  State := rtexpr ;
  Trace__Instance := TMS__TraceParams ;
  step := estep ;
  is_value := rtexpr_is_val ;
}.
Definition tracepref : Type := @CSC.Shared.Trace.tracepref TMS__TraceParams.
Import LangNotations.
Open Scope LangNotationsScope.

(** Functional style version of star step from above. We need another parameter "fuel" to sidestep termination. *)
Definition star_stepf (fuel : nat) (r : rtexpr) : option(tracepref * rtexpr) :=
  let fix doo (fuel : nat) (r : rtexpr) :=
    match r with
    | RCrash => Some((SCrash :: nil)%list, (↯ ▷ stuck))
    | RTerm Ω e =>
      match fuel, e with
      | _, Xval _ => (* refl *)
        Some(nil, (Ω ▷ e))
      | S fuel', _ => (* trans variants *)
        let* (o, r') := estepf (Ω ▷ e) in
        let* (As, r'') := doo fuel' r' in
        match o with
        | None => (* trans-unimportant *) Some(As, r'')
        | Some a => (* trans-important *) Some(a :: As, r'')
        end
      | _, _ => (* garbage *)
        Some(nil, Ω ▷ e)
      end
    end
  in doo fuel r
.

Lemma different_reduction Ω Ω' e v v' As :
  ((Ω ▷ e ==[As]==>* Ω' ▷ v) -> False) ->
  Ω ▷ e ==[As]==>* Ω' ▷ v' ->
  v <> v'
.
Proof. intros H0 H1 H2; now subst. Qed.

Lemma star_step_is_nodupinv_invariant Ω e Ω' e' As :
  Ω ▷ e ==[ As ]==>* Ω' ▷ e' ->
  nodupinv Ω ->
  nodupinv Ω'
.
Proof.
  intros H; cbv in H; dependent induction H; try easy; intros.
  - destruct r2 as [Ω0 e0|]. specialize (IHstar_step Ω0 e0 Ω' e' As0 JMeq_refl JMeq_refl JMeq_refl).
    apply IHstar_step. eapply estep_is_nodupinv_invariant; eauto.
    inv H0. inv H2. inv H2.
  - destruct r2 as [Ω0 e0|]. specialize (IHstar_step Ω0 e0 Ω' e' As JMeq_refl JMeq_refl JMeq_refl).
    apply IHstar_step. eapply estep_is_nodupinv_invariant; eauto.
    inv H0. inv H2. inv H2.
Qed.

(** Inductive relation modelling linking *)
Inductive link : symbols -> symbols -> symbols -> Prop :=
| linkEmptyL : forall (Ξ__ctx : symbols), link (mapNil _ _) Ξ__ctx Ξ__ctx
| linkConsL : forall (name : vart) (s : symbol) (Ξ__ctx Ξ__comp Ξ : symbols),
    ~(In name (dom Ξ)) ->
    ~(In name (dom Ξ__ctx)) ->
    ~(In name (dom Ξ__comp)) ->
    link Ξ__ctx Ξ__comp Ξ ->
    link (name ↦ s ◘ Ξ__ctx) Ξ__comp (name ↦ s ◘ Ξ)
.
#[export] Hint Constructors link : core.
Fixpoint linkf (Ξ__ctx Ξ__comp : symbols) : option symbols :=
  match Ξ__ctx with
  | mapNil _ _ => Some(Ξ__comp)
  | (name ↦ s ◘ Ξ__ctx) =>
    let* Ξ := linkf Ξ__ctx Ξ__comp in
    match List.find (fun x => x == name) (dom Ξ),
          List.find (fun x => x == name) (dom Ξ__ctx),
          List.find (fun x => x == name) (dom Ξ__comp) with
    | None, None, None => Some(name ↦ s ◘ Ξ)
    | _, _, _ => None
    end
  end
.
Lemma linkf_equiv_link (Ξ__ctx Ξ__comp Ξ : symbols) :
  linkf Ξ__ctx Ξ__comp = Some Ξ <-> link Ξ__ctx Ξ__comp Ξ
.
Proof.
  split; intros.
  - revert Ξ__comp Ξ H; induction Ξ__ctx; intros; cbn in H.
    + inv H; constructor.
    + crush_option (linkf Ξ__ctx Ξ__comp).
      crush_option (List.find (fun x : vart => vareq x a) (dom x)); try now inv H.
      crush_option (List.find (fun x : vart => vareq x a) (dom Ξ__ctx)); try now (rewrite Hx0 in H; inv H).
      crush_option (List.find (fun x : vart => vareq x a) (dom (Ξ__comp))); try now (rewrite Hx0, Hx1 in H; inv H).
      rewrite Hx0, Hx1, Hx2 in H; inv H; constructor; eauto.
      * intros Hy; eapply List.find_none in Hx0; eauto; eq_to_defeq vareq; apply neqb_neq in Hx0; contradiction.
      * intros Hy; eapply List.find_none in Hx1; eauto; eq_to_defeq vareq; apply neqb_neq in Hx1; contradiction.
      * intros Hy; eapply List.find_none in Hx2; eauto; eq_to_defeq vareq; apply neqb_neq in Hx2; contradiction.
  - induction H; cbn; try easy; rewrite IHlink.
    crush_option (List.find (fun x : vart => vareq x name) (dom Ξ)); try now (apply List.find_some in Hx as [Hx1 Hx2]; eq_to_defeq vareq).
    rewrite Hx.
    crush_option (List.find (fun x : vart => vareq x name) (dom Ξ__ctx)); try now (apply List.find_some in Hx0 as [Hx1 Hx2]; eq_to_defeq vareq).
    rewrite Hx0.
    crush_option (List.find (fun x : vart => vareq x name) (dom (Ξ__comp))); try now (apply List.find_some in Hx1 as [Hx2 Hx3]; eq_to_defeq vareq).
    rewrite Hx1.
    easy.
Qed.

Lemma link_determ (Ξ__ctx Ξ__comp Ξ0 Ξ1 : symbols) :
  link Ξ__ctx Ξ__comp Ξ0 ->
  link Ξ__ctx Ξ__comp Ξ1 ->
  Ξ0 = Ξ1
.
Proof.
  intros H0%linkf_equiv_link H1%linkf_equiv_link;
  revert Ξ__comp Ξ0 Ξ1 H0 H1; induction Ξ__ctx; cbn in *; intros; inv H0; try now inv H1;
  crush_option (linkf Ξ__ctx Ξ__comp);
  crush_option (List.find (fun x : vart => vareq x a) (dom x)).
  now inv H1.
Qed.

(** Top-level programs *)
Inductive prog : Type := Cprog (Ξ__ctx Ξ__comp : symbols) : prog.
