Set Implicit Arguments.
Require Import Lists.List.


Section Util.

Class HasEquality (A : Type) := eq : A -> A -> bool.

Inductive mapind {A : Type} (H : HasEquality A) (B : Type) : Type :=
| mapNil : mapind H B
| mapCons : A -> B -> mapind H B -> mapind H B
.
Fixpoint length { A : Type } {H : HasEquality A} {B : Type} (x : mapind H B) : nat :=
  match x with
  | mapNil _ _ => 0
  | mapCons _a _b xs => 1 + (length xs)
  end
.

Definition dom { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) : list A :=
  let fix dom_aux (m : mapind H B) :=
    match m with
    | mapNil _ _ => @List.nil A
    | mapCons a _b m' => @List.cons A a (dom_aux m')
    end
  in dom_aux m
.
Definition img { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) : list B :=
  let fix img_aux (m : mapind H B) :=
    match m with
    | mapNil _ _ => @List.nil B
    | mapCons _a b m' => @List.cons B b (img_aux m')
    end
  in img_aux m
.
Definition append { A : Type } {H : HasEquality A} {B : Type} (m0 m1 : mapind H B) : mapind H B :=
  let fix append_aux (m0 : mapind H B) :=
    match m0 with
    | mapNil _ _ => m1
    | mapCons a b m' => mapCons a b (append_aux m')
    end
  in append_aux m0
.
(* '↦' is `\mapsto` and '◘' is `\inversebullet`*)
Notation "a '↦' b '◘' M" := (mapCons a b M) (at level 81, b at next level).
Notation "M1 '◘' M2" := (append M1 M2) (at level 82, M2 at next level).

Definition splitat { A : Type } {H : HasEquality A} {B : Type} (m : mapind H B) (x : A)
  : option((mapind H B) * A * B * (mapind H B)) :=
  let fix doo (accM : mapind H B) (m : mapind H B) :=
    match m with
    | mapNil _ _ => None
    | mapCons a b m' => if eq a x then
                         Some(accM, a, b, m')
                       else
                         doo (a ↦ b ◘ accM) m'
    end
  in doo (mapNil H B) m
.

Definition mget { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) : option B :=
  let fix doo (m : mapind H B) :=
    match m with
    | mapNil _ _=> None
    | mapCons a b m' => if eq a x then
                         Some b
                       else
                         doo m'
    end
  in doo m
.
Definition mset { A : Type } { H : HasEquality A } { B : Type } (m : mapind H B) (x : A) (v : B)
  : option(mapind H B) :=
  let fix doo (m : mapind H B) :=
    match m with
    | mapNil _ _ => None
    | mapCons a b m'  => if eq a x then
                          Some(mapCons a v m')
                        else
                          match doo m' with
                          | None => None
                          | Some m'' => Some(a ↦ b ◘ m'')
                          end
    end
  in doo m
.

(** These are synthetic. They simply allow us to write e.g. `PrimStep` instead of supplying it with parameters *)
Class ExprClass (Expr : Type) := {}.
Class RuntimeExprClass (Expr : Type) := {}.
Class EvalCtxClass (Ectx : Type) := {}.
Class TraceEvent (Ev : Type) := {}.

(** Definition of the symbol table. *)
Definition symbols {V E} `{H: HasEquality V} `{EvalCtxClass E} := mapind H E.
Definition nosymb {V E} `{H: HasEquality V} `{EvalCtxClass E} : symbols := mapNil H E.

Class ProgClass {V E} (Prog : Type) `{Hv: HasEquality V}
                      `{He: EvalCtxClass E} := Cprog__Class : symbols -> Prog.

(** Since we only care about security properties anyways, it's fine to stay in "traces are lists"-land *)
Inductive tracepref {Ev : Type} `{TraceEvent Ev} : Type :=
| Tnil : tracepref
| Tcons (e : Ev) (As : tracepref) : tracepref
.
Fixpoint Tappend {Ev : Type} `{TraceEvent Ev} (As Bs : tracepref) : tracepref :=
  match As with
  | Tnil => Bs
  | Tcons e Cs => Tcons e (Tappend Cs Bs)
  end
.
(* Use this to define a coercion *)
Definition ev_to_tracepref {Ev : Type} `{TraceEvent Ev} (e : Ev) : tracepref := Tcons e Tnil.

(* Step-Relation typeclasses. Used as a hack for "overloading" notations *)
Class PrimStep (A : Type) (Ev : Type) `{RuntimeExprClass A} `{TraceEvent Ev} := pstep__Class : A -> (option Ev) -> A -> Prop.
Class CtxStep (A : Type) (Ev : Type) `{RuntimeExprClass A} `{TraceEvent Ev} := estep__Class : A -> (option Ev) -> A -> Prop.
Class MultStep (A : Type) (Ev : Type) `{RuntimeExprClass A} `{TraceEvent Ev} := sstep__Class : A -> tracepref -> A -> Prop.
Class ProgStep (A B : Type) (Ev : Type) (Prog : Type)
               `{ExprClass A} `{RuntimeExprClass B} `{TraceEvent Ev} `{ProgClass A Prog}
  := wstep__Class : Prog -> tracepref -> B -> Prop.
Class VDash (A B C : Type) `{ExprClass B} := vDash : A -> B -> C -> Prop.

End Util.

#[global]
Notation "a '↦' b '◘' M" := (mapCons a b M) (at level 81, b at next level).
#[global]
Notation "M1 '◘' M2" := (append M1 M2) (at level 82, M2 at next level).
#[global]
Notation "As '·' Bs" := (Tappend As Bs) (at level 81).
#[global]
Notation "e0 '--[]-->' e1" := (pstep__Class e0 (None) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[]==>' e1" := (estep__Class e0 (None) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[]==>*' e1" := (sstep__Class e0 (Tnil) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '--[,' a ']-->' e1" := (pstep__Class e0 a e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[,' a ']==>' e1" := (estep__Class e0 a e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '--[' a ']-->' e1" := (pstep__Class e0 (Some a) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[' a ']==>' e1" := (estep__Class e0 (Some a) e1) (at level 82, e1 at next level).
#[global]
Notation "e0 '==[' a ']==>*' e1" := (sstep__Class e0 a e1) (at level 82, e1 at next level).
#[global]
Notation "'PROG[' e0 '][' ep '][' e1 ']====[' As ']===>' r" := (wstep__Class (Cprog__Class e0 ep e1) As r) (at level 81, r at next level).
#[global]
Notation "G '|-' e ':' t" := (vDash G e t) (at level 200, t at next level).
