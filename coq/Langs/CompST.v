Set Implicit Arguments.
Require Import Strings.String Strings.Ascii Numbers.Natural.Peano.NPeano Lists.List Program.Equality Recdef.
Require Import CSC.Sets CSC.Util CSC.Fresh CSC.Langs.Util.
Require CSC.Langs.TMMon CSC.Langs.S CSC.Langs.T.

(** * Secure Compiler from S to T *)

(** compilation of binary operator symbols *)
Definition comp__b (b : S.binopsymb) : T.binopsymb :=
  match b with
  | S.Badd => T.Badd
  | S.Bsub => T.Bsub
  | S.Bmul => T.Bmul
  | S.Bless => T.Bless
  end
.
(** compilation of expressions *)
Fixpoint comp__e (e : S.expr) : T.expr :=
  match e with
  | S.Xabort => T.Xabort
  | S.Xres(S.Fabrt) => T.Xres(T.Fabrt)
  | S.Xres(S.Fres f) =>
      match f with
      | S.Fvar x => T.Xres(T.Fres(T.Fvar x))
      | S.Fval(S.Vnat n) => T.Xres(T.Fres(T.Fval(T.Vnat n)))
      end
  | S.Xbinop b e1 e2 =>
      let c1 := comp__e e1 in
      let c2 := comp__e e2 in
      let bb := comp__b b in
      T.Xbinop bb c1 c2
  | S.Xget x e =>
      let c := comp__e e in
      T.Xget x c
  | S.Xset x e0 e1 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      T.Xset x c0 c1
  | S.Xlet x e0 e1 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      T.Xlet x c0 c1
  | S.Xnew x e0 e1 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      T.Xnew x c0 c1
  | S.Xdel x => T.Xdel x
  | S.Xreturn e =>
      let c := comp__e e in
      T.Xreturn c
  | S.Xcall foo e =>
      let c := comp__e e in
      T.Xcall foo c
  | S.Xifz e0 e1 e2 =>
      let c0 := comp__e e0 in
      let c1 := comp__e e1 in
      let c2 := comp__e e2 in
      T.Xifz c0 c1 c2
  end
.

(** Compiling symbols *)
Definition comp__symb (F : S.symbol) : option(T.symbol) :=
  let '(x__arg', τ__fn, e__bdy) := F in
  let x__arg := T.Xres(T.Fres(T.Fvar(x__arg'))) in
  match τ__fn with
  | S.Tectx(S.Tarrow τ0 _τ1) =>
     match τ0 with
     | S.Tnat =>
         Some(x__arg', T.Xifz (T.Xhas x__arg T.Tnat) (comp__e e__bdy) (T.Xabort))
     | S.Tnatptr S.Qhalf =>
         Some(x__arg', T.Xifz (T.Xhas x__arg T.Tnat)
                      (T.Xabort)
                      (T.Xifz (T.Xhas x__arg T.Tpair)
                              (T.Xabort)
                              (T.Xifz (T.Xispoison x__arg')
                                      (T.Xabort)
                                      (comp__e e__bdy))))
     | _ => None
     end
  | _ => None
  end
.
Fixpoint comp__symbs (Fs : S.symbols) : option(T.symbols) :=
  match Fs with
  | mapNil _ _ => Some(mapNil _ _)
  | mapCons foo symb rest =>
      let* thesymb := comp__symb symb in
      let* therest := comp__symbs rest in
      Some(mapCons foo thesymb therest)
  end
.

(** Definition of various relations *)
Definition locmap_st (ℓ : S.loc) : T.loc :=
  let '(S.addr n) := ℓ in T.addr n
.
Inductive poison_eq : S.poison -> T.poison -> Prop :=
| poisonedEqual : poison_eq S.poisoned T.poisoned
| poisonlessEqual : poison_eq S.poisonless T.poisonless
.
Inductive memstate_eq : (S.heap * S.store) -> (T.heap * T.store) -> Prop :=
| empty_memstate_eq : memstate_eq (mapNil _ _, mapNil _ _) (mapNil _ _, mapNil _ _)
(* TODO *)
.

(** Lemmas *)

Lemma injective_comp__e (e : S.expr) (et₁ et₂ : T.expr) :
  comp__e e = et₁ ->
  comp__e e = et₂ ->
  et₁ = et₂
.
Proof.
  now induction e; intros H1 H2; match goal with | [H: _ = et₁ |- et₁ = et₂] => inv H end.
Qed.
