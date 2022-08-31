Set Implicit Arguments.
Require Import Strings.String.

Record fresh_state := { counter : nat }.

Definition empty_fresh := {| counter := 0 |}.
Definition fresh (x : fresh_state) : nat := x.(counter).
Definition freshv (x : fresh_state) : string := "x"%string.
Definition advance (x : fresh_state) : fresh_state := {| counter := x.(counter) + 1 |}.

