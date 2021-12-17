Set Implicit Arguments.

Record fresh_state := { counter : nat }.

Definition empty_fresh := {| counter := 0 |}.
Definition fresh (x : fresh_state) : nat := x.(counter).
Definition advance (x : fresh_state) : fresh_state := {| counter := x.(counter) + 1 |}.

