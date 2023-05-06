From Coq Require Export ZArith.
Require Export compcert.lib.Integers.

Local Open Scope Z.

Module Representation.

Definition var_id : Type := nat.
Definition func_id : Type := nat.

Definition word : Type := int64.

Definition word_from_Z x := Int64.repr x.
Definition Z_from_word w := Int64.signed w.
Definition Z_word_min : Z := Int64.min_signed.
Definition Z_word_max : Z := Int64.max_signed.

Definition Z_in_range (x : Z) := Z_word_min <= x <= Z_word_max.
Definition Z_out_of_range (x : Z) := x < Z_word_min \/ x > Z_word_max.

Definition word_div := Int64.divs.
Definition word_mod := Int64.mods.
Definition div_mod_safe (x y : Z) := y <> 0 /\ (x <> Int64.min_signed \/ y <> -1).
Definition div_mod_unsafe (x y : Z) := not (div_mod_safe x y).

Definition word_cmp := Int64.cmp.
Definition word_neg := Int64.neg.
Definition neg_safe (x : Z) := x <> Int64.min_signed.
Definition neg_unsafe (x : Z) := x = Int64.min_signed.

Definition address : Type := int64.

Inductive val : Type :=
| Vuninit : val
| Vint (i : word) : val
.

Inductive memory_state :=
| Memp : memory_state
| Mstore (v : val) : memory_state
.

End Representation.
