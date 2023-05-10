From Coq Require Export ZArith.
Require Export compcert.lib.Integers.

Local Open Scope Z.

Module Representation.

Definition var_id : Type := nat.
Definition func_id : Type := nat.

Definition var_id_eqb := Nat.eqb.

Definition word : Type := int64.

Definition word_from_Z x := Int64.repr x.
Definition Z_from_word w := Int64.signed w.
Definition Z_word_min : Z := Int64.min_signed.
Definition Z_word_max : Z := Int64.max_signed.

Definition Z_in_range (x : Z) := Z_word_min <= x <= Z_word_max.
Definition Z_out_of_range (x : Z) := x < Z_word_min \/ x > Z_word_max.

Definition word_div := Int64.divs.
Definition word_mod := Int64.mods.
Definition Z_div (x y : Z) :=
  Z_from_word (word_div (word_from_Z x) (word_from_Z y)).
Definition Z_mod (x y : Z) :=
  Z_from_word (word_mod (word_from_Z x) (word_from_Z y)).
Definition div_mod_safe (x y : Z) := y <> 0 /\ (x <> Int64.min_signed \/ y <> -1).
Definition div_mod_unsafe (x y : Z) := not (div_mod_safe x y).

Definition word_cmp := Int64.cmp.
Definition word_neg := Int64.neg.
Definition Z_neg (v : Z) := Z_from_word (word_neg (word_from_Z v)).
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

Record state: Type := {
  var: var_id -> address;
  mem: address -> memory_state;
}.
Notation "x '.(var)'" := (var x)
  (at level 1).
Notation "x '.(mem)'" := (mem x)
  (at level 1).


Definition set_addr
             (x: var_id)
             (l1 l2: word):
  state -> state -> Prop :=
  fun s1 s2 => s1.(var) x = l1 /\ s2.(var) x = l2.

Definition alloc_mem (l: word) (v : val):
  state -> state -> Prop :=
  fun s1 s2 =>
    (s1.(mem) l = Memp /\ s2.(mem) l = Mstore v) /\
    (forall l', l <> l' -> s1.(mem) l' = s2.(mem) l').

Definition dealloc_mem (l: word):
  state -> state -> Prop :=
  fun s1 s2 =>
    (s1.(mem) l <> Memp /\ s2.(mem) l = Memp) /\
    (forall l', l <> l' -> s1.(mem) l' = s2.(mem) l').

End Representation.
