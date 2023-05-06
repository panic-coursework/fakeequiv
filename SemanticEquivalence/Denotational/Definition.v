Require Export SemanticEquivalence.Representation.

Module DntSem.
Import Representation.

Record state: Type := {
  var: var_id -> address;
  mem: address -> memory_state;
}.
Notation "x '.(var)'" := (var x)
  (at level 1).
Notation "x '.(mem)'" := (mem x)
  (at level 1).

Module EDenote.
Record EDenote: Type := {
  nrm: state -> word -> Prop;
  err: state -> Prop;
}.
End EDenote.
Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).
Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).


Module CDenote.
Record CDenote: Type := {
  nrm: state -> state -> Prop;
  brk: state -> state -> Prop;
  cnt: state -> state -> Prop;
  ret: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop;
}.
End CDenote.
Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).
Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).
Notation "x '.(brk)'" := (CDenote.brk x)
  (at level 1).
Notation "x '.(cnt)'" := (CDenote.cnt x)
  (at level 1).
Notation "x '.(ret)'" := (CDenote.ret x)
  (at level 1).
Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1, only printing).


Module PDenote.
Record PDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop;
}.
End PDenote.
Import PDenote.

Notation "x '.(nrm)'" := (PDenote.nrm x)
  (at level 1, only printing).
Notation "x '.(err)'" := (PDenote.err x)
  (at level 1, only printing).
Notation "x '.(inf)'" := (PDenote.inf x)
  (at level 1, only printing).

Ltac any_nrm x :=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  | PDenote => exact (PDenote.nrm x)
  end.

Ltac any_err x :=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  | PDenote => exact (PDenote.err x)
  end.

Ltac any_inf x :=
  match type of x with
  | CDenote => exact (CDenote.err x)
  | PDenote => exact (PDenote.err x)
  end.

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).
Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).
Notation "x '.(inf)'" := (ltac:(any_inf x))
  (at level 1, only parsing).

End DntSem.
