Require Import SetsClass.SetsClass.

Require Import SemanticEquivalence.Syntax.
Require Import SemanticEquivalence.Representation.
Require Import SemanticEquivalence.Denotational.Definition.

Local Open Scope Z.
Local Open Scope sets.

Module DntSem_WhileDCF_Expr.
Import Representation DntSem Lang_WhileDCF.
Import EDenote.

Definition arith_compute_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: word): Prop :=
  let res := Zfun (Z_from_word i1) (Z_from_word i2) in
    i = word_from_Z res /\ Z_in_range res.

Definition arith_compute_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: word): Prop :=
  let res := Zfun (Z_from_word i1) (Z_from_word i2) in
    Z_out_of_range res.

Definition arith_compute_div_mod_nrm
             (f: word -> word -> word)
             (i1 i2 i: word): Prop :=
  i = f i1 i2 /\ div_mod_safe (Z_from_word i1) (Z_from_word i2).

Definition arith_compute_div_mod_err (i1 i2: word): Prop :=
  div_mod_unsafe (Z_from_word i1) (Z_from_word i2).


Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: word): Prop :=
  i = if word_cmp c i1 i2
      then word_from_Z 1
      else word_from_Z 0.


Definition neg_compute_nrm (i1 i: word): Prop :=
  i = word_neg i1 /\ neg_safe (Z_from_word i1).
Definition neg_compute_err (i1: word): Prop :=
  neg_unsafe (Z_from_word i1).

Definition not_compute_nrm (i1 i: word): Prop :=
  Z_from_word i1 <> 0 /\ i = word_from_Z 0 \/
  i1 = word_from_Z 0 /\ i = word_from_Z 1.

Definition SC_and_compute_nrm (i1 i: word): Prop :=
  i1 = word_from_Z 0 /\ i = word_from_Z 0.

Definition SC_or_compute_nrm (i1 i: word): Prop :=
  Z_from_word i1 <> 0 /\ i = word_from_Z 1.

Definition NonSC_and (i1: word): Prop :=
  Z_from_word i1 <> 0.

Definition NonSC_or (i1: word): Prop :=
  i1 = word_from_Z 0.

Definition NonSC_compute_nrm (i2 i: word): Prop :=
  i2 = word_from_Z 0 /\ i = word_from_Z 0 \/
  Z_from_word i2 <> 0 /\ i = word_from_Z 1.

Definition arith_sem_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute_nrm Zfun i1 i2 i.

Definition arith_sem_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> word -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute_err Zfun i1 i2.

Definition arith_sem Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem_div_mod_nrm
             (f: word -> word -> word)
             (D1 D2: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute_div_mod_nrm f i1 i2 i.

Definition arith_sem_div_mod_err
             (D1 D2: state -> word -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute_div_mod_err i1 i2.

Definition arith_sem_div_mod f (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem_div_mod_nrm f D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem_div_mod_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_sem_nrm
             (D1: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> word -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

Definition and_sem_nrm
             (D1 D2: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> word -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> word -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem Z.add D1 D2
  | OMinus => arith_sem Z.sub D1 D2
  | OMul => arith_sem Z.mul D1 D2
  | ODiv => arith_sem_div_mod word_div D1 D2
  | OMod => arith_sem_div_mod word_mod D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = word_from_Z n /\ Z_in_range n;
    err := fun s => Z_out_of_range n;
  |}.

Definition deref_sem_nrm
             (D1: state -> word -> Prop)
             (s: state)
             (i: word): Prop :=
  exists i1, D1 s i1 /\ s.(mem) i1 = Mstore (Vint i).

Definition deref_sem_err
             (D1: state -> word -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\
    (s.(mem) i1 = Memp \/ s.(mem) i1 = Mstore Vuninit).

Definition deref_sem_r (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

Definition var_sem_l (X: var_id): EDenote :=
  {|
    nrm := fun s i => s.(var) X = i;
    err := ∅;
  |}.

Definition var_sem_r (X: var_id): EDenote :=
  deref_sem_r (var_sem_l X).

Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem_r X
  | EBinop op e1 e2 =>
      binop_sem op (eval_r e1) (eval_r e2)
  | EUnop op e1 =>
      unop_sem op (eval_r e1)
  | EDeref e1 =>
      deref_sem_r (eval_r e1)
  | EAddrOf e1 =>
      eval_l e1
  end
with eval_l (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l X
  | EDeref e1 =>
      eval_r e1
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

End DntSem_WhileDCF_Expr.
