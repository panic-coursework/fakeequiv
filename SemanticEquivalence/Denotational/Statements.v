Require Import SetsClass.SetsClass.

Require Import SemanticEquivalence.Syntax.
Require Import SemanticEquivalence.Denotational.Definition.
Require Import SemanticEquivalence.Denotational.Expressions.

Local Open Scope Z.
Local Open Scope sets.

Module DntSem_WhileDCF_Com.
Import SetsNotation.
Import Representation DntSem Lang_WhileDCF.
Import EDenote CDenote.
Import DntSem_WhileDCF_Expr.


Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    brk := ∅;
    cnt := ∅;
    ret := ∅;
    err := ∅;
    inf := ∅;
  |}.

Definition brk_sem: CDenote :=
  {|
    nrm := ∅;
    brk := Rels.id;
    cnt := ∅;
    ret := ∅;
    err := ∅;
    inf := ∅;
  |}.

Definition cnt_sem: CDenote :=
  {|
    nrm := ∅;
    brk := ∅;
    cnt := Rels.id;
    ret := ∅;
    err := ∅;
    inf := ∅;
  |}.

Definition ret_sem: CDenote :=
  {|
    nrm := ∅;
    brk := ∅;
    cnt := ∅;
    ret := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    brk := D1.(brk) ∪ (D1.(nrm) ∘ D2.(brk));
    cnt := D1.(cnt) ∪ (D1.(nrm) ∘ D2.(cnt));
    ret := D1.(ret) ∪ (D1.(nrm) ∘ D2.(ret));
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Z_from_word i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (word_from_Z 0)).


Definition if_sem_wrap
  (D0 : EDenote)
  (D1 D2 : CDenote)
  (field : CDenote -> state -> state -> Prop) :=
     (test_true D0 ∘ (field D1)) ∪
     (test_false D0 ∘ (field D2)).

Definition if_sem_wrap_noreturn
  (D0 : EDenote)
  (D1 D2 : CDenote)
  (field : CDenote -> state -> Prop) :=
     (test_true D0 ∘ (field D1)) ∪
     (test_false D0 ∘ (field D2)).

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := if_sem_wrap D0 D1 D2 CDenote.nrm;
    brk := if_sem_wrap D0 D1 D2 CDenote.brk;
    cnt := if_sem_wrap D0 D1 D2 CDenote.cnt;
    ret := if_sem_wrap D0 D1 D2 CDenote.ret;
    err := D0.(err) ∪ (if_sem_wrap_noreturn D0 D1 D2 CDenote.err);
    inf := if_sem_wrap_noreturn D0 D1 D2 CDenote.inf;
  |}.

Definition asgn_deref_sem_nrm
             (D1 D2: state -> word -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> Memp /\
    s2.(mem) i1 = Mstore (Vint i2) /\
    (forall X, s1.(var) X = s2.(var) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> word -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    s1.(mem) i1 = Memp.

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    brk := ∅;
    cnt := ∅;
    ret := ∅;
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

Definition asgn_var_sem
             (X: var_id)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

Module WhileSem.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D1.(nrm) ∘ iter_nrm_lt_n D0 D1 n0) ∪
          (D1.(cnt) ∘ iter_nrm_lt_n D0 D1 n0) ∪
          D1.(brk))) ∪
      (test_false D0)
  end.

Fixpoint iter_ret_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D1.(nrm) ∘ iter_ret_lt_n D0 D1 n0) ∪
          D1.(ret)))
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ iter_err_lt_n D0 D1 n0) ∪
         (D1.(cnt) ∘ iter_err_lt_n D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘
        ((D1.(nrm) ∘ X) ∪
         (D1.(cnt) ∘ X) ∪
         D1.(inf)).

End WhileSem.

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (WhileSem.iter_nrm_lt_n D0 D1);
    brk := ∅;
    cnt := ∅;
    ret := ⋃ (WhileSem.iter_ret_lt_n D0 D1);
    err := ⋃ (WhileSem.iter_err_lt_n D0 D1);
    inf := Sets.general_union (WhileSem.is_inf D0 D1);
  |}.

Definition do_while_sem
             (D0: CDenote)
             (D1: EDenote): CDenote :=
  {|
    nrm := (D0.(nrm) ∪ D0.(cnt)) ∘
           ⋃ (WhileSem.iter_nrm_lt_n D1 D0);
    brk := ∅;
    cnt := ∅;
    ret := D0.(ret) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            ⋃ (WhileSem.iter_ret_lt_n D1 D0));
    err := D0.(err) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            ⋃ (WhileSem.iter_err_lt_n D1 D0));
    inf := D0.(inf) ∪
           ((D0.(nrm) ∪ D0.(cnt)) ∘
            Sets.general_union (WhileSem.is_inf D1 D0));
  |}.

Module ForSem.

Fixpoint iter_nrm_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘
         ((D2.(nrm) ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 D2 n0) ∪
          (D2.(cnt) ∘ D1.(nrm) ∘ iter_nrm_lt_n D0 D1 D2 n0) ∪
          D2.(brk))) ∪
      (test_false D0)
  end.

Fixpoint iter_ret_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ iter_ret_lt_n D0 D1 D2 n0) ∪
         (D2.(nrm) ∘ D1.(ret)) ∪
         (D2.(ret)))
  end.

Fixpoint iter_err_lt_n
           (D0: EDenote)
           (D1: CDenote)
           (D2: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ iter_err_lt_n D0 D1 D2 n0) ∪
         (D2.(cnt) ∘ D1.(nrm) ∘ iter_err_lt_n D0 D1 D2 n0) ∪
         D2.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (D2: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘
        ((D2.(nrm) ∘ D1.(nrm) ∘ X) ∪
         (D2.(cnt) ∘ D1.(nrm) ∘ X) ∪
         (D2.(nrm) ∘ D1.(inf)) ∪
         (D2.(nrm) ∘ D1.(inf)) ∪
         D2.(inf)).

End ForSem.

Definition for_sem
             (D: CDenote)
             (D0: EDenote)
             (D1: CDenote)
             (D2: CDenote): CDenote :=
  {|
    nrm := D.(nrm) ∘ ⋃ (ForSem.iter_nrm_lt_n D0 D1 D2);
    brk := ∅;
    cnt := ∅;
    ret := D.(ret) ∪ (D.(nrm) ∘ ⋃ (ForSem.iter_ret_lt_n D0 D1 D2));
    err := D.(err) ∪ (D.(nrm) ∘ ⋃ (ForSem.iter_err_lt_n D0 D1 D2));
    inf := D.(inf) ∪ (D.(nrm) ∘ Sets.general_union (ForSem.is_inf D0 D1 D2));
  |}.

Definition set_addr
             (x: var_id)
             (l1 l2: word):
  state -> state -> Prop :=
  fun s1 s2 => s1.(var) x = l1 /\ s2.(var) x = l2.

Definition alloc_mem (l: word):
  state -> state -> Prop :=
  fun s1 s2 =>
    (s1.(mem) l = Memp /\ s2.(mem) l = Mstore Vuninit) /\
    (forall l', l <> l' -> s1.(mem) l' = s2.(mem) l').

Definition dealloc_mem (l: word):
  state -> state -> Prop :=
  fun s1 s2 =>
    (s1.(mem) l <> Memp /\ s2.(mem) l = Memp) /\
    (forall l', l <> l' -> s1.(mem) l' = s2.(mem) l').

Definition alloc_mem_err: state -> Prop :=
  fun s => forall l, s.(mem) l <> Memp.

Definition local_var_sem_wrap (x : var_id) (rel : state -> state -> Prop) :=
  ⋃ (fun l1 =>
    ⋃ (fun l2 =>
      (set_addr x l1 l2 ∩ alloc_mem l2) ∘
      rel ∘
      (set_addr x l2 l1 ∩ dealloc_mem l2))).

Definition local_var_sem_wrap_noreturn (x : var_id) (rel : state -> Prop) :=
  ⋃ (fun l1 =>
    ⋃ (fun l2 =>
      (set_addr x l1 l2 ∩ alloc_mem l2) ∘
      rel)).

Definition local_var_sem
             (x: var_id)
             (D: CDenote): CDenote :=
  {|
    nrm := local_var_sem_wrap x D.(nrm);
    brk := local_var_sem_wrap x D.(cnt);
    cnt := local_var_sem_wrap x D.(cnt);
    ret := local_var_sem_wrap x D.(ret);
    err := local_var_sem_wrap_noreturn x D.(err) ∪ alloc_mem_err;
    inf := local_var_sem_wrap_noreturn x D.(inf);
  |}.

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CLocalVar x c =>
      local_var_sem x (eval_com c)
  | CAsgnVar X e =>
      asgn_var_sem X (eval_r e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_r e1) (eval_r e2)
  | CProcCall p es =>
      skip_sem (* bogus *)
      (* proc_call_sem p (map eval_r es) *)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_r e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_r e) (eval_com c1)
  | CDoWhile c1 e =>
      do_while_sem (eval_com c1) (eval_r e)
  | CFor c0 e c1 c2 =>
      for_sem
        (eval_com c0) (eval_r e) (eval_com c1) (eval_com c2)
  | CContinue =>
      cnt_sem
  | CBreak =>
      brk_sem
  | CReturn =>
      ret_sem
  end.


End DntSem_WhileDCF_Com.
