From Coq Require Import List.
Require Import SetsClass.SetsClass.

Require Import SemanticEquivalence.Syntax.
Require Import SemanticEquivalence.Representation.
Require Import SemanticEquivalence.Denotational.Definition.
Require Import SemanticEquivalence.Denotational.Expressions.
Require Import SemanticEquivalence.Denotational.Statements.
Require Import SemanticEquivalence.SmallStep.Step.

Local Open Scope Z.
Local Open Scope sets.

Module Equivalence_Com.
Import Representation Lang_WhileDCF.
Import SetsNotation WhileDCF_Notation DntSem.
Import DntSem_WhileDCF_Expr DntSem_WhileDCF_Com SmallStep_WhileDCF.

Definition multistep_com_term (s' : state) (k : list com_context) : (state * com * list com_context) :=
  (s', [[skip]], k).

Definition not_multistep_com_term (k : list com_context) (p : state * com * list com_context) : Prop :=
  match p with
  | (_, [[skip]], k) => False
  | _ => True
  end.

Lemma step_com_ctx (prog : program) : forall s s' c c' k1 k1' k2,
  multistep_com prog (s, c, k1) (s', c', k1') ->
  multistep_com prog (s, c, k1 ++ k2) (s', c', k1' ++ k2).
Proof.
  intros.
  destruct H.
  induction x.
  - unfold nsteps in H; sets_unfold in H.
    injection H; intros; subst.
    unfold multistep_com, clos_refl_trans.
    sets_unfold.
    exists 0%nat; simpl; sets_unfold.
    reflexivity.
  - simpl in H.
    sets_unfold in H.
    destruct H, H, x0, p.
Admitted.


Definition com_equiv_nrm (prog : program) : forall s s' c,
  (eval_com prog c).(nrm) s s' <->
  forall k,
  multistep_com prog (s, c, k) (s', [[skip]], k).
Proof.
  intros.
Admitted.

Definition com_equiv_brk (prog : program) : forall s s' c,
  (eval_com prog c).(brk) s s' <->
  forall k,
  multistep_com prog (s, c, k) (s', [[break]], k).
Proof.
  intros.
Admitted.

Definition com_equiv_cnt (prog : program) : forall s s' c,
  (eval_com prog c).(cnt) s s' <->
  forall k,
  multistep_com prog (s, c, k) (s', [[continue]], k).
Proof.
  intros.
Admitted.

Definition com_equiv_ret (prog : program) : forall s s' c,
  (eval_com prog c).(ret) s s' <->
  forall k,
  multistep_com prog (s, c, k) (s', [[return]], k).
Proof.
  intros.
Admitted.

Definition com_equiv_err (prog : program) : forall s c,
  (eval_com prog c).(err) s <->
  exists x',
  forall k x'',
  not_multistep_com_term k x' /\
  multistep_com prog (s, c, k) x' /\
  not (multistep_com prog x' x'').
Proof.
  intros.
Admitted.

Definition com_equiv_inf (prog : program) : forall s c,
  (eval_com prog c).(inf) s <->
  forall x' k,
  multistep_com prog (s, c, k) x' ->
  exists x'',
  multistep_com prog x' x''.
Proof.
  intros.
Admitted.


Theorem program_equiv_nrm (prog : program) : forall s s',
  (eval_program prog).(nrm) s s' <->
  multistep_com prog (prog_entry prog s) (multistep_com_term s' nil).
Proof.
  intros.
Admitted.

Theorem program_equiv_err (prog : program) : forall s,
  (eval_program prog).(err) s <->
  exists x',
  not_multistep_com_term nil x' ->
  multistep_com prog (prog_entry prog s) x' ->
  forall x'',
  not (step_com prog x' x'').
Proof.
  intros.
Admitted.

Theorem program_equiv_inf (prog : program) : forall s,
  (eval_program prog).(inf) s <->
  forall x',
  multistep_com prog (prog_entry prog s) x' ->
  exists x'',
  multistep_com prog x' x''.
Proof.
  intros.
Admitted.

End Equivalence_Com.
