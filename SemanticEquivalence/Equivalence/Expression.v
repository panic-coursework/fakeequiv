From Coq Require Import List.
Require Import SetsClass.SetsClass.

Require Import SemanticEquivalence.Syntax.
Require Import SemanticEquivalence.Representation.
Require Import SemanticEquivalence.Denotational.Definition.
Require Import SemanticEquivalence.Denotational.Expressions.
Require Import SemanticEquivalence.SmallStep.Step.

Local Open Scope Z.
Local Open Scope sets.

Module Equivalence_Expr.
Import Representation Lang_WhileDCF.
Import SetsNotation WhileDCF_Notation DntSem.
Import DntSem_WhileDCF_Expr SmallStep_WhileDCF.

Theorem eval_multistep_nrm : forall s e v,
  Z_in_range v ->
  (eval_r e).(nrm) s (word_from_Z v) ->
  multistep_expr s e (EConst v).
Proof.
  intros.
  unfold multistep_expr, clos_refl_trans.
  sets_unfold.
  exists 114514%nat.
Admitted.

Definition not_const (e : expr) :=
  match e with
  | EConst _ => False
  | _ => True
  end.

Theorem eval_multistep_err : forall s e,
  (eval_r e).(err) s ->
  exists e',
  not_const e' /\
  multistep_expr s e e' /\
  forall e'',
  not (step_expr s e' e'').
Proof.
  intros.
Admitted.

Theorem multistep_eval_nrm : forall s e v,
  Z_in_range v ->
  multistep_expr s e (EConst v) ->
  (eval_r e).(nrm) s (word_from_Z v).
Proof.
  intros.
Admitted.

Theorem multistep_eval_err : forall s e e',
  not_const e' ->
  multistep_expr s e e' ->
  (forall e'', not (step_expr s e' e'')) ->
  (eval_r e).(err) s.
Proof.
  intros.
Admitted.

End Equivalence_Expr.
