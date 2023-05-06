From Coq Require Import List.
Require Import SetsClass.SetsClass.

Require Import SemanticEquivalence.Syntax.
Require Import SemanticEquivalence.Denotational.Definition.
Require Import SemanticEquivalence.Denotational.Expressions.
Require Import SemanticEquivalence.Denotational.Statements.

Local Open Scope sets.

Module DntSem_WhileDCF.
Import SetsNotation.
Import Representation DntSem Lang_WhileDCF.
Import CDenote PDenote.
Import DntSem_WhileDCF_Com.

Definition find_entry (p : program) :=
  find (fun f => name f =? entry p) (procs p).

Definition eval_program_nrm (p : program) :=
  match (find_entry p) with
  | Some f => (eval_com (body f)).(nrm)
  | None => ∅
  end.

Definition eval_program_err (p : program) :=
  match (find_entry p) with
  | Some f => (eval_com (body f)).(err)
  | None => Sets.full
  end.

Definition eval_program_inf (p : program) :=
  match (find_entry p) with
  | Some f => (eval_com (body f)).(inf)
  | None => ∅
  end.

Definition eval_program (p : program) : PDenote := {|
  nrm := eval_program_nrm p;
  err := eval_program_err p;
  inf := eval_program_inf p;
|}.

End DntSem_WhileDCF.
