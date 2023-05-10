From Coq Require Import ZArith.
Require Import SemanticEquivalence.Representation.
Local Open Scope Z.

Module Lang_WhileDCF.
Import Representation.

Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_id): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr.

Inductive com : Type :=
  | CSkip: com
  | CLocalVar (x: var_id) (c1: com): com
  | CAsgnVar (x: var_id) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CProcCall (p: func_id) (es: list expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CFor (c1: com) (e: expr) (c2: com) (c3: com): com
  | CDoWhile (c: com) (e: expr): com
  | CContinue: com
  | CBreak: com
  | CReturn: com.

Record proc: Type := {
  name_proc: func_id;
  body_proc: com;
  params_proc: list var_id;
}.

Record program: Type := {
  global_vars: list var_id;
  procs: func_id -> option proc;
  entry: func_id;
}.

End Lang_WhileDCF.
