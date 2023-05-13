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
  | EAddrOf (e: expr): expr
.

Inductive com : Type :=
  | CSkip: com
  | CLocalVar (x: var_id) (v: val) (c1: com): com
  | CLocalVarEnv (x: var_id) (a : address) (c: com): com
  | CAsgnVar (x: var_id) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CProcCall (p: func_id) (es: list expr): com
  | CProcCallEnv (xs : list var_id) (vs: list word) (c: com): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CFor (c1: com) (e: expr) (c2: com) (c3: com): com
  | CDoWhile (c: com) (e: expr): com
  | CContinue: com
  | CBreak: com
  | CReturn: com
.

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

Module WhileDCF_Notation.
Import Representation.
Import Lang_WhileDCF.

Declare Custom Entry whiledcf_entry.
Coercion EConst: Z >-> expr.
Coercion EVar: var_id >-> expr.

Notation "[[ e ]]" := e
  (at level 0, e custom whiledcf_entry at level 99).
Notation "( x )" := x
  (in custom whiledcf_entry, x custom whiledcf_entry at level 99).
Notation "x" := x
  (in custom whiledcf_entry at level 0, x constr at level 99).
Notation "x ` op ` y" := (EBinop op x y)
  (in custom whiledcf_entry at level 0, op constr at level 99, x custom whiledcf_entry, y custom whiledcf_entry at level 99).
Notation "` op ` x" := (EUnop op x)
  (in custom whiledcf_entry at level 0, op constr at level 99, x custom whiledcf_entry at level 99).
Notation "* x" := (EDeref x)
  (in custom whiledcf_entry at level 0, x custom whiledcf_entry at level 99).
Notation "& x" := (EAddrOf x)
  (in custom whiledcf_entry at level 0, x custom whiledcf_entry at level 99).

Notation "'skip'" := CSkip
  (in custom whiledcf_entry at level 0).
Notation "'let' x <- v 'in' c" := (CLocalVar x v c)
  (in custom whiledcf_entry at level 0, x constr at level 99, c custom whiledcf_entry at level 99).
Notation "'let' x 'prev' a 'in' c" := (CLocalVarEnv x a c)
  (in custom whiledcf_entry at level 0, x constr at level 99, a constr at level 99, c custom whiledcf_entry at level 99).
Notation "x <- e" := (CAsgnVar x e)
  (in custom whiledcf_entry at level 0, x constr at level 99, e custom whiledcf_entry at level 99).
Notation "* e1 <- e2" := (CAsgnDeref e1 e2)
  (in custom whiledcf_entry at level 0, e1 custom whiledcf_entry at level 99, e2 custom whiledcf_entry at level 99).
Notation "p '.apply' ( es )" := (CProcCall p es)
  (in custom whiledcf_entry at level 0, p constr at level 99, es constr at level 99).
Notation "'fn' ( xs <- vs ) c" := (CProcCallEnv xs vs c)
  (in custom whiledcf_entry at level 0, xs constr at level 99, vs constr at level 99, c custom whiledcf_entry at level 99).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom whiledcf_entry at level 0).
Notation "'if' e 'then' c1 'else' c2" := (CIf e c1 c2)
  (in custom whiledcf_entry at level 0).
Notation "'while' e 'do' c" := (CWhile e c)
  (in custom whiledcf_entry at level 0).
Notation "'for' c1 ; e ; c2 'do' c3" := (CFor c1 e c2 c3)
  (in custom whiledcf_entry at level 0).
Notation "'do' c 'while' e" := (CDoWhile c e)
  (in custom whiledcf_entry at level 0).
Notation "'continue'" := CContinue
  (in custom whiledcf_entry at level 0).
Notation "'break'" := CBreak
  (in custom whiledcf_entry at level 0).
Notation "'return'" := CReturn
  (in custom whiledcf_entry at level 0).

End WhileDCF_Notation.
