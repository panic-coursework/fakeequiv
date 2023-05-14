From Coq Require Import List.
Require Import SetsClass.SetsClass.

Require Import SemanticEquivalence.Syntax.
Require Import SemanticEquivalence.Representation.

Local Open Scope Z.
Local Open Scope sets.

Module SmallStep_WhileDCF.
Import Representation Lang_WhileDCF.
Import SetsNotation WhileDCF_Notation.

Inductive binop_class_t :=
| OCOr | OCAnd | OCCmp | OCArith | OCDivMod.
Definition binop_class (op : binop) :=
  match op with
  | OOr => OCOr
  | OAnd => OCAnd
  | OLt => OCCmp
  | OLe => OCCmp
  | OGt => OCCmp
  | OGe => OCCmp
  | OEq => OCCmp
  | ONe => OCCmp
  | OPlus => OCArith
  | OMinus => OCArith
  | OMul => OCArith
  | ODiv => OCDivMod
  | OMod => OCDivMod
  end.

Definition cmp_compute (op : binop) (v1 v2 : Z) :=
  let c := match op with
    | OLt => Clt
    | OLe => Cle
    | OGt => Cgt
    | OGe => Cge
    | OEq => Ceq
    | ONe => Cne
    | _ => Clt (* bogus *)
  end in
  if word_cmp c (word_from_Z v1) (word_from_Z v2)
  then 1
  else 0.

Definition arith_compute (op : binop) :=
  match op with
  | OPlus => Z.add
  | OMinus => Z.sub
  | OMul => Z.mul
  | _ => (fun _ _ => 0) (* bogus *)
  end.

Definition not_compute (v : Z) :=
  if v =? 0 then 1 else 0.

Definition trueval (v : Z) : Prop :=
  v <> 0 /\ Z_in_range v.

Inductive step_expr (s : state) : expr -> expr -> Prop :=
| ES_Var (x : var_id) :
    step_expr s [[ x ]] [[ *(Z_from_word (s.(var) x)) ]]

| ES_Binop_L (op : binop) : forall e1 e1' e2,
    step_expr s e1 e1' ->
    step_expr s [[ e1 `op` e2 ]] [[ e1' `op` e2 ]]
| ES_Binop_R (op : binop) : forall (v1 : Z) e2 e2',
    op <> OOr /\ op <> OAnd ->
    Z_in_range v1 ->
    step_expr s e2 e2' ->
    step_expr s [[ v1 `op` e2 ]] [[ v1 `op` e2' ]]

| ES_Binop_Or_NonSC_0 :
    step_expr s [[ 0 `OOr` 0 ]] [[ 0 ]]
| ES_Binop_Or_NonSC_1 : forall v2,
    trueval v2 ->
    step_expr s [[ 0 `OOr` v2 ]] [[ 1 ]]
| ES_Binop_Or_NonSC_R : forall e2 e2',
    step_expr s e2 e2' ->
    step_expr s [[ 0 `OOr` e2 ]] [[ 0 `OOr` e2' ]]
| ES_Binop_Or_SC : forall v1 e2,
    trueval v1 ->
    step_expr s [[ v1 `OOr` e2 ]] [[ 1 ]]

| ES_Binop_And_NonSC_0 : forall v1,
    trueval v1 ->
    step_expr s [[ v1 `OAnd` 0 ]] [[ 0 ]]
| ES_Binop_And_NonSC_1 : forall v1 v2,
    trueval v1 /\ trueval v2 ->
    step_expr s [[ v1 `OAnd` v2 ]] [[ 1 ]]
| ES_Binop_And_NonSC_R : forall v1 e2 e2',
    trueval v1 ->
    step_expr s e2 e2' ->
    step_expr s [[ v1 `OAnd` e2 ]] [[ v1 `OAnd` e2' ]]
| ES_Binop_And_SC : forall e2,
    step_expr s [[ 0 `OAnd` e2 ]] [[ 0 ]]

| ES_Binop_Cmp (op : binop) : forall (v1 v2 : Z),
    binop_class op = OCCmp ->
    Z_in_range v1 /\ Z_in_range v2 ->
    step_expr s [[ v1 `op` v2 ]] [[ cmp_compute op v1 v2 ]]

| ES_Binop_Arith (op : binop) : forall v1 v2,
    binop_class op = OCArith ->
    Z_in_range v1 /\ Z_in_range v2 ->
    let res := arith_compute op v1 v2 in
    Z_in_range res ->
    step_expr s [[ v1 `op` v2 ]] [[ res ]]

| ES_Binop_Div : forall v1 v2,
    Z_in_range v1 /\ Z_in_range v2 ->
    div_mod_safe v1 v2 ->
    step_expr s [[ v1 `ODiv` v2 ]] [[ Z_div v1 v2 ]]
| ES_Binop_Mod : forall v1 v2,
    Z_in_range v1 /\ Z_in_range v2 ->
    div_mod_safe v1 v2 ->
    step_expr s [[ v1 `OMod` v2 ]] [[ Z_mod v1 v2 ]]

| ES_Unop_Not : forall (v : Z),
    Z_in_range v ->
    step_expr s [[ `ONot` v ]] [[ not_compute v ]]
| ES_Unop_Neg : forall (v : Z),
    Z_in_range v ->
    neg_safe v ->
    step_expr s [[ `ONeg` v ]] [[ Z_neg v ]]

| ES_Deref_0 : forall i v,
    Z_in_range v ->
    s.(mem) (word_from_Z i) = Mstore (Vint (word_from_Z v)) ->
    step_expr s [[ *i ]] [[ v ]]
| ES_Deref_1 : forall e e',
    step_expr s e e' ->
    step_expr s [[ *e ]] [[ *e' ]]

| ES_AddrOf_Var : forall (x : var_id),
    step_expr s [[ &x ]] [[ Z_from_word (s.(var) x) ]]
| ES_AddrOf_Deref_0 : forall (v : Z),
    Z_in_range v ->
    step_expr s [[ &*v ]] [[ v ]]
| ES_AddrOf_Deref_1 : forall e e',
    step_expr s e e' ->
    step_expr s [[ &*e ]] [[ &*e' ]]
.


Definition local_var_enter (x : var_id) (l0 l1 : address) (v : val) : state -> state -> Prop :=
  set_addr x l0 l1 ∘ alloc_mem l1 v.

Definition local_var_exit (x : var_id) (l0 : address) : state -> state -> Prop :=
  fun s s' =>
    let l1 := s.(var) x in
    set_addr x l1 l0 s s' /\ dealloc_mem l1 s s'.


Inductive step_expr_list (s : state) : list expr -> list expr -> Prop :=
| ELS_Car : forall e1 e1' l2,
    step_expr s e1 e1' ->
    step_expr_list s (e1 :: l2) (e1' :: l2)
| ELS_Cdr : forall v1 l2 l2',
    step_expr_list s l2 l2' ->
    Z_in_range v1 ->
    step_expr_list s ((EConst v1) :: l2) ((EConst v1) :: l2')
.

Fixpoint expr_list_to_word (es : list expr) : option (list word) :=
  match es with
  | nil => Some nil
  | cons e es' =>
    match e with
    | EConst v =>
      if Z_in_range_b v then
      match expr_list_to_word es' with
      | None => None
      | Some vs' => Some (cons (word_from_Z v) vs')
      end
      else None
    | _ => None
    end
  end.


Inductive com_context : Type :=
| LocalVarEnv (x : var_id) (a : address) : com_context
| ProcCallEnv (xs : list var_id) (vs : list val) : com_context
| TestEnv (e : expr) : com_context
| WhileEnv (e : expr) (c : com) : com_context
| ForEnv (e : expr) (c2 c3 : com) : com_context
.


Inductive step_com (prog : program) : (state * com * list com_context) -> (state * com * list com_context) -> Prop :=
| CS_LocalVar (x : var_id) (v : val) : forall s s' c k,
    let l0 := s.(var) x in
    let l1 := s'.(var) x in
    local_var_enter x l0 l1 v s s' ->
    step_com prog (s, [[ let x <- v in c ]], k) (s', c, LocalVarEnv x l0 :: k)
| CS_LocalVarEnv_Skip (x : var_id) (a : address) : forall s s' k',
    local_var_exit x a s s' ->
    step_com prog (s, [[skip]], LocalVarEnv x a :: k') (s', [[skip]], k')
| CS_LocalVarEnv_Break (x : var_id) (a : address) : forall s s' k',
    local_var_exit x a s s' ->
    step_com prog (s, [[break]], LocalVarEnv x a :: k') (s', [[break]], k')
| CS_LocalVarEnv_Continue (x : var_id) (a : address) : forall s s' k',
    local_var_exit x a s s' ->
    step_com prog (s, [[continue]], LocalVarEnv x a :: k') (s', [[continue]], k')
| CS_LocalVarEnv_Return (x : var_id) (a : address) : forall s s' k',
    local_var_exit x a s s' ->
    step_com prog (s, [[return]], LocalVarEnv x a :: k') (s', [[return]], k')

| CS_AsgnVar (x : var_id) (e : expr) : forall s k,
    let addr := (EConst (Z_from_word (s.(var) x))) in
    step_com prog (s, [[ x <- e ]], k) (s, [[ *(addr) <- e ]], k)
| CS_AsgnDeref : forall (v1 v2 : Z) s1 s2 k,
    Z_in_range v1 /\ Z_in_range v2 ->
    set_mem (word_from_Z v1) (Vint (word_from_Z v2)) s1 s2 ->
    step_com prog (s1, [[ *(v1) <- v2 ]], k) (s2, [[ skip ]], k)
| CS_AsgnDeref_L : forall e1 e1' e2 s k,
    step_expr s e1 e1' ->
    step_com prog (s, [[ *(e1) <- e2 ]], k) (s, [[ *(e1') <- e2 ]], k)
| CS_AsgnDeref_R : forall v1 e2 e2' s k,
    Z_in_range v1 ->
    step_expr s e2 e2' ->
    step_com prog (s, [[ *(v1) <- e2 ]], k) (s, [[ *(v1) <- e2' ]], k)

| CS_ProcCall : forall p pb s es vs k,
    expr_list_to_word es = Some vs ->
    procs prog p = Some pb ->
    let xs := params_proc pb in
    let body := body_proc pb in
    step_com prog (s, [[ p.apply(es) ]], k) (s, body, ProcCallEnv xs (map Vint vs) :: k)
| CS_ProcCall_Args : forall s p es es' k,
    step_expr_list s es es' ->
    step_com prog (s, [[ p.apply(es) ]], k) (s, [[ p.apply(es') ]], k)
| CS_ProcCallEnv_Unfold : forall s s' x xs' v vs' c k',
    let l0 := s.(var) x in
    let l1 := s'.(var) x in
    local_var_enter x l0 l1 v s s' ->
    step_com prog (s, c, ProcCallEnv (x :: xs') (v :: vs') :: k') (s', c, ProcCallEnv xs' vs' :: LocalVarEnv x l0 :: k')
| CS_ProcCallSkip : forall s k',
    step_com prog (s, [[skip]], ProcCallEnv nil nil :: k') (s, [[skip]], k')
| CS_ProcCallReturn : forall s k',
    step_com prog (s, [[return]], ProcCallEnv nil nil :: k') (s, [[skip]], k')
(* No break and continue here *)

| CS_Seq_Skip : forall s c2 k,
    step_com prog (s, [[ skip; c2 ]], k) (s, c2, k)
| CS_Seq_Continue : forall s c2 k,
    step_com prog (s, [[ continue; c2 ]], k) (s, [[continue]], k)
| CS_Seq_Break : forall s c2 k,
    step_com prog (s, [[ break; c2 ]], k) (s, [[break]], k)
| CS_Seq_Return : forall s c2 k,
    step_com prog (s, [[ return; c2 ]], k) (s, [[return]], k)
| CS_Seq : forall s c1 k s' c1' k' c2,
    step_com prog (s, c1, k) (s', c1', k') ->
    step_com prog (s, [[ c1; c2 ]], k) (s', [[ c1'; c2 ]], k')

| CS_If : forall s e e' c1 c2 k,
    step_expr s e e' ->
    step_com prog (s, [[ if e then c1 else c2 ]], k) (s, [[ if e' then c1 else c2 ]], k)
| CS_If_True : forall v s c1 c2 k,
    trueval v ->
    step_com prog (s, [[ if v then c1 else c2 ]], k) (s, c1, k)
| CS_If_False : forall s c1 c2 k,
    step_com prog (s, [[ if 0 then c1 else c2 ]], k) (s, c2, k)

| CS_Test_Cond : forall s e e' k',
    step_expr s e e' ->
    step_com prog (s, [[continue]], TestEnv e :: k') (s, [[continue]], TestEnv e' :: k')
| CS_Test_False : forall s loop k',
    step_com prog (s, [[continue]], TestEnv [[0]] :: loop :: k') (s, [[break]], k')

| CS_While : forall s e c k,
    step_com prog (s, [[ while e do c ]], k) (s, [[continue]], WhileEnv e c :: k)
| CS_While_True : forall v e c s k',
    trueval v ->
    let k := WhileEnv e c :: k' in
    step_com prog (s, [[continue]], TestEnv [[v]] :: k) (s, c, k)
| CS_While_Skip : forall s e c k',
    let k := WhileEnv e c :: k' in
    step_com prog (s, [[skip]], k) (s, [[continue]], k)
| CS_While_Break : forall s e c k',
    step_com prog (s, [[break]], WhileEnv e c :: k') (s, [[skip]], k')
| CS_While_Continue : forall s e c k',
    let k := WhileEnv e c :: k' in
    step_com prog (s, [[continue]], k) (s, [[continue]], TestEnv e :: k)
| CS_While_Return : forall s e c k',
    step_com prog (s, [[return]], WhileEnv e c :: k') (s, [[return]], k')

| CS_For : forall s c1 e c2 c3 k,
    step_com prog (s, [[ for c1, e, c2 do c3 ]], k) (s, c1, TestEnv e :: ForEnv e c2 c3 :: k)
| CS_For_True : forall v e c2 c3 s k',
    trueval v ->
    let k := ForEnv e c2 c3 :: k' in
    step_com prog (s, [[continue]], TestEnv [[v]] :: k) (s, c3, k)
| CS_For_Skip : forall s e c2 c3 k',
    let k := ForEnv e c2 c3 :: k' in
    step_com prog (s, [[skip]], k) (s, [[continue]], k)
| CS_For_Break : forall s e c2 c3 k',
    step_com prog (s, [[break]], ForEnv e c2 c3 :: k') (s, [[skip]], k')
| CS_For_Continue : forall s e c2 c3 k',
    let k := ForEnv e c2 c3 :: k' in
    step_com prog (s, [[continue]], k) (s, [[c2; continue]], TestEnv e :: k)
| CS_For_Return : forall s e c2 c3 k',
    step_com prog (s, [[return]], ForEnv e c2 c3 :: k') (s, [[return]], k')

| CS_DoWhile : forall s c e k,
    step_com prog (s, [[ do c while e ]], k) (s, c, WhileEnv e c :: k)
.

Definition multistep_expr (s : state) := clos_refl_trans (step_expr s).
Definition multistep_com (prog : program) := clos_refl_trans (step_com prog).

Definition prog_entry (prog : program) (s : state) : (state * com * list com_context) :=
  match procs prog (entry prog) with
  | None => (s, [[return]], nil) (* bogus *)
  | Some entry_proc =>
    match params_proc entry_proc with
    | _ :: _ => (s, [[return]], nil) (* bogus *)
    | nil =>
      let gvars := global_vars prog in
      (s, (body_proc entry_proc), ProcCallEnv gvars (map (fun _ => Vuninit) gvars) :: nil)
    end
  end.

End SmallStep_WhileDCF.
