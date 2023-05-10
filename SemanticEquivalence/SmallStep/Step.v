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

Inductive step_expr (s : state) : expr -> expr -> Prop :=
| ES_Var (x : var_id) :
    step_expr s [[ x ]] [[ *(Z_from_word (s.(var) x)) ]]

| ES_Binop_L (op : binop) : forall e1 e1' e2,
    step_expr s e1 e1' ->
    step_expr s [[ e1 `op` e2 ]] [[ e1' `op` e2 ]]
| ES_Binop_R (op : binop) : forall (v1 : Z) e2 e2',
    op <> OOr /\ op <> OAnd ->
    step_expr s e2 e2' ->
    step_expr s [[ v1 `op` e2 ]] [[ v1 `op` e2' ]]

| ES_Binop_Or_NonSC_0 :
    step_expr s [[ 0 `OOr` 0 ]] [[ 0 ]]
| ES_Binop_Or_NonSC_1 : forall v2,
    v2 <> 0 ->
    step_expr s [[ 0 `OOr` v2 ]] [[ 1 ]]
| ES_Binop_Or_NonSC_R : forall e2 e2',
    step_expr s e2 e2' ->
    step_expr s [[ 0 `OOr` e2 ]] [[ 0 `OOr` e2' ]]
| ES_Binop_Or_SC : forall v1 e2,
    v1 <> 0 ->
    step_expr s [[ v1 `OOr` e2 ]] [[ 1 ]]

| ES_Binop_And_NonSC_0 : forall v1,
    v1 <> 0 ->
    step_expr s [[ v1 `OAnd` 0 ]] [[ 0 ]]
| ES_Binop_And_NonSC_1 : forall v1 v2,
    v1 <> 0 /\ v2 <> 0 ->
    step_expr s [[ v1 `OAnd` v2 ]] [[ 1 ]]
| ES_Binop_And_NonSC_R : forall v1 e2 e2',
    v1 <> 0 ->
    step_expr s e2 e2' ->
    step_expr s [[ v1 `OAnd` e2 ]] [[ v1 `OAnd` e2' ]]
| ES_Binop_And_SC : forall e2,
    step_expr s [[ 0 `OAnd` e2 ]] [[ 0 ]]

| ES_Binop_Cmp (op : binop) : forall (v1 v2 : Z),
    binop_class op = OCCmp ->
    step_expr s [[ v1 `op` v2 ]] [[ cmp_compute op v1 v2 ]]

| ES_Binop_Arith (op : binop) : forall v1 v2,
    binop_class op = OCArith ->
    let res := arith_compute op v1 v2 in
    Z_in_range res ->
    step_expr s [[ v1 `op` v2 ]] [[ res ]]

| ES_Binop_Div : forall v1 v2,
    div_mod_safe v1 v2 ->
    step_expr s [[ v1 `ODiv` v2 ]] [[ Z_div v1 v2 ]]
| ES_Binop_Mod : forall v1 v2,
    div_mod_safe v1 v2 ->
    step_expr s [[ v1 `OMod` v2 ]] [[ Z_mod v1 v2 ]]

| ES_Unop_Not : forall (v : Z),
    step_expr s [[ `ONot` v ]] [[ not_compute v ]]
| ES_Unop_Neg : forall (v : Z),
    neg_safe v ->
    step_expr s [[ `ONeg` v ]] [[ Z_neg v ]]

| ES_Deref_0 : forall i v,
    s.(mem) (word_from_Z i) = Mstore (Vint (word_from_Z v)) ->
    step_expr s [[ *i ]] [[ v ]]
| ES_Deref_1 : forall e e',
    step_expr s e e' ->
    step_expr s [[ *e ]] [[ *e' ]]

| ES_AddrOf_Var : forall (x : var_id),
    step_expr s [[ &x ]] [[ Z_from_word (s.(var) x) ]]
| ES_AddrOf_Deref_0 : forall (v : Z),
    step_expr s [[ &*v ]] [[ v ]]
| ES_AddrOf_Deref_1 : forall e e',
    step_expr s e e' ->
    step_expr s [[ &*e ]] [[ &*e' ]]
.


Parameter x : var_id.
Definition test :=
  [[
    let x in
    *(EConst 4) = 0
  ]].
Print test.

Definition local_var_enter (x : var_id) (v : val) : state -> state -> Prop :=
  ⋃ (fun l1 =>
    ⋃ (fun l2 =>
      ((set_addr x l1 l2 ∩ alloc_mem l2 v)) ∘
       (set_addr x l2 l1 ∩ dealloc_mem l2))).


Inductive step_com (prog : program) : (state * com) -> (state * com) -> Prop :=
(* | CS_LocalVar (x : var_id) :
    local_var_enter x Vuninit s *)
.

End SmallStep_WhileDCF.
