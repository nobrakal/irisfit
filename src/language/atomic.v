From stdpp Require Import base tactics option numbers.
From irisfit Require Import semantics invert_step.

Inductive Atomic : tm -> Prop :=
| ACallPrim : forall p v1 v2,
    is_Some (eval_call_prim p v1 v2) ->
    Atomic (tm_call_prim p v1 v2)
| AAlloc : forall (n:Z),
    Atomic (tm_alloc n)
| ALoad : forall (l:loc) (n:Z),
    Atomic (tm_load l n)
| AStore : forall (l:loc) (n:Z) (v:val),
    Atomic (tm_store l n v)
| AFork : forall t,
    Atomic (tm_fork t)
| ACAS : forall (l:loc) (i:Z) (v1 v2:val),
    Atomic (tm_cas l i v1 v2)
.

Lemma Atomic_correct t σ g t' σ' g' efs :
  Atomic t ->
  atomic_step t g σ t' g' σ' efs ->
  exists v, t' = tm_val v /\ g = g'.
Proof.
  inversion_clear 1; intros Hs.
  { apply invert_step_call_prim in Hs. naive_solver. }
  { apply invert_step_alloc in Hs. naive_solver. }
  { apply invert_step_load in Hs. naive_solver. }
  { apply invert_step_store in Hs. naive_solver. }
  { apply invert_step_fork in Hs. naive_solver. }
  { apply invert_step_cas in Hs. naive_solver. }
Qed.
