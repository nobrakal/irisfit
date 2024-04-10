From Coq Require Import Program.Equality.
From stdpp Require Import gmap relations.

From irisfit.spacelang Require Import hypotheses.
From irisfit Require Export syntax_instances head_semantics store.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* An [atomic_step] is a [head_step], possibly under an evaluation context. *)

Inductive atomic_step :
  tm → status -> store →
  tm → status -> store →
  option tm -> Prop :=
| StepCtx t1 σ1 g1 t2 σ2 g2 E t1' t2' efs :
  t1' = fill_item E t1 ->
  t2' = fill_item E t2 ->
  atomic_step t1 g1 σ1 t2 g2 σ2 efs ->
  atomic_step t1' g1 σ1 t2' g2 σ2 efs
| StepHead t1 σ1 g1 t2 σ2 g2 efs :
  head_step_conc t1 g1 σ1 t2 g2 σ2 efs →
  atomic_step t1 g1 σ1 t2 g2 σ2 efs.

Definition opt_to_list {A:Type} (xs:option A) : list (A*status) :=
  match xs with
  | None => nil
  | Some x => [(x,Out)] end.

(* [reduction] is either an atomic step of a thread, or a GC. *)
Inductive step_oblivious :
  (list (tm*status)*store) ->
  (list (tm*status)*store) -> Prop :=
| StepAtomic θ1 θ2 t1 σ1 g1 t2 σ2 g2 efs ts1 ts2 :
  θ1 = ts1 ++ (t1,g1) :: ts2 →
  θ2 = ts1 ++ (t2,g2) :: ts2 ++ opt_to_list efs →
  atomic_step t1 g1 σ1 t2 g2 σ2 efs →
  step_oblivious (θ1,σ1) (θ2,σ2)
.

Lemma head_step_conc_grow_store t1 σ1 g1 t2 σ2 g2 efs :
  head_step_conc t1 g1 σ1 t2 g2 σ2 efs ->
  dom σ1 ⊆ dom σ2.
Proof. inversion_clear 1; subst; eauto using head_step_grow_store. Qed.

Lemma atomic_step_grow_store efs t σ g t' σ' g' :
  atomic_step t g σ t' g' σ' efs ->
  dom σ ⊆ dom σ'.
Proof.
  induction 1; eauto using head_step_conc_grow_store.
Qed.
