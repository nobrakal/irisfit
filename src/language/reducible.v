From Coq Require Import Program.Equality.
From stdpp Require Import gmap relations.

From irisfit.spacelang Require Import hypotheses.
From irisfit Require Import substitution semantics invert_step.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* reducible *)

Definition reducible (t:tm) (g:status) (σ:store) : Prop :=
  exists t' σ' g' efs, atomic_step t g σ t' g' σ' efs.

Lemma reducible_no_val t g σ :
  reducible t g σ ->
  to_val t = None.
Proof.
  intros (?&?&?&?&?). eauto using atomic_step_no_val.
Qed.

Lemma reducible_context E t σ g :
  reducible t g σ ->
  reducible (fill_item E t) g σ.
Proof.
  intros (?,(?,(?,(?,?)))). unfold reducible.
  eauto 15 using StepCtx.
Qed.

Local Ltac reduce :=
  unfold reducible; intros; eauto 15 using StepHead,HeadFork,HeadSeq,head_step.

Lemma reducible_fork t σ:
  reducible (tm_fork t) Out σ.
Proof. reduce. Qed.

Lemma reducible_load l n vs σ g :
  σ !! l = Some (BBlock vs) ->
  (0 <= n < Z.of_nat (length vs))%Z ->
  reducible (tm_load (tm_val (val_loc l)) (tm_val (val_int n))) g σ.
Proof.
  intros ? (?&?).
  assert (Z.to_nat n < length vs) as E by lia.
  apply lookup_lt_is_Some_2 in E. destruct E. reduce.
Qed.

Lemma reducible_cas (l:loc) (n:Z) (v1 v1' v2:val) vs σ g :
  σ !! l = Some (BBlock vs) ->
  vs !! (Z.to_nat n) = Some v1' ->
  (0 <= n)%Z ->
  reducible (tm_cas l n v1 v2) g σ.
Proof. reduce. Qed.

Lemma reducible_store l n v vs g σ :
  σ !! l = Some (BBlock vs) ->
  (0 <= n < Z.of_nat (length vs))%Z ->
  reducible (tm_store (tm_val (val_loc l)) (tm_val (val_int n)) (tm_val v)) g σ.
Proof. reduce. Qed.

Lemma reducible_alloc n σ:
  (0 < n)%Z ->
  reducible (tm_alloc (tm_val (val_int n))) Out σ.
Proof.
  intros.
  do 4 eexists.
  apply StepHead,HeadSeq.
  eapply HeadAlloc; try done.
  apply not_elem_of_dom, is_fresh.
Qed.

Lemma reducible_if b t1 t2 g σ :
  reducible (tm_if (tm_val (val_bool b)) t1 t2) g σ.
Proof. destruct b; reduce. Qed.

Lemma reducible_enter σ :
  reducible tm_enter Out σ.
Proof. reduce. Qed.

Lemma reducible_exit σ  :
  reducible tm_exit In σ.
Proof. reduce. Qed.

Lemma reducible_let_val x v t g σ :
  reducible (tm_let x (tm_val v) t) g σ.
Proof. reduce. Qed.

Lemma reducible_call self args vs body σ :
  length args = length vs ->
  locs body = ∅ ->
  reducible (tm_call (val_code self args body) (fmap tm_val vs)) Out σ.
Proof. reduce. Qed.

Lemma reducible_prim p (v1 v2:val) g σ :
  is_Some (eval_call_prim p v1 v2) ->
  reducible (tm_call_prim p v1 v2) g σ.
Proof. intros (?,?). reduce. Qed.

Lemma reducible_poll σ :
  reducible tm_poll Out σ.
Proof. reduce.  Qed.
