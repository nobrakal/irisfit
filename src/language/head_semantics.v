From stdpp Require Import sets gmap gmultiset.
From irisfit Require Import substitution.
From irisfit Require Export store.

Set Implicit Arguments.

Inductive status := In | Out.

(* ------------------------------------------------------------------------ *)
(* The actual semantics *)

Definition exec_int_bin_op op :=
  match op with
  | IntAdd => Z.add
  | IntMul => Z.mul
  | IntSub => Z.sub
  | IntDiv => Z.div end.

Definition exec_bool_bin_op op :=
  match op with
  | BoolAnd => andb
  | BoolOr => orb end.

Definition eval_call_prim p v1 v2 :=
  match p,v1,v2 with
  | prim_bool_op op, val_bool b1, val_bool b2 => Some (val_bool (exec_bool_bin_op op b1 b2))
  | prim_int_op op, val_int m, val_int n => Some (val_int (exec_int_bin_op op m n))
  | prim_eq, v1, v2 => Some (val_bool (bool_decide (v1=v2)))
  | prim_neq, v1, v2 => Some (val_bool (bool_decide (v1≠v2)))
  | _,_,_ => None end.

(* A head step *)
(* The boolean indicates whether or not the thread is in a GC-critical section *)
Inductive head_step : tm -> status -> store -> tm -> status -> store -> Prop :=
| HeadLet : forall σ1 σ2 t1 t2 x v g,
    t1 = tm_val v ->
    σ1 = σ2 ->
    head_step
      (tm_let x t1 t2) g σ1
      (subst' x v t2) g σ2
| HeadCall : forall σ t1 ts self args body vs,
    length args = length vs ->
    t1 = tm_val (val_code self args body) ->
    locs body = ∅ ->
    ts = fmap tm_val vs ->
    head_step
      (tm_call t1 ts) Out σ
      (substs' (zip (self::args) (val_code self args body::vs)) body) Out σ
| HeadCallPrim : forall σ p v1 v2 v g,
    eval_call_prim p v1 v2 = Some v ->
    head_step
      (tm_call_prim p v1 v2) g σ
      (tm_val v) g σ
| HeadIf : forall σ t1 t2 t3 b g,
    t1 = tm_val (val_bool b) ->
    head_step
      (tm_if t1 t2 t3) g σ
      (if b then t2 else t3) g σ
| HeadAlloc : forall σ σ' l t1 n bs,
    σ !! l = None →
    (0 < n)%Z ->
    t1 = tm_val (val_int n) ->
    bs = BBlock (replicate (Z.to_nat n) val_unit) ->
    σ' = <[l:=bs]> σ →
    head_step
      (tm_alloc t1) Out σ
      (tm_val (val_loc l)) Out σ'
| HeadLoad : forall σ l t1 t2 n v bs g,
    t1 = tm_val (val_loc l) ->
    σ !! l = Some (BBlock bs) ->
    t2 = tm_val (val_int n) ->
    (0 <= n)%Z ->
    bs !! (Z.to_nat n) = Some v ->
    head_step
      (tm_load t1 t2) g σ
      (tm_val v) g σ
| HeadStore : forall σ σ' t1 t2 t3 l n v bs g,
    t1 = tm_val (val_loc l) ->
    t2 = tm_val (val_int n) ->
    t3 = tm_val v ->
    (0 <= n < Z.of_nat (length bs))%Z ->
    σ !! l = Some (BBlock bs) ->
    σ' = insert l (BBlock (insert (Z.to_nat n) v bs)) σ ->
    head_step
      (tm_store t1 t2 t3) g σ
      (tm_val (val_unit)) g σ'
| HeadCAS : forall (σ:store) σ' t1 t2 t3 t4 v1 v1' v2 l n bs g,
    t1 = tm_val (val_loc l) ->
    t2 = tm_val (val_int n) ->
    t3 = tm_val v1 ->
    t4 = tm_val v2 ->
    (0 <= n)%Z ->
    σ !! l = Some (BBlock bs) ->
    bs !! (Z.to_nat n) = Some v1' ->
    σ' = (if decide (v1=v1') then (insert l (BBlock (insert (Z.to_nat n) v2 bs)) σ) else σ) ->
    head_step
      (tm_cas t1 t2 t3 t4) g σ
      (tm_val (val_bool (bool_decide (v1=v1')))) g σ'
| HeadEnter : forall σ,
    head_step tm_enter Out σ val_unit In σ
| HeadExit : forall σ,
    head_step tm_exit In σ val_unit Out σ
| HeadPoll : forall σ,
    head_step tm_poll Out σ val_unit Out σ
.

#[export] Hint Constructors head_step : head_step.

Lemma head_step_grow_store t1 σ1 t2 σ2 g1 g2 :
  head_step t1 g1 σ1 t2 g2 σ2 ->
  dom σ1 ⊆ dom σ2.
Proof.
  inversion 1; subst; try easy; try set_solver.
  case_decide; set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* Inversion lemmas *)

Lemma invert_head_step_alloc n σ t' σ' g g' :
  head_step (tm_alloc (tm_val (val_int n))) g σ t' g' σ' ->
  exists l, t' = tm_val (val_loc l)
       /\ σ !! l = None
       /\ (0 < n)%Z
       /\ σ' = <[l:=BBlock (replicate (Z.to_nat n) val_unit)]> σ
       /\ g = Out /\ g' = Out.
Proof. inversion_clear 1. naive_solver. Qed.

Ltac rev_inject H :=
  injection H; intros <-.

Lemma invert_head_step_if b t1 t2 σ t' σ' g g' :
  head_step (tm_if (tm_val (val_bool b)) t1 t2) σ g t' σ' g' ->
  σ = σ' ∧ (t' = if b then t1 else t2) /\ g = g'.
Proof. inversion_clear 1. naive_solver. Qed.

Lemma invert_head_step_load (l:loc) (n:Z) σ t' σ' g g' :
  head_step (tm_load l n) g σ t' g' σ' ->
  σ = σ' /\ (exists bs v, σ !! l = Some (BBlock bs) /\ t' = tm_val v /\ (0 <= n)%Z /\ bs !! (Z.to_nat n) = Some v) /\ g = g'.
Proof. inversion_clear 1. naive_solver. Qed.

Lemma invert_head_step_cas (l:loc) (n:Z) (v1 v2:val) σ t' σ' g g' :
  head_step (tm_cas l n v1 v2) g σ t' g' σ' ->
  exists bs (v1':val), σ !! l = Some (BBlock bs) /\ (0 <= n)%Z /\ bs !! (Z.to_nat n) = Some v1' /\ t' = tm_val (bool_decide (v1=v1')) /\ g =g' /\
             if decide (v1=v1') then σ' = <[l:=BBlock (<[Z.to_nat n:=v2]> bs)]> σ
             else σ' = σ.
Proof.
  inversion_clear 1.
  rev_inject H0. rev_inject H1.
  rev_inject H2. rev_inject H3. subst.
  eexists _,_.
  split_and !; eauto; try lia.
  destruct (decide (v1 = v1')); eauto.
Qed.

Lemma invert_head_step_store (l:loc) (n:Z) (v:val) σ t' σ' g g' :
  head_step (tm_store l n v) g σ t' g' σ' ->
  exists bs, σ !! l = Some (BBlock bs)
        /\ (0 <= n < Z.of_nat (length bs))%Z
        /\ σ' = <[l:=BBlock (<[Z.to_nat n:=v]> bs)]> σ
        /\ t' = tm_val val_unit
        /\ g=g'.
Proof. inversion_clear 1. naive_solver. Qed.

Lemma invert_head_step_call self args body vs σ t' σ' g g' :
  head_step (tm_call (val_code self args body) (fmap tm_val vs)) g σ t' g' σ' ->
  σ = σ' /\ length args = length vs /\  t' = substs' (zip (self::args) (val_code self args body::vs)) body /\ g = Out /\ g' = Out.
Proof.
  inversion_clear 1; subst.
  split; try easy.
  apply list_fmap_eq_inj in H3.
  2:{ intros ? ? E. now injection E. }
  rev_inject H1. intros. subst. eauto.
Qed.

Lemma invert_head_step_call_prim p (v1 v2:val) σ t' σ' g g' :
  head_step (tm_call_prim p v1 v2) σ g t' σ' g' ->
  σ = σ' ∧ g = g' /\ exists v, t' = tm_val v /\ eval_call_prim p v1 v2 = Some v.
Proof. inversion_clear 1. naive_solver. Qed.

Inductive head_step_conc :
  tm -> status -> store ->
  tm -> status -> store ->
  option tm -> Prop :=
| HeadSeq t1 g1 σ1 t2 g2 σ2 :
  head_step t1 g1 σ1 t2 g2 σ2 ->
  head_step_conc t1 g1 σ1 t2 g2 σ2 None
| HeadFork t σ:
  head_step_conc
    (tm_fork t) Out σ
    (tm_val val_unit) Out σ (Some t).
