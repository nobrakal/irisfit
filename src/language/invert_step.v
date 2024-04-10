From Coq Require Import Program.Equality.
From stdpp Require Import gmap relations.

From irisfit Require Import semantics substitution.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* Some inversion lemmas *)

Lemma head_step_no_val t1 σ1 g1 t2 σ2 g2 :
  head_step t1 σ1 g1 t2 σ2 g2 ->
  to_val t1 = None.
Proof. by inversion 1. Qed.

Lemma atomic_step_no_val t1 σ1 g1 t2 σ2 g2 efs :
  atomic_step t1 σ1 g1 t2 σ2 g2 efs ->
  to_val t1 = None.
Proof.
  inversion 1; subst.
  { by destruct E. }
  { inversion H0; eauto using head_step_no_val. }
Qed.

Lemma has_to_be_val vs l l' t :
  to_val t = None ->
  tm_val <$> vs = (tm_val <$> l) ++ t :: l' ->
  False.
Proof.
  revert l l' t. induction vs; intros l l' t; intros ? Heq.
  { destruct l; try easy. }
  { destruct l; injection Heq; intros; subst; now eauto. }
Qed.

Lemma head_step_conc_no_ctx E t σ t' σ' efs g1 g2 :
  to_val t = None ->
  head_step_conc (fill_item E t) σ t' g1 σ' g2 efs ->
  False.
Proof.
  inversion 2; subst.
  2:{ by destruct E. }
  clear H0. inversion H1; subst.
  all:destruct E; simpl in *; try inversion H0; subst; try done.
  all:eauto using has_to_be_val.
Qed.

Lemma invert_step_context E t σ t' σ' efs g1 g2 :
  to_val t = None ->
  atomic_step (fill_item E t) σ g1 t' σ' g2 efs ->
  exists t'',  t' = fill_item E t'' /\ atomic_step t σ g1 t'' σ' g2 efs .
Proof.
  inversion_clear 2; subst.
  (* ctx *)
  { apply fill_item_inj in H1; eauto using atomic_step_no_val.
    destruct H1; subst. eexists. done.  }
  (* head step *)
  { exfalso. eauto using head_step_conc_no_ctx. }
Qed.

Lemma invert_step_fork t σ g g' t' σ' efs :
  atomic_step (tm_fork t) g σ t' g' σ' efs ->
  σ = σ' /\ g' = Out /\ g = Out /\ t' = val_unit /\ efs = Some t.
Proof.
  inversion_clear 1; subst.
  2:{ inversion H0. inversion H. naive_solver. }
  by destruct E.
Qed.

Ltac cannot_be_distant :=
  let E := fresh "E" in
  intros [] ? ?; inversion_clear 1;
  intros E; apply atomic_step_no_val in E;
  easy.

Lemma invert_must_be_head t1 σ1 t2 σ2 efs g1 g2 :
  (forall E t t', t1 = fill_item E t -> atomic_step t g1 σ1 t' g2 σ2 efs -> False) ->
  atomic_step t1 g1 σ1 t2 g2 σ2 efs ->
  head_step_conc t1 g1 σ1 t2 g2 σ2 efs.
Proof.
  intros Hnd Hstep.
  inversion Hstep; subst; eauto.
  exfalso. eauto.
Qed.

Ltac invert_step :=
  let E := fresh "E" in
  intros E;
  apply invert_must_be_head in E;
  [ inversion_clear E as [?????? Hdstep| ]; subst | ]; first last.


Lemma invert_step_load (l:loc) (n:Z) σ t' σ' efs g g' :
  atomic_step (tm_load l n) g σ t' g' σ' efs ->
 σ = σ' /\ (exists bs v, σ !! l = Some (BBlock bs) /\ t' = tm_val v /\ (0 <= n)%Z /\ bs !! (Z.to_nat n) = Some v) /\ g = g' /\ efs = None.
Proof.
  invert_step.
  { cannot_be_distant. }
  apply invert_head_step_load in Hdstep. naive_solver.
Qed.

Lemma invert_step_cas (l:loc) (n:Z) (v1 v2:val) σ t' σ' efs g g' :
  atomic_step (tm_cas l n v1 v2) g σ t' g' σ' efs ->
  efs = None /\ exists bs (v1':val), σ !! l = Some (BBlock bs) /\ (0 <= n)%Z /\ bs !! (Z.to_nat n) = Some v1' /\ t' = tm_val (bool_decide (v1=v1')) /\ g =g' /\
             if decide (v1=v1') then σ' = <[l:=BBlock (<[Z.to_nat n:=v2]> bs)]> σ
             else σ' = σ.
Proof.
  invert_step.
  { cannot_be_distant. }
  apply invert_head_step_cas in Hdstep.
  naive_solver.
Qed.

Lemma invert_step_alloc (n:Z) σ t' σ' g g' efs :
  atomic_step (tm_alloc n) g σ t' g' σ' efs ->
  exists l, t' = tm_val (val_loc l)
       /\ σ !! l = None
       /\ (0 < n)%Z
       /\ σ' = <[l:=BBlock (replicate (Z.to_nat n) val_unit)]> σ
       /\ g = Out /\ g' = Out
       /\ efs = None
.
Proof.
  invert_step.
  { cannot_be_distant. }
  apply invert_head_step_alloc in Hdstep. naive_solver.
Qed.

Lemma invert_step_if (b:bool) t1 t2 σ t' σ' g g' efs :
  atomic_step (tm_if b t1 t2) g σ t' g' σ' efs ->
  g = g' /\ σ' = σ /\ efs = None /\ (t' = if b then t1 else t2).
Proof.
  invert_step.
  { cannot_be_distant. }
  apply invert_head_step_if in Hdstep.
  naive_solver.
Qed.

Lemma invert_step_enter σ t' σ' g g' efs :
  atomic_step tm_enter g σ t' g' σ' efs ->
  g = Out /\ g' = In /\ σ' = σ /\ efs = None /\ t'=val_unit.
Proof.
  invert_step.
  { cannot_be_distant. }
  inversion Hdstep. naive_solver.
Qed.

Lemma invert_step_exit σ t' σ' g g' efs :
  atomic_step tm_exit g σ t' g' σ' efs ->
  g = In /\ g' = Out /\ σ = σ' /\ efs = None /\ t'=val_unit.
Proof.
  invert_step.
  { cannot_be_distant. }
  inversion Hdstep. naive_solver.
Qed.

Lemma invert_step_store (l:loc) (n:Z) (v:val) σ t' σ' g g' efs :
  atomic_step (tm_store l n v) g σ t' g' σ' efs ->
  exists bs, σ !! l = Some (BBlock bs)
        /\ (0 <= n < Z.of_nat (length bs))%Z
        /\ σ' = <[l:=BBlock (<[Z.to_nat n:=v]> bs)]> σ
        /\ t' = tm_val val_unit
        /\ g=g'
        /\ efs = None
.
Proof.
  invert_step.
  { cannot_be_distant. }
  apply invert_head_step_store in Hdstep.
  naive_solver.
Qed.

Lemma invert_step_let_val x (v:val) t σ t' σ' g g' efs :
  atomic_step (tm_let x v t) g σ t' g' σ' efs ->
  t' = subst' x v t /\ σ = σ' /\ efs = None /\ g = g'.
Proof.
  invert_step.
  { cannot_be_distant. }
  inversion_clear Hdstep; try easy; subst. naive_solver.
Qed.

Lemma invert_step_call self args body vs σ t' σ' g g' efs :
  atomic_step (tm_call (val_code self args body) (fmap tm_val vs)) g σ t' g' σ' efs ->
  g = Out /\ g' = Out /\ σ = σ' /\ t' = substs' (zip (self::args) (val_code self args body::vs)) body /\ efs = None.
Proof.
  invert_step.
  { intros [] ? ?; try easy; simpl;
      intros Eq; injection Eq; clear Eq.
    { intros _ ? Hd. apply atomic_step_no_val in Hd. subst. easy. }
    intros Eq.
    assert (exists v, t = tm_val v) as (?,->).
    { apply (f_equal (lookup (length l))) in Eq.
      rewrite list_lookup_fmap, list_lookup_middle in Eq; try easy.
      destruct (vs !! length l); try easy. injection Eq.
      intros <-. now eexists. now rewrite fmap_length. }
    intros _ Hd. apply atomic_step_no_val in Hd. easy. }
  apply invert_head_step_call in Hdstep. naive_solver.
Qed.

Lemma invert_step_call_prim p (v1 v2:val) σ t' σ' g g' efs :
  atomic_step (tm_call_prim p v1 v2) g σ t' g' σ' efs ->
  g = g' /\ σ = σ' ∧ exists v, t' = tm_val v /\ eval_call_prim p v1 v2 = Some v /\ efs = None.
Proof.
  invert_step.
  { cannot_be_distant. }
  apply invert_head_step_call_prim in Hdstep. naive_solver.
Qed.

Lemma invert_step_poll σ t' σ' g g' efs :
  atomic_step tm_poll g σ t' g' σ' efs ->
  g=Out /\ g'=Out /\ σ = σ' ∧ t' = val_unit /\ efs = None.
Proof.
  invert_step.
  { cannot_be_distant. }
  inversion Hdstep; eauto.
Qed.
