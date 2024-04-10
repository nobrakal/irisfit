From iris.algebra Require Export cmra local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

From irisfit Require Import qz.

Notation gfrac := Qz (only parsing).

Section gfrac.
  Canonical Structure gfracO := leibnizO Qz.

  Local Instance gfrac_valid_instance : Valid gfrac := λ x, (x ≤ 1)%Qz.
  Local Instance gfrac_pcore_instance : PCore gfrac := λ _, Some 0%Qz.
  Local Instance gfrac_op_instance : Op gfrac := λ x y, (x + y)%Qz.
  Local Instance gfrac_unit_instance : Unit gfrac := 0%Qz.

  Lemma gfrac_valid p : ✓ p ↔ (p ≤ 1)%Qz.
  Proof. done. Qed.
  Lemma gfrac_op p q : p ⋅ q = (p + q)%Qz.
  Proof. done. Qed.
  Lemma gfrac_included (p q:Qz) : p ≼ q ↔ (p ≤ q)%Qz.
  Proof. by rewrite Qz_le_sum. Qed.

  Corollary gfrac_included_weak p q : p ≼ q → (p ≤ q)%Qz.
  Proof. now rewrite gfrac_included. Qed.

  Definition gfrac_ra_mixin : RAMixin gfrac.
  Proof.
    apply ra_total_mixin; eauto; try apply _.
    { intros. by rewrite left_id_L. }
    { intros. by rewrite gfrac_included. }
    { intros p q. rewrite !gfrac_valid gfrac_op => ?.
      trans (p + q)%Qz; last done. apply Qz_le_add_l. }
  Qed.
  Canonical Structure gfracR := discreteR gfrac gfrac_ra_mixin.

  Global Instance gfrac_cmra_discrete : CmraDiscrete gfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma gfrac_ucmra_mixin : UcmraMixin gfrac.
  Proof. split; apply _ || done. Qed.
  Canonical Structure gfracUR : ucmra := Ucmra gfrac gfrac_ucmra_mixin.

  Global Instance gfrac_cancelable (q : gfrac) : Cancelable q.
  Proof. intros n p1 p2 _. apply (inj (Qz_add q)). Qed.

  Global Instance gfrac_is_op q1 q2 : IsOp (q1 + q2)%Qz q1 q2 | 10.
  Proof. done. Qed.
  Global Instance is_op_gfrac q : IsOp' q (q/2)%Qz (q/2)%Qz.
  Proof. by rewrite /IsOp' /IsOp gfrac_op Qz_div_2. Qed.
End gfrac.

(* Using a Definition, so Coq infers gfrac *)
Definition ugfrac := Qz.

Section ugfrac.
  Implicit Type p q : ugfrac.
  Open Scope Qz_scope.
  Canonical Structure ugfracO := leibnizO ugfrac.

  Local Instance ugfrac_valid_instance : Valid ugfrac := λ x, True.
  Local Instance ugfrac_pcore_instance : PCore ugfrac := λ _, Some 0%Qz.
  Local Instance ugfrac_op_instance : Op ugfrac := λ x y, (x + y)%Qz.
  Local Instance ugfrac_unit_instance : Unit ugfrac := 0%Qz.

  Lemma ugfrac_valid p : ✓ p.
  Proof. done. Qed.
  Lemma ugfrac_op p q : p ⋅ q = p + q.
  Proof. done. Qed.
  Lemma ugfrac_included p q : p ≼ q ↔ p ≤ q.
  Proof. by rewrite Qz_le_sum. Qed.

  Corollary ugfrac_included_weak p q : p ≼ q → p ≤ q.
  Proof. now rewrite ugfrac_included. Qed.

  Definition ugfrac_ra_mixin : RAMixin ugfrac.
  Proof.
    apply ra_total_mixin; eauto; try apply _.
    { intros. by rewrite left_id_L. }
  Qed.
  Canonical Structure ugfracR := discreteR ugfrac ugfrac_ra_mixin.

  Global Instance ugfrac_cmra_discrete : CmraDiscrete ugfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma ugfrac_ucmra_mixin : UcmraMixin ugfrac.
  Proof. split; apply _ || done. Qed.
  Canonical Structure ugfracUR : ucmra := Ucmra ugfrac ugfrac_ucmra_mixin.

  Global Instance ugfrac_cancelable (q : ugfrac) : Cancelable q.
  Proof. intros n p1 p2 _. apply (inj (Qz_add q)). Qed.

  Lemma ugfrac_local_update (x y x' y' : ugfracUR) :
    x + y' = x' + y → (x,y)  ~l~> (x',y').
  Proof.
    intros Heq ?; apply local_update_unital_discrete => z _.
    intros ->. split; try easy.
    rewrite ugfrac_op in Heq. rewrite ugfrac_op.
    rewrite (comm _ _ y) -assoc inj_iff in Heq.
    rewrite -Heq. rewrite (comm _ z) //.
  Qed.

  Global Instance ugfrac_is_op q1 q2 : IsOp (q1 + q2) q1 q2 | 10.
  Proof. done. Qed.
  Global Instance is_op_ugfrac q : IsOp' q (q/2) (q/2).
  Proof. by rewrite /IsOp' /IsOp ugfrac_op Qz_div_2. Qed.
End ugfrac.
