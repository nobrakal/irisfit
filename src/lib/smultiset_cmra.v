From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates big_op.
From iris.algebra Require Import proofmode_classes.

From irisfit Require Export smultiset.

Section smultiset.
  Context `{Countable K}.
  Implicit Types X Y : smultiset K.

  Canonical Structure smultisetO := discreteO (smultiset K).

  Local Instance smultiset_valid_instance : Valid (smultiset K) := λ _, True.
  Local Instance smultiset_validN_instance : ValidN (smultiset K) := λ _ _, True.
  Local Instance smultiset_unit_instance : Unit (smultiset K) := (∅ : smultiset K).
  Local Instance smultiset_op_instance : Op (smultiset K) := disj_union.
  Local Instance smultiset_pcore_instance : PCore (smultiset K) := λ X, Some ∅.

  Lemma smultiset_op X Y : X ⋅ Y = X ⊎ Y.
  Proof. done. Qed.
  Lemma smultiset_core X : core X = ∅.
  Proof. done. Qed.


  Lemma smultiset_ra_mixin : RAMixin (smultiset K).
  Proof.
    apply ra_total_mixin; eauto; try smultiset_solver; try apply _; try easy.
    intros. exists ∅.  smultiset_solver.
  Qed.

  Canonical Structure smultisetR := discreteR (smultiset K) smultiset_ra_mixin.

  Global Instance smultiset_cmra_discrete : CmraDiscrete smultisetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma smultiset_ucmra_mixin : UcmraMixin (smultiset K).
  Proof.
    split; [done | | done]. intros ?.
    smultiset_solver.
  Qed.
  Canonical Structure smultisetUR := Ucmra (smultiset K) smultiset_ucmra_mixin.

  Global Instance smultiset_cancelable X : Cancelable X.
  Proof.
    apply: discrete_cancelable => Y Z _ ?. by apply (inj (X ⊎.)).
  Qed.

  Global Instance smultiset_is_op X Y : IsOp (X ⊎ Y) X Y | 10.
  Proof. done. Qed.
End smultiset.
