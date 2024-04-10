From stdpp Require Export sets countable.
From stdpp Require gmultiset.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates big_op.
From iris.prelude Require Import options.

From irisfit Require Import qz qz_cmra.
From irisfit Require Import smultiset.
From irisfit Require Export nfrac.

Section Smultiset.

  Context `{Countable K}.
  Implicit Types X Y : smultiset K.

  Canonical Structure smultisetO := discreteO (smultiset K).

  Local Instance smultiset_valid_instance : Valid (smultiset K) := λ _, True.
  Local Instance smultiset_validN_instance : ValidN (smultiset K) := λ _ _, True.
  Local Instance smultiset_op_instance : Op (smultiset K) := smultiset_disj_union.
  Local Instance smultiset_pcore_instance : PCore (smultiset K) := λ _, Some ∅.
  Local Instance smultiset_unit_instance : Unit (smultiset K) := (∅:smultiset K).

  Lemma smultiset_op X Y : X ⋅ Y = X ⊎ Y.
  Proof. done. Qed.
  Lemma smultiset_core X : core X = ∅.
  Proof. done. Qed.

  (* NB The reverse is false. *)
  Lemma smultiset_included X Y :
    X ⊆ Y -> X ≼ Y.
  Proof.
    exists (Y ⊎ opposite X). smultiset_solver.
  Qed.

  Lemma smultiset_ra_mixin : RAMixin (smultiset K).
  Proof.
    apply ra_total_mixin; eauto; try apply _.
    { intros ? ? ?. easy. }
    { intros ?. rewrite left_id //. }
    { intros ? ? ?. exists ∅. rewrite left_id //. }
  Qed.

  Canonical Structure smultisetR := discreteR (smultiset K) smultiset_ra_mixin.

  Global Instance smultiset_cmra_discrete : CmraDiscrete smultisetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma smultiset_ucmra_mixin : UcmraMixin (smultiset K).
  Proof.
    split; [done | | done]. intros X.
    by rewrite smultiset_op left_id.
  Qed.
  Canonical Structure smultisetUR := Ucmra (smultiset K) smultiset_ucmra_mixin.

  Global Instance smultiset_cancelable X : Cancelable X.
  Proof.
    apply: discrete_cancelable => Y Z _ ?. smultiset_solver.
  Qed.

End Smultiset.

Global Instance Negligible_smultiset `{Countable K} : IsNegligible (@smultisetUR K _ _) AllNeg.
Proof.
  constructor; try apply _; try easy.
  apply AllNeg_disj_union.
Qed.

Notation fracset K := (nfrac (@smultisetUR K _ _) AllNeg).

Notation fracsetUR K := (@nfracUR (@smultisetUR K _ _) AllNeg).

Section Fracset.

  Context `{Countable K}.

  Lemma alln_upd {frac} {ls1 ls2 : smultiset K}:
    ls1 ≡ ls2 ->
    (frac = 0%Qz -> AllNeg ls1) ->
    frac = 0%Qz -> AllNeg ls2.
  Proof.
    intros R A Hf. pose proof (A Hf).
    now rewrite <- R.
  Qed.

  Lemma fracset_from_full (x y : fracset K) :
    frac x = frac y ->
    AllPos (supp y) ->
    x ≼ y ->
    supp y ⊆ supp x /\ AllPos (supp x).
  Proof.
    intros ? ? Hi.
    apply from_full in Hi; try easy.
    destruct Hi as (z, (HZ&?&?)).
    apply nfrac_equiv_supp in HZ.
    smultiset_solver.
  Qed.

End Fracset.

Section From_gmultiset.
  Context `{Countable K}.

  Program Definition full_gmultiset : gmultiset.gmultiset K -> (fracset K) :=
    fun M => mk_nf 1 (of_gmultiset M) _.
  Next Obligation. intros ? E. injection E. lia. Qed.

  Program Definition null_neg_part M :(fracset K) :=
    mk_nf 0 (negative_part M) _.
  Next Obligation. smultiset_solver. Qed.

End From_gmultiset.
