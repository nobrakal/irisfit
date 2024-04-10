From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets.
From irisfit Require Import interp.

Section Wp_call_prim.

Context `{!interpGS sz Σ}.

Lemma locs_result_eval_call_prim p v1 v2 x :
  eval_call_prim p v1 v2 = Some x ->
  locs_val x = ∅.
Proof.
  intros E.
  destruct p.
  all:destruct v1,v2,x; simpl in E; try congruence.
  all:injection E; intros <-; auto_locs; set_solver.
Qed.

Lemma wp_call_prim E b tid (p:prim) (v1 v2 w:val) :
  eval_call_prim p v1 v2 = Some w ->
  ⊢ wp E b tid (tm_call_prim p v1 v2) (fun v => ⌜v = w⌝ ∗ £1).
Proof.
  iIntros (Hv).

  rewrite wp_unfold /wp_pre. simpl.
  intros_wp. intros_mod.
  iSplitR; first eauto using reducible_prim.

  iIntros (? ? ? ?) "%Hstep Hc".
  apply invert_step_call_prim in Hstep.
  destruct Hstep as (?&?&?&?&?&?). subst.
  iModIntro.

  iMod "Hclose" as "_".
  auto_locs. rewrite !right_id (insert_id e) //.

  iSplitR "Hc".
  { iMod (interp_weak with "[$]"). 2:eauto. 2:by iFrame.
    erewrite locs_result_eval_call_prim; eauto. set_solver. }

  iModIntro. iApply wp_val. iFrame. iPureIntro. naive_solver.
Qed.

End Wp_call_prim.
