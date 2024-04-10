From iris.proofmode Require Import base proofmode classes.
From stdpp Require Import base.

From irisfit.language Require Import language.
From irisfit Require Import interp.

Section Wp_poll.

Context `{!interpGS sz Σ}.

Lemma wp_call_prim E b π (p:prim) (v1 v2 w:val) :
  outside π -∗ wp E b π (tm_poll) (fun v => ⌜v = val_unit⌝ ∗ outside π ∗ £1).
Proof.
  iIntros "Hout".
  rewrite wp_unfold /wp_pre. simpl.
  intros_wp. intros_mod.

    iDestruct (use_outside with "[$][$]") as "%Hg'".
  assert (g=Out) as ->. { rewrite Hg in Hg'. naive_solver. }

  iSplitR; first eauto using reducible_poll.

  iIntros (? ? ? ?) "%Hstep Hc".
  apply invert_step_poll in Hstep.
  destruct Hstep as (?&?&?&?&?). subst.
  iModIntro.

  iMod "Hclose" as "_".
  auto_locs. rewrite !right_id (insert_id e) //.

  iSplitR "Hc Hout".
  { iMod (interp_weak with "[$]"). 2:eauto. 2:by iFrame.
    set_solver. }

  iModIntro. iApply wp_val. iFrame. iPureIntro. naive_solver.
Qed.

End Wp_poll.
