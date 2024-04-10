From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets.
From irisfit Require Import interp.

Section Wp_call.

Context `{!interpGS sz Σ}.

Lemma zip_cons {A B} (x:A) (y:B) xs ys :
  zip (x::xs) (y::ys) = (x,y)::zip xs ys.
Proof. easy. Qed.

Lemma wp_call E b π self args body ts vs Q :
  length args = length vs →
  locs body = ∅ ->
  ts = tm_val <$> vs ->
  outside π ∗ ▷ (outside π  -∗ £1 -∗ wp E b π (substs' (zip (self::args) (val_code self args body::vs)) body) Q)
  ⊢ wp E b π (tm_call (val_code self args body) ts) Q.
Proof.
  iIntros (? ? ->) "(?&Hspec)".
  setoid_rewrite wp_unfold at 2.
  intros_wp. intros_mod.
  iDestruct (use_outside with "[$][$]") as "%Hg'".
  assert (g=Out) as ->. { rewrite Hg in Hg'. naive_solver. }

  iSplitR; first eauto using reducible_call.

  iIntros (t' ? ? ?) "%Hstep ?".

  apply invert_step_call in Hstep.
  destruct Hstep as (Hgc&?&?&?&?). subst.

  simpl. rewrite Nat.add_0_r !right_id (insert_id e) //.
  iModIntro.
  iSpecialize ("Hspec" with "[$][$]").
  iMod (interp_weak with "[$]"); last by iFrame.
  2:eauto.
  pose proof (locs_substs' (zip (self :: args) (val_code self args body :: vs)) body) as Hlocs.
  rewrite zip_cons fmap_cons snd_zip in Hlocs; last lia.
  auto_locs. set_solver.
Qed.

End Wp_call.
