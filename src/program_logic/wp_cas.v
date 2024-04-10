From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import qz more_maps_and_sets more_space_lang smultiset.
From irisfit Require Import ph interp wp_store.

Section Wp_cas.

Context `{!interpGS sz Σ}.

Lemma wp_cas (c:bool) E b tid (l:loc) (i:Z) (q:dfrac) (v1 v1' v2:val) qv (bs:list val) :
  bs !! (Z.to_nat i) = Some v1' ->
  (0 <= i)%Z ->
  (v1=v1' -> q=DfracOwn 1%Qp) ->
  (v1=v1' -> is_loc v2 -> qv≠0%Qz) ->
  l ↦{q} bs ∗ (if (decide (v1=v1')) then if c then v2 ↤?{qv} ∅ else † l else True)
  ⊢ wp E b tid (tm_cas l i v1 v2)
      (fun r => ⌜ r= val_bool (bool_decide (v1=v1')) ⌝ ∗ £ 1 ∗
             l ↦{q} (if decide (v1=v1') then <[Z.to_nat i:=v2]> bs else bs) ∗
             ((if (decide (v1=v1')) then if c then v1 ↤?{0} {[-l-]} ∗ v2 ↤?{qv} {[+l+]} else True else True))).
Proof.
  iIntros (Hi ? Hq Hqv) "(Hpt&Hm)".
  rewrite wp_unfold /wp_pre. simpl.
  intros_wp. intros_mod.

  assert (l ∈ image k).
  { apply elem_of_image. eexists _,_. split; eauto. auto_locs. set_solver. }

  iDestruct (exploit_mapsto with "[$]") as "%Hl".

  iSplitR; first eauto using reducible_cas.

  iIntros (????) "%Hstep Hlater".
  apply invert_step_cas in Hstep. destruct Hstep as (?&Hcas). subst.
  destruct Hcas as (bs1&(n1,(E1&E3&E2&->&->&Hcas))). subst.
  assert (bs = bs1) as ->. by naive_solver.
  rewrite Hi in E2. inversion E2. subst.

  rewrite !right_id (insert_id e) //. iModIntro.

  destruct_decide (decide (v1=n1)) as Hv; try rewrite Hv; subst; last first.
  { subst. iMod (interp_weak with "[$]"); last iFrame. 2:eauto. set_solver.
    iMod "Hclose". iApply wp_val. by iFrame. }

  assert (locs v2 ⊆ image k).
  { apply image_elem_subset in Htid. auto_locs. simpl in *. set_solver. }
  rewrite Hq //.

  destruct_interp "Hi".

  iMod (store_update _ _ (<[Z.to_nat i:=v2]> bs1) with "[$][$]") as "(?&Hl)".
  { rewrite insert_length //. }

  (* We have to deal with the case that l may be already deallocated *)
  destruct_decide (decide (freed τ l)).
  { iAssert (|==>  ph_interp τ ∗ (if c then  n1 ↤?{0} {[-l-]} ∗ v2 ↤?{qv} {[+l+]} else True))%I with "[Hph Hm]" as ">(Hph&X)".
    { destruct c; last by iFrame.
      iMod (ph_store_heap_dead n1 with "[$]") as "(?&Hl1&Hl2)". 1,2:naive_solver.
      { destruct n1; try done. erewrite <- linked_dom; last done.
        eapply closed_rtc_in_dom; eauto.
        apply rtc_once. eapply prove_successor; try done.
        apply pointers_locs. apply locs_elem_subseteq in Hi. set_solver. }
      rewrite left_id. by iFrame. }

    iMod "Hclose" as "_". iSplitR "Hlater X Hl".
    { iApply bupd_fupd. iApply interp_weak. 2:done. set_solver.
      iExists _,τ,_,_. rewrite dom_insert_lookup_L //. iFrame "∗%". iPureIntro.
      eauto 15 using update_preserves_closed, linked_store1. }
    { iModIntro. iApply wp_val. by iFrame. } }

  assert (τ !! l = Some (BBlock bs1)).
  { assert (is_Some (τ !! l)) as (b2&Hb2).
    { apply elem_of_dom. erewrite <-linked_dom; try done. eauto using elem_of_dom. }
    destruct Hτ as [_ X1 _ _]. destruct (X1 l _ _ Hl Hb2); naive_solver. }

  destruct c.
  2:{ iDestruct (pbt_dead_exploit with "[$]") as "%Hdead". exfalso.
      erewrite linked_dom in Hdead; last done.
      apply H2. destruct Hdead. eauto using use_synchro_dead. }
  iDestruct (vmapsfrom_alive with "[$][$]") as "%". naive_solver.

  iMod (ph_store_heap _ l with "[Hm Hph]") as "(?&X1&X2)".
  5:{ by iFrame. }
  1-4:eauto.
  { split; try lia. eauto using lookup_lt_is_Some_1. }

  iMod "Hclose" as "_".
  iSplitR "Hl Hlater X1 X2"; last first.
  { iModIntro. iApply wp_val. rewrite left_id. by iFrame. }

  iApply bupd_fupd. iApply interp_weak. 2:done. set_solver.
  iExists _,_,_,_. iFrame.
  erewrite available_update; eauto using size_block_update.
  rewrite dom_insert_lookup_L //. iFrame.

  iPureIntro.

  split_and !; eauto using update_preserves_closed,linked_store2.
  { eapply valid_store_update; eauto.
    rewrite size_block_update. unfold valid_store in *. simpl in *. lia. }
  { intros l'. rewrite /freed lookup_insert_case. clear H0.
    case_decide; eauto. subst. intros ?. inversion 1. subst.
    apply Htauro in H3. set_solver. }
Qed.

Ltac enter_deriv b q :=
  iIntros;
  iApply (wp_mono with "[-]");
  [ iApply (@wp_cas b _ _ _ _ _ _ _ _ _ q); [ | | | | iFrame] | ].

Lemma wp_cas_fail E b tid (l:loc) (i:Z) (v1 v1' v2:val) q (bs:list val) :
  bs !! (Z.to_nat i) = Some v1' ->
  (0 <= i)%Z ->
  ¬ (v1=v1') ->
  l ↦{q} bs ⊢
  wp E b tid (tm_cas l i v1 v2)
    (fun r => ⌜r=false⌝ ∗ £1 ∗ l ↦{q} bs).
Proof.
  enter_deriv true 0. all:eauto. naive_solver.
  { rewrite decide_False //. }
  iIntros (?) "[% (?&?&?)]". iFrame. subst.
  rewrite !decide_False //. iFrame. iPureIntro. rewrite bool_decide_eq_false_2 //.
Qed.

Lemma wp_cas_suc E b tid (l:loc) (i:Z) qv (v1 v2:val) (bs:list val) :
  bs !! (Z.to_nat i) = Some v1 ->
  (0 <= i)%Z ->
  (is_loc v2 -> qv≠0%Qz) ->
  l ↦ bs ∗ v2 ↤?{qv} ∅ ⊢
  wp E b tid (tm_cas l i v1 v2)
    (fun r => ⌜r=true⌝ ∗ £1 ∗ l ↦ (<[Z.to_nat i:=v2]> bs) ∗ v1 ↤?{0} {[-l-]} ∗ v2 ↤?{qv} {[+l+]}).
Proof.
  enter_deriv true qv. all:eauto.
  { rewrite decide_True //. }
  iIntros (?) "[% (?&?&?)]". iFrame. subst.
  rewrite !decide_True // bool_decide_eq_true_2 //.
  by iFrame.
Qed.

Lemma wp_cas_suc_dead E b tid (l:loc) (i:Z) qv (v1 v2:val) (bs:list val) :
  bs !! (Z.to_nat i) = Some v1 ->
  (0 <= i)%Z ->
  (is_loc v2 -> qv≠0%Qz) ->
  l ↦ bs ∗ †l ⊢
  wp E b tid (tm_cas l i v1 v2)
    (fun r => ⌜r=true⌝ ∗ £1 ∗ l ↦ (<[Z.to_nat i:=v2]> bs)).
Proof.
  enter_deriv false qv. all:eauto.
  { rewrite decide_True //. }
  iIntros (?) "[% (?&?&?)]". iFrame. subst.
  rewrite !decide_True // bool_decide_eq_true_2 //.
  by iFrame.
Qed.

End Wp_cas.
