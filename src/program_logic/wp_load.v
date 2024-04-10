From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets.
From irisfit Require Import interp pbt wp_clean.

Set Implicit Arguments.

Section Wp_load.

Context `{!interpGS sz Σ}.

Lemma roots_inv_load k ρ mt π lk l lt η :
  k !! π = Some (lk, lt) ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk,{[l]})]> k) η (<[l:={[π]} ∪ ρ !!! l]> ρ) mt.
Proof.
  intros Hπ [Hk Hmt Hdom].
  constructor.
  { intros i l' r' x Hi Hr' ?.
    destruct (decide (π = i)); subst.
    { rewrite lookup_insert in Hi. inversion Hi. subst.
      destruct (decide (l=l')); subst.
      { rewrite lookup_total_insert. set_solver. }
      { rewrite lookup_total_insert_ne //. eapply Hk; eauto. set_solver. } }
    { rewrite lookup_insert_ne // in Hi.
      destruct (decide (l=l')); subst.
      { rewrite lookup_total_insert. apply elem_of_union.
        eauto. }
      { rewrite lookup_total_insert_ne //. eauto. } } }
  { apply ndom_lt_insert; eauto. }
  { rewrite dom_insert_lookup_L //. }
Qed.

Lemma linked_load η k θ τ π lk l' lt l bs:
  k !! π = Some (lk,lt) ->
  θ !! l = Some (BBlock bs) ->
  l' ∈ locs bs ->
  ¬ freed τ l' ->
  linked (image_less η k) θ τ ->
  linked (image_less η (<[π:=(lk, {[l']})]> k)) θ τ.
Proof.
  intros Hk Hl Hbs Hf [X1 X2 X3 X4].
  constructor; eauto.
  intros l0. rewrite elem_of_image_less.
  intros (π'&?&H'&?). rewrite lookup_insert_case in H'.
  case_decide.
  { inversion H'. subst.
    destruct_decide (decide (l0 = l')); subst.
    { eauto.  }
    { eapply X4. apply elem_of_image_less. do 2 eexists.
      split; first done. unfold xroot_less in *. set_solver. } }
  { eapply X4. eapply elem_of_image_less. eauto. }
Qed.

Lemma interp_load π b lk (l:loc) mt k (σ:store) p (v:val) bs n e :
  k !! π = Some (lk,{[l]}) ->
  σ !! l = Some (BBlock bs) ->
  bs !! n = Some v ->
  v ⟸?{p} ∅ -∗
  interp mt b k e σ ==∗
   v ⟸?{p} {[π]} ∗ interp mt b (<[π:=(lk,locs v)]> k) e σ.
Proof.
  iIntros (Hπ Hl Hn) "X Hi".
  destruct_decide (decide (is_loc v)) as Hv.
  2:{ rewrite !vpbt_not_loc //. iFrame.
      iMod (interp_weak with "[$]"); last by iFrame.
      2:{ eauto. }
      rewrite locs_no_loc //. }
  { apply is_loc_inv in Hv.
    destruct Hv as (l',Hl'). subst. simpl.
    destruct_interp "Hi".
    iDestruct (pbt_exploit with "[$]") as "%E". destruct E as (?&?).

    rewrite pbt_PBT.
    iMod (PBT_update_fork with "[$] [$]") as "(? & ?)".
    rewrite left_id_L -pbt_PBT.
    iFrame.
    iExists _,_,_,_. iFrame.
    iMod (if_update with "[] [$]"); last iFrame.
    { iIntros. iDestruct (big_sepM_insert_override_2 with "[$] []") as "?"; last by iFrame.
      { eauto. }
      { iIntros. iFrame. } }
    iPureIntro.

    assert (l ∈ image k).
    { apply elem_of_image. eexists _,_. split; eauto. set_solver. }

    pose (locs_elem_subseteq _ _ _ Hn).
    pose proof (image_delete_subseteq k π).
    pose proof (image_elem_subset k π Hπ).

    assert (image (<[π:=(lk, {[l']})]> k) ⊆ image k ∪ locs bs).
    { rewrite image_insert2; eauto.
      set_solver. }

    auto_locs.
    split_and !; eauto.
    { eapply closed_inline_root in Hσ; eauto.
      eauto using closed_weak. }
    { eauto using roots_inv_load. }
    { eapply linked_load; eauto.
      { apply elem_of_union_list. exists {[l']}. split; last set_solver.
        apply elem_of_list_fmap_1_alt with (x:=val_loc l').
        { apply elem_of_list_lookup. eauto. }
        { set_solver. } }
      { intros X. apply Htauro in X. naive_solver. } }
    { eapply synchro_dead_same_dom; last done.
      rewrite dom_insert_lookup_L //. } }
Qed.

Lemma wp_load E b (l:loc) (n:Z) q p vs π w :
  w = vs !!! (Z.to_nat n) ->
  (0 <= n < Z.to_nat (length vs))%Z ->
  l ↦{q} vs ∗ w ⟸?{p} ∅ ⊢
    wp E b π (tm_load l n)
    (fun v => ⌜v = w⌝ ∗ £1 ∗ l ↦{q} vs ∗ w ⟸?{p} {[π]}).
Proof.
  iIntros (? ?) "(Hmapsto & Hpbt)". subst.
  rewrite wp_unfold /wp_pre. simpl.
  iIntros (? ? ? ? ? ? (Hπ&?)) "Hi".

  iDestruct (exploit_mapsto with "[$]") as "%Hl".

  iApply fupd_mask_intro. set_solver. iIntros "Hclose".
  iSplitR.
  { iPureIntro. eapply reducible_load; eauto. lia. }

  iIntros (? ? ? ?) "%Hstep ?".
  apply invert_step_load in Hstep.
  destruct Hstep as (?&(bs,(v,(Hload&?&?&Hn)))&?&?). subst.
  assert (bs = vs) by naive_solver. subst.

  auto_locs. rewrite !right_id_L.
  iModIntro.

  simpl in *. rewrite locs_val_loc locs_val_nat right_id_L in Hπ.
  rewrite list_lookup_total_alt Hn (insert_id e) //. simpl.
  iMod (interp_load with "[$] [$]") as "(? & ?)"; eauto.

  iFrame. simpl.
  iMod "Hclose".
  iModIntro. rewrite right_id.
  iApply wp_val. by iFrame.
Qed.

Lemma wp_load' S E b (l:loc) (n:Z) q p vs π w :
  w = vs !!! (Z.to_nat n) ->
  (0 <= n < Z.to_nat (length vs))%Z ->
  l ↦{q} vs ∗ w ⟸?{p} S ⊢
    wp E b π (tm_load l n)
    (fun v => ⌜v = w⌝ ∗ £1 ∗ l ↦{q} vs ∗ w ⟸?{p} (S ∪ {[π]})).
Proof.
  iIntros (? ?) "(? & ?)".
  replace S with (S ∪ ∅) by set_solver.
  replace p with (p/2 + p/2)%Qp.
  2:{ rewrite Qp.div_2 //. }
  iDestruct (vpbt_split with "[$]") as "(HS & ?)".
  iApply (wp_mono with "[-HS]").
  iApply wp_load; eauto. by iFrame.
  iIntros (?) "(? & ? & ? & ?)". iFrame.
  rewrite right_id_L.
  iApply vpbt_join. iFrame.
Qed.

Lemma wp_load_no_loc E b (l:loc) (n:Z) q vs π w :
  w = vs !!! (Z.to_nat n) ->
  ¬ is_loc w ->
  (0 <= n < Z.to_nat (length vs))%Z ->
  l ↦{q} vs ⊢
    wp E b π (tm_load l n)
    (fun v => ⌜v = w⌝ ∗ £1 ∗ l ↦{q} vs).
Proof.
  iIntros.
  iAssert (vpbt w 1%Qp ∅) as "?".
  { destruct w; eauto. simpl in *. naive_solver. }
  iApply (wp_mono with "[-]").
  iApply wp_load; eauto. iFrame. iFrame "#".
  iIntros (?) "(?&?&?&?)". by iFrame.
Qed.

Lemma roots_inv_load_debt k ρ mt π lk lt η S S' :
  η !! π = Some (Some S) ->
  k !! π = Some (lk, lt) ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk, S')]> k) (<[π:=Some (S ∪ S')]> η) ρ mt.
Proof.
  intros ? ? [E1 E2 E3].
  constructor; eauto using ndom_lt_insert.
  { intros i l (lk',lt') x. rewrite !lookup_insert_case.
    case_decide; eauto. inversion 1. inversion 1. intros. subst. simpl.
    eapply E1 in H; last done. simpl in *. eapply H. set_solver. }
  { rewrite !dom_insert_L //. set_solver. }
Qed.

Lemma linked_load_debt η k θ τ π S lk lt S' :
  η !! π = Some (Some S) ->
  k !! π = Some (lk, lt) ->
  linked (image_less η k) θ τ ->
  linked (image_less (<[π:=Some (S ∪ S')]> η) (<[π:=(lk, S')]> k)) θ τ.
Proof.
  intros H1 H2 [X1 X2 X3 X4]. constructor; eauto.
  intros l. rewrite elem_of_image_less. intros (π'&(?&?)&?&?).
  eapply X4. eapply elem_of_image_less.
  destruct_decide (decide (π=π')); subst.
  { do 2 eexists. split; first done.
    rewrite lookup_insert in H. inversion H. subst.
    rewrite lookup_total_insert in H0.
    rewrite lookup_total_alt H1. unfold xroot_less in *. set_solver. }
  { rewrite lookup_insert_ne // in H.
    clear H2. do 2 eexists. split; first done.
    rewrite lookup_total_insert_ne // in H0. }
Qed.

Lemma wp_load_inside E b (l:loc) (n:Z) q vs π S :
  (0 <= n < length vs)%Z ->
  l ↦{q} vs ∗ inside π S ⊢
    wp E b π (tm_load l n)
      (fun v => ⌜v = vs !!! (Z.to_nat n)⌝ ∗ £1 ∗ l ↦{q} vs ∗ inside π (S∪ locs v)).
Proof.
  iIntros (?) "(Hl&D)".

  rewrite wp_unfold /wp_pre. simpl.
  iIntros (? ? ? ? ? ? (Hπ&?)) "Hi".

  assert (l ∈ image k).
  { apply elem_of_image. eexists _,_. split; eauto. auto_locs. set_solver. }

  iDestruct (exploit_mapsto with "[$]") as "%Hl".

  iApply fupd_mask_intro. set_solver. iIntros "Hclose".
  iSplitR.
  { iPureIntro. eapply reducible_load; eauto. }

  iIntros (? ? ? ?) "%Hstep Hc".
  apply invert_step_load in Hstep.
  destruct Hstep as (?&(bs,(v,(Hload&?&?&Hn)))&?&?). subst.
  assert (bs=vs) by naive_solver. subst.

  auto_locs. rewrite right_id_L !right_id. iModIntro.

  simpl in *. rewrite locs_val_loc locs_val_nat right_id_L in Hπ.
  rewrite list_lookup_total_alt Hn (insert_id e) //. simpl.

  destruct_interp "Hi".
  iDestruct (ghost_map.ghost_map_lookup with "Hinside [$]") as "%".
  iMod (ghost_map.ghost_map_update with "Hinside [$]") as "(?&D)".

  iMod "Hclose" as "_". iModIntro.
  iSplitR "Hl Hc D"; last first.
  { iApply wp_val. by iFrame. }

  iExists _,_,_,_. iFrame "∗%".
  iDestruct (if_update' with "[] [$]") as "?"; last iFrame.
  { iIntros. iDestruct (big_sepM_insert_override_2 with "[$] []") as "?"; last by iFrame.
    eauto. iIntros. iFrame. }
  iPureIntro.

  pose proof (locs_elem_subseteq _ _ _ Hn).
  pose proof (image_delete_subseteq k π).
  pose proof (image_elem_subset k π Hπ).

  assert (image (<[π:=(lk, locs_val v)]> k) ⊆ image k ∪ locs vs).
  { rewrite image_insert2; eauto. set_solver. }

  eapply closed_inline_root in Hσ; eauto.
  split_and!;
    eauto using closed_weak,roots_inv_load_debt,debt_update_Some,linked_load_debt.
Qed.

End Wp_load.
