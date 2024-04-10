From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets more_space_lang.
From irisfit Require Import interp.

Set Implicit Arguments.

Section Wp_store.

Context `{!interpGS sz Σ}.

Lemma ph_store_heap_dead `{!interpGS sz Σ} σ l v  w qw lsw :
  (is_loc w → qw ≠ 0%Qz) ->
  freed σ l →
  (match v with val_loc l' => l' ∈ dom σ | _ => True end) ->
  ph_interp σ ∗ w ↤?{qw}  lsw ==∗
  ph_interp σ ∗ w ↤?{qw} (lsw ⊎ {[+l+]}) ∗ v ↤?{0} {[-l-]}.
Proof.
  iIntros (???) "(?&?)".
  iDestruct (vmapsfrom_weak with "[$]") as "X"; last iFrame "X".
  { naive_solver. }
  { intros x. rewrite smultiset.multiplicity_disj_union.
    destruct_decide (decide (x=l)); subst.
    rewrite smultiset.multiplicity_psingleton. lia.
    rewrite smultiset.multiplicity_psingleton_ne. lia. done. }
  destruct v; try by iFrame.
  iMod (ph_cleanup_singleton with "[$]") as "(?&?)"; eauto.
  by iFrame.
Qed.

Lemma linked_store1 r θ τ l vs n v:
  θ !! l = Some (BBlock vs) ->
  freed τ l ->
  linked r θ τ ->
  linked r (<[l:=BBlock (<[n:=v]> vs)]> θ) τ.
Proof.
  intros ? Hf []. constructor; eauto.
  { rewrite dom_insert_lookup_L //. }
  { intros l' b1 b2. rewrite lookup_insert_case.
    case_decide; subst; last eauto.
    rewrite Hf. do 2 inversion 1. subst. eauto. }
Qed.

Lemma linked_store2 r θ τ l vs n v:
  θ !! l = Some (BBlock vs) ->
  τ !! l = Some (BBlock vs) ->
  (forall l', v=val_loc l' -> ¬ freed τ l') ->
  linked r θ τ ->
  linked r (<[l:=BBlock (<[n:=v]> vs)]> θ) (<[l:=BBlock (<[n:=v]> vs)]> τ).
Proof.
  intros ? Hf ? [X1 X2 X3 X4]. constructor; eauto.
  { rewrite !dom_insert_lookup_L //. }
  { intros l' b1 b2. rewrite !lookup_insert_case.
    case_decide; naive_solver. }
  { intros l0 l'. destruct_decide (decide (l0=l)); subst.
    { rewrite successor_insert // /freed lookup_insert_case.
      case_decide; eauto. intros ?.
      specialize (X3 l l').
      apply block_pointer_set_insert in H2. destruct H2.
      { destruct v; try done. auto_locs.
        rewrite locs_val_loc elem_of_singleton in H2. naive_solver. }
      { apply X3. by eapply prove_successor. } }
    { rewrite successor_insert_ne //.
      intros ?. rewrite /freed.
      rewrite lookup_insert_case. case_decide; first done.
      by eapply X3. } }
  { intros l' ?. rewrite /freed lookup_insert_case.
    case_decide; subst. done. eapply X4. done. }
Qed.

Lemma vmapsfrom_alive τ v q L :
  (is_loc v -> q ≠ 0%Qz) ->
  ph_interp τ -∗
  v ↤?{q} L -∗
  ⌜(forall l', v=val_loc l' -> ¬ freed τ l') ⌝.
Proof.
  iIntros (?) "??". iIntros (l' ->).
  iDestruct (exploit_mapsfrom_dom with "[$][$]") as "%".
  { naive_solver. }
  iDestruct (exploit_mapsfrom_dag with "[$]") as "%E". naive_solver.
  iPureIntro. rewrite /freed. naive_solver.
Qed.

Local Lemma wp_store_aux (c:bool) E b tid (l:loc) (n:Z) v qv lsv vs :
  (is_loc v -> qv <> 0%Qz) ->
  (0 <= n < Z.of_nat (length vs))%Z ->
  l ↦ vs ∗ (if c then v ↤?{qv} lsv else †l) ⊢
    wp E b tid (tm_store l n v)
    (fun tt => ⌜tt = val_unit⌝ ∗ £1 ∗ l ↦ (<[Z.to_nat n:=v]> vs) ∗
             if c then v↤?{qv}(lsv ⊎ {[+ l +]})
             ∗ (vs !!! (Z.to_nat n))↤?{0}({[-l-]}) else True).
Proof.
  iIntros (? (E1&E2)) "[Hmapsto Hv]".
  rewrite wp_unfold /wp_pre. simpl.
  auto_locs. rewrite right_id_L.
  intros_wp. intros_mod.

  iDestruct (interp_valid with "[$]") as "%Hv".

  iDestruct (exploit_mapsto with "[$]") as "%Hl".

  iSplitR; first eauto using reducible_store.
  iIntros (t' σ' ? ?) "%Hstep Hcred".
  apply invert_step_store in Hstep.
  destruct Hstep as ( bs, (Hbs&?&?&?&?&?)). subst.
  assert (l ∈ image k).
  { apply elem_of_image. do 2 eexists; split; first done. set_solver. }
  assert (bs = vs) as ->.
  { naive_solver. }
  iModIntro.
  assert (exists w, vs !! (Z.to_nat n) = Some w) as (w,Hw).
  { apply lookup_lt_is_Some. lia. }
  auto_locs.

  destruct_interp "Hi".

  iMod (store_update _ _ (<[Z.to_nat n:=v]> vs) with "[$][$]") as "(?&Hl)".
  { rewrite insert_length //. }

  rewrite !right_id_L (insert_id e) //.
  assert ({[l]} ∪ dom σ = dom σ) as Hdom.
  { assert (l ∈ dom σ) by (now apply elem_of_dom). set_solver. }

  pose proof (image_delete_subseteq k tid).
  pose proof (image_elem_subset _ _ Htid).
  rewrite list_lookup_total_alt Hw.
  assert (image_less η (<[tid:=(lk, ∅)]> k) ⊆ image_less η (<[tid:=(lk, {[l]} ∪ locs_val v)]> k)).
  { assert (tid ∈ dom k) by eauto using elem_of_dom.
    rewrite !image_less_insert2 // /xroot_less. simpl. set_solver. }

  simpl.

  (* Deal with the case where l was already freed in τ... *)
  destruct_decide (decide (freed τ l)).
  { iAssert (|==> ph_interp τ ∗ (if c then v ↤?{qv} (lsv ⊎ {[+ l +]}) ∗ w ↤?{0} {[-l-]} else True))%I with "[Hph Hv]" as ">(?&X)".
    { destruct c; last by iFrame.
      iMod (ph_store_heap_dead w with "[$]") as "(?&Hl1&Hl2)". 1,2:done.
      { destruct w; try done. erewrite <- linked_dom; last done.
        eapply closed_rtc_in_dom; eauto.
        apply rtc_once. eapply prove_successor; try done.
        apply pointers_locs. apply locs_elem_subseteq in Hw. set_solver. }
      by iFrame. }

    iMod "Hclose" as "_". iModIntro.
    iSplitR "Hl X Hcred".
    { iExists _, τ,_,_.
      iFrame. rewrite !dom_insert_L Hdom. iFrame.
      iDestruct (if_update' with "[] [$]") as "?"; last iFrame.
      { iIntros.
        iDestruct (big_sepM_insert_override_2 with "[$] []") as "?"; last by iFrame.
        all:eauto. }

      iPureIntro. rewrite image_insert2; last eauto.
      split_and !; eauto.
      { eapply closed_weak; last first.
        apply update_preserves_closed with w. 5:apply Hσ.
        all: try easy; set_solver. }
      { eapply roots_inv_weak. 2:apply Htid. set_solver. eauto. }
      { eapply linked_weak. done. rewrite (insert_id k) //.
        eauto using linked_store1. } }
    rewrite right_id. iApply wp_val. by iFrame. }

  assert (τ !! l = Some (BBlock vs)).
  { assert (is_Some (τ !! l)) as (b2&Hb2).
    { apply elem_of_dom. erewrite <- linked_dom; try done. eauto using elem_of_dom. }
    apply linked_inv in Hτ. specialize (Hτ l _ _ Hl Hb2). naive_solver. }

  destruct c; last first.
  { iDestruct (pbt_dead_exploit with "[$]") as "%". exfalso.
    erewrite linked_dom in H7; last done. apply H5. destruct H7.
    eauto using use_synchro_dead. }

  iDestruct (vmapsfrom_alive with "[$][$]") as "%". done.
  iMod (ph_store_heap with "[$]") as "(Hi&Hl1&Hl2)".
  1-4:eauto. lia.

  iMod "Hclose" as "_". iModIntro.
  iSplitR "Hl Hl1 Hl2 Hcred".
  { iExists _, _,_,_. iFrame.
    rewrite !dom_insert_L Hdom. iFrame.
    iDestruct (if_update' with "[] [$]") as "?"; last iFrame.
    { iIntros.
      iDestruct (big_sepM_insert_override_2 with "[$] []") as "?"; last by iFrame.
      all:eauto. }

    erewrite available_update; try done; last eauto using size_block_update. iFrame.

    iPureIntro. rewrite !image_insert2; last eauto.
    split_and !; eauto.
    { eapply closed_weak; last first.
      apply update_preserves_closed with w.
      5:apply Hσ. all: try easy; set_solver. }
    { eapply valid_store_update; eauto.
      rewrite size_block_update. unfold valid_store in *. simpl in *. lia. }
    { eapply roots_inv_weak. 2:apply Htid. set_solver. eauto. }
    { eapply linked_weak. done. rewrite (insert_id k) //.
      eauto using linked_store2. }
    { intros l'. rewrite /freed lookup_insert_case.
      case_decide; eauto. subst. intros ?. inversion 1. subst.
      split; first done. intros. eapply Htauro in H9; last done. done. } }
  rewrite right_id. iApply wp_val. by iFrame.
  Unshelve. all:exact inhabitant.
Qed.

Lemma wp_store E b tid (l:loc) (n:Z) v qv lsv vs :
  (is_loc v -> qv <> 0%Qz) ->
  (0 <= n < Z.of_nat (length vs))%Z ->
  l ↦ vs ∗ v ↤?{qv} lsv ⊢
    wp E b tid (tm_store l n v)
    (fun tt => ⌜tt = val_unit⌝ ∗ £1 ∗ l ↦ (<[Z.to_nat n:=v]> vs) ∗
            v↤?{qv}(lsv ⊎ {[+ l +]}) ∗ (vs !!! Z.to_nat n)↤?{0}({[-l-]})).
Proof. apply (wp_store_aux true). Qed.

Lemma wp_store_no_loc E b tid (l:loc) (n:Z) v vs :
  (0 <= n < Z.of_nat (length vs))%Z ->
  is_loc v = false ->
  l ↦ vs ⊢
    wp E b tid (tm_store l n v)
    (fun tt => ⌜tt = val_unit⌝ ∗ £1 ∗ l ↦ (<[Z.to_nat n:=v]> vs)
             ∗ (vs !!! (Z.to_nat n))↤?{0}({[-l-]})).
Proof.
  iIntros.
  iAssert (v ↤?{1%Qz} ∅)%I as "?".
  { destruct v; simpl in *; eauto. congruence. }
  iApply (wp_mono with "[-]").
  iApply (wp_store with "[$]").
  { intros. destruct v; eauto. }
  lia. iIntros (?) "(? & ? & ? & ?&?)". iFrame.
Qed.

Lemma wp_store_dead E b tid (l:loc) (n:Z) (l':loc) vs :
  (0 <= n < Z.of_nat (length vs))%Z ->
  l ↦ vs ∗ † l ⊢
    wp E b tid (tm_store l n l')
      (fun tt => ⌜tt = val_unit⌝ ∗ £1 ∗ l ↦ (<[Z.to_nat n:=val_loc l']> vs)).
Proof.
  iIntros. iApply (wp_mono with "[-]").
  iApply (@wp_store_aux false _ _ _ _ _ _ 1%Qz with "[$]").
  exact inhabitant. by compute_done. done. iIntros (?) "(->&?&?&_)". by iFrame.
Qed.

End Wp_store.
