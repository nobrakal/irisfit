From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From iris Require Import gen_heap.
From stdpp Require Import gmap gmultiset.

From irisfit.language Require Import language.
From irisfit.lib Require Import qz qz_cmra.
From irisfit Require Import disc interp pbt mapsto predecessors.

Section Wp_alloc.

Context `{!interpGS sz Σ}.

Lemma ugfrac_le (γ : gname) (m n : ugfrac) :
    @own Σ (authR (ugfracUR)) _ γ (● m) -∗
    @own Σ (authR (ugfracUR)) _  γ (◯ n) -∗
    ⌜(n ≤ m)%Qz⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as "%E".
  iPureIntro. apply auth_both_valid_discrete in E. destruct E.
  now apply ugfrac_included.
Qed.

Lemma ugfrac_remove (γ : gname) (m n : ugfrac) :
  @own Σ (authR (ugfracUR)) _ γ (● m) -∗
  @own Σ (authR (ugfracUR)) _  γ (◯ n) ==∗
  @own Σ (authR (ugfracUR)) _  γ (● (m - n : ugfrac)%Qz).
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as "%E".
  apply auth_both_valid_discrete in E. destruct E.
  iApply (own_update_2 with "Ha Hf").
  apply auth_update_dealloc.
  apply ugfrac_local_update.
  rewrite right_id.
  symmetry. apply Qz_sub_add.
  now apply ugfrac_included.
Qed.

Lemma add_fresh_ctx l u ρ π :
  l ∉ u ->
  auth_ctx ρ u ==∗
  auth_ctx (<[l:={[π]}]>ρ) ({[l]} ∪ u)∗ l ⟸ {[π]}.
Proof.
  iIntros (?) "[% (%Hv&?)]". destruct Hv.
  iMod (own_update with "[$]") as "(E1&E2)".
  { apply auth_update_alloc.
    apply alloc_singleton_local_update with (i:=l) (x:=live (1%Qp,{[π]})); last easy.
    apply not_elem_of_dom.
    rewrite dom_op. set_solver. }

  iModIntro. iSplitL "E1".
  { rewrite insert_op_l.
    2:{ set_solver. }
    iExists μ. rewrite /map1 fmap_insert. iFrame.
    rewrite dom_insert_L.
    iPureIntro. split; eauto. set_solver. }
  { iExists _.  iFrame. done. }
Qed.

Lemma remove_diamonds (p q : ugfrac) :
  own γdia (● q) ∗ ♢ p ==∗ own γdia (● (q - p : ugfrac)%Qz).
Proof.
  iIntros "[? ?]".
  iApply (ugfrac_remove with "[$] [$]").
Qed.

Lemma roots_inv_alloc k ρ mt lk π l lt η :
  l ∉ dom ρ ->
  k !! π = Some (lk,lt) ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk, {[l]})]> k) η (<[l:={[π]}]> ρ) mt.
Proof.
  intros Hl Hπ [Hk Hmt].
  constructor; eauto.
  { unfold mirror. intros j l' r' ? Hj Hr' Hl'.
    rewrite lookup_insert_case in Hj. case_decide; subst.
    { destruct (decide (l=l')); subst.
      { rewrite lookup_total_insert. set_solver. }
      { rewrite lookup_total_insert_ne //. eapply Hk; eauto.
        set_solver. } }
    { destruct (decide (l=l')); subst.
      { exfalso. apply Hl.
        specialize (Hk _ _ _ _ Hj Hr' Hl').
        apply elem_of_dom.
        rewrite lookup_total_alt in Hk.
        destruct (ρ !!l'); eauto.
        exfalso. set_solver. }
      { rewrite lookup_total_insert_ne //. eapply Hk; eauto. } } }
  { eauto using ndom_lt_insert. }
  { rewrite dom_insert_lookup_L //. }
Qed.

Lemma auth_ctx_use_dom ρ u :
  auth_ctx ρ u -∗ ⌜dom ρ ⊆ u⌝.
Proof. iIntros "[% (%Hv&?)]". destruct Hv. iPureIntro. set_solver. Qed.

Lemma linked_alloc η k θ τ l n π lk:
  k !! π = Some (lk,∅) ->
  l ∉ dom τ ->
  linked (image_less η k) θ τ ->
  linked (image_less η (<[π:=(lk, {[l]})]> k))
    (<[l:=BBlock (replicate n val_unit)]> θ)
    (<[l:=BBlock (replicate n val_unit)]> τ).
Proof.
  intros Hk Hl [X1 X2 X3 X4].
  constructor.
  { rewrite !dom_insert_L X1 //. }
  { intros l' b1 b2. rewrite !lookup_insert_case.
    case_decide; eauto. inversion 1. inversion 1. subst. eauto. }
  { intros l0 l'.
    destruct_decide (decide (l0=l)); subst.
    { rewrite successor_insert.
      erewrite block_no_pointers; try done. set_solver. }
    { rewrite successor_insert_ne // => Hl0. apply X3 in Hl0.
      rewrite /freed lookup_insert_case. case_decide; done. } }
  { intros l'. rewrite !elem_of_image_less.
    intros (π'&(lk',lt')&E1&E2). unfold freed.
    destruct_decide (decide (l=l')); subst.
    { rewrite lookup_insert //. }
    rewrite lookup_insert_ne //. eapply X4. apply elem_of_image_less.
    rewrite lookup_insert_case in E1. case_decide; subst; last eauto.
    inversion E1; subst. do 2 eexists.
    split; first done. unfold xroot_less in *. set_solver. }
Qed.

Lemma synchro_dead_alloc x τ ρ l π :
  synchro_dead τ ρ ->
  synchro_dead (<[l:=BBlock x]> τ) (<[l:={[π]}]> ρ).
Proof.
  intros Hs l'. rewrite /freed !dom_insert_L lookup_insert_case.
  case_decide; subst.
  { inversion 1. specialize (Hs l'). set_solver. }
  { intros ? E. apply Hs in E. set_solver. }
Qed.

Lemma wp_alloc' E b (n:Z) π :
  (0 < n)%Z ->
  ♢ (sz (Z.to_nat n)) ∗ outside π -∗
  wp E b π (tm_alloc n)
    (fun v => ∃ l, ⌜v = val_loc l⌝ ∗ £1 ∗ meta_token l (⊤ ∖ ↑irisfit_nm) ∗
           l ↦ (replicate (Z.to_nat n) val_unit) ∗
           l ↤ ∅ ∗
           l ⟸ {[π]} ∗ outside π).
Proof.
  iIntros (?) "(Hdiams'&Hcrit)".
  rewrite wp_unfold /wp_pre. simpl.
  intros_wp. intros_mod.

  iDestruct (use_outside with "[$][$]") as "%Hg'".
  assert (g=Out) as ->. { rewrite Hg in Hg'. naive_solver. }

  iSplitR; first eauto using reducible_alloc.
  iIntros (t' σ' ? ?) "%Hstep ?".

  (* Invert the step *)
  apply invert_step_alloc in Hstep.
  destruct Hstep as (l,(?&?&?&?&?&?&?)). subst.

  auto_locs.

  iModIntro.

  iAssert (|==> interp mt b (<[π:=(lk,{[l]})]>k) e (<[l:=BBlock (replicate (Z.to_nat n) val_unit)]> σ) ∗ l↦(replicate (Z.to_nat n) val_unit) ∗ meta_token l (⊤∖↑irisfit_nm) ∗ l↤∅ ∗ l ⟸ {[π]})%I with "[Hdiams' Hi]" as ">(?&?&?&?&?)".
  { destruct_interp "Hi".

    iDestruct (auth_ctx_use_dom with "[$]") as "%Hi".

    assert (σ !! l = None) by eauto using not_elem_of_dom.
    assert (τ !! l = None).
    { apply not_elem_of_dom. destruct Hτ as [<- _ _ _].
      by apply not_elem_of_dom. }

    iAssert (interpret []) as "?".
    { by rewrite interpret_nil. }

    iMod (store_alloc with "[$]") as "(?&?&?)".
    { by apply not_elem_of_dom. }
    iMod (ph_alloc _ _ (replicate (Z.to_nat n) val_unit) with "[$]") as "(?&?)"; first done.
    { simpl. rewrite block_pointer_set_new_block //. }

    iMod (add_fresh_ctx l with "[$]") as "[? ?]".
    { by apply not_elem_of_dom. }
    iFrame.

    iDestruct (ugfrac_le with "[$] [$]") as "%Hav".
    apply nat_to_Qz_inj_le in Hav.
    iMod (remove_diamonds with "[$]") as "?".

    iExists _,(<[l:=BBlock (replicate (Z.to_nat n) val_unit)]> τ),(<[l:={[π]}]> ρ ),η. simpl.
    iFrame.

    rewrite !dom_insert_L .
    iFrame.

    rewrite available_alloc; try easy.
    simpl. rewrite replicate_length nat_to_Qz_sub //.
    iFrame.

    iMod (if_update with "[] [$]") ; last iFrame.
    { iIntros. iDestruct (big_sepM_insert_override_2 with "[$] []") as "?"; last iFrame; eauto. }

    iPureIntro.

    pose proof (image_delete_subseteq k π).
    pose proof (image_elem_subset _ _ Htid).

    split_and !; eauto using linked_alloc, synchro_dead_alloc.
    { rewrite image_insert2 /xroot; eauto. simpl.
      eapply closed_weak; last first.
      eapply alloc_preserves_closed; eauto.
      set_solver. }
    { eapply valid_store_alloc; eauto.
      simpl. rewrite replicate_length. unfold valid_store, available in *. lia. }
    { eapply roots_inv_alloc; eauto.
      intros I. apply Hi in I.
      assert (l ∉ dom σ) by eauto. set_solver. } }
  iMod "Hclose". iModIntro.
  rewrite Nat.add_0_r !right_id (insert_id e) //. iFrame.
  iApply wp_val.
  iExists _. by iFrame.
Qed.
End Wp_alloc.
