From iris.proofmode Require Import proofmode.
From stdpp Require Import base.
From iris.algebra Require Import gmap.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit.lib Require Import qz qz_cmra.
From irisfit Require Import more_maps_and_sets hypotheses.
From irisfit Require Import disc interp more_interp pbt more_space_lang.

Section Cloud.

Context `{!interpGS sz Σ}.

(* ------------------------------------------------------------------------ *)

(* An open cloud [ocloud antecedents n ls] represents the ownership of a set
   of heap objects whose predecessors are contained in [antecedents], whose
   total size is [n], and whose addresses form the set [ls]. *)

Fixpoint ocloud (antecedents : gset loc) (n : nat) (locs : list loc) : iProp Σ
:=
  match locs with
  | [] =>
      ⌜ n = 0%nat ⌝
  | l :: locs' =>
      ∃ n1 n2, sizeof l n1 ∗
        ⌜ n = (n1 + n2)%nat ⌝ ∗
        mapsfrom_set l 1%Qz antecedents ∗
        l ⟸ ∅ ∗
        ocloud antecedents n2 locs'
  end%I.

(* A closed cloud is an open cloud whose domain is [X] and whose
   antecedents are contained in [X]. It is therefore closed under
   predecessors. *)

Definition cloud (X : gset loc) n : iProp Σ :=
  ∃ ls, ⌜X ⊆ locs ls⌝ ∗ ocloud X n ls.

Lemma ocloud_cloud ls X n :
  X ⊆ locs ls ->
  ocloud X n ls -∗
  cloud X n.
Proof. iIntros. iExists _. by iFrame. Qed.

Notation "locs ☁ n" :=
  (cloud locs n)
  (at level 20) : bi_scope.

(* ------------------------------------------------------------------------ *)

(* Auxiliary lemmas about clouds. *)

(* These two lemmas allow building clouds and are provided for use by an
   end user. *)

Lemma ocloud_empty antecedents :
  ⊢ ocloud antecedents 0 [].
Proof.
  simpl ocloud. eauto.
Qed.

Lemma ocloud_cons_mapsto antecedents n (locs : list loc) l dq b ls :
  dom ls ⊆ antecedents  ->
  ocloud antecedents n locs ∗ l ↦{dq} b ∗ l ↤ ls ∗ l ⟸ ∅
  ⊢ ocloud antecedents (sz (length b) + n) (l :: locs) ∗ l ↦{dq} b .
Proof.
  iIntros (?) "(Hcloud & ? & ? & ?)".
  iDestruct (mapsto_extract_size with "[$]") as "#?". iFrame.
  do 2 iExists _. rewrite /mapsfrom_set.
  iSplit; [ eauto | iFrame; eauto].
Qed.

Lemma ocloud_extend S1 S2 n ls :
  S1 ⊆ S2 ->
  ocloud S1 n ls -∗ ocloud S2 n ls.
Proof.
  iIntros (?) "HO".
  iInduction (ls) as [|] "IH" forall (n); first done.
  iDestruct "HO" as "[%[%(?&?&?&?&?)]]".
  iDestruct ("IH" with "[$]") as "?". iExists _,_. iFrame.
  by iApply more_space_lang.mapsfrom_set_overapprox.
Qed.

Lemma ocloud_cons antecedents n n' (locs : list loc) l ls :
  dom ls ⊆ antecedents  ->
  sizeof l n' -∗
  ocloud antecedents n locs ∗ l ↤ ls ∗ l ⟸ ∅ -∗
  ocloud antecedents (n' + n) (l :: locs).
Proof.
  iIntros (?) "? (Hcloud & ? & ?)".
  iFrame.
  do 2 iExists _. rewrite /mapsfrom_set.
  iSplit; [ eauto | iFrame; eauto].
Qed.

Lemma ocloud_add antecedents n n' (locs : list loc) l ls :
  sizeof l n' -∗
  ocloud antecedents n locs ∗ l ↤ ls ∗ l ⟸ ∅ -∗
  ocloud (dom ls ∪ antecedents) (n' + n) (l :: locs).
Proof.
  iIntros "? (?&?&?)". iApply (ocloud_cons with "[$]").
  2:{ iFrame. iApply (ocloud_extend with "[$]"). set_solver. }
  set_solver.
Qed.

Local Lemma not_in l ls :
  l ⟸ ∅ -∗
  ([∗ list] l0 ∈ ls, l0 ⟸ ∅) -∗
  ⌜l ∉ ls⌝.
Proof.
  iIntros "? X".
  iInduction ls as [|] "IH".
  { iPureIntro. set_solver. }
  iDestruct "X" as "(?&?)".
  iDestruct (confront_pbt_pbt with "[$]") as "%". by vm_compute.
  iDestruct ("IH" with "[$][$]") as "%".
  iPureIntro. set_solver.
Qed.

(* XXX move *)

Lemma exploit_sizeof σ l n :
  store_interp σ -∗  sizeof l n -∗ ⌜exists b, σ !! l = Some (BBlock b) /\ sz (length b) = n⌝.
Proof.
  iIntros "[% (?&?&%)] ?".
  iDestruct (meta_in_dom with "[$][$]") as "%Hl".
  apply elem_of_dom in Hl. destruct Hl as (?,Hl).
  assert (σ !! l = Some (BBlock x)) as E.
  { rewrite H lookup_fmap Hl //. }
  iDestruct (big_sepM_lookup _ _ l (sz (length x)) with "[$]") as "#?".
  { rewrite lookup_fmap Hl //. }
  iDestruct (gen_heap.meta_agree with "[$][$]") as "%".
  iPureIntro. naive_solver. Unshelve. apply _.
Qed.

Lemma use_sizeof r τ θ l n A  :
  linked r θ τ ->
  sizeof l n -∗
  store_interp θ ∗ ph_interp τ ∗ mapsfrom_set l 1%Qz A  -∗
  ⌜exists b, τ !! l = Some (BBlock b) /\ sz (length b) = n⌝.
Proof.
  iIntros ([Hdom]) "? (Hi&?&E)".
  iDestruct (exploit_sizeof with "[$][$]") as "%E".
  destruct E as (b&Hl0&?).
  pose proof (elem_of_dom_2 _ _ _ Hl0) as Hl. rewrite Hdom elem_of_dom in Hl.
  destruct Hl as (b',Hb'). destruct b' as [b'|]; last first.
  { iExFalso.
    iDestruct "E" as "[% (?&?)]".
    iDestruct (exploit_mapsfrom_dag with "[$]") as "[% %]". compute_done. naive_solver. }
  assert (b=b') as -> by (unfold same_or_dead in *; naive_solver).
  iFrame. iPureIntro. naive_solver.
Qed.

Lemma ocloud_split r antecedents (ls : list loc) n θ τ :
  linked r θ τ ->
  store_interp θ ∗ ph_interp τ ∗ ocloud antecedents n ls ==∗
  store_interp θ ∗ ph_interp τ ∗ ⌜list_to_set ls ⊆ dom τ /\ (size_heap sz (hypotheses.deallocate (list_to_set ls) τ) + n = size_heap sz τ)%nat ⌝ ∗
  ([∗ list] l ∈ ls, l ⟸ ∅) ∗
  ([∗ list] l ∈ ls, mapsfrom_set l 1%Qz antecedents).
Proof.
  intros ?.
  rewrite /hypotheses.deallocate.
  iInduction ls as [| l ls' IH ] "IH" forall (n); simpl ocloud.
  { iIntros "(?&?&%)". simpl.  iIntros. iFrame. rewrite stdpp.gmap_mset_empty.
    iPureIntro. rewrite !right_id. split; first set_solver. lia. }
  { iIntros "(?&Hi&H)".
    iDestruct "H" as (n' ?) "(? & % & ? & ? & Hcloud)".
    iMod ("IH" with "[$]") as "(?&Hi&%Eq&?&?)". destruct Eq as (?&Eq).
    iDestruct (not_in with "[$][$]") as "%".
    iDestruct (use_sizeof with "[$][$]") as "%E"; first done.
    destruct E as (b,(Hl&Hb)).

    iFrame. iPureIntro. simpl. split.
    { apply elem_of_dom_2 in Hl. set_solver. }
    rewrite -> stdpp.gmap_mset_snoc'; eauto.
    subst. rewrite Nat.add_assoc -Eq. f_equal.
    replace (sz (length b)) with (size_block sz (BBlock b)) by done.
    rewrite size_heap_dealloc //.
    rewrite stdpp.gmap_lookup_mset_outside //.
    rewrite elem_of_list_to_set //. }
Qed.

Lemma cloud_split r θ X n τ :
  linked r θ τ ->
  store_interp θ ∗ ph_interp τ ∗ cloud X n ==∗
  store_interp θ ∗ ph_interp τ ∗ ∃ S, ⌜X ⊆ S ⊆ dom τ /\ (size_heap sz (hypotheses.deallocate S τ) + n = size_heap sz τ)%nat ⌝ ∗
  ([∗ set] l ∈ S, l ⟸ ∅) ∗
  ([∗ set] l ∈ S, mapsfrom_set l 1%Qz S).
Proof.
  iIntros (Hlink) "(?&?&[%(%&?)])".
  assert ((list_to_set ls) = locs ls) as Hls.
  { clear dependent τ. revert X H. induction ls; try done. auto_locs. set_solver. }
  iMod (ocloud_split with "[$]") as "(?&?&%Hok&Hpbt&Hmt)"; eauto.
  iFrame. rewrite Hls in Hok.
  iAssert (⌜NoDup ls⌝)%I as "%".
  { iClear "Hmt".
    rewrite NoDup_alt. iIntros (i j x ??).
    rewrite (big_sepL_delete' _ _ i x) //. iDestruct "Hpbt" as "(?&Hpbt)".
    destruct_decide (decide (i=j)); try done.
    rewrite (big_sepL_delete' _ _ j x) //. iDestruct "Hpbt" as "(X&_)".
    iSpecialize ("X" with "[%//]"). iDestruct (confront_pbt_pbt with "[$]") as "%".
    by vm_compute. by congruence. }
  do 2 rewrite -big_sepS_list_to_set // Hls. iModIntro.
  iExists (locs ls).
  iFrame. iSplitR.
  { iPureIntro. set_solver. }
  iApply (big_sepS_impl with "[$]"). iModIntro. iIntros.
  by iApply (mapsfrom_set_overapprox with "[$]").
Qed.

(* ------------------------------------------------------------------------ *)

Lemma interp_exploit_pbt_full k ρ mt (σ:store) l η :
  dom k = dom η ->
  roots_inv k η ρ mt ->
  auth_ctx ρ (dom σ) -∗ l ⟸ ∅ -∗ ⌜l ∉ image_less η k⌝.
Proof.
  iIntros (Hdom [Hρ ?]) "Hi [% (%&Hn)]".
  iDestruct (pbt_precise_exploit_full with "[$]") as "%Hl".
  iPureIntro.
  intros Hlk.
  apply elem_of_image_less in Hlk. destruct Hlk as (tid,(ls,(Htid&Hr))).
  assert (exists r, η !! tid = Some r) as (r',Hr').
  { apply elem_of_dom. rewrite -Hdom. by apply elem_of_dom. }
  specialize (Hρ _ l _ _ Htid Hr').
  rewrite lookup_total_alt Hl in Hρ. simpl in *.
  rewrite lookup_total_alt Hr' in Hr. simpl in *.
  unfold xroot, xroot_less in *.
  set_solver.
Qed.

Lemma exploit_pbt_full_iterated k ρ mt (σ:store) locs η :
  dom k = dom η ->
  roots_inv k η ρ mt ->
  auth_ctx ρ (dom σ) -∗ ([∗ set] l ∈ locs, l ⟸ ∅) -∗ ⌜locs ∩ image_less η k = ∅⌝.
Proof.
  iIntros (??) "? HX".
  iInduction locs as [|] "IH" using set_ind_L.
  { iPureIntro. set_solver. }
  { rewrite big_sepS_union; last set_solver. rewrite big_sepS_singleton.
    iDestruct "HX" as "(?&?)". iDestruct ("IH" with "[$][$]") as "%".
    iDestruct (interp_exploit_pbt_full with "[$][$]") as "%"; eauto.
    iPureIntro. set_solver. }
Qed.

Local Lemma dealloc_pbt l ρ μ :
  <[l:=discarded tt]> (map1 ρ ⋅ μ) =
    delete l (map1 ρ) ⋅ <[l:=discarded tt]> μ.
Proof.
  eapply (@map_eq _ (gmap loc )). apply _. intros l'.
  rewrite lookup_op.
  destruct (decide (l=l')); subst.
  { rewrite lookup_insert lookup_delete lookup_insert //. }
  { rewrite !lookup_insert_ne // lookup_delete_ne // lookup_op //. }
Qed.

Local Lemma delete_map1 l ρ : delete l (map1 ρ) = map1 (delete l ρ).
Proof. rewrite /map1 fmap_delete //. Qed.

Local Lemma auth_ctx_free l ρ u :
  auth_ctx ρ u ∗ l ⟸ ∅ ==∗ auth_ctx (delete l ρ) u ∗ pbt_dead l.
Proof.
  iIntros "(Ha&[% (%&Hf)])".
  iDestruct (pbt_precise_exploit_full with "[$]") as "%Hl".
  iDestruct "Ha" as "[% (%Hv&Ha)]".
  iMod (own_update_2 with "Ha Hf") as "(?&_)".
  { apply auth_update.
    apply delete_singleton_local_update . apply _. }
  iMod (own_update with "[$]") as "(?&?)".
  { apply auth_update_alloc.
    apply alloc_singleton_local_update with (i:=l) (x:=discarded tt).
    { rewrite lookup_delete //. }
    easy. }
  iFrame.
  rewrite insert_delete_insert dealloc_pbt delete_map1.
  iExists _. iFrame.
  destruct Hv.
  iPureIntro.
  split.
  { rewrite dom_delete dom_insert.
    assert (l ∈ dom ρ) by eauto.
    set_solver. }
  intros l' ?. destruct (decide (l=l')); subst.
  { rewrite lookup_insert //. naive_solver. }
  { rewrite lookup_insert_ne //. naive_solver. }
Qed.

Local Definition delete_all {A} (S:gset loc) (ρ:gmap loc A) : gmap loc A :=
  set_fold delete ρ S.

Local Lemma delete_disj_union {A} (X Y:gset loc) (ρ:gmap loc A) :
  X ## Y ->
  delete_all X (delete_all Y ρ) = delete_all (X ∪ Y) ρ.
Proof.
  intros.
  rewrite /delete_all /set_fold. simpl.
  rewrite <-foldr_app. apply foldr_permutation; try apply _.
  2:{ rewrite elements_disj_union //. }
  intros. apply delete_commute.
Qed.

Local Lemma auth_ctx_free' k mt locs ρ η u :
  roots_inv k η ρ mt ->
  auth_ctx ρ u ∗ ([∗ set] l ∈ locs, l ⟸ ∅) ==∗ ⌜roots_inv k η (delete_all locs ρ) mt⌝ ∗ auth_ctx (delete_all locs ρ) u ∗ ([∗ set] l ∈ locs, pbt_dead l).
Proof.
  iIntros (E) "(?&HX)".
  iInduction locs as [|] "IH" using set_ind_L forall (ρ E).
  { rewrite /delete_all set_fold_empty !big_sepS_empty //. by iFrame. }
  rewrite !big_sepS_insert; try done.
  iDestruct "HX" as "([%(%&?)]&X)".
  iDestruct (pbt_precise_exploit_full with "[$]") as "%".
  iMod (auth_ctx_free with "[-X]") as "(?&?)".
  { iFrame. iExists _. iFrame. done. }
  iMod ("IH" with "[%][$][$]") as "(?&?&?)".
  { apply roots_inv_delete. assert (S' = ∅) by set_solver. naive_solver. done. }
  iFrame. iModIntro.

  replace (delete x ρ) with (delete_all {[x]} ρ).
  2:{ rewrite /delete_all set_fold_singleton //.  }
  rewrite delete_disj_union; last set_solver.
  rewrite comm_L. iFrame.
Qed.

Lemma dom_delete_all locs (ρ:gmap loc (gset thread_id)) :
  dom (delete_all locs ρ) = dom ρ ∖ locs.
Proof.
  unfold delete_all.
  eapply set_fold_ind_L with (P:=fun X L => dom X = dom ρ ∖ L).
  { set_solver. }
  { intros l X r  Hx. rewrite dom_delete_L. set_solver. }
Qed.

Lemma synchro_dead_deallocate τ ρ locs :
  (forall l, l ∈ locs -> l ∈ dom τ) ->
  synchro_dead τ ρ ->
  synchro_dead (deallocate locs τ) (delete_all locs ρ).
Proof.
  intros ? Hs l x. rewrite dom_delete_all /freed /deallocate.
  destruct_decide (decide (l ∈ locs)).
  { rewrite stdpp.gmap_lookup_mset_inside //; set_solver. }
  { rewrite stdpp.gmap_lookup_mset_outside //.
    intros Hf. apply Hs in Hf. set_solver. }
Qed.

(* This ghost operation consumes a closed cloud [locs☁n]. It produces a
   witness [††locs] that every location [l] in the set [locs] has been
   deallocated, and produces [n] space credits. *)

Lemma supd_free_group locs n :
  locs☁n =[#]=∗ ††locs ∗ ♢n.
Proof.
  iIntros "Hcloud".
  iIntros (?????) "Hi".

  destruct_interp "Hi".
  inversion Hdebt.
  iMod (cloud_split with "[$]") as "(?&?&[%S (((%&%)&%)&?&?)])"; only 1,2:eauto.
  iDestruct (exploit_pbt_full_iterated with "[$][$]") as "%". 2:eauto.
  { destruct Hρ. congruence. }

  iMod (ph_free_group τ S with "[$]") as "(Hph&%Hfacts)".
  iMod (auth_ctx_free' with "[$]") as "(%&?&H2)".
  { eauto. }

  iAssert (††locs)%I with "[H2]" as "?".
  { iApply (big_sepS_subseteq _ S). done.
    iApply (big_sepS_mono with "[$]"). iIntros.
    rewrite dagger_eq //. }

  set (τ' := hypotheses.deallocate S τ).
  (* The available space in the heap increases by [n]. *)
  assert (Hspace: (available sz ms τ + n = available sz ms τ')%nat).
  { unfold available.
    unfold valid_store in *.
    simpl in *. unfold τ'. lia. }

  (* Perform a ghost update to create [n] new diamonds. *)
  iMod (ugfrac_update_incr _ _ n with "Hdiams") as "[Hauth Hfrag]".
  rew_qz.
  rewrite Hspace.
  fold (♢n)%I.
  (* Conclude. *)
  iModIntro. iFrame "#∗".
  (* Close the state interpretation invariant. *)
  iExists _,τ',_,_. iFrame.
  iPureIntro. split_and !; eauto.
  { eapply free_group_preserves_valid_store; eauto. }
  { pose proof image_less_subseteq_image.
    eapply free_group_preserves_linked; eauto using closed_weak. }
  { eauto using synchro_dead_deallocate. }
Qed.

Lemma supd_free_ocloud P n D :
  P ⊆ list_to_set D ->
  ocloud P n D =[#]=∗ ††(list_to_set D) ∗ ♢n.
Proof.
  iIntros (?) "Ho". iIntros.
  iMod (supd_free_group (list_to_set D) n with "[Ho][$]") as "(?&?&?)";
    last by iFrame.
  iApply ocloud_cloud.
  2:{ iApply (ocloud_extend with "[$]"). done. }
  clear H. intros l Hl. apply elem_of_list_to_set in Hl.
  induction D. set_solver. inversion Hl. subst. auto_locs. set_solver.
  subst. auto_locs. set_solver.
Qed.

End Cloud.

Section Wp_free.
Context `{!interpGS sz Σ}.

Lemma interp_free (l:loc) q bs (blk:list val) :
  dom bs ⊆ {[l]} →
  pbt l 1%Qp ∅ ∗ l ↦{q} blk ∗ l ↤ bs =[#]=∗
  ♢(sz (length blk)) ∗  l ↦{q} blk ∗ † l.
Proof.
  iIntros (Hl) "[Hnctx [Hmapsto Hmapsfrom]]". iIntros (?????) "Hi".
  iDestruct (mapsto_extract_size with "[$]") as "#?".
  iFrame "Hmapsto".
  iAssert (cloud {[l]} (sz (length blk))) with "[-Hi]" as "?".
  { rewrite /cloud. iExists [l]. iSplitR. { iPureIntro. auto_locs. set_solver. }
    iExists _,0.
    iFrame "#∗". iSplitR.
    { iPureIntro. lia. }
    iSplitL; last done.
    iExists _. iFrame. done. }
  iMod (supd_free_group with "[$][$]") as "(?&?&?)". iFrame.
  rewrite /daggers big_sepS_singleton //.
Qed.

(* interp_free without cycles *)
Lemma interp_free' (l:loc) q (blk:list val) :
  pbt l 1%Qp ∅ ∗ l ↦{q} blk ∗ l ↤ ∅ =[#]=∗
  ♢(sz (length blk)) ∗ l ↦{q} blk ∗ † l.
Proof. iApply interp_free. done. Qed.

(* interp_free without pointso! *)
Lemma interp_free'' (l:loc) n :
  sizeof l n ∗ pbt l 1%Qp ∅ ∗  l ↤ ∅ =[#]=∗
  ♢n ∗ † l.
Proof.
  iIntros "(?&?&?)". iIntros (?????) "Hi".
  iAssert (cloud {[l]} n) with "[-Hi]" as "?".
  { rewrite /cloud. iExists [l]. iSplitR. { iPureIntro. auto_locs. set_solver. }
    iExists _,0.
    iFrame "#∗". iSplitR.
    { iPureIntro. lia. }
    iSplitL; last done.
    iExists _. iFrame. done. }
  iMod (supd_free_group with "[$][$]") as "(?&?&?)". iFrame.
  rewrite /daggers big_sepS_singleton //.
Qed.

End Wp_free.

Global Opaque cloud.
Global Opaque ocloud.
