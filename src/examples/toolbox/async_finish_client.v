From irisfit.examples Require Import diaframe proofmode spawn_join pair par async_finish.

Definition af_client : val :=
  λ: [[]],
    let: "af" := af_alloc [[]] in
    let: "skip" := mk_clo BAnon [[]] val_unit in
    let: "f" := mk_clo BAnon [] (af_async [["af", "skip"]]) in
    af_async [["af", "f"]];;
    af_finish [["af"]].

Section af_client.
Context `{interpGS0 Σ, !AFG Σ}.

Definition skip_spec (f:loc) (_:list val) (t:tm) : iProp Σ :=
  ∀ i, f ⟸ {[i]} -∗
  wpc ⊤ i (Some ∅) t (fun (_:unit) => f ⟸ ∅).

Definition call_async_spec (l s:loc) (f:loc) (_:list val) (t:tm): iProp Σ :=
  ∀ i, af nroot l ∗ f ⟸ {[i]} ∗ f ↤ ∅ ∗ Spec 0 [] skip_spec s ∗ s ⟸ {[i]} -∗
   wpc ⊤ i (Some {[l]}) t (fun (_:unit) => ♢3 ∗ spawned nroot l (fun (_:unit) =>s ⟸ ∅)%I ∗ s ↤ ∅ ∗ l ↤ ∅).

Lemma af_client_ok i :
  CODE (af_client [[]])
  TID i
  PRE (♢ 5)
  POST (fun (_:unit) => ♢5).
Proof.
  iIntros.

  wpc_call.
  wpc_let_empty.
  mine 1.
  wpc_apply (af_alloc_spec nroot).
  iIntros (l) "(#Hl&?&Hpl)". simpl.

  iApply (wpc_let_vsingleton l with "Hpl").
  { auto_locs. rewrite !locs_subst_precise.
    compute_decide_in_fv. simpl. auto_locs. rewrite locs_mk_clo.
    set_solver. }

  rewrite subst_not_in. 2:compute_done.

  wpc_apply (wpc_mk_spec i skip_spec nil nil). set_solver.
  1-4:compute_done.
  { iModIntro. iIntros (f). iIntros. iIntros (?) "?". pclean f. by iSteps. }

  mine 1. iFrame. iSplitR. rewrite /group_pointedbys. easy.
  iIntros (f) "(#Hskip&?&Hf&_) Hpl".

  iApply (wpc_let_vsingleton l with "Hpl").
  { set_solver. }

  iDestruct (mapsfrom_confront f _ _ l with "[$][$]") as "%". by vm_compute.

  wpc_apply (wpc_mk_spec i (call_async_spec l f) [("skip",val_loc f); ("af", val_loc l)] [1%Qz;1%Qz]). set_solver.
  1-4:compute_done.
  { iModIntro.
    iIntros (h). iIntros. iIntros (?) "(?&?&?&Hskip'&?)". simpl.

    iApply wpc_postpone.
    pose (Q:=(λ _ : (), f ⟸ ∅)%I).
    wpc_apply (af_async_spec _ _ _ _ _ _ _ Q)%I.
    iSplitR.
    { iIntros. rewrite pbt_PBT. iApply (wpc_call_spec_tac with "Hskip [$]"). 1,2:reflexivity. set_solver.
      iModIntro. iIntros (?) "_ ? HS". simpl. rewrite -pbt_PBT.
      iSpecialize ("HS" with "[$]").
      iApply (wpc_weak ∅). set_solver.
      iFrame. }
    iIntros ([]) "?". simpl. subst.
    pclean h. iApply wpc_fconseq. iApply spec_free. iFrame "∗#".
    iIntros "(?&(?&?&_)&_)".
    iApply wpc_val. iFrame. }
  rew_qz. iFrame. iSplitR. easy.

  iIntros (h) "(#Hspec&?&?&_) Hpl". simpl.

  iApply (wpc_let_vsingleton l with "Hpl"). set_solver.

  iDestruct (confront_pbt_pbt f h with "[$]") as "%". by vm_compute.

  pclean f with "Hf".

  wpc_apply (@af_async_spec _ _ _ _ unit). set_solver. iFrame "#".
  iSplitL.
  { iIntros.
    papprox f. simpl. rewrite !pbt_PBT. iDestruct (PBT_union with "[$]") as "?".
    iApply (wpc_call_spec_tac with "Hspec [$]"). reflexivity. reflexivity.
    rewrite gmap.dom_op. set_solver.
    iModIntro. iIntros (?) "_ ? Hspec'". iDestruct (PBT_split with "[$]") as "(?&?)".
    rewrite -!pbt_PBT.
    iApply ("Hspec'" with "[$]"). }

  iIntros ([]) "? ?". simpl.

  iApply wpc_postpone.
  wpc_apply af_finish_spec. iFrame "#".
  iIntros ([]) "#Hfinished".

  iApply fupd_wpc. iMod (fupd_mask_subseteq (↑nroot)) as "HClose". set_solver.
  iMod (redeem with "[$]") as "[% (?&?&?&?)]".
  iMod (redeem with "[$]") as "[% ?]".

  iMod "HClose" as "_". iModIntro. iClear "Hspec".
  iApply wpc_fconseq. iApply spec_free. iFrame "# ∗". iIntros "(?&_)".
  iApply wpc_fconseq. iApply sfupd_weak_mask. 2:iApply (free_finish nroot). eauto.
  iFrame "#∗". iIntros. wpc_val. conclude_diamonds.
Qed.

End af_client.
