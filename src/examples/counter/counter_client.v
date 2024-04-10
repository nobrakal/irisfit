From irisfit.examples Require Import proofmode.
From irisfit.examples Require Import counter par.

Definition client : tm :=
  let: "r" := mk_counter [[]] in
  let: "incr" := "r".[0] in
  let: "get"  := "r".[1] in
  par_clo [["incr", "incr"]];;
  call_clo "get" [[]].

Section Counter_client.
Context `{!spawnG Σ,interpGS0 Σ,ccounterG Σ,spawn_join.spawnG Σ}.

Lemma client_spec tid :
  CODE client
  TID tid
  PRE ♢11
  POST (fun m:Z => ⌜m=2⌝ ∗ ♢11).
Proof.
  iIntros "Hd".
  replace (nat_to_Qz 11) with (nat_to_Qz 7 + nat_to_Qz 4)%Qz by compute_done.
  iDestruct "Hd" as "(Hd1 & Hd2)". simpl.
  rewrite /client.

  wpc_let_empty.
  unshelve wpc_apply mk_counter_spec. exact nroot.

  iIntros (?) "[% [% (Hpv&?&?&Hcfi&?&Hcfg&?&Hcounter)]]". simpl.

  wpc_let_noclean.
  wpc_load. iIntros "(?&?&?)".

  wpc_let_noclean.
  wpc_load. iIntros "(?&Hcfg)".
  repeat (rewrite subst_call_clo). simpl.

  iApply (wpc_let_vsingleton fg with "Hcfg").
  set_solver.

  pose (Q := fun (_:val) => (IsCounter nroot (1 / 2) 1 fi fg ∗ fi ⟸{1/2} ∅)%I ).

  unshelve iApply wpc_apply.
  8:iApply (@par_clo_spec _ _ _ _ _ _ _ _ _ 1 1 Q Q 1 1). apply _. apply opt_incl_refl.
  1,2:compute_done.
  iFrame.

  iSplitL "Hcounter".
  { iAssert (IsCounter nroot (1/2)%Qp 0 fi fg ∗ IsCounter nroot (1/2)%Qp 0 fi fg)%I with "[Hcounter]" as "(Hc1&Hc2)".
    { iApply IsCounter_split. rewrite Qp.div_2 //. }

    iSplitL "Hc1".
    { iIntros.
      iApply wpc_postpone.
      iApply (wpc_mono_val with "[Hc1]").
      { iApply wpc_weak. 2:iApply incr_spec. set_solver. iFrame. }
      iIntros.
      pclean fi. iSteps. }
    { iIntros.
      iApply wpc_postpone.
      iApply (wpc_mono_val with "[Hc2]").
      { iApply wpc_weak. 2:iApply incr_spec. set_solver. iFrame. }
      iIntros.
      pclean fi. iSteps. } }

  iIntros (?) "[% [% (?&?&?&?&(?&?)&?&?&(?&?)&?&?)]] ?". simpl.

  iDestruct (IsCounter_join with "[$]") as "Hc".
  iDestruct (pbt_join fi with "[$]") as "?".
  rewrite Qp.div_2. simpl.

  iApply wpc_postpone.

  wpc_apply get_spec.
  iIntros (?) "(%Hv & ?)". simpl in *. subst.

  rewrite left_id_L.

  pclean v.

  iApply wpc_tconseq.
  { iApply (interp_free' v). }
  iFrame. iIntros "(?&?&#?)".

  iApply wpc_tconseq.
  { iApply (mapsfrom_cleanup fi v). }
  iFrame "∗ #". iIntros.
  iApply wpc_tconseq.
  { iApply (mapsfrom_cleanup fg v). }
  iFrame "∗ #". iIntros.

  assert ({[+ v +]} ⊎ {[-v-]} ≡ (∅ : smultiset loc)) as -> by smultiset_solver.

  pclean fg.

  iApply wpc_fconseq.
  { iApply (counter_free nroot 2 fi fg). }
  iFrame. iIntros.

  pclean v0.

  iApply wpc_tconseq.
  { iApply (interp_free' v0). }
  iFrame. iIntros "(?&_&#?)".

  iApply wpc_val. iSplitR; first (iPureIntro; lia). conclude_diamonds.
Qed.
End Counter_client.
