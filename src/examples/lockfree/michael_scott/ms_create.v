From iris Require Import gen_heap.
From iris.algebra Require Import auth gset gmap list excl excl_auth.

From irisfit.program_logic Require Import wpc_logatom.
From irisfit.examples.lockfree.michael_scott Require Import ms_common.

Section MS_create.
Context `{!interpGS0 Σ, queueG Σ}.

Local Lemma IsGuardedQueue_alloc γ l :
  ⊢ IsGuardedQueue γ l nil l nil.
Proof. eauto. Qed.

Local Lemma lt_inv_alloc l : ⊢ lt_inv [l] l.
Proof.
  iSplit.
  { iPureIntro. split. set_solver. apply NoDup_singleton. }
  simpl. eauto.
Qed.

Local Lemma tie_alloc γi l :
  ⊢ |==> ∃ γ, tie γi γ l ∗ l -r-> γ.
Proof.
  iMod (own_alloc (● ({[l]}:gsetUR loc))) as "[% ?]".
  { apply auth_auth_valid. easy. }
  iMod (extract_witness_gset with "[$]") as "(?&#?)".
  iModIntro. iExists _.
  iSplitL.
  { iExists _. iFrame.  iApply big_sepS_singleton.
    iApply reachable_refl.  }
  eauto.
Qed.

Local Lemma mapsfrom_split_2 l l1 l2 :
  l ↤ {[+l1;l2+]} -∗ l ↤{1/2} {[+l1+]} ∗ l ↤{1/2} {[+l2+]}.
Proof.
  iIntros.
  iApply (mapsfrom_split with "[$]"); try done. compute_done.
Qed.

Local Lemma cells_alloc γ :
  ghost_map_auth γ.(i) 1 (∅:gmap loc val) -∗
  ghost_map_auth γ.(j) 1 ∅ -∗
  cells γ.
Proof.
  iIntros. iExists ∅,∅. iFrame.
  by iApply big_sepM2_empty.
Qed.

Lemma create_spec N π :
  CODE (create [[]])
  TID π
  WITH ↑N
  PRE (♢4)
  POST (fun (l:loc) => queue N l ∗ queue_content l nil ∗ l ↤ ∅ ∗ l ⟸ {[π]}).
Proof.
  iIntros.
  wpc_call.
  wpc_let_empty.
  wpc_alloc.
  iIntros (s) "(Hs&?&Hps&_)".

  (* XXX add a proper spec for pair. *)
  wpc_call.
  wpc_let_noclean.
  wpc_alloc.
  iIntros (l) "(?&?&?&?)".

  iDestruct (mapsto.mapsto_ne with "[$][$]") as "%".

  wpc_let_noclean.
  wpc_apply wpc_store; eauto. simpl. compute_done.
  iIntros (v) "(?&?&_)". simpl. clear v.

  wpc_let_noclean.
  wpc_apply wpc_store. eauto. simpl. compute_done.
  iIntros (v) "(Hl&?&_)". simpl. clear v.

  pclean s with "Hps".
  rewrite left_id.

  (* Alloc names *)
  iMod (@ghost_map_alloc _ loc val) as "[%gi (Hi&_)]".
  iMod (@ghost_map_alloc _ loc (option loc)) as "[%gj (Hj&_)]".
  iMod (own_alloc (●E nil ⋅ ◯E nil)) as "[%gm (Hg1 & Hg2)]".
  { by apply auth_both_valid_2. }
  iMod (tie_alloc gj s) as "[%gs (Hs1&Hs2)]".
  iMod (tie_alloc gj s) as "[%gt (Ht1&Ht2)]".
  iMod (tie_alloc gj s) as "[%ga (Ha1&Ha2)]".
  iDestruct (mapsfrom_split_2 with "[$]") as "(Hm1&Hm2)".

  (* Set meta *)
  pose (γ := (mk_gq gm gi gj gs gt ga)).
  iMod (meta_set _ l γ queue_nm with "[$]") as "#?".
  { solve_ndisj. }
  simpl.

  iDestruct (cells_alloc γ with "[$][$]") as "Hi".
  iMod (cells_add_last γ with "[$]") as "(Hi&Hs&_)".

  (* Alloc inv *)
  iMod (inv_alloc N _ (queue_inv_inner γ l) with "[Hl Hs Hi Hg1 Hs1 Hs2 Ht1 Ht2 Ha1 Ha2 Hm1 Hm2 Hps]")%I as "#?".
  { iModIntro. iExists nil,s,s,s,nil. subst γ.
    iDestruct (IsGuardedQueue_alloc) as "?".
    iDestruct (lt_inv_alloc s) as "?".
    iFrame "#∗". iRight. iFrame. }

  iSmash.
Qed.

End MS_create.
