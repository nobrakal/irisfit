From iris Require Import gen_heap.
From iris.algebra Require Import auth gset gmap list excl.

From irisfit.program_logic Require Import wpc_logatom.
From irisfit.examples.lockfree.michael_scott Require Import ms_common.

Section MS_enqueue.
Context `{!interpGS0 Σ, queueG Σ}.

Local Lemma IsQueue_snoc v qp qz γ la x xs l zs lz :
  IsQueue γ la x xs l zs  -∗
  lz ↤{1/2} {[+la+]} ∗ lz ⟸ ∅ ∗ value γ lz v ∗ la ↪[ γ.(j) ]□ (Some lz) ∗ v ⟸?{qp} ∅ ∗ v ↤?{qz} {[+ lz +]} -∗
  IsQueue γ lz x (xs ++ [(v,(qp,qz))]) l (zs ++ [lz]).
Proof.
  iIntros "Hq (?&?&?&?&?&?)".
  iInduction xs as [|] "IH" forall (x l zs lz); destruct x as (?,(?,?)); simpl.
  { destruct zs; eauto. simpl.
    iDestruct "Hq" as "(%&?&?&?)". subst. by iFrame. }
  { destruct zs; eauto. iSmash. }
Qed.

Local Lemma IsGuardedQueue_snoc v γ la xs l zs lz qp qz :
  IsGuardedQueue γ la xs l zs  -∗
  lz ↤{1/2} {[+la+]} ∗ lz ⟸ ∅ ∗ value γ lz v ∗ la ↪[ γ.(j) ]□ (Some lz) ∗ v ⟸?{qp} ∅ ∗  v ↤?{qz} {[+ lz +]} -∗
  IsGuardedQueue γ lz (xs ++ [(v,(qp,qz))]) l (zs ++ [lz]).
Proof.
  iIntros "Hq (?&?&?&?&?&?)".
  destruct xs; simpl.
  { destruct zs; simpl; eauto.
    iDestruct "Hq" as "%". subst. by iFrame. }
  { destruct zs; simpl; eauto.
    iDestruct "Hq" as "(?&?&?&?)". iFrame.
    iApply (IsQueue_snoc with "[$][$]"). }
Qed.

Local Lemma IsQueue_confront lz γ la x xs ls zs vs2  :
  IsQueue γ la x xs ls zs ∗
  islast γ la ∗ lz ↦ vs2 ∗ cells γ -∗
  ⌜lz ∉ (la::ls::zs)⌝.
Proof.
  iIntros "(Hq&?&?&?)".
  iInduction (xs) as [|] "IH" forall (x ls zs); destruct x as (?,(?,?)); destruct zs; eauto.
  { iDestruct "Hq" as "(%&?)". subst.
    destruct_decide (decide (lz=ls)). 2:iPureIntro; set_solver. subst.
    iDestruct (cells_borrow with "[$][$]") as "(_&[% (?&_)])".
    iDestruct (mapsto.mapsto_ne with "[$][$]") as "%". congruence. }
  { iDestruct "Hq" as "(?&?&?&?&?)".
    iDestruct ("IH" with "[$][$][$][$]") as "%".
    iDestruct (cells_borrow _ ls with "[$][$]") as "(_&[% (?&_)])".
    iDestruct (mapsto.mapsto_ne with "[$][$]") as "%".
    iPureIntro. set_solver. }
Qed.

Local Lemma IsGuardedQueue_confront lz γ la xs ls zs vs2  :
  IsGuardedQueue γ la xs ls zs ∗
  islast γ la ∗ lz ↦ vs2 ∗ cells γ -∗
  ⌜lz ∉ (la::ls::zs)⌝.
Proof.
  iIntros "(Hq&?&?&?)".
  destruct xs,zs;eauto.
  { iDestruct "Hq" as "%M". subst.
    destruct_decide (decide (lz=ls)). 2:iPureIntro; set_solver.
    subst.
    iDestruct (cells_borrow with "[$][$]") as "(_&[% (?&_)])".
    iDestruct (mapsto.mapsto_ne with "[$][$]") as "%". congruence. }
  { iDestruct "Hq" as "(?&?&?&?)".
    iDestruct (IsQueue_confront  with "[$]") as "%".
    iDestruct (cells_borrow _ ls with "[$][$]") as "(_&[% (?&_)])".
    iDestruct (mapsto.mapsto_ne with "[$][$]") as "%".
    iPureIntro. set_solver. }
Qed.

Local Lemma load_tail_spec N l γ ql Sl π :
  queue_inv N γ l ∗
  l ⟸{ql} Sl ∗ inside π ∅ -∗
  wp ⊤ false π (#l.[^otail])%T (fun v => ∃ lt, ⌜v=val_loc lt⌝ ∗ lt -r-> γ.(a)  ∗ l ⟸{ql} Sl ∗ inside π {[lt]}).
Proof.
  iIntros "(?&?&?)".
  wp_apply (load_tail_spec' None).
  iIntros (?) "(?&[% (->&?&?&?&_)])".
  rewrite left_id_L. iExists _. iSmash.
Qed.

Local Lemma lt_inv_add zs lt lz :
  lz ∉ zs ->
  lt_inv zs lt -∗
  lz ↤{1 / 2} ∅ -∗
  lt_inv (zs ++ [lz]) lt.
Proof.
  iIntros (?) "((%&%)&?) ?".
  iSplitR.
  { iPureIntro. split.
    { set_solver. }
    apply NoDup_app. split; eauto.
    split. { intros. set_solver. }
    apply NoDup_singleton. }
  iApply big_sepL_app. by iFrame.
Qed.

Local Lemma cells_switch_last γ la :
  islast γ la ∗ cells γ -∗
  (∃v, la ↦ [v;val_unit] ∗ (∀ l', la ↦ [v;val_loc l'] ==∗ la ↪[γ.(j)]□ (Some l') ∗ cells γ)).
Proof.
  iIntros "(?&I)". iDestruct "I" as cells_pat.
  iDestruct (ghost_map_lookup with "[$][$]") as "%".

  iDestruct (big_sepM2_lookup_iff with "[$]") as "%Hl".
  assert (is_Some (σ !! la)) as (x2,E2).
  { apply Hl. eauto. }
  iDestruct (big_sepM2_insert_acc with "Hσρ") as "(H1&H2)". 1,2:done.
  iExists _. iFrame. iIntros.
  iMod (ghost_map_update with "[$][$]") as "(?&?)". iMod (ghost_map_elem_persist with "[$]") as "?".
  iFrame. iModIntro. iExists _,_. iFrame.
  iSpecialize ("H2" $! x2 (Some l') with "[$]"). rewrite (insert_id σ la) //.
Qed.

Local Lemma load_cell_spec N l γ π ce D lq Sq :
  queue_inv N γ l ∗  ce -r-> γ.(a) ∗
  l ⟸{lq} Sq ∗ inside π D -∗
  wp ⊤ false π (#ce.[^1]) (fun v:val => l ⟸{lq} Sq ∗ inside π (D ∪ locs v) ∗ (⌜v=val_unit⌝ ∨ (∃ lp, ⌜v=val_loc lp⌝ ∗ lp -r-> γ.(a) ∗ ce ↪[γ.(j)]□ (Some lp)))).
Proof.
  iIntros "(HI&?&?&HD)".
  iInv "HI" as qintro. solve_atomic.
  iMod (use_cell γ γ.(a) ce with "[$][$]") as "(?&?&#Hce)".
  iDestruct "Hce" as "[%|[% (Hp&Hpe)]]".
  { iDestruct "Hl" as qintrol.
    { not_dead l. }
    subst.
    iDestruct (cells_borrow with "[$][$]") as "(?&[%v (Hla&Hb)])".

    wp_apply wp_load.wp_load_no_loc.
    { simpl. reflexivity. }
    { compute_done. }
    { simpl. lia. }
    iIntros (?) "(->&_&?)". subst.
    iModIntro. iSplitR "HD".
    iSpecialize ("Hb" with "[$]").
    { conclude_inv ls lt la. }
    simpl. replace (D ∪ locs ()%V) with D by set_solver. iSmash. }
  { iDestruct (cells_borrow with "[$][$]") as "(_&[%v (Hce&Hback)])".
    wp_apply wp_load.wp_load_inside.
    { compute_done. }
    simpl. iIntros (?) "(->&_&?&D)".
    iSpecialize ("Hback" with "[$]").
    iSplitR "D".
    { conclude_inv ls lt la. }
    auto_locs. iSmash. }
Qed.

Lemma enqueue_spec N π l p q x :
  (is_loc x → q ≠ 0%Qz) ->
  ACODE (enqueue [[l,x]])%T
  TID π
  WITH ↑N
  SOUV {[l]}
  <<< (queue N l ∗ ♢2 ∗ x ⟸?{p} {[π]} ∗ x ↤?{q} ∅) | ∀∀ xs, queue_content l xs >>>
  <<< queue_content l (xs++[(x,(p,q))])
    | (fun (_:unit) => True) >>>.
Proof.
  iIntros (?) "([% #(Hmeta&HI)]&X&Hv1&Hv2)". iIntros (Φ) "AU".
  iLöb as "IH".

  wpc_call.
  wpc_let_noclean.
  wpc_alloc. iIntros (lz) "(Hl&Hlz1&Hlz2&_)". iClear "X".

  wpc_let_noclean.
  wpc_apply wpc_store. easy. simpl; lia.
  iIntros ([]) "(Hlz&Hmz&_)". simpl. rewrite left_id.

  iApply @wpc_enter. iIntros (k) "%Ek Hk D".
  apply dom_singleton_inv_L in Ek. destruct Ek as (p'&->).

  iApply wp_let_noclean. rewrite -{1}pbt_PBT.
  wp_apply load_tail_spec.
  iIntros (?) "[% (->&#Hlt&D)] _". simpl.

  iApply wp_let_noclean.
  wp_apply load_cell_spec.
  iIntros (next) "(Hk&D&Hnext) _". simpl.
  iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).
  iDestruct "Hnext" as "[ -> | [%lp (->&#Hlp1&#Hlp2)] ]".

  (* next is nil *)
  { iApply wp_mono. iApply wp_call_prim.wp_call_prim. reflexivity.
    iIntros (?) "(->&_)". simpl.
    iApply wp_if. iIntros "!> _".

    iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).

    iInv "HI" as qintro'. solve_atomic.
    iDestruct "Hl'" as qintrol'.
    { not_dead l. }

    iMod (use_cell γ (a γ) lt with "[$][$]") as "(Hna'&Hcells'&#Hclt)".

    (* Is lt still the last node? *)
    iDestruct "Hclt" as "[ -> | [% (#?&#Hlp)]]".
    (* Yes, CAS succeeds, and we terminate.  *)
    { iDestruct (IsGuardedQueue_confront lz with "[$]") as "%".
      iDestruct (cells_switch_last with "[$]") as "[%v0 (Hla'&Hcells')]".

      iApply wp_tconseq. iApply (tupd_vclean_debt x). iFrame.
      iIntros "(Hv1&D)". rewrite difference_diag_L.
      iApply wp_tconseq. iApply (tupd_vclean_debt lz). iFrame.
      iIntros "(Hlz2&D)". rewrite difference_diag_L.

      wp_apply wp_cas.wp_cas_suc.
      1-3:naive_solver by vm_compute.
      iIntros (?) "(->&_&?&_&?)".
      iMod ("Hcells'" with "[$]") as "(?&Hcells')". simpl.

      (* We commit. *)
      iMod "AU" as (zs) "[H [_ HClose]]".
      iDestruct (queue_content_open with "[$][$]") as "?".
      iDestruct (auth_excl_agree (γ.(m)) with "[$][$]") as "%". subst zs.
      iMod (auth_excl_update (γ.(m)) (xs'++[(x,(p,q))]) with "[$] [$]") as "(Hmodel'&HF)".
      iAssert (queue_content l (xs'++[(x,(p,q))])) with "[HF]" as "?".
      { iSmash. }
      iMod ("HClose" with "[$]") as "HPOST".

      iAssert (la' ~γ.(j)~> lz) as "#Haz'".
      { iExists 1. iSmash. }

      iMod (cells_add_last _ lz with "[$]") as "(Hcells'&Hlz&?)".

      iDestruct (mapsfrom_split_half_empty lz with "[$]") as "(?&?)".
      iDestruct (IsGuardedQueue_snoc x _ la' _ _ _ lz p q with "[$][$]") as "Hqueue'".

      iDestruct (lt_inv_add with "[$][$]") as "Hltinv'".
      { set_solver. }
      iMod (reach_set_advance (j γ) (a γ) la' lz  with "[$][$]") as "(Hna'&?)".

      iModIntro. iSplitL "Hl' Hmodel' Hnt' Hns' Hcells' Hps' Hss' Hpl' Hlz Hqueue' Hltinv' Hna'".
      { iModIntro. iExists (xs' ++ [(x, (p, q))]),ls',lt',lz,(zs' ++ [lz]). iFrame "#∗". iRight. iFrame. }

      iApply wp_if. iIntros "!> _".
      iApply wp_let_noclean.

      wp_apply advance_tail_pointer. iIntros (?) "[% (->&?)] _".
      simpl.

      iApply wp_conseq. iApply inside_clean. iFrame. iIntros "D".
      replace (_ ∩ locs tm_exit) with (∅:gset loc) by set_solver.
      wp_apply wp_exit.  iIntros. rewrite pbt_PBT. iSmash. }
    (* We are going to fail. *)
    { iDestruct (cells_borrow _ lt with "[$][$]") as "(_&[% (Plt&Hcells')])".
      wp_apply wp_cas.wp_cas_fail.
      1-3:naive_solver by vm_compute.
      iIntros (?) "(->&_&?)". iSpecialize ("Hcells'" with "[$]"). iModIntro.
      iSplitL "Hl' Hmodel' Hnt' Hns' Hss' Hcells' Hps' Hpl' Ht' Hqueue' Hltinv' Hna'".
      { conclude_inv ls' lt' la'. }

      iApply wp_if. iIntros "!> _".

      iApply wp_tconseq. iApply (debt_vtransfer l). iFrame. rewrite !idemp_L. iIntros "(?&?)".
      iApply wp_tconseq. iApply (debt_vtransfer x). iFrame. rewrite !idemp_L. iIntros "(?&?)".

      iApply @wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L -pbt_PBT. iFrame.

      iApply wpc_conseq. iApply (vpbt_transfer x lz). 3:iFrame.
      1,2:set_solver. rewrite difference_diag_L.
      iIntros "(?&?)".

      iApply wpc_tconseq. iApply (interp_free' lz). iFrame. simpl. iIntros "(?&_&?)".
      iApply wpc_tconseq. iApply (vmapsfrom_cleanup x lz). iFrame. iIntros.
      assert ({[+ lz +]} ⊎ smultiset.singletonNS lz ≡ ∅) as -> by smultiset.smultiset_solver.

      iApply ("IH" with "[$][$][$] AU"). } }
  { iApply wp_mono. iApply wp_call_prim.wp_call_prim. done.
    iIntros (?) "(->&_)". simpl.

    iApply wp_if. iIntros "!> _".
    iApply wp_let_noclean.
    wp_apply advance_tail_pointer.
    iSplitR.
    { iExists 1. simpl. eauto. }
    iIntros (?) "[% (->&?)] _".

    iApply wp_tconseq. iApply (debt_vtransfer l). iFrame. rewrite !idemp_L. iIntros "(?&?)".
    iApply wp_tconseq. iApply (debt_vtransfer x). iFrame. rewrite !idemp_L. iIntros "(?&?)".

    iApply @wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L -pbt_PBT. iFrame.

    iApply wpc_conseq. iApply (vpbt_transfer x lz). 3:iFrame.
    1,2:set_solver. rewrite difference_diag_L.
    iIntros "(?&?)".

    iApply wpc_tconseq. iApply (interp_free' lz). iFrame. simpl. iIntros "(?&_&?)".
    iApply wpc_tconseq. iApply (vmapsfrom_cleanup x lz). iFrame. iIntros.
    assert ({[+ lz +]} ⊎ smultiset.singletonNS lz ≡ ∅) as -> by smultiset.smultiset_solver.

    iApply ("IH" with "[$][$][$] AU"). }
Qed.

End MS_enqueue.
