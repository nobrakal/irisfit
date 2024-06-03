From iris Require Import gen_heap.
From iris.algebra Require Import auth gset gmap list excl.

From irisfit.program_logic Require Import wpc_logatom.
From irisfit.examples.lockfree.michael_scott Require Import ms_common.

Section MS_dequeue.
Context `{!interpGS0 Σ, queueG Σ}.

Local Lemma load_sentinel_spec N γ l π ql Sl :
  queue_inv N γ l ∗ l ⟸{ql} Sl ∗ inside π ∅ -∗
  wp ⊤ false π (#l.[^osent]) (fun v => ∃ ls, ⌜v=val_loc ls⌝ ∗ ls -r-> γ.(s) ∗ ls-r->γ.(t) ∗ ls-r->γ.(a) ∗ l ⟸{ql} Sl ∗ inside π {[ls]}).
Proof.
  iIntros "(HI&?&?)".
  iInv "HI" as qintro. solve_atomic.
  iDestruct "Hl" as qintrol. { not_dead l. }
  iDestruct (IsGuardedQueue_acc ls with "[][$][$]") as "#(_&Hls')".
  { iApply reachable_refl. }
  iDestruct (lookup_reach_set (j γ) _ (t γ) with "[$][$]") as "#?".
  iDestruct (lookup_reach_set (j γ) _ (a γ) with "[$][$]") as "#?".
  iMod (insert_reach_set (j γ) (a γ) ls with "[$][]" ) as "(?&#?)".
  { iApply (reachable_trans _ _ lt with "[$][$]"). }
  iMod (insert_reach_set (j γ) (s γ) ls with "[$][]" ) as "(?&#?)".
  { iApply reachable_refl. }

  wp_apply wp_load.wp_load_inside.
  { compute_done. }
  simpl. iIntros (?) "(->&_&?&D) !>".
  rewrite left_id_L.

  auto_locs. iSplitR "D".
  { conclude_inv ls lt la. }
  { iSmash. }
Qed.

Local Lemma reach_is_skel l l' γ la xs zs  x :
  l ~γ.(j)~> l' -∗
  islast γ la ∗ IsQueue γ la x xs l zs -∗
  ⌜l' ∈ (l::zs)⌝.
Proof.
  rewrite reachable_eq.
  iIntros "[%n Hn] (?&Hq)".
  iInduction n as [|] "IH" forall (x xs l zs).
  { iDestruct "Hn" as "%".  subst. iPureIntro. set_solver. }
  iDestruct "Hn" as "[% (?&Hn)]".
  destruct xs,zs; eauto.
  { iDestruct "Hq" as "(%&?)". subst.
    iDestruct (ghost_map_elem_agree with "[$][$]") as "%". congruence. }
  iDestruct "Hq" as "(?&?&?&?&?)".
  iDestruct (ghost_map_elem_agree with "[$][$]") as "%E". inversion E. subst.
  iDestruct ("IH" with "[$][$][$]") as "%".
  iPureIntro. set_solver.
Qed.

Local Lemma no_circ_in_queue l l' γ la xs zs :
  l ∉ zs ->
  l ~γ.(j)~> l' ∗ l' ~γ.(j)~> l -∗
  islast γ la ∗ IsGuardedQueue γ la xs l zs -∗
  ⌜l = l'⌝.
Proof.
  iIntros (?) "(Hn&Hm) (?&Hq)".
  destruct xs as [|x xs], zs; eauto.
  { iDestruct "Hq" as "%". subst. rewrite reachable_eq.
    iDestruct "Hn" as "[%n Hn]".
    destruct n; eauto.
    iDestruct "Hn" as "[% (?&_)]".
    iDestruct (ghost_map_elem_agree with "[$][$]") as "%". congruence. }
  { iDestruct "Hq" as "(?&?&?&?)". rewrite reachable_eq.
    iDestruct "Hn" as "[%n Hn]".
    destruct n; eauto.
    iDestruct "Hn" as "[% (?&Hn)]".
    iDestruct (ghost_map_elem_agree with "[$][$]") as "%E". inversion E. subst.
    iAssert (lp ~γ.(j)~> l') with "[Hn]" as "Hn".
    { iExists _. iFrame. }
    iDestruct (reachable_trans with "[$][$]") as "?".
    iDestruct (reach_is_skel with "[$][$]") as "%".
    exfalso. set_solver. }
Qed.

Local Lemma reach_from_last l la γ:
  la ~γ.(j)~> l -∗
  islast γ la -∗ ⌜l=la⌝.
Proof.
  rewrite reachable_eq.
  iIntros "[%n Hn] ?".
  destruct n.
  { iDestruct "Hn" as "%". eauto. }
  { iExFalso.
    iDestruct "Hn" as "[%(?&?)]".
    iDestruct (ghost_map_elem_agree with "[$][$]") as "%". congruence. }
Qed.

Local Lemma IsGuardedQueue_nil γ (la:loc) xs zs :
  IsGuardedQueue γ la xs la zs ∗ islast γ la -∗ ⌜xs=nil⌝.
Proof.
  iIntros "(Hq&?)".
  destruct xs; eauto.
  iExFalso. destruct zs; eauto. iDestruct "Hq" as "(?&?)".
  iDestruct (ghost_map_elem_agree with "[$][$]") as "%". congruence.
Qed.

Local Lemma IsGuardedQueue_uncons γ  la  x qp qz xs l zs :
  IsGuardedQueue γ la ((x,(qp,qz))::xs) l zs -∗
  ∃ z zs', ⌜zs=z::zs'⌝ ∗ value γ z x ∗ x ⟸?{qp} ∅ ∗ x ↤?{qz} {[+ z +]} ∗ z ↤{1 / 2} {[+ l +]} ∗ z ⟸ ∅ ∗ l↪[γ.(j)]□ (Some z) ∗ IsGuardedQueue γ la xs z zs'.
Proof.
  iIntros "Hq".
  destruct zs; eauto.
  iDestruct "Hq" as "(?&?&?&Hq)".
  destruct xs,zs; eauto; simpl.
  { iDestruct "Hq" as "(%&?&?&?)". subst. simpl.
    iFrame. iExists _,nil. by iFrame. }
  { iDestruct "Hq" as "(?&(?&?&?)&?&?&?)".
    iFrame. iExists l0,_. iFrame. iSplitR; eauto. simpl.
    iFrame. }
Qed.

Local Lemma lt_inv_uncons l ls lt :
  l ≠ lt ->
  lt_inv (l::ls) lt -∗
  l ↤{1/2} ∅ ∗ lt_inv ls lt.
Proof.
  iIntros (?) "((%&%Hnd)&Hlt)".
  inversion Hnd. subst.
  rewrite big_sepL_cons.
  iDestruct "Hlt" as "(Hl&?)".
  iFrame.
  iDestruct "Hl" as "[%|?]".
  { congruence. }
  iFrame. iPureIntro. set_solver.
Qed.

Local Lemma value_use γ l x :
  value γ l x ∗ cells γ -∗
  (∃ v, l ↦ [x;v] ∗ (∀x', l ↦ [x';v] ==∗ value γ l x' ∗ cells γ)).
Proof.
  iIntros "(Hv&I)". iDestruct "I" as cells_pat.
  iDestruct (ghost_map_lookup with "Hσ Hv") as "%Hv".

  iDestruct (big_sepM2_lookup_iff with "[$]") as "%Hl".
  assert (is_Some (ρ !! l)) as (x2,E2).
  { apply Hl. eauto. }
  iDestruct (big_sepM2_insert_acc with "Hσρ") as "(H1&H2)". 1,2:done.

  iExists _. iFrame. iIntros.
  iMod (ghost_map_update with "Hσ Hv") as "(Hσ&Hv)". iModIntro. iFrame.
  iDestruct ("H2" with "[$]") as "?".
  iExists _,_. iFrame. rewrite insert_id //.
Qed.

Local Lemma wp_load_value N γ (l l':loc) p b ti x ql Sl:
  queue_inv N γ l ∗
  value γ l' x ∗ x ⟸?{p} ∅ ∗ l ⟸?{ql} Sl -∗
  wp ⊤ b ti (l'.[0])%T (fun (y:val) => ⌜x=y⌝ ∗ value γ l' x ∗ x ⟸?{p} {[ti]} ∗ l ⟸?{ql} Sl).
Proof.
  iIntros "(HI&?&?&?)".
  iInv "HI" as qintro. solve_atomic.
  iDestruct "Hl" as qintrol. not_dead l.
  iDestruct (value_use with "[$]") as "[% (?&Hb)]".
  wp_apply wp_load.wp_load.
  { reflexivity. }
  { compute_done. }
  simpl. iIntros (?) "(->&_&?&Hpbt)". subst.
  iMod ("Hb" with "[$]") as "(Hv&?)".
  iModIntro.
  iSplitR "Hpbt Hv".
  { iModIntro. iExists xs,ls,lt,_,_. iFrame. iFrame "#". iRight. iFrame. }
  { iSplitR; first easy. iFrame "#∗". }
Qed.

Local Lemma wp_store_value N l γ π lp x b :
  queue_inv N γ l ∗
  value γ lp x  -∗
  wp ⊤ b π (#lp.[^0] <- ())
  (fun v => ⌜v=val_unit⌝ ∗ x ↤?{0} {[- lp -]}).
Proof.
  iIntros "(HI&?)".
  iInv "HI" as qintro. solve_atomic.
  iDestruct (value_use with "[$]") as "[% (?&Hb)]".
  wp_apply wp_store.wp_store. easy. compute_done.
  iIntros (?) "(->&_&?&_&?)". iFrame.
  iMod ("Hb" with "[$]") as "(_&?)". iModIntro.
  iSplitL; last done.
  iModIntro. iExists xs,ls,lt,la,zs. iFrame "#∗".
  Unshelve. all:exact inhabitant.
Qed.

Definition is_loc_head (xs:model) :=
  match xs with
  | (v,_)::_ => is_loc v
  | _ => true end.

Lemma dequeue_spec N π l:
  ACODE (dequeue [[l]])%T
  TID π
  WITH ↑N
  SOUV {[l]}
  <<< queue N l | ∀∀ xs, queue_content l xs >>>
  <<< ∃∃ x p q xs', ⌜xs=(x,(p,q))::xs'⌝ ∗ queue_content l xs' ∗ ♢2
    | (fun (v:val) => ⌜v=x⌝ ∗ x ⟸?{p} {[π]} ∗ x ↤?{q} ∅) >>>.
Proof.
  iIntros "[% #(Hmeta&HI)]". iIntros (Φ) "AU".
  iLöb as "IH".

  wpc_call.
  iApply wpc_enter. iIntros (k) "%Ek Hk D".
  apply dom_singleton_inv_L in Ek. destruct Ek as (p'&->).

  iApply wp_let_noclean. rewrite -{1}pbt_PBT.
  wp_apply load_sentinel_spec.
  iIntros (?) "[%ls (->&#?&#?&#?&D)] _". simpl.

  iApply wp_let_noclean.
  wp_apply (load_tail_spec' (Some ls)).
  iIntros (?) "(Hk&[% (->&D&#?&#?&#?)]) _". simpl.

  iApply wp_let_noclean.

  (* We must open the invariant now, as the linearization point depends on the read. *)
  iInv "HI" as qintro'. solve_atomic.
  iDestruct "Hl'" as qintrol'.
  { not_dead l. }
  iMod (use_cell γ _ ls with "[$][$]") as "(Hna'&Hcells'&#Hce)".

  iDestruct "Hce" as "[%lp|[%(#?&#Hmls)]]"; subst.
  (* The queue is empty! *)
  { iDestruct (lookup_reach_set (j γ) la' (s γ) with "[$][$]") as "#?".
    iDestruct (lookup_reach_set (j γ) la' (t γ) with "[$][$]") as "#?".
    iDestruct (lookup_reach_set (j γ) lt (a γ) with "[$][$]") as "#?".

    iDestruct (no_circ_in_queue la' lt _ la' nil nil with "[$][Ht' Hcells']") as "%".
    { set_solver. }
    { iFrame. eauto. }

    iDestruct (reach_from_last ls' with "[$][$]") as "%". subst.
    iDestruct (reach_from_last lt' with "[$][$]") as "%". subst.

    iDestruct (IsGuardedQueue_nil with "[$]") as "%". subst. simpl.

    iMod "AU" as (xs) "[H [Hclose _]]". solve_atomic.
    iDestruct (queue_content_open with "[$][$]") as "HF".
    iDestruct (auth_excl_agree with "[$][$]") as "%". subst xs.
    iAssert (queue_content l nil) with "[HF]" as "?".
    { iSmash. }

    iDestruct (cells_borrow with "[$][$]") as "(Ht'&[% (?&Hcells')])".
    wp_apply wp_load.wp_load_no_loc. simpl. reflexivity. compute_done. compute_done.
    iIntros (?) "(->&_&?)". iSpecialize ("Hcells'" with "[$]").

    destruct zs'; last done.
    iMod ("Hclose" with "[$]") as "AU".
    do 2 iModIntro.
    iSplitL "Hl' Hns' Hmodel' Hnt' Hcells' Hss' Hps' Hpl' Hqueue' Hltinv' Ht' Hna'".
    { iModIntro. iExists nil,lt,lt,lt,nil. iFrame "#∗". iRight. iFrame. }
    iIntros "_".

    iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).
    iApply wp_mono. iApply wp_call_prim.wp_call_prim. done.
    iIntros (?) "(->&_)".

    iApply wp_if. iIntros "!> _". rewrite bool_decide_eq_true_2 //.
    iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).
    iApply wp_mono. iApply wp_call_prim.wp_call_prim. done.
    iIntros (?) "(->&_)".

    iApply wp_if. iIntros "!> _". rewrite bool_decide_eq_true_2 //.

    iApply wp_tconseq. iApply (debt_vtransfer l). iFrame. rewrite !idemp_L.
    iIntros "(?&?)".
    iApply @wpc_exit; last iFrame. { set_solver. }
    rewrite dom_singleton_L -pbt_PBT. iFrame. iApply ("IH" with "AU"). }

  (* The queue is not empty, proceed *)
  iDestruct (cells_borrow _ ls with "[$][$]") as "(_&[%v (Hls&Hcells')])".
  wp_apply wp_load.wp_load_inside.
  { compute_done. }
  simpl. iIntros (?) "(->&_&?&D)".
  iSpecialize ("Hcells'" with "[$]").
  iModIntro.
  iSplitL "Hl' Hns' Hmodel' Hnt' Hcells' Hss' Hps' Hpl' Hqueue' Hltinv' Ht' Hna'".
  { iModIntro. conclude_inv ls' lt' la'. }
  iIntros "_".

  iClear "Hlta'".  clear lt' v.
  iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).
  destruct_decide (decide (ls=lt)); subst.
  { iApply wp_mono. iApply wp_call_prim.wp_call_prim. done.
    iIntros (?) "(->&_)". simpl. rewrite bool_decide_eq_true_2 //.
    iApply wp_if. iIntros "!> _".

    iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).
    iApply wp_mono. iApply wp_call_prim.wp_call_prim. done.
    iIntros (?) "(->&_)". simpl.

    iApply wp_if. iIntros "!> _".
    iApply wp_let_noclean.

    wp_apply advance_tail_pointer. iSplitR.
    { iExists 1. simpl. iExists _. iFrame "#". eauto. }
    iIntros (?) "[% (->&?)] _". simpl.

    iApply wp_tconseq. iApply (debt_vtransfer l). iFrame. rewrite !idemp_L.
    iIntros "(?&?)".
    iApply @wpc_exit; last iFrame. { set_solver. }
    rewrite dom_singleton_L -pbt_PBT. iFrame. iApply ("IH" with "AU"). }

  iApply wp_mono. iApply wp_call_prim.wp_call_prim. done.
  iIntros (?) "(->&_)". simpl.
  rewrite bool_decide_eq_false_2 //. 2:naive_solver.

  iApply wp_if. iIntros "!> _".
  iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).

  iInv "HI" as qintro_. solve_atomic.
  iDestruct "Hl_" as qintrol. { not_dead l. }
  destruct_decide (decide (ls_=ls)); subst.
  (* Success! We reached a linearization point ! *)
  { iMod "AU" as (xs) "[H [_ Hclose]]". solve_atomic.

    iDestruct (queue_content_open with "[$] H") as "?".
    iDestruct (auth_excl_agree (γ.(m)) with "[$][$]") as "%Eq". subst xs_.

    (* The model cannot be empty! *)
    destruct xs as [|(v,(qp,qz)) xs].
    { iExFalso. destruct zs_; last eauto.
      iDestruct "Hqueue_" as "%". subst.
      iDestruct (ghost_map_elem_agree ls with "[$][$]") as "%". congruence. }

    iMod (auth_excl_update (γ.(m)) xs with "[$] [$]") as "(Hmodel_&HF)".
    iAssert (queue_content l xs) with "[HF]" as "HF".
    { iSmash. }

    iAssert (⌜ls≠lt_⌝)%I as "%".
    { iIntros (<-).
      iDestruct (lookup_reach_set _ lt (t γ) with "[$][$]") as "#?".
      subst. iExFalso.
      iDestruct "Hltinv_" as "((_&%Hzs_)&_)".
      iDestruct (no_circ_in_queue ls lt _ la_ with "[$][$]") as "%".
      { inversion Hzs_. subst.  eauto. }
      congruence. }

    iDestruct (IsGuardedQueue_uncons with "[$]") as "[%lp' [%zs_0 (%&?&?&?&?&Hlp1&X&Hqueue_)]]". subst zs_.
    iDestruct (ghost_map_elem_agree with "[$][$]") as "%Eq". inversion Eq. subst lp'.
    iClear "X".

    iDestruct (mapsfrom_split lp _ _ (1/4)%Qz (1/4)%Qz {[+ls+]} ∅ with "[$]") as "(?&?)".
    1,2:done.
    { compute_done. }
    { rewrite right_id //. }

    (* get the size of ls *)
    iDestruct (cells_borrow _ ls with "[$][$]") as "(_&[%v0 (Hv&Hcells_)])".
    iDestruct (mapsto_extract_size with "Hv") as "#?". simpl.
    iSpecialize ("Hcells_" with "Hv"). clear v0.

    iApply wp_postpone.
    wp_apply wp_cas.wp_cas_suc.
    1-3: naive_solver by vm_compute.
    iIntros (?) "(->&_&Hl_&?&?)". simpl.

    iDestruct (lt_inv_uncons with "[$]") as "(?&Hltinv_)".
    { done. }

    iMod (reach_set_advance _ _ ls lp with "[$][]") as "(Hns_&?)".
    { iExists 1. simpl. iExists _. iFrame "#". eauto. }

    do 2 iDestruct (mapsfrom_join ls with "[$][$]") as "?".
    rewrite right_id_L left_id Qz_div_2.
    assert (smultiset.singletonNS l ⊎ {[+ l +]} ≡ ∅) as -> by smultiset.smultiset_solver.

    iApply wp_tconseq. iApply (interp_free'' ls). iFrame "#∗". iIntros "(cred&#?)".

    iDestruct (mapsfrom_join lp with "[$][$]") as "Hlp2".
    iApply wp_tconseq. iApply (mapsfrom_cleanup lp ls). iFrame "#∗". iIntros "Hlp2".
    assert (({[+ l; ls +]} ⊎ smultiset.singletonNS ls) ≡ {[+l+]}) as -> by smultiset.smultiset_solver.
    replace (1 / 4 + 1 / 4)%Qz with (1/2)%Qz by compute_done.

    iAssert (lp ~γ.(j)~> lt_) as "#Hlplt_".
    { iDestruct (lookup_reach_set _ ls (t γ) with "[$][$]") as "#Hls". rewrite !reachable_eq.
      iDestruct "Hls" as "[%i Hi]".
      destruct i as [|i].
      { iDestruct "Hi" as "%". subst. congruence. }
      iDestruct "Hi" as "[% (Hls1&?)]".
      iDestruct (ghost_map_elem_agree ls with "Hls1 Hmls") as "%E". inversion E. subst.
      iExists i. iFrame "#". }
    iMod (insert_reach_set _ _ lp lt_ with "[$][$]") as "(Hnt_&X)".

    iApply wp_val.
    iMod ("Hclose" with "[HF cred]") as "HPOST". by iFrame.
    do 2 iModIntro.
    iSplitL "Hl_ Ht Hns_ Hmodel_ Hnt_ Hcells_ Hpl Hqueue_ Hltinv_ Hna_ Hlp1 Hlp2 X".
    { iModIntro. iExists xs, lp,lt_,la_,zs_0. iFrame "∗#".
      iRight. iFrame. }

    iApply wp_if. iIntros "!> _".
    iApply wp_let_noclean.
    iClear "Hlta_ Hls' Hlplt_". clear dependent lt_ la_ ls' la' zs_0 xs' zs'.

    wp_apply (wp_load_value N γ l lp).
    iIntros (?) "(<-&?&?&?) _". simpl.

    iApply wp_let_noclean.
    wp_apply wp_store_value.
    iIntros (?) "(->&?) _".

    iDestruct (vmapsfrom_join with "[$]") as "?". rewrite left_id.
    assert (({[-lp-]} ⊎ {[+ lp +]}) ≡ ∅) as -> by smultiset_solver. simpl.

    iApply wp_tconseq. iApply (debt_vtransfer v). iFrame. rewrite idemp_L pbt_PBT.
    iIntros "(?&?)".
    iApply @wpc_exit; last iFrame.
    { set_solver. }
    iSmash. }
  { wp_apply wp_cas.wp_cas_fail.
    1-3:naive_solver by vm_compute.
    iIntros (?) "(->&_&Hl_) !>".

    iSplitL "Hl_ Hns_ Hmodel_ Hnt_ Hss Hps Hpl Hqueue_ Hltinv_ Ht Hna_".
    { iModIntro. conclude_inv ls_ lt_ la_. }

    iApply wp_if. iIntros "!> _".

    iApply wp_tconseq. iApply (debt_vtransfer l). iFrame. rewrite idemp_L.
    iIntros "(?&?)".
    iApply @wpc_exit; last iFrame. { set_solver. }
    rewrite dom_singleton_L -pbt_PBT. iFrame. iApply ("IH" with "AU"). }
Qed.

End MS_dequeue.
