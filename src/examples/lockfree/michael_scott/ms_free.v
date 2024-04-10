From iris Require Import gen_heap.
From iris.algebra Require Import auth gset gmap list excl.

From irisfit.lib Require Import qz.
From irisfit.program_logic Require Import wpc_logatom.
From irisfit.examples.lockfree.michael_scott Require Import ms_common.

Section MS_free.
Context `{!interpGS0 Σ, queueG Σ}.

Lemma free_lt_inv zs lt :
  lt_inv zs lt -∗
  lt ↤{1/2} ∅ -∗
  [∗ list] l ∈ zs, l ↤{1/2} ∅.
Proof.
  iIntros "((%Hlt&%Hdup)&Hs) ?".
  apply elem_of_list_lookup_1 in Hlt. destruct Hlt as [i Hi].
  rewrite (big_sepL_delete _ _ i); last eauto.
  iApply (big_sepL_delete _ _ i); eauto.
  iFrame.
  iDestruct "Hs" as "(_&?)".
  iApply (big_sepL_impl with "[$]").
  iModIntro. iIntros (j l Hj) "H".
  case_decide; eauto.
  iDestruct "H" as "[%|?]"; iFrame.
  exfalso. subst. rewrite NoDup_alt in Hdup.
  eauto.
Qed.

Lemma free_IsQueue γ la x xs ls zs :
  islast γ la -∗
  ([∗ list] l ∈ zs, l ↤{1/2} ∅) -∗
  ls ↤ ∅ -∗ ls ⟸ ∅ -∗
  IsQueue γ la x xs ls zs -∗
  cells γ =[#]=∗
  cells γ ∗ ♢(2 + 2*length xs) ∗ †la ∗ handles (x::xs).
Proof.
  iIntros "? Ha ? ? Hq ?"; iIntros.
  iInduction xs as [|y ys] "IH" forall (x ls zs);  destruct zs as [|z zs]; eauto; destruct x as (?,(?,?)).
  { iDestruct "Hq" as "(%&?&?&?)". subst.
    iDestruct (cells_borrow with "[$][$]") as "(?&[% (H1&H2)])".
    iMod (interp_free' ls with "[$][$]") as "(?&?&?&#?)". simpl.
    iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".
    rewrite smultiset.disj_union_singleton_opposite.
    iSpecialize ("H2" with "[$]"). iFrame "#∗". rewrite big_sepL_nil.
    iSplitL; last done. conclude_diamonds. }
  { iDestruct "Hq" as "(?&(?&?&?)&?&?&?)".
    iDestruct (cells_borrow with "[$][$]") as "(?&[% (H1&H2)])".
    iMod (interp_free' ls with "[$][$]") as "(?&?&?&#?)". simpl.
    iMod (mapsfrom_cleanup with "[$][$]") as "(?&?)".
    rewrite smultiset.disj_union_singleton_opposite.
    iSpecialize ("H2" with "[$]").
    iDestruct "Ha" as "(?&?)".
    iDestruct (mapsfrom_join with "[$][$]") as "?". rewrite Qz_div_2 left_id.

    iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".
    rewrite smultiset.disj_union_singleton_opposite.
    iMod ("IH" with "[$][$][$][$][$][$][$]") as "(?&?&?&?&?)".
    iFrame "∗#". conclude_diamonds. }
Qed.

Lemma free_IsGuardedQueue γ la xs ls zs :
  islast γ la -∗
  ([∗ list] l ∈ zs, l ↤{1/2} ∅) -∗
  ls ↤ ∅ -∗ ls ⟸ ∅ -∗
  IsGuardedQueue γ la xs ls zs -∗
  cells γ =[#]=∗
  cells γ ∗ ♢(2 + 2*length xs) ∗ †la ∗ handles xs.
Proof.
  iIntros "? Ha ? ? Hq ?"; iIntros.
  destruct xs,zs; eauto.
  { iDestruct "Hq" as "%". subst.
    iDestruct (cells_borrow with "[$][$]") as "(?&[% (H1&H2)])".
    iMod (interp_free' ls with "[$][$]") as "(?&?&?&#?)". simpl.
    iSpecialize ("H2" with "[$]"). iFrame "#∗". rewrite /handles big_sepL_nil.
    iSplitL; last done.
    conclude_diamonds. }
  iDestruct "Hq" as "(?&?&?&?)". simpl.

  iDestruct (cells_borrow with "[$][$]") as "(?&[% (H1&H2)])".
  iMod (interp_free' ls with "[$][$]") as "(?&?&?&#?)". simpl.
  iSpecialize ("H2" with "[$]").

  iDestruct "Ha" as "(?&?)".
  iDestruct (mapsfrom_join with "[$][$]") as "?".
  rewrite Qz_div_2 right_id.
  iMod (mapsfrom_cleanup with "[$][$]") as "(?&?)".
  rewrite smultiset.disj_union_singleton_opposite.
  iMod (free_IsQueue with "[$][$][$][$][$][$][$]") as "(?&?&?&?&?)".
  iFrame "∗#". conclude_diamonds.
Qed.

Lemma queue_free N l xs X1 X2 X3 :
  queue N l ∗ l ↤ ∅ ∗ l ⟸ ∅ ∗ queue_content l xs =[↑N|X1|X2|X3]=∗
  ♢(4 + 2*length xs) ∗ handles xs.
Proof.
  iIntros "([% (Hm1&HI)]&?&?&[%γ'(Hm2&?)])". iIntros.
  iDestruct (meta_agree with "Hm2 Hm1") as "->".
  rename xs into L.
  iInv "HI" as qintro.
  iDestruct "Hl" as qintrol.
  { not_dead l. }

  iMod (interp_free' l with "[$][$]") as "(?&?&_&#?)".
  iMod (mapsfrom_cleanup lt l with "[$][$]") as "(?&?)".
  iMod (mapsfrom_cleanup ls l with "[$][$]") as "(?&?)".
  assert ({[+ l +]} ⊎ smultiset.singletonNS l ≡ ∅) as -> by smultiset.smultiset_solver.

  iDestruct (free_lt_inv with "[$][$]") as "X". rewrite big_sepL_cons.
  iDestruct "X" as "(?&?)".
  iDestruct (mapsfrom_join with "[$][$]") as "?". rewrite Qz_div_2 left_id.

  iMod (free_IsGuardedQueue with "[$][$][$][$][$][$][$]") as "(?&?&?&?&Hh)".
  iDestruct (diamonds_join with "[$]") as "Hd".
  iDestruct (auth_excl_agree (γ.(m)) with "[$][$]") as "%". subst xs.
  iMod (auth_excl_update _ nil with "[$] [$]") as "(Hb3&_)".

  iDestruct (lookup_reach_set with "Hls [$]") as "#?".
  iDestruct (lookup_reach_set with "Hlta [$]") as "#?".
  iMod (reach_set_advance _ (s γ) _ la with "[$][]") as "(?&?)".
  { iApply (reachable_trans _ _ lt with "[$][$]"). }
  iMod (reach_set_advance _ (t γ) _ la with "[$][$]") as "(?&?)".
  iMod (insert_reach_set _ (a γ) la with "[$][]") as "(?&?)".
  { iApply reachable_refl. }

  iModIntro. iFrame.
  iSplitR "Hd".
  { iModIntro. iExists nil,la,la,la,nil. iFrame "#∗".
    iSplitR. done. unfold lt_inv.
    iSplitR. { iPureIntro.  split. set_solver. apply NoDup_singleton. }
    iApply big_sepL_cons. iSplitR; first eauto. by iApply big_sepL_nil. }

  iModIntro. conclude_diamonds.
Qed.

End MS_free.
