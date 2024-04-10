From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import gen_heap.
From iris.algebra Require Import gmap auth gset excl_auth.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap gmultiset.

Section auth_excl.
Context `{OfeDiscrete  A}.
Context `{inG Σ (excl_authUR A)}.

Lemma auth_excl_agree `{!LeibnizEquiv A} γ xs ys :
  own γ (●E xs) -∗ own γ (◯E ys) -∗ ⌜xs = ys⌝.
Proof.
  iIntros "Hγ● Hγ◯".
  iDestruct (own_valid_2 with "Hγ● Hγ◯") as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  eauto.
Qed.

Lemma auth_excl_update γ ys xs1 xs2 :
  own γ (●E xs1) -∗ own γ (◯E xs2) ==∗
    own γ (●E ys) ∗ own γ (◯E ys).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 with "Hγ● Hγ◯") as "[$$]".
  apply excl_auth_update . easy.
Qed.
End auth_excl.

Section gset.
Context `{Countable K}.
Context `{inG Σ (authUR (gsetUR K))}.

Lemma elem_of_gset  γ (S:gset K) l :
  own γ (●S) -∗ own γ (◯ {[l]}) -∗ ⌜l ∈ S⌝.
Proof.
  iIntros.
  iDestruct (own_valid_2 γ with "[$][$]") as "%Hv".
  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv,?).
  apply gset_included in Hv.
  iPureIntro. set_solver.
Qed.

Lemma extract_witness_gset γ (S:gset K) :
  own γ (● S) ==∗ own γ (● S) ∗ own γ (◯ S).
Proof.
  iIntros.
  iApply own_op. iApply (own_update with "[$]").
  apply auth_update_alloc . apply gset_local_update. set_solver.
Qed.

Lemma gset_conclude γ S1 S2 :
  S1 ⊆ S2 ->
  own γ (◯ S2) -∗ own γ (◯ S1).
Proof.
  intros ?.
  replace S2 with (S1 ∪ S2) by set_solver.
  rewrite -gset_op. iIntros "(?&?)". by iFrame.
Qed.

Lemma extract_witness_gset_elem l γ (S:gset K) :
  l ∈ S ->
  own γ (● S) ==∗ own γ (● S) ∗ own γ (◯ {[l]}).
Proof.
  iIntros. iMod (extract_witness_gset with "[$]") as "(?&?)".
  iFrame. iModIntro. iApply (gset_conclude with "[$]"). set_solver.
Qed.

End gset.
