From iris.proofmode Require Import base proofmode classes.
From iris Require Import gen_heap.
From iris.algebra Require Import gset gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.
From irisfit.program_logic Require Import more_space_lang more_maps_and_sets interp utils.

From irisfit.program_logic Require Import wp_alloc wp_call wp_load wp_store wp_fork wp_cas wp_closure wp_spec.
From irisfit.program_logic Require Export pbt wp_free wp_enc wpc.

Section Wpc_more.
Context `{interpGS sz Σ}.

Lemma wpc_mk_spec tid P (env:list (string*val)) lq self args code:
  correct_name self args ->
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  locs code = ∅ ->
  env.*1 = fv_clo' self args code ->
  □(∀ l vs, Spec (length args) (zip env.*2 lq) P l -∗ P l vs (substs env (substs' (zip args vs) (subst' self l code)))) -∗
  ♢ (sz (1 + length env)) ∗ group_pointedbys ∅ env.*2 lq -∗
  wpc ⊤ tid (Some ∅) (substs env (mk_clo self args code))
  (fun (l:loc) => Spec (length args) (zip env.*2 lq)  P l ∗ l ↤ ∅ ∗ l ⟸ {[tid]} ∗  meta_token l (⊤ ∖ ↑irisfit_nm)).
Proof.
  iIntros.
  iApply wp_wpc. iIntros.
  iApply (wp_mono with "[-]").
  iApply (wp_mk_spec with "[$][$][$]"); eauto.
  iIntros (?) "(?&[% (%&?&?&?&?)])". subst. rewrite post_loc. iFrame.
Qed.

Lemma wpc_call_spec (A:Type) (EA:Enc A) k E i r n (env:list (val*Qz)) l vals P (Ψ:A -> iProp Σ) :
  length vals = n ->
  locs env.*1 ∖ set_of_option r ⊆ dom k ->
  Spec n env P l -∗
  PBT {[i]} k -∗
  ▷ (∀ t, £1 -∗ PBT {[i]} k -∗ P l vals t  -∗ wpc E i r t Ψ) -∗
  wpc E i r (call_clo l (tm_val <$> vals)) Ψ.
Proof.
  iIntros (??) "? ? Hwpc".
  rewrite !wpc_eq. iIntros "?".
  destruct r as [r|].
  { iIntros (k' Hk') "?".

    iDestruct (PBT_union _ k k' with "[$]") as "Hkk'".
    assert (locs env.*1 ⊆ dom k ∪ dom k').
    { transitivity (locs env.*1 ∖ r ∪ r). 2:set_solver.
      rewrite -difference_union. set_solver.  }
    rewrite (split_map (k ⋅ k') (locs env.*1)).
    2:{ rewrite dom_op. set_solver. }
    iDestruct (PBT_split with "[$]") as "(H1&H2)".
    iAssert (wp E true i (call_clo l (tm_val <$> vals)) (fun v => outside i ∗ post (λ a : A, PBT {[i]} k' ∗  Ψ a) v))%I with "[-]" as "?".
    2:{ iApply (wp_mono with "[$]"). iIntros (?) "(X&[% (->&?&?)])".
        iFrame. iExists _. by iFrame. }
    iApply (wp_call_spec with "[$]H1[$]"); eauto.
    { rewrite dom_restrict dom_op. set_solver. }
    iModIntro. iIntros (?) "? H1 ? HP".
    iDestruct (PBT_union with "[H1 H2]") as "Hkk'".
    iFrame "H1". iFrame "H2".
    rewrite -split_map. 2:{ rewrite dom_op //. }
                      iDestruct (PBT_split with "[$]") as "(H1&H2)".
    iSpecialize ("Hwpc" with "[$][$]"). rewrite wpc_eq.
    iSpecialize ("Hwpc" with "[$][$][%//][$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(Hi&Hc&?)". iFrame "Hi". iApply (post_mono with "[Hc][$]").
    iIntros. iFrame. }
  { iApply (wp_call_spec with "[$][$][$]"). done. set_solver.
    iModIntro. iIntros.
    iSpecialize ("Hwpc" with "[$][$]"). rewrite wpc_eq.
    iSpecialize ("Hwpc" with "[$][$]"). done. }
Qed.

(* A variation when the souvenir contains everything *)
Lemma wpc_call_spec_souv (A:Type) (EA:Enc A) E i r n env l vals P (Ψ:A -> iProp Σ) :
  length vals = n ->
  locs env.*1 ⊆ set_of_option r ->
  Spec n env P l -∗
  ▷ (∀ t, £1 -∗ P l vals t -∗ wpc E i r t Ψ) -∗
  wpc E i r (call_clo l (tm_val <$> vals)) Ψ.
Proof.
  iIntros (? ?) "? Hwpc".
  iApply (wpc_call_spec with "[$][]"). eauto.
  2:{ iApply PBT_empty. }
  { rewrite dom_empty_L. set_solver. }
  iModIntro. iIntros. iApply ("Hwpc" with "[$][$]").
Qed.

(* A useful variant when no frame is needed *)
Lemma wpc_let_empty (A:Type) (EA:Enc A) E i lt2 r x t1 t2 (Q:A -> iProp Σ) :
  lt2 = locs t2 ->
  lt2 ⊆ r ->
  wpc E i (Some r) t1 (fun v => wpc E i (Some r) (subst' x v t2) Q) -∗
  wpc E i (Some r) (tm_let x t1 t2) Q.
Proof.
  intros -> ?.
  iIntros "Hwpc".
  iApply (wpc_mono with "[-]").
  { iDestruct PBT_empty as "?".
    iApply (wpc_let with "[$]").
    { set_solver. }
    iApply (wpc_mono with "[-]").
    { iApply (wpc_weak with "[$]").
      set_solver. }
    iIntros (?) "HP ?". iApply "HP". }
  eauto.
Qed.

Lemma wpc_let_vsingleton v (A:Type) (EA:Enc A) E i r x t1 t2 p (Q : A -> iProp Σ) :
  locs t2 ⊆ r ∪ locs v ->
  v ⟸?{p} {[i]} -∗
  wpc E i (Some (r∪ locs v)) t1 (λ v' : val, v ⟸?{p} {[i]} -∗ wpc E i (Some r) (subst' x v' t2) Q) -∗
  wpc E i (Some r) (tm_let x t1 t2) Q.
Proof.
  iIntros (Hlocs) "? ?".
  destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv as (?,->).
    simpl. rewrite {1}pbt_PBT.
    iApply (wpc_let with "[$]"). set_solver.
    rewrite dom_singleton_L. auto_locs.
    iApply (wpc_mono with "[$]"). iIntros (?) "HP ?". iApply "HP".
    rewrite pbt_PBT. iFrame. }
  { iApply wpc_let_empty. reflexivity.
    rewrite locs_no_loc // in Hlocs. set_solver.
    rewrite locs_no_loc // right_id_L.
    iApply (wpc_mono with "[$]"). iIntros (?) "HP". iApply ("HP" with "[$]"). }
Qed.
End Wpc_more.
