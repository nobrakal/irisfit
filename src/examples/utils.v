From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import gen_heap.
From iris.algebra Require Import gmap auth gset excl_auth.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language notation .

From irisfit.program_logic Require Import more_space_lang more_maps_and_sets.
From irisfit.program_logic Require Import interp pbt wpc.
From irisfit.program_logic Require Export more_cmras utils wp_clean.

From irisfit.examples Require Import instantiation.

(* ------------------------------------------------------------------------ *)

(* Usually returned after a [free] *)
Definition handles `{interpGS0 Σ}  (xs:list (val * (Qp*Qz))) : iProp Σ :=
  [∗ list] x ∈ xs, let '(v,(p,q)) := x in v ⟸?{p} ∅ ∗ v ↤?{q} ∅.

Lemma handles_nil `{interpGS0 Σ} :
  handles nil ≡ True%I.
Proof. easy. Qed.

Lemma handles_cons `{interpGS0 Σ}  v p q xs :
  handles ((v,(p,q))::xs) ≡ (v ⟸?{p} ∅ ∗ v ↤?{q} ∅ ∗ handles xs)%I.
Proof.
  rewrite /handles big_sepL_cons. iSplit.
  iIntros "((?&?)&?)". by iFrame.
  iIntros "(?&?&?)". by iFrame.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma wpc_store_no_loc `{interpGS0 Σ} E tid X (l:loc) (n:Z) v vs :
  ¬(is_loc v) ->
  (0 <= n < Z.to_nat (length vs))%Z ->
  l ↦ vs ⊢
    wpc E tid X (tm_store l n v) (fun (_:unit) => l ↦ (<[Z.to_nat n:=v]> vs)).
Proof.
  iIntros (Hv). iIntros.
  iApply (wpc_mono with "[-]").
  iApply (wpc_store _ _ _ 1%Qz ∅).
  3:iFrame.
  { congruence. }
  { eauto. }
  { destruct v; eauto. exfalso. by apply Hv. }
  iIntros (_) "(?&?&?)". iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* LATER move to iris *)

Lemma big_sepM2_lookup_acc_l {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type}
    (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B) (i : K) (x1 : A) :
  m1 !! i = Some x1 →
  ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
  ∃ x2, ⌜m2 !! i = Some x2⌝ ∗ Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
Proof.
  iIntros (E1) "HM".
  iDestruct (big_sepM2_lookup_iff with "HM") as "%Hl".
  assert (is_Some (m2 !! i)) as (x2,E2).
  { apply Hl. eauto. }
  iExists x2. iSplitR; first done. iApply big_sepM2_lookup_acc; eauto.
Qed.

Lemma big_sepM2_lookup_acc_r {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type}
    (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B) (i : K) (x2 : B) :
  m2 !! i = Some x2 →
  ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
  ∃ x1, ⌜m1 !! i = Some x1⌝ ∗ Φ i x1 x2 ∗ (Φ i x1 x2 -∗ [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
Proof.
  iIntros (?) "HM".
  iDestruct (big_sepM2_lookup_iff with "HM") as "%Hl".
  assert (is_Some (m1 !! i)) as (x1,?).
  { apply Hl. eauto. }
  iExists x1. iSplitR; first done. iApply big_sepM2_lookup_acc; eauto.
Qed.
