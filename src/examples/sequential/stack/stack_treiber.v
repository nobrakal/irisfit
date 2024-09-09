From irisfit.program_logic Require Import wpc_logatom.
From irisfit.examples Require Import proofmode stack seqproofmode list.
From irisfit.examples Require treiber.

Module StackTreiber : StackOf with
Definition capacity := @None positive.
Definition capacity := @None positive.

Definition stack_empty : val := treiber.create.
Definition stack_push : val := treiber.push.
Definition stack_pop : val := treiber.pop.
Definition stack_is_empty : val := treiber.is_empty.
Definition stack_is_full : val :=
  λ: [["_"]], false.


Lemma locs_stack_empty : locs stack_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_push : locs stack_push = ∅.
Proof. easy. Qed.
Lemma locs_stack_pop : locs stack_pop = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_empty : locs stack_is_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_full : locs stack_is_full = ∅.
Proof. easy. Qed.

(* Constant factors *)
Definition empty_cost : Qz := 1.
Definition cell_cost  : Qz := 2.

Definition StackOf `{!interpGSMore Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qp * Qz))) (s:loc) : iProp Σ :=
  ∃ vs, treiber.stack s vs ∗ [∗ list] _ ↦x;v ∈ xs;vs, R (fst x) (fst v) ∗ ⌜snd x = snd v⌝.

Lemma stack_is_empty_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "[%vs (?&?)]".
  wpc_apply treiber.is_empty_spec.
  iDestruct (big_sepL2_length with "[$]") as "%".
  iIntros (?) "(->&?)". iSplitR.
  { iPureIntro. destruct xs,vs; simpl in *; naive_solver. }
  iSteps.
Qed.

Lemma stack_is_full_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  TID π
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof. iSteps. Qed.

Lemma stack_empty_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  TID π
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros.
  wpc_apply treiber.create_spec.
  iIntros (?) "(?&?&?)". iFrame. iExists nil. iFrame. done.
Qed.

Lemma stack_push_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) s qp qz v x xs :
  size_lt (length xs) capacity ->
  qz ≠ 0%Qz ->
  CODE (stack_push [[s, v]])
  TID π
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅)
  POST (fun (_:unit) => StackOf R ((x,(qp,qz))::xs) s).
Proof.
  iIntros (_ ?) "(?&[%vs (Hs&?)]&?&?&?)".
  iApply (treiber.push_spec with "[$]"). naive_solver.
  iAuIntro.
  iAaccIntro with "Hs"; iIntros "? !>".
  { iFrame. }
  { iIntros ([]) "_". iExists ((v,(qp, qz))::vs). by iFrame. }
Qed.

Lemma stack_pop_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) s qp qz x xs :
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R ((x,(qp,qz))::xs) s)
  POST (fun v => R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).
Proof.
  iIntros "[%vs (Hs&?)]".
  iApply (treiber.pop_spec with "[$]").
  iAuIntro.
  rewrite /atomic_acc /=. iApply fupd_mask_intro. set_solver.
  iIntros "Hclose".
  iExists _. iFrame "Hs". iSplit.
  { iIntros. iMod "Hclose" as "_". by iFrame. }
  { iIntros (????) "(->&?&?)". iMod "Hclose" as "_". iModIntro.
    iIntros (?) "(->&?&?)".
    iDestruct (big_sepL2_cons_inv_l with "[$]") as "[% [% (%Eq&(?&%Eq')&?)]]".
    inversion Eq. subst. simpl in Eq'. inversion Eq'. subst. iFrame.
    iExists _. iFrame. }
Qed.

Lemma stack_free `{!interpGSMore Σ} A (R:A -> val -> iProp Σ) s xs :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ StackOf R xs s =[#]=∗
  ♢(empty_cost + cell_cost*length xs) ∗ † s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(Hs1 & Hs2 & [% (?&X)])". iIntros.
  iMod (treiber.treiber_free with "[$][$]") as "(?&?&?&H)".
  iDestruct (big_sepL2_length with "[$]") as "->". iFrame. iModIntro.
  iInduction vs as [| (?&(?&?))] "IH" forall (xs) "X".
  { iExists nil. iDestruct (big_sepL2_nil_inv_r with "X") as "->". done. }
  { rewrite /handles big_sepL_cons.
    iDestruct "H" as "((?&?)&?)".
    iDestruct (big_sepL2_cons_inv_r with "X") as "(%&%&%Eq&(?&%Eq')&?)".
    subst xs. destruct x1. simpl in Eq'. inversion Eq'. subst. simpl.
    iDestruct ("IH" with "[$][$]") as "(%&?)".
    iExists (v::_). iFrame. }
Qed.
End StackTreiber.
