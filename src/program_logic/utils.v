From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import gen_heap.
From iris.algebra Require Import gmap auth.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_space_lang more_maps_and_sets more_cmras.
From irisfit Require Import interp pbt more_interp wp_clean.

Section Utils.
Context `{interpGS sz Σ}.

(* ------------------------------------------------------------------------ *)
(* A group of pointed-by and their operations. *)

Definition group_pointedbys (E:smultiset loc) (vs:list val) (lq:list Qz) : iProp Σ :=
  [∗ list] v;q ∈ vs;lq, v ↤?{q} E.


Lemma vmapsfrom_cleanup_iterated l q l' (n:nat) :
  l ↤?{q} {[ l' := Z.of_nat n ]} ∗ † l' =[#]=∗ l ↤?{q} ∅.
Proof.
  induction n; iIntros "(?&#?)"; iIntros.
  { iFrame. rewrite singleton_empty //. }
  assert ({[l' := Z.of_nat (S n)]} ≡ {[+l'+]} ⊎ {[l' := Z.of_nat n]} ) as ->. smultiset_solver.
  iIntros.
  iMod (vmapsfrom_cleanup with "[$][$]") as "(? & ?)".
  rewrite (comm _ {[+ l' +]}) -assoc.
  assert (({[+ l' +]} ⊎ {[-l'-]}) ≡ ∅) as -> by smultiset_solver.
  rewrite right_id. iApply (IHn with "[$][$]").
Qed.

Lemma group_pointedbys_pred_free l vs lq :
  † l ∗ group_pointedbys {[+ l +]} vs lq =[#]=∗ group_pointedbys ∅ vs lq.
Proof.
  iRevert (lq).
  iInduction vs as [|] "IH"; iIntros (lq) "(#? & ?)".
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hl". subst.
    iIntros. iModIntro. iFrame. easy. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%x [%xs (%He & ? & ?)]]". subst.
    iIntros.
    iMod (vmapsfrom_cleanup with "[$][$]") as "(? & ?)".
    iMod ("IH" with "[$][$]") as "(? & ?)".
    assert (({[+ l +]} ⊎ {[-l-]}) ≡ ∅) as -> by smultiset_solver.
    by iFrame. }
Qed.

End Utils.


Lemma diamonds_eq `{!interpGS sz Σ} d1 d2 :
  d1 = d2 ->
  ♢ d1 ⊢ ♢ d2.
Proof. intros ->. easy. Qed.

Ltac conclude_diamonds :=
  repeat (iDestruct (diamonds_join with "[$]") as "?");
  simpl;
  iApply (diamonds_eq with "[$]");
  rew_qz; try lia; try easy.
