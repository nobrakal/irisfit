From stdpp Require Import base binders.

From iris.algebra Require Import auth gset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.

From irisfit.language Require Import syntax.
From irisfit.examples Require Import utils.

(******************************************************************************)
(* Reachable *)
(* We rest on immutability to express an abstract reachability predicate which
   is persistent.

   Heavily rests on the work by Vindum & Birkedal
   https://zenodo.org/record/4317021

   LATER we can make this abstract w.r.t the  "reachable_1" predicate.
   LATER use the bi_rtc constructioon, when ready
 *)

Section Reachable.
Context `{ghost_mapG Σ loc (option loc), inG Σ (authUR (gsetUR loc))}.

Fixpoint reachable_l (γ:gname) (n:nat) ln lm : iProp Σ :=
  match n with
  | O => ⌜ln = lm⌝
  | S n' => ∃ lp, ln ↪[γ]□ (Some lp) ∗ reachable_l γ n' lp lm
  end.
Global Instance reachable_l_timeless γ n ln lm : Timeless (reachable_l γ n ln lm).
Proof. revert ln. induction n; intros; apply _. Qed.
Global Instance reachable_l_persistent γ n ln lm : Persistent (reachable_l γ n ln lm).
Proof. revert ln. induction n; intros; apply _. Qed.

Definition reachable γ ln lm : iProp Σ := ∃ n, reachable_l γ n ln lm.
Global Instance reachable_timeless γ ln lm : Timeless (reachable γ ln lm).
Proof. apply _. Qed.
Global Instance reachable_persistent γ ln lm : Persistent (reachable γ ln lm).
Proof. apply _. Qed.

Lemma reachable_eq γ ln lm :
  reachable γ ln lm = (∃ n, reachable_l γ n ln lm)%I.
Proof. reflexivity. Qed.

Local Notation "a ~ γ ~> b" :=
  (reachable γ a b) (at level 20, format "a  ~ γ ~>  b").

Lemma reachable_refl γ lm : ⊢ lm ~γ~> lm.
Proof. iExists 0. easy. Qed.

Lemma reachable_trans γ a b c : reachable γ a b -∗ reachable γ b c -∗ reachable γ a c.
Proof.
  iDestruct 1 as (n) "Ha".
  iInduction n as [|n'] "IH" forall (a); simpl.
  - iDestruct "Ha" as "->". subst. auto.
  - iIntros "bRc".
    iDestruct "Ha" as "[% (#?&?)]".
    iDestruct ("IH" with "[$] bRc") as (n) "Ho".
    iExists (S n). iExists _. iFrame "#∗".
Qed.

Definition can_reach a b := own b (◯ {[ a ]}).

Local Notation "a -r-> b" := (can_reach a b) (at level 20).

Global Instance can_reach_timeless a b: Timeless (can_reach a b).
Proof. apply _. Qed.

Global Instance can_reach_persistent a b : Persistent (can_reach a b).
Proof. apply _. Qed.

Definition tie γi γt lt : iProp Σ :=
  ∃ (s:gset loc), own γt (● s) ∗ ([∗ set] ln ∈ s, ln ~γi~> lt).

Global Instance tie_timeless γi γt lt : Timeless (tie γi γt lt).
Proof. apply _. Qed.

Lemma lookup_reach_set_map γ s ln lt :
  ln ∈ s → ([∗ set] ln ∈ s, ln ~γ~> lt) -∗ ([∗ set] ln ∈ s, ln ~γ~> lt) ∗ ln ~γ~> lt.
Proof.
  iIntros (elem) "map".
  iDestruct (big_sepS_elem_of_acc _ _ ln with "map") as "[#reach reins]"; first by set_solver.
  iFrame "#". by iApply "reins".
Qed.

Lemma lookup_reach_set γ ln γt lt :
  ln -r-> γt -∗ tie γ γt lt -∗ ln ~γ~> lt.
Proof.
  iIntros "#frag". iDestruct 1 as (s) "[auth map]".
  iDestruct (own_valid_2 with "auth frag") as %[subset%gset_included]%auth_both_valid.
  iDestruct (lookup_reach_set_map _ _ ln with "map") as "[??]". set_solver.
  iFrame. exact 0.
Qed.

Lemma insert_reach_set γ α ℓn ℓt :
  tie γ α ℓt -∗ ℓn ~γ~> ℓt ==∗ tie γ α ℓt ∗ ℓn -r-> α.
Proof.
  iDestruct 1 as (s) "[auth map]".
  iIntros "reach".
  iMod (own_update _ _ (● ({[ ℓn ]} ∪ s)) with "auth") as "auth".
  { eapply auth_update_auth. apply gset_local_update. set_solver. }
  iMod (extract_witness_gset_elem ℓn with "auth") as "(?&?)". set_solver.
  iFrame. iModIntro.
  destruct (decide (ℓn ∈ s)).
  - iExists _. replace ({[ℓn]} ∪ s) with s; last by set_solver. iFrame.
  - iExists _. iFrame. iApply big_sepS_insert. set_solver. iFrame.
Qed.

Lemma reach_set_advance γ1 γ2 ℓ ℓ' :
  tie γ1 γ2 ℓ -∗ ℓ ~γ1~> ℓ' ==∗ tie γ1 γ2 ℓ' ∗ ℓ' -r-> γ2.
Proof.
  iDestruct 1 as (s) "[auth map]".
  iMod (own_update _ _ (● ({[ ℓ' ]} ∪ s)) with "auth") as "auth".
  { eapply auth_update_auth. apply gset_local_update. set_solver. }
  iMod (extract_witness_gset_elem ℓ' with "[$]") as "(?&?)". set_solver.
  iIntros "#rRn".
  iModIntro. iFrame. iExists _. iFrame.
  destruct (decide (ℓ' ∈ s)) as [?|elem].
  - replace ({[ℓ']} ∪ s) with s; last by set_solver.
    iApply (big_sepS_impl with "map []"). iModIntro.
    iIntros (x _) "#xRn".
    iApply reachable_trans; done.
  - iApply big_sepS_insert. done.
    iSplitR; first by iApply reachable_refl.
    iApply (big_sepS_impl with "map []"). iModIntro. iIntros (? _) "#xRn".
    iApply reachable_trans; done.
Qed.
End Reachable.

Global Opaque reachable tie can_reach.

Global Notation "a ~ γ ~> b" :=
  (reachable γ a b) (at level 20, format "a  ~ γ ~>  b").
Global Notation "a -r-> b" :=
  (can_reach a b) (at level 20).
