From Coq Require Import Program.Equality Wellfounded.
From stdpp Require Import base option relations.
From iris.proofmode Require Import proofmode.
From irisfit.lib Require Import qz.
From irisfit.language Require Import language.
From irisfit.language Require Import semantics reducible syntax_instances.
From irisfit.program_logic Require Import wp interp wp_adequacy.
From irisfit.final Require Import addpp common temporal_logic liveness_addpp strong_safety strong_safety_addpp weak_anf.

Lemma EveryAllocFits_all_enabled sz ms ρ:
  EveryAllocFits sz ms ρ ->
  (forall π, WellFormed sz (Thread π) ρ -> Enabled sz ms (Thread π) ρ).
Proof.
  destruct ρ as (θ,σ). simpl. intros Hall π Hπ.
  apply elem_of_list_lt in Hπ. destruct Hπ as ((?&?)&Hπ).
  eexists _,_. split_and !; try done.
  eapply list.Forall_forall. done.
  apply elem_of_list_lookup. exists π. rewrite list_lookup_fmap Hπ //.
Qed.

Lemma step_default_preserves_size sz ms ts σ ts' σ' :
  size_heap sz σ <= ms ->
  step_default sz ms (ts,σ) (ts',σ') ->
  size_heap sz σ' <= ms.
Proof.
  intros Hx Hstep.
  destruct Hstep as (c&Hc&Hstep).
  destruct c; inversion Hstep; subst.
  2:{ apply gc_non_size_increasing with (sz:=sz) in H3. lia. }
  destruct_decide (decide (∃ n, IsAlloc n t)) as Ha.
  { destruct Ha as (n'&Ha).
    erewrite atomic_step_alloc_size; eauto.
    simpl in Hc. destruct Hc as (t0&g0&?&Hwill&?).
    assert (t0=t/\g0=g) as (->&->) by naive_solver.
    apply Hwill in Ha. unfold available in Ha. lia. }
  { erewrite <- atomic_step_not_alloc_preserves_size; eauto. }
Qed.

Theorem wp_safety (sz:nat -> nat) (ms:nat) (t:tm) :
  locs t = ∅ ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_default sz ms) (init t) (Safe sz ms).
Proof.
  intros.
  eapply always_mono.
  2:{ eauto using wp_strong_safety_strong. }
  intros ? (?&?&?). done.
Qed.

(* How to transform an "eventually weak" into an "eventually" *)
Lemma strongify_eventually (P:configuration -> Prop) sz ms θ σ:
  Always (step_default sz ms) (θ, σ) (StronglySafe sz ms) ->
  Always (step_default sz ms) (θ, σ) (fun '(θ',σ') => Forall is_val θ'.*1 -> P (θ',σ')) ->
  EventuallyWeak (step_default sz ms) P (θ, σ) ->
  Eventually (step_default sz ms) P (θ, σ).
Proof.
  intros Hsafe Hal (n&Hn).
  exists n.
  remember (θ,σ) as ρ.
  replace θ with ρ.1 by naive_solver.
  replace σ with ρ.2 by naive_solver.
  clear Heqρ σ θ.

  revert ρ Hsafe Hal Hn.
  induction n using lt_wf_ind.
  intros (θ,σ) Hsafe  Hal Hn.

  inversion Hn.
  { subst n0 X. apply HoldsNow. eauto. }
  subst n X. rename n0 into n. simpl.

  destruct_decide (decide (Forall is_val θ.*1)) as Hall.
  (* If all are vals, I know that all will fits, the game is over. *)
  { apply HoldsNow. pose proof (Hal _ (rtc_refl _ _) Hall). done. }

  apply HoldsAfter.
  { destruct (Hsafe _ (rtc_refl _ _)) as (X1&X2).
    apply strongly_safe_globally_not_stuck; try done. }

  intros (θ',σ') Hstep.

  simpl. apply H. lia.
  { intros ??. apply Hsafe. by eapply rtc_l. }
  { intros ??. apply Hal. by eapply rtc_l. }
  { by apply H0. }
Qed.

Lemma strongifiy_liveness sz ms ρ:
  Always (step_default sz ms) ρ (StronglySafe sz ms) ->
  Always (step_default sz ms) ρ (EventuallyWeak (step_default sz ms) (EveryAllocFits sz ms)) ->
  Always (step_default sz ms) ρ (Eventually (step_default sz ms) (EveryAllocFits sz ms)).
Proof.
  intros Hsafe Hn. intros (?&?) ?.
  eapply strongify_eventually; eauto.
  { intros ??. eapply Hsafe. by etrans. }
  { intros (?&?) ?. apply allvalwillfit. }
Qed.

Theorem wp_liveness_addpp sz (ms:nat) (t:tm) :
  weak_anf t ->
  locs t = ∅ ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_default sz ms) (init (addpp t))
    (Eventually (step_default sz ms) (EveryAllocFits sz ms)).
Proof.
  intros ?? Hwp.
  apply (wp_strong_safety_strong _ ms ms ms) in Hwp; try done.
  eapply strongifiy_liveness.
  { eauto using addpp_preserves_safety. }
  { eauto using weak_liveness_addpp. }
Qed.

Theorem wp_safety_addpp sz (ms:nat) (t:tm) :
  weak_anf t ->
  locs t = ∅ ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_default sz ms) (init (addpp t)) (Safe sz ms).
Proof.
  intros ?? Hwp.
  eapply always_mono with (P:= (StronglySafe sz ms)).
  { intros ? (?&?&?). done. }
  eapply addpp_preserves_safety. done.
  eapply wp_strong_safety_strong; eauto.
Qed.
