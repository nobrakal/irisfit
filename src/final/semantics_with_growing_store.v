From Coq Require Import Program.Equality ssreflect.
From stdpp Require Import gmap relations list ssreflect.

From irisfit.spacelang Require Import hypotheses.

From irisfit Require Import linked wp_adequacy.
From irisfit.final Require Import addpp common temporal_logic strong_safety strong_safety_addpp weak_anf mcs liveness_addpp.

Section WithSize.
Context (sz:nat -> nat).

Definition config : Type := (nat * configuration).

Inductive action_growing :=
| Main : action -> action_growing
| Grow : action_growing.

Inductive step_action_growing (grow:nat -> nat) : action_growing -> config -> config -> Prop :=
| StepEnabled : forall a ms ρ ρ',
    step_action a ρ ρ' ->
    step_action_growing grow (Main a) (ms,ρ) (ms,ρ')
| StepGrow : forall ms ρ,
    step_action_growing grow Grow (ms,ρ) (grow ms,ρ).

Definition Enabled_growing (a:action_growing) (c:config) :=
  let '(ms,ρ) := c in
  match a with
  | Main a => Enabled sz ms a ρ
  | Grow =>
      (* There is an alloc. such that, even if a full GC was performed, would not fit. *)
      let '(θ,σ) := ρ in
      AllOut θ /\ ¬ EveryAllocFits sz ms (θ, collect (locs θ.*1) σ) end.

Definition step_growing grow c c' := exists a, Enabled_growing a c /\ step_action_growing grow a c c'.

Definition Reducible_growing grow π c :=
  Enabled_growing (Main (Thread π)) c /\ ∃ c', step_action_growing grow (Main (Thread π)) c c'.

Definition NotStuck_growing grow π c := Ended (Thread π) c.2 ∨ Reducible_growing grow π c.

Definition Safe_growing grow c :=
  ∀ π, Enabled_growing (Main (Thread π)) c → NotStuck_growing grow π c.

(* ------------------------------------------------------------------------ *)
(* Towards [rtc_default_to_growing] *)

Lemma main_to_growing grow ms ρ ρ' :
  step_default sz ms ρ ρ' ->
  step_growing grow (ms,ρ) (ms,ρ').
Proof.
  intros (a&?&?). exists (Main a). eauto using StepEnabled.
Qed.

Lemma rtc_default_to_growing grow ms ρ ρ' :
  rtc (step_default sz ms) ρ ρ' ->
  rtc (step_growing grow) (ms,ρ) (ms,ρ').
Proof. induction 1; eauto using rtc_refl,rtc_l,main_to_growing. Qed.

(* ------------------------------------------------------------------------ *)
(* Towards [rtc_growing_to_default] *)

Lemma growing_to_safe_action grow ms ρ ms' ρ' a :
  step_action_growing grow (Main a) (ms, ρ) (ms', ρ') ->
  step_action a ρ ρ'.
Proof.
  inversion 1; subst; eauto using ActionGC, gc_collect.
Qed.

Lemma growing_to_default grow n ρ n' ρ' :
  step_growing grow (n,ρ) (n',ρ') ->
  step_default sz n ρ ρ' \/ ρ = ρ'.
Proof.
  intros (a&Hen&Hstep). destruct a.
  { left. exists a. unfold step_enabled. eauto using growing_to_safe_action. }
  { inversion Hstep. naive_solver. }
Qed.

Lemma AllocFits_weak m1 m2 σ t :
  m1 <= m2 ->
  AllocFits sz m1 σ t →
  AllocFits sz m2 σ t.
Proof.
  intros ? X n Hn. specialize (X n Hn).
  unfold available in *. lia.
Qed.

Lemma EveryAllocFits_weak m1 m2 ρ :
  m1 <= m2 ->
  EveryAllocFits sz m1 ρ ->
  EveryAllocFits sz m2 ρ.
Proof.
  destruct ρ.
  intros. eapply Forall_impl; first done.
  intros ?. apply AllocFits_weak. done.
Qed.

Lemma Enabled_weak m1 m2 a ρ:
  m1 <= m2 ->
  Enabled sz m1 a ρ →
  Enabled sz m2 a ρ.
Proof.
  destruct ρ,a; last done.
  intros ? (?&?&?&?&?).
  eexists _,_; eauto 15 using AllocFits_weak, EveryAllocFits_weak.
Qed.

Lemma step_default_weak_bound m1 m2 ρ ρ' :
  m1 <= m2 ->
  step_default sz m1 ρ ρ' ->
  step_default sz m2 ρ ρ'.
Proof.
  intros ? (a&Henabled&?).
  exists a. split; eauto using Enabled_weak.
Qed.

Lemma rtc_step_default_weak_bound m1 m2 ρ ρ' :
  m1 <= m2 ->
  rtc (step_default sz m1) ρ ρ' ->
  rtc (step_default sz m2) ρ ρ'.
Proof.
  induction 2; eauto using rtc_refl,rtc_l,step_default_weak_bound.
Qed.

Lemma step_growing_grows grow n ρ n' ρ' :
  (forall x, x <= grow x) ->
  step_growing grow (n,ρ) (n',ρ') ->
  n <= n'.
Proof.
  intros ? (?&?&Hstep). inversion Hstep; subst; done.
Qed.

Lemma rtc_growing_grows grow n ρ n' ρ' :
  (forall x, x <= grow x) ->
  rtc (step_growing grow) (n,ρ) (n',ρ') ->
  n <= n'.
Proof.
  remember (n,ρ) as c. remember (n',ρ') as c'.
  intros ? Hrtc.
  revert n ρ n' ρ' Heqc Heqc'.
  induction Hrtc; intros; subst.
  { inversion Heqc'. subst. lia. }
  { destruct y. etrans. eapply step_growing_grows; try done. eauto. }
Qed.

Lemma rtc_growing_to_default grow n ρ n' ρ' :
  (forall x, x <= grow x) ->
  rtc (step_growing grow) (n,ρ) (n',ρ') ->
  rtc (step_default sz n') ρ ρ'.
Proof.
  remember (n,ρ) as c. remember (n',ρ') as c'.
  intros ? Hrtc.
  revert n ρ n' ρ' Heqc Heqc'.
  induction Hrtc; intros n ρ n' ρ' ??; subst.
  { inversion Heqc'. subst. reflexivity. }
  { destruct y. destruct H0 as (a&?&?).
    inversion H1; subst; eauto.
    eapply rtc_l; last eauto using IHHrtc. exists a0. split; last done.
    eapply Enabled_weak; last done. eauto using rtc_growing_grows. }
Qed.

Lemma liveness_weak_pre grow n ms θ σ M (xs:list nat) :
  (forall x, x < grow x) ->
  Always (step_growing grow) (n,(θ,σ)) (fun '(n2,_) => n2 <= ms) ->
  ¬ EveryAllocFits sz n (θ,σ) ->
  store_inv σ ->
  Always (step_default sz ms) (θ,σ) ((fun ρ => Forall (fun '(t,_) => mcs M t) ρ.1)) ->
  Forall2 (λ '(t, _) n, almost n t) θ xs ->
  AfterAtMostWeak (step_growing grow) (fun '(n,σ) => EveryAllocFits sz n σ)
    (S (2*(sizecfg M θ xs) + count_allocated σ + (ms - n))) (n,(θ, σ)).
Proof.
  intros E Hle Hneed Hinv Halmcs Hfor.
  remember (2*(sizecfg M θ xs) + count_allocated σ + (ms - n)) as m.
  revert θ σ xs n Heqm Hneed Halmcs Hfor Hinv Hle.
  induction m using lt_wf_ind; intros θ σ xs n -> Hneed Halmcs Hfor Hinv Hle.
  apply HoldsWLater.
  intros (n',(θ',σ')) Hstep.

  assert (Forall (λ '(t, _), mcs M t) θ) as Hmcs.
  { specialize (Halmcs _ (rtc_refl _ _)). done. }
  assert (Always (step_default sz ms) (θ', σ') (λ ρ : configuration, Forall (λ '(t, _), mcs M t) ρ.1)) as Halmcs'.
  { intros ??. apply Halmcs.
    apply growing_to_default in Hstep. destruct Hstep; last naive_solver.
    eapply rtc_l; last done.
    eapply step_default_weak_bound; last done.
    specialize (Hle _ (rtc_refl _ _)). done. }
  clear Halmcs.

  assert (Always (step_growing grow) (n', (θ', σ')) (λ '(n2, _), n2 ≤ ms)) as Hle'.
  { intros ??. eapply Hle. by eapply rtc_l. }

  assert (store_inv σ') as Hinv'.
  { apply growing_to_default in Hstep. destruct Hstep; last naive_solver.
    eapply step_addpp_almost in H0; eauto using exhibit_back.
    naive_solver. }

  generalize Hstep. intros (c&Hen&Hstep').
  destruct c as [c|].
  { destruct c as [π|].
    { inversion Hstep'; subst. clear Hstep'. inversion_clear H2.
    destruct Hen as (t0&g0&Hn&Hwill&Hpoll).
    assert (t0=t/\g0=g) as (->&->) by naive_solver.
    assert (¬ IsPoll t).
    { naive_solver. }
    clear Hpoll H0 Hneed.
    destruct_decide (decide (EveryAllocFits sz n' (θ',σ'))).
    { by apply HoldsWNow. }

    destruct (sizecfg M θ xs + (count_allocated σ + sizecfg M θ xs + (ms - n'))) eqn:R.
    { exfalso. unfold sizecfg in *. assert (sumsize θ=0). lia. destruct θ.
      { inversion Hn. }
      { destruct p; simpl in *. destruct t0; simpl in *; lia. } }

    generalize Hfor. intros ?.
    eapply Forall2_lookup_l in Hfor; eauto. destruct Hfor as (?&Hxs&?).

    assert (Forall (λ '(t0, _), almost 0 t0) (opt_to_list efs)).
    { eapply atomic_step_addpp_almost_forked; eauto. by eexists. }

    assert (count_allocated σ' <= count_allocated σ + 1)
      by eauto using atomic_step_count_allocated_le.

    eapply atomic_step_almost_almostex in H1; eauto; first last.
    { eapply Forall_lookup in Hmcs; eauto. apply Hmcs. }

    destruct H1 as [(n''&?&?&?)| (n''&->&->&?&?&?)].
    { assert (Forall2 (λ '(t, _) (n : nat), almost n t) θ' (<[π:=n'']>xs ++ add_forked efs)).
      { subst. apply Forall2_app.
        { apply Forall2_insert; eauto. }
        { destruct efs. apply Forall2_cons. inversion H5. done. constructor. } }

      assert (2* (sizecfg M θ' (<[π:=n'']> xs ++ add_forked efs)) + count_allocated σ' + (ms - n') < S n).
      { rewrite -R. unfold sizecfg.
        assert (sumsize θ' + M * sum_list (<[π:=n'']> xs ++ add_forked efs) < sumsize θ + M * sum_list xs).
        { subst. clear H.
          apply lookup_extract_middle in Hn. destruct Hn as (l1&l2&->&?).
          apply lookup_extract_middle in Hxs. destruct Hxs as (l1'&l2'&->&?).
          rewrite !sumsize_app !sum_list_app sumsize_cons. simpl.
          rewrite !insert_app_r_alt; try lia.
          replace (π - length l1) with 0 by lia.
          replace (π - length l1') with 0 by lia.
          rewrite !sumsize_app !sum_list_app sumsize_cons. simpl.
          destruct efs; simpl in *.
          { rewrite sumsize_cons sumsize_nil. nia. }
          { rewrite sumsize_nil. nia. } }
        lia. }
      eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto.
      lia. lia.  }
    { assert (Forall2 (λ '(t, _) (n : nat), almost n t) θ' (<[π:=n'']>xs)).
      { subst. simpl. rewrite right_id_L.
        apply Forall2_insert; eauto. }

      assert (2*(sizecfg M θ' (<[π:=n'']> xs)) + count_allocated σ  + (ms - n') < S n).
      { rewrite -R. subst. simpl.
        apply lookup_extract_middle in Hn. destruct Hn as (l1&l2&->&?).
        apply lookup_extract_middle in Hxs. destruct Hxs as (l1'&l2'&->&?).
        unfold sizecfg.
        rewrite !insert_app_r_alt; try lia.
        replace (π - length l1) with 0 by lia.
        replace (π - length l1') with 0 by lia.
        rewrite !sumsize_app !sum_list_app !sumsize_cons sumsize_nil. simpl.
        nia. }
      eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto.
      all:lia. } }
    { inversion Hstep'. subst a ms0 ρ n ρ'. inversion H2. subst θ'. subst. clear Hneed.
      destruct (2*(sizecfg M θ xs + count_allocated σ + (ms - n'))) eqn:R.
      { exfalso. unfold sizecfg in *. assert (count_allocated σ=0). lia.
        eauto using gc_no_allocated_block. }

      destruct_decide (decide (EveryAllocFits sz n' (θ,σ'))).
      { by apply HoldsWNow. }

      apply gc_neq_size_lt in H5; eauto.
      eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto.
      all:lia. } }
  { destruct (2 * sizecfg M θ xs + count_allocated σ + (ms - n)) eqn:R.
    { exfalso. unfold sizecfg in *. assert (sumsize θ=0). lia.
      assert (θ = nil).
      { destruct θ; first easy.
        destruct p; simpl in *. destruct t; simpl in *; lia. }
      subst. apply Hneed. apply Forall_nil. done. }
    pose proof (E n).
    assert (n <= ms).
    { specialize (Hle _ (rtc_refl _ _)). done. }
    inversion Hstep'. subst θ' σ' n'. subst.
    assert (grow n <= ms).
    { specialize (Hle _ (rtc_once _ _ Hstep)). done. }

    destruct_decide (decide (EveryAllocFits sz (grow n) (θ, σ))). by apply HoldsWNow.

    eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto. all:lia. }
Qed.

Theorem weak_liveness_addpp grow n ms t :
  (forall x, x < grow x) ->
  Always (step_growing grow) (n,init (addpp t)) (fun '(n2,_) => n2 <= ms) ->
  Always (step_growing grow) (n,init (addpp t))
    (EventuallyWeak (step_growing grow) (fun '(n,σ) => EveryAllocFits sz n σ)).
Proof.
  intros X Hlittle (n',ρ') Hsteps.

  assert (rtc (step_default sz ms) (init (addpp t)) ρ').
  { eapply rtc_step_default_weak_bound.
    { apply Hlittle in Hsteps. done. }
    eapply rtc_growing_to_default; last done. intros x. specialize (X x). lia. }

  assert (Forall (fun '(t,_) => almostex t) ρ'.1 /\ store_inv ρ'.2) as (Hfor&Hinv).
  { eapply rtc_step_addpp_almost; eauto.
    { apply map_Forall_empty. }
    simpl. apply Forall_singleton. by eapply al0. }
  destruct ρ' as (θ,σ). simpl in *.

  destruct_decide (decide (EveryAllocFits sz n' (θ,σ))).
  { exists 0. by constructor. }

  apply exhibit in Hfor. destruct Hfor as (xs&Hfor).
  edestruct (rtc_step_mcs_init sz ms (addpp t)) as (M&HM).
  eexists. eapply liveness_weak_pre; eauto.
  { by eapply always_middle. }
  { by eapply always_middle. }
Qed.

Lemma EveryAllocFits_gc ms θ σ σ' :
  gc (locs θ.*1) σ σ' ->
  EveryAllocFits sz ms (θ,σ) ->
  EveryAllocFits sz ms (θ,σ').
Proof.
  intros Hgc ?.
  eapply Forall_impl. done.
  intros ? Z n Hn. apply Z in Hn. etrans. done.
  pose proof (gc_non_size_increasing sz Hgc).
  unfold available. lia.
Qed.

Lemma step_growing_identifiy_last_grow grow n1 ρ1 n2 ρ2 :
  rtc (step_growing grow) (n1, ρ1) (n2, ρ2) ->
  n1 = n2 \/ (exists n0 ρ0, n2 = grow n0 /\ rtc (step_growing grow) (n1, ρ1) (n0, ρ0) /\ rtc (step_growing grow) (n2, ρ0) (n2, ρ2) /\ Enabled_growing Grow (n0,ρ0) ).
Proof.
  intros Hrtc.
  remember (n1, ρ1) as c1. remember (n2,ρ2) as c2.
  revert n1 ρ1 n2 ρ2 Heqc1 Heqc2.

  eapply (rtc_ind_r (fun c2 => forall n1 ρ1 n2 ρ2,
    c1 = (n1, ρ1) → c2 = (n2, ρ2) → n1 = n2
    ∨ (∃ n0 ρ0, n2 = grow n0
             ∧ rtc (step_growing grow) c1 (n0, ρ0)
               ∧ rtc (step_growing grow) (n2, ρ0) c2
                 ∧ Enabled_growing Grow (n0,ρ0)))); last done.
  { intros n1 ρ1 n2 ρ2 Heqc1 Heqc2. subst. inversion Heqc2. naive_solver. }
  { intros (?,?) (?,?) Hsteps Hstep IH.
    intros n1 ρ1 n2 ρ2 Heqc1 Heqc2. subst. inversion Heqc2. subst.
    destruct Hstep as (a&Henabled&Hstep).
    inversion Hstep; subst.
    { destruct (IH _ _ _ _ eq_refl eq_refl) as [X|X]. eauto. right.
      destruct X as (?&?&?&?&?&?). eexists _,_. split_and !; try done.
      eapply rtc_r. done. eexists. split; done. }
    { right. destruct ρ2. destruct Henabled. eexists _,_.
      split_and !; done. } }
Qed.

Lemma bound_is_preserved grow ms ρ1 n1 :
  (forall x, x <= grow x) ->
  (forall x y, x <= y -> grow x <= grow y) ->
  (forall x, Always (step_default sz x) ρ1 (gccmeaf sz ms)) ->
  Always (step_growing grow) (n1,ρ1) (fun '(n2,_) => n2 <= max n1 (grow ms)).
Proof.
  intros Hf1 Hf2 Halways (n2,ρ2) Hsteps.
  apply step_growing_identifiy_last_grow in Hsteps.
  destruct Hsteps as [|(?&?&?&?&?&?)]; subst.
  { lia. }
  { apply rtc_growing_to_default in H0; last done.
    destruct x0 as (θ,σ).
    destruct H2 as (Hout&Hne).
    apply Halways in H0. apply H0 in Hout.
    destruct_decide (decide (x <= ms)) as X.
    { apply Hf2 in X. lia. }
    { exfalso.
      pose proof (gc_non_size_increasing sz (gc_collect (locs θ.*1) σ)).
      assert (¬ EveryAllocFits sz ms (θ, σ)) as Hne'.
      { intros Z. apply Hne. eapply Forall_impl. done. clear Z.
        intros ? Z n Hn. apply Z in Hn. etrans. done.
        unfold available. lia. }
      apply Hout in Hne'.
      destruct Hne' as (?&Hgc&?).
      apply Hne. eapply Forall_impl. done.
      intros ? Z n Hn. apply Z in Hn. etrans. done. clear Hn.
      unfold available.
      pose proof (gc_non_size_increasing sz (gc_pursue_collect _ _ _ Hgc)).
      lia. } }
Qed.

Definition StronglySafe_growing grow '(ms,ρ) :=
  paao ρ /\ Safe_growing grow (ms,ρ).

Lemma safety ms grow ρ n :
  (forall x, x <= grow x) ->
  (forall x y, x <= y -> grow x <= grow y) ->
  (forall x y, ms <= y -> Always (step_default sz x) ρ (StronglySafe sz y)) ->
  Always (step_growing grow) (n,ρ) (StronglySafe_growing grow).
Proof.
  intros X1 X2 Halways (n',ρ') Hrtc.

  assert (Always (step_growing grow) (n,ρ) (fun '(n2,_) => n2 <= max n (grow ms))) as Hlittle.
  { eapply bound_is_preserved; try done.
    intros. eapply always_mono.
    2:{ apply Halways. reflexivity. }
    intros ? (?&?&?). naive_solver. }

  assert (n' <= n `max` grow ms).
  { apply Hlittle in Hrtc. done. }
  apply rtc_growing_to_default in Hrtc; eauto.
  eapply rtc_step_default_weak_bound in Hrtc; last done.

  apply Halways with (y:=(n `max` grow ms)) in Hrtc.
  2:{ etrans. apply X1. lia. }
  destruct Hrtc as (?&?&Hsafe).
  split; first done.
  intros ? ?. simpl in *.

  pose proof (Enabled_weak _ _ _ _ H H2). apply Hsafe in H3.
  unfold NotStuck_growing. simpl.
  destruct H3. naive_solver. right.
  destruct H3 as (?&?&?). split. done. eexists (_,_). by eapply StepEnabled.
Qed.

Lemma not_all_outside_exists f ms θ σ :
  ¬ AllOut θ ->
  paao (θ, σ) ->
  (Safe_growing f (ms,(θ, σ))) ->
  ∃ a, step_growing f (ms,(θ, σ)) a.
Proof.
  intros Hout Haaa Hall.
  apply neg_Forall_Exists_neg in Hout.
  2:{ destruct x. by right. by left. }
  apply Exists_exists in Hout.
  destruct Hout as (g&Hg&Hout).
  apply elem_of_list_fmap in Hg.
  destruct Hg as ((t&g')&Eq&Htg). simpl in Eq. subst g'. generalize Htg. intros X.
  apply elem_of_list_lookup in Htg. destruct Htg as (π&Hπ).
  assert (NotStuck_growing f π (ms,(θ,σ))) as Hne.
  { apply Hall.
    apply Haaa in X.
    eexists _,_. split_and !; try done.
    { intros ??. naive_solver. }
    { naive_solver. } }
  destruct Hne as [|(?&?&?)]. naive_solver. eexists _. exists (Main (Thread π)).
  done.
Qed.

Lemma safe_growing_globally_not_stuck f ms θ σ :
  StronglySafe_growing f (ms,(θ, σ)) ->
  ¬ Forall (λ t : tm, is_val t) θ.*1 ->
  exists a, step_growing f (ms,(θ,σ)) a.
Proof.
  intros (Hall&Hsafe) Hne.
  destruct_decide (decide (EveryAllocFits sz ms (θ,σ))) as Hwill.
  { apply neg_Forall_Exists_neg in Hne.
    2:{ intros x. destruct (is_val x); naive_solver. }
    apply Exists_exists in Hne.
    destruct Hne as (t'&Ht'&Hneed).
    apply elem_of_list_fmap in Ht'. destruct Ht' as (u&?&Htg). destruct u as (tX,g').
    simpl in H. subst tX.
    apply elem_of_list_lookup in Htg. destruct Htg as (π&Hπ).
    assert (Enabled sz ms (Thread π) (θ,σ)) as Hen.
    { eauto using EveryAllocFits_enabled, lookup_lt_Some. }
    apply Hsafe in Hen. destruct Hen as [X|(a&?&?)].
    { exfalso. eauto using ended_no_val. }
    destruct a. eexists _, (Main (Thread π)). split; last done.
    simpl. eauto. }
  destruct_decide (decide (AllOut θ)) as Hout.
  { destruct_decide (decide (σ = collect (locs θ.*1) σ)).
    { eexists. exists Grow. split; last apply StepGrow.
      split; try done. rewrite -H //. }
    { eexists. exists (Main GC). split. done. apply StepEnabled.
      apply ActionGC. apply gc_collect. done. } }
  { eauto using not_all_outside_exists. }
Qed.

Lemma strongify_eventually (P:config -> Prop) c f :
  Always (step_growing f) c (StronglySafe_growing f) ->
  Always (step_growing f) c (fun '(n,(θ,σ)) => Forall is_val θ.*1 -> P (n,(θ,σ))) ->
  EventuallyWeak (step_growing f) P c ->
  Eventually (step_growing f) P c.
Proof.
  intros Hsafe Hal (n&Hn).
  exists n.
  revert c Hsafe Hal Hn.
  induction n using lt_wf_ind.
  intros c Hsafe Hal Hn.

  inversion Hn.
  { subst n0 X. apply HoldsNow. eauto. }
  subst n X. rename n0 into n. simpl.

  destruct c as (ms,(θ,σ)).

  destruct_decide (decide (Forall is_val θ.*1)) as Hall.
  (* If all are vals, I know that all will fits, the game is over. *)
  { apply HoldsNow. pose proof (Hal _ (rtc_refl _ _) Hall). done. }

  apply HoldsAfter.
  { pose proof (Hsafe _ (rtc_refl _ _)).
    eapply safe_growing_globally_not_stuck; try done. }

  intros (θ',σ') Hstep.

  simpl. apply H. lia.
  { intros ??. apply Hsafe. by eapply rtc_l. }
  { intros ??. apply Hal. by eapply rtc_l. }
  { by apply H0. }
Qed.

Lemma strongifiy_liveness f ρ :
  Always (step_growing f) ρ (StronglySafe_growing f) ->
  Always (step_growing f) ρ (EventuallyWeak (step_growing f) (fun '(n,σ) => EveryAllocFits sz n σ)) ->
  Always (step_growing f) ρ (Eventually (step_growing f) (fun '(n,σ) => EveryAllocFits sz n σ)).
Proof.
  intros Hsafe Hn. intros (?&?) ?.
  eapply strongify_eventually; eauto.
  { intros ??. eapply Hsafe. by etrans. }
  { intros (?&(?,?)) ?. apply allvalwillfit. }
Qed.

Lemma liveness ms f n t :
  (forall x, x < f x) ->
  (forall x y, x <= y -> f x <= f y) ->
  (forall x y, ms <= y -> Always (step_default sz x) (init (addpp t)) (StronglySafe sz y)) ->
  Always (step_growing f) (n,init (addpp t))
    (Eventually (step_growing f) (fun '(n,σ) => EveryAllocFits sz n σ)).
Proof.
  intros X1 X2 Halways.
  assert (Always (step_growing f) (n,(init (addpp t))) (StronglySafe_growing f)).
  { eapply safety; try done. intros x. specialize (X1 x). lia. }

  eapply strongifiy_liveness.
  { done. }
  { eapply weak_liveness_addpp; eauto.
    eapply bound_is_preserved; try done.
    { intros. specialize (X1 x). lia. }
    { intros. eapply always_mono.
      2:{ apply Halways. reflexivity. }
      intros ? (?&?&?). done. } }
Qed.

End WithSize.

From iris Require Import proofmode.proofmode.
From irisfit.lib Require Import qz.
From irisfit.program_logic Require Import wp interp wp_adequacy.
From irisfit.final Require Import final_theorems.

Lemma wp_safety_growing (sz grow:nat -> nat) (n ms:nat) (t:tm) :
  locs t = ∅ ->
  (forall x, x <= grow x) ->
  (forall x y, x <= y -> grow x <= grow y) ->
  n <= grow ms ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_growing sz grow) (n,init t) (Safe_growing sz grow).
Proof.
  intros.
  eapply always_mono; last first.
  { eapply (safety _ ms); eauto using wp_strong_safety_strong. }
  intros (?&?). naive_solver.
Qed.

Lemma wp_liveness_addpp_growing sz f n (ms:nat) (t:tm) :
  weak_anf t ->
  locs t = ∅ ->
  (forall x, x < f x) ->
  (forall x y, x <= y -> f x <= f y) ->
  n <= f ms ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_growing sz f) (n,init (addpp t))
    (Eventually (step_growing sz f) (fun '(n,σ) => EveryAllocFits sz n σ)).
Proof.
  eauto using liveness, addpp_preserves_safety, wp_strong_safety_strong.
Qed.

Theorem wp_safety_addpp_growing sz f (ms:nat) (t:tm) n :
  weak_anf t ->
  locs t = ∅ ->
  (forall x, x < f x) ->
  (forall x y, x <= y -> f x <= f y) ->
  n <= f ms ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_growing sz f) (n,init (addpp t)) (Safe_growing sz f).
Proof.
  intros ?? ??? Hwp.
  eapply always_mono with (P:= (StronglySafe_growing sz f)).
  { intros (?&?). naive_solver. }
  eapply (safety _ ms); eauto.
  { intros x. specialize (H1 x). lia. }
  { eauto using addpp_preserves_safety, wp_strong_safety_strong. }
Qed.

Lemma wp_bound_is_preserved sz grow (ms:nat) n1 t :
  weak_anf t ->
  locs t = ∅ ->
  (forall x, x <= grow x) ->
  (forall x y, x <= y -> grow x <= grow y) ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_growing sz grow) (n1,init (addpp t)) (fun '(n2,_) => n2 <= max n1 (grow ms)).
Proof.
  intros.
  eapply bound_is_preserved; eauto.
  intros.
  eapply always_mono; last first.
  { eapply addpp_preserves_safety; first done.
    eauto using (wp_strong_safety_strong _ _ ms). }
  intros ? (?&?&?). done.
Qed.
