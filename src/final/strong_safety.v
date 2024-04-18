From Coq Require Import Program.Equality Wellfounded.
From stdpp Require Import base option relations.
From iris.proofmode Require Import proofmode.
From irisfit.lib Require Import qz.
From irisfit.language Require Import language.
From irisfit.language Require Import semantics reducible syntax_instances.
From irisfit.program_logic Require Import wp interp wp_adequacy.
From irisfit.final Require Import common instances final_semantics.

Section WithSize.
Context (sz:nat -> nat).

(* ------------------------------------------------------------------------ *)
(* Definitions *)

Definition Ended a (ρ:configuration) :=
  match a with
  | Thread π => exists t g, ρ.1 !! π = Some (t,g) /\ is_Some (to_val t) /\ g =Out
  | _ => False end.

Definition Reducible ms a ρ :=
  exists ρ', step_enabled sz ms a ρ ρ'.

Definition NotStuck ms a ρ :=
  Ended a ρ \/ Reducible ms a ρ.

(* All Alloc and Poll Are Out *)
Definition Aapao : configuration -> Prop := fun '(θ,σ) =>
  (forall t g, (t,g) ∈ θ -> (IsPoll t \/ exists n, IsAlloc n t) -> g = Out).

(* I forgot what was the intent of the name. *)
Definition Gns ms : configuration -> Prop := fun '(θ,σ) =>
   AllOut θ -> ¬ EveryAllocFits sz ms (θ,σ) ->
   exists σ', gc (locs θ.*1) σ σ' /\ EveryAllocFits sz ms (θ,σ') .

Definition Safe ms ρ :=
  (forall π, Enabled sz ms (Thread π) ρ -> NotStuck ms (Thread π) ρ).

Definition StronglySafe ms ρ :=
  Aapao ρ /\ Gns ms ρ /\ Safe ms ρ.

(* ------------------------------------------------------------------------ *)
(* Towards [wp_strong_safety] *)

Lemma size_heap_after_collect r σ σ' :
  gc r σ' σ ->
  size_heap sz (collect r σ) <= size_heap sz (collect r σ').
Proof.
  rewrite /size_heap => Hgc.
  eapply stdpp.map_fold_ind_2 with (P:= fun x1 x2 _ _ => x1 <= x2).
  all:try (intros; lia).
  { intros. destruct Hgc as (Hd&_).
    rewrite -!not_elem_of_dom !dom_collect Hd //. }
  { intros. unfold collect in *.
    rewrite !map_lookup_imap in H1,H2.
    destruct (σ' !! i) eqn:E2; last inversion H2.
    unfold collect_block in *. simpl in *.
    destruct_decide (decide (reachable r σ' i)).
    { inversion H2. subst. destruct Hgc as (_&Hgc). destruct (Hgc i).
      eauto using elem_of_dom. 2:naive_solver.
      rewrite !lookup_total_alt E2 in H5.
      destruct (σ !! i); simpl in *; inversion H1.
      case_decide; simpl in *; simpl; subst; lia. }
    { inversion H2. subst.
      destruct (σ !! i); last inversion H1. simpl in *.
      rewrite decide_False in H1.
      { inversion H1; subst. simpl. lia. }
      { rewrite -gc_preserves_reachable //. } } }
Qed.

Lemma atomic_step_gc_insensitive2 t1 g1 σ1 t2 g2 σ2 σ1' r efs:
  atomic_step t1 g1 σ1 t2 g2 σ2 efs ->
  gc r σ1 σ1' ->
  locs t1 ⊆ r ->
  ∃ σ2, atomic_step t1 g1 σ1' t2 g2 σ2 efs.
Proof.
  intros Hstep. revert r. induction Hstep; intros r Hgc Hi; subst.
  { rewrite locs_fill_item in Hi. edestruct IHHstep; eauto using StepCtx. set_solver. }

  assert (∃ σ2', head_step_conc t1 g1 σ1' t2 g2 σ2' efs) as (?&?); last eauto using StepHead.
  inversion H; subst; last first.
  { eexists. eapply HeadFork. }

  assert (∃ σ2', head_step t1 g1 σ1' t2 g2 σ2') as (?&?); last eauto using HeadSeq.
  inversion H0; subst; eauto using head_step; eexists.
  { eapply HeadAlloc; eauto. apply not_elem_of_dom.
    erewrite <- gc_dom; last done. eauto using not_elem_of_dom. }
  { eapply HeadLoad; eauto. eapply gc_read_root; try done. set_solver. }
  { eapply HeadStore; eauto. eapply gc_read_root; try done. set_solver. }
  { eapply HeadCAS; eauto. eapply gc_read_root; try done. set_solver. }
Qed.

Lemma atomic_step_false_sz_lt t  σ t' g' σ' efs :
  atomic_step t In σ t' g' σ' efs -> tm_size t' < tm_size t.
Proof.
  intros Hstep. dependent induction Hstep; eauto.
  { assert (forall E t1 t2, tm_size t1 < tm_size t2 -> tm_size (fill_item E t1) < tm_size (fill_item E t2)); eauto.
    intros. destruct E0; simpl; try lia. rewrite !fmap_app. simpl. rewrite !list_sum_app. simpl.
    lia. }
  { inversion H; subst.
    inversion H0; subst; simpl; try lia.
    { destruct x; simpl; try lia. rewrite size_subst. lia. }
    { destruct b; lia. } }
Qed.

Lemma atomic_step_not_alloc_preserves_size t g σ t' g' σ' efs :
  (forall n, ¬ IsAlloc n t) ->
  atomic_step t g σ t' g' σ' efs ->
  size_heap sz σ = size_heap sz σ'.
Proof.
  intros Ha Hstep. dependent induction Hstep; subst.
  { apply IHHstep. intros ??. apply (Ha n). by econstructor. }
  inversion H; subst; last done.
  inversion H0; subst; eauto.
  { exfalso. apply (Ha n). by econstructor. }
  { erewrite size_heap_insert_same_size; eauto. by rewrite size_block_update. }
  { case_decide; eauto; subst.  erewrite size_heap_insert_same_size; eauto. by rewrite size_block_update. }
Qed.

Lemma IsAlloc_fill_item_inv n E t :
  to_val t = None ->
  IsAlloc n (fill_item E t) ->
  IsAlloc n t.
Proof.
  inversion 2.
  { destruct E; naive_solver. }
  apply fill_item_inj in H1; eauto using IsAlloc_no_val.
  naive_solver.
Qed.

Lemma atomics_step_false_not_alloc t σ t' σ' g' efs :
  atomic_step t In σ t' σ' g' efs ->
 (forall n, ¬ IsAlloc n t).
Proof.
  intros Hstep n.
  dependent induction Hstep.
  { intros ?. apply (IHHstep eq_refl n); eauto.
    eapply IsAlloc_fill_item_inv; eauto using atomic_step_no_val. }
  inversion H; try done; subst.
  inversion H0; subst; try done.
  all: intros X; inversion X; destruct E; subst; try done; exfalso.
  all: try (inversion H1; subst; by apply IsAlloc_no_val in H3).
  { inversion H2. subst. apply IsAlloc_no_val in H4. done. }
  { inversion H2. subst. apply IsAlloc_no_val in H4. done. }
  { inversion H1. subst. apply IsAlloc_no_val in H6. done. }
  { inversion H1. subst. apply IsAlloc_no_val in H6. done. }
Qed.

Lemma atomics_step_false_not_poll t σ t' σ' g' efs :
  atomic_step t In σ t' σ' g' efs ->
  ¬ IsPoll t.
Proof.
  intros Hstep Hpoll.
  dependent induction Hstep.
  { apply (IHHstep eq_refl); eauto.
    eapply IsPoll_fill_item_inv; eauto using atomic_step_no_val. }
  inversion H; try done; subst.
  inversion H0; subst; try done.
  all:inversion Hpoll; destruct E; subst; try done; exfalso.
  all: try (inversion H1; subst; by apply IsPoll_no_val in H2).
  { inversion H2. subst. apply IsPoll_no_val in H3. done. }
  { inversion H2. subst. apply IsPoll_no_val in H3. done. }
  { inversion H1. subst. apply IsPoll_no_val in H3. done. }
  { inversion H1. subst. apply IsPoll_no_val in H3. done. }
Qed.

Lemma collect_lookup_notin l r σ :
  σ !! l = None ->
  collect r σ !! l = None.
Proof. rewrite /collect map_lookup_imap => -> //. Qed.

Lemma collect_insert_fresh r l n σ :
  l ∉ dom σ ->
  l ∈ r ->
  collect r (<[l:=BBlock (replicate n val_unit)]> σ) = <[l:=BBlock (replicate n val_unit)]> (collect r σ).
Proof.
  intros Hl Hr.
  apply map_eq. intros l'. rewrite /collect lookup_insert_case !map_lookup_imap lookup_insert_case.
  case_decide; subst.
  { simpl. rewrite /collect_block. rewrite decide_True //.
    exists l'. split; eauto using rtc_refl. }
  destruct (σ !! l'); try done. simpl.
  rewrite /collect_block. destruct_decide (decide (reachable r (<[l:=BBlock (replicate n val_unit)]> σ) l')).
  { rewrite decide_True //.
    eapply analyze_reachable_after_alloc; eauto.
    by eapply not_elem_of_dom. intros ?. simpl. rewrite block_pointer_set_new_block. set_solver. }
  { rewrite decide_False //. intros (?&?&Hrtc). apply H0.
    exists x. split; first done.
    clear H0 H1. eapply rtc_subrel; last done.
    intros l0 ??. apply successor_insert_ne; eauto. intros ->.
    eauto using successor_in_dom. }
Qed.

Lemma reachable_remove_root l r σ l'  :
  l ≠ l' ->
  l ∉ dom σ ->
  reachable (r ∖ {[l]}) σ l' <-> reachable r σ l'.
Proof.
  intros. split.
  { apply reachable_mono_roots. set_solver. }
  { intros (?&?&Hrtc).
    assert (x ≠ l).
    { inversion Hrtc; subst; eauto. apply successor_in_dom in H2. intros ->. set_solver. }
    exists x. set_solver. }
Qed.

Lemma collect_loc_not_in l r σ :
  l ∉ dom σ ->
  collect r σ = collect (r ∖ {[l]}) σ.
Proof.
  intros Hl.
  apply map_eq. intros l'. rewrite /collect !map_lookup_imap.
  destruct (σ !! l') eqn:E; try done. simpl.
  assert (l ≠ l').
  { intros ->. eauto using elem_of_dom. }
  unfold collect_block. case_decide; [rewrite decide_True | rewrite decide_False]; eauto.
  all: rewrite reachable_remove_root //.
Qed.

Lemma atomic_step_alloc_size_gc r t g σ t' g' σ' efs n :
  IsAlloc n t ->
  atomic_step t g σ t' g' σ' efs ->
  live_heap_size sz (locs t' ∪ r) σ' = live_heap_size sz (locs t ∪ r)  σ + sz (Z.to_nat n).
Proof.
  intros Hsz Hstep. revert r; induction Hstep; intros r; subst.
  { rewrite !locs_fill_item.
    replace (locs E ∪ locs t2 ∪ r) with (locs t2 ∪ (locs E ∪ r)) by set_solver.
    replace (locs E ∪ locs t1 ∪ r) with (locs t1 ∪ (locs E ∪ r)) by set_solver.
    eauto using IsAlloc_fill_item_inv,atomic_step_no_val. }
  inversion Hsz; subst; last first.
  { exfalso. eapply head_step_conc_no_ctx; eauto using IsAlloc_no_val. }
  inversion H; subst. inversion H0; subst. inversion H4; subst n0.
  clear H H0 H3 Hsz.
  rewrite /live_heap_size /size_heap collect_insert_fresh; last first.
  { set_solver. }
  { eauto using not_elem_of_dom. }
  rewrite map_fold_insert; first last.
  { eauto using collect_lookup_notin. }
  { intros. lia. }
  { simpl. rewrite replicate_length. f_equal.
    rewrite (collect_loc_not_in l (locs_tm l ∪ r)); eauto using not_elem_of_dom.
    rewrite (collect_loc_not_in l (locs (tm_alloc n) ∪ r)); eauto using not_elem_of_dom.
    do 2 f_equal. auto_locs. set_solver. }
Qed.

Lemma atomic_step_alloc_size t g σ t' g' σ' efs n :
  IsAlloc n t ->
  atomic_step t g σ t' g' σ' efs ->
  size_heap sz σ' = size_heap sz σ + sz (Z.to_nat n).
Proof.
  intros Hsz. induction 1; subst.
  { eauto using IsAlloc_fill_item_inv,atomic_step_no_val. }
  inversion Hsz; subst; last first.
  { exfalso. eapply head_step_conc_no_ctx; eauto using IsAlloc_no_val. }
  inversion H; subst. inversion H0; subst. inversion H4; subst n0.
  unfold size_heap. rewrite map_fold_insert; eauto.
  { f_equal. simpl. rewrite replicate_length //. }
  { intros. lia. }
Qed.

Lemma atomic_step_alloc_no_fork n t g σ t' g' σ' efs :
  IsAlloc n t ->
  atomic_step t g σ t' g' σ' efs ->
  efs=None.
Proof.
  intros Hsz. induction 1; subst.
  { eauto using IsAlloc_fill_item_inv,atomic_step_no_val. }
  inversion Hsz; subst; last first.
  { exfalso. eapply head_step_conc_no_ctx; eauto using IsAlloc_no_val. }
  by inversion H.
Qed.

Lemma atomic_step_alloc_cangc n t g σ t' g' σ' efs :
  IsAlloc n t ->
  atomic_step t g σ t' g' σ' efs ->
  g = Out /\ g'=Out.
Proof.
  intros Hsz. induction 1; subst.
  { eauto using IsAlloc_fill_item_inv,atomic_step_no_val. }
  inversion Hsz; subst; last first.
  { exfalso. eapply head_step_conc_no_ctx; eauto using IsAlloc_no_val. }
  inversion H; subst. by inversion H0.
Qed.

Lemma locs_middle  t g (l1 l2:list (tm*status)) :
  locs (l1 ++ (t,g)::l2).*1 = locs t ∪ (locs l1.*1 ∪ locs l2.*1).
Proof.
  auto_locs. rewrite !fmap_app !fmap_cons union_list_app_L. simpl. set_solver.
Qed.

Lemma atomic_step_fork_inv_size e g σ e' g' σ' t :
  atomic_step e g σ e' g' σ' (Some t) ->
  tm_size e' + tm_size t < tm_size e.
Proof.
  intros Hstep. remember (Some t) as St. revert t HeqSt.
  induction Hstep; subst; intros ? ->.
  { pose proof (tm_size_ctx_lt E t1). pose proof (tm_size_ctx_lt E t2).
    specialize (IHHstep _ eq_refl). destruct E; simpl; try lia.
    rewrite !fmap_app !list_sum_app. simpl. lia. }
  { inversion H; subst. simpl. lia. }
Qed.

Lemma NotWillNeed ms σ t:
  ¬ AllocFits sz ms σ t ->
  NeedGC sz ms σ t.
Proof.
  intros Hw.
  destruct_decide (decide (NeedGC sz ms σ t)) as Hn; try done.
  exfalso. eapply Hw. by eapply NotNeedWill.
Qed.

Lemma safe_gc ms ts σ :
  AllOut ts ->
  (forall ts' σ', AllOut ts' -> step_oblivious (ts,σ) (ts',σ') -> live_heap_size sz (locs ts'.*1) σ' <= ms) ->
  all_not_stuck ts σ ->
  EveryAllocFits sz ms (ts, (collect (locs ts.*1) σ)).
Proof.
  intros Hcan E1 E2. apply Forall_forall. intros t Ht.
  apply elem_of_list_fmap_2 in Ht.
  destruct Ht as ((t',g)&->&Ht).
  intros n Ha.
  edestruct E2 as [(?&?)| X]; try done.
  { exfalso. apply IsAlloc_no_val in Ha. rewrite Ha in H. by inversion H. }
  rename t' into t.
  destruct X as (t'&σ'&g'&efs&Hstep).
  assert (efs=None) by eauto using atomic_step_alloc_no_fork. subst efs.
  apply elem_of_list_lookup in Ht. destruct Ht as (i&Htg).
  assert (exists l1 l2, ts = l1 ++ (t,g)::l2) as (l1&l2&Hts2).
  { do 2 eexists. symmetry. apply take_drop_middle. done. }
  assert (step_oblivious (ts,σ) (l1 ++ (t',g')::l2,σ')) as Hstep'.
  { subst ts. eapply StepAtomic; eauto. rewrite right_id //. }
  subst. apply E1 in Hstep'.
  2:{ rewrite AllOut_app AllOut_cons in Hcan. rewrite AllOut_app AllOut_cons.
      eapply atomic_step_alloc_cangc in Hstep; eauto. naive_solver. }
  simpl in *. subst.
  rewrite locs_middle in Hstep'. rewrite locs_middle.
  erewrite atomic_step_alloc_size_gc in Hstep'; eauto.
  unfold available, live_heap_size in *. lia.
Qed.


Lemma elem_of_list_lt {A:Type} (l:list A) i :
  i < length l ->
  exists x, l !! i = Some x.
Proof.
  revert l. induction i; intros l; intros Hl.
  all:destruct l; simpl in Hl; first lia.
  { eexists _. reflexivity. }
  { apply Nat.succ_lt_mono in Hl.
    apply IHi in Hl. destruct Hl.
    eexists. simpl. done. }
Qed.

Lemma willfit_weak ms r σ' σ t :
  gc r σ σ' →
  AllocFits sz ms σ t ->
  AllocFits sz ms σ' t.
Proof.
  intros Hgc Hwill n Ha.
  apply Hwill in Ha.
  apply gc_non_size_increasing with (sz:=sz)in Hgc.
  unfold available in *. lia.
Qed.

Lemma allwillfit_weak ms r σ' σ ts :
  gc r σ σ' →
  EveryAllocFits sz ms (ts,σ) ->
  EveryAllocFits sz ms (ts,σ').
Proof.
  intros ?. apply List.Forall_impl. eauto using willfit_weak.
Qed.

Lemma enabled_gc ms r σ σ' ts π :
  gc r σ σ' ->
  Enabled sz ms (Thread π) (ts, σ) ->
  Enabled sz ms (Thread π) (ts, σ').
Proof.
  intros Hgc (?&?&?&?&?).
  eexists _,_. eauto 15 using willfit_weak,allwillfit_weak.
Qed.

Lemma reducible_gc_insensitive ms r t g σ σ' π ts :
  locs t ⊆ r ->
  gc r σ σ' ->
  ts !! π = Some (t, g) ->
  Enabled sz ms (Thread π) (ts, σ') ->
  reducible.reducible t g σ ->
  Reducible ms (Thread π) (ts, σ').
Proof.
  intros ? ? ? ? (?&?&?&?&?).
  edestruct atomic_step_gc_insensitive2; try done.
  eexists. split. eauto. by econstructor.
Qed.

Lemma six_four ms ts σ σ' π t g:
  Enabled sz ms (Thread π) (ts, σ') ->
  gc (locs ts.*1) σ σ' ->
  all_not_stuck ts σ ->
  ts !! π = Some (t,g) ->
  NotStuck ms (Thread π) (ts, σ').
Proof.
  intros ? Hgc Hall Htg.
  assert ((t,g) ∈ ts) as Htg' by eauto using elem_of_list_lookup_2.
  destruct (Hall t g Htg').
  { left. naive_solver. }
  { right.
    eapply (reducible_gc_insensitive ms (locs ts.*1)); try done.
    auto_locs. apply elem_of_middle in Htg. destruct Htg as (?&?&?&?). subst.
    rewrite !fmap_app !fmap_cons union_list_app union_list_cons. set_solver. }
Qed.

Lemma deduce_gns ms ts σ σ' :
  gc (locs ts.*1) σ' σ ->
  all_not_stuck ts σ' ->
  (forall ts' σ, AllOut ts' → step_oblivious (ts, σ') (ts', σ) → live_heap_size sz (locs ts'.*1) σ ≤ ms) ->
  Gns ms (ts,σ).
Proof.
  intros Hgc Hs1 Hs2 Hall Hne.
  exists (collect (locs ts.*1) σ).
  split. apply gc_collect.
  eapply allwillfit_weak.
  { apply gc_collect_2. done.  }
  eapply safe_gc; eauto.
Qed.

Lemma all_not_stuck_aapao θ σ' σ :
  all_not_stuck θ σ' ->
  Aapao (θ, σ).
Proof.
  intros Hall t g Htg HP.
  apply Hall in Htg.
  destruct g; try done. exfalso.
  destruct Htg as [(?&?)|(?&?&?&?&Htg)]. naive_solver.
  destruct HP as [|(?&?)].
  by eapply atomics_step_false_not_poll in Htg.
  by eapply atomics_step_false_not_alloc in Htg.
Qed.

Lemma wp_strong_safety (ms:nat) (t:tm) :
  locs t = ∅ ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t (fun _ => outside π)) ->
  Always (step_main sz ms) (init t) (StronglySafe ms).
Proof.
  intros ? Hwp (ts,σ) Hsteps.
  apply main_to_oblivious in Hsteps. destruct Hsteps as (?&Hsteps&Hgc).
  assert (all_not_stuck ts x) as Hs.
  { by eapply wp_adequacy_core; eauto. }
  split_and !.
  { eauto using all_not_stuck_aapao. }
  { eapply deduce_gns; eauto.
    intros ????.
    eapply wp_adequacy_core; eauto.
    by eapply rtc_r. }
  { intros π Hwf. generalize Hwf. intros ?.
    destruct Hwf as (t'&g'&Htg&_).
    eapply six_four; done. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Towards [strongly_safe_globally_not_stuck] *)

Lemma was_gc ms θ σ ρ :
  ¬ EveryAllocFits sz ms (θ,σ) ->
  step_main sz ms (θ, σ) ρ ->
  (∀ t, t ∈ θ.*1 → NeedGC sz ms σ t ∨ IsPoll t) ->
  exists σ', ρ = (θ,σ') /\ gc (locs θ.*1) σ σ' /\ σ ≠ σ'.
Proof.
  intros W (c&Henabled&Hstep) Hyp.
  inversion Hstep.
  { subst. simpl in Henabled.
    destruct Henabled as (t0&g0&?&E1&E2).
    assert (t0=t /\ g0=g) as (->&->) by naive_solver.
    destruct (Hyp t).
    { apply elem_of_list_fmap. exists (t,g). split. done. eauto using elem_of_list_lookup_2. }
    { destruct H0 as (?&Ha&?). apply E1 in Ha. lia. }
    { naive_solver. } }
  { naive_solver. }
Qed.


Lemma AllWillWill ms θ σ t π (g:status) :
  θ !! π = Some (t,g) ->
  EveryAllocFits sz ms (θ,σ) -> AllocFits sz ms σ t.
Proof.
  intros X E. eapply (Forall_lookup_1 _ _ π); eauto.
  rewrite list_lookup_fmap X //.
Qed.

Lemma atomic_step_alloc_size_gc' t σ  σ' n θ g i θ' :
  θ !! i = Some (t,g) ->
  IsAlloc n t ->
  step_action (Thread i) (θ, σ) (θ',σ') ->
  live_heap_size sz (locs θ'.*1) σ' = live_heap_size sz (locs θ.*1) σ + sz (Z.to_nat n).
Proof.
  intros Hi ? Hstep.
  inversion Hstep. subst.
  assert (t0=t /\ g0=g) as (->&->) by naive_solver.
  assert (exists l1 l2, θ = l1 ++ (t,g)::l2 /\ length l1 = i) as (l1&l2&Hts2&?).
  { do 2 eexists. split. symmetry. apply take_drop_middle. done.
    rewrite take_length. apply lookup_lt_Some in H5. lia. }
  subst. rewrite -(right_id_L _ _ (length l1)) insert_app_r. simpl.
  assert (efs=None) as ->.
  { by eapply atomic_step_alloc_no_fork. }
  rewrite right_id_L.
  rewrite !locs_middle.
  eapply atomic_step_alloc_size_gc. done. done.
Qed.

Lemma need_untouched θ σ θ' σ' t g ms π :
  θ !! π = Some (t, g) ->
  NeedGC sz ms σ t ->
  step_main sz ms (θ, σ) (θ', σ') ->
  θ' !! π = Some (t,g).
Proof.
  intros E1 E2 (c&X&Hc).
  inversion Hc; subst; last done.
  rewrite lookup_app_l.
  2:{ rewrite insert_length. eauto using lookup_lt_Some. }
  rewrite list_lookup_insert_ne //. intros ->.
  assert (t0=t /\ g0=g) as (->&->) by naive_solver.
  destruct X as (t0&g0&X1&X2&_).
  assert (t0=t /\ g0=g) as (->&->) by naive_solver.
  destruct E2 as (?&E2&?).
  apply X2 in E2. lia.
Qed.

Lemma IsAllocPoll n t :
  IsAlloc n t ->
  IsPoll t ->
  False.
Proof.
  induction 1.
  { inversion 1. destruct E; try done. inversion H0.
    subst. eapply IsPoll_no_val in H1. done. }
  { inversion 1. by destruct E.
    apply fill_item_inj in H1; eauto using IsAlloc_no_val,IsPoll_no_val.
    naive_solver. }
Qed.

Lemma step_gc_length ms θ σ θ' σ' :
  step_main sz ms (θ, σ) (θ', σ') ->
  length θ <= length θ'.
Proof.
  intros (?&?&Hstep).
  inversion Hstep; subst; last lia.
  rewrite app_length insert_length. lia.
Qed.

Definition is_val (t:tm) :=
  match t with
  | tm_val _ => true
  | _ => false end.

Lemma allvalwillfit ms σ θ :
  Forall is_val θ.*1 ->
  EveryAllocFits sz ms (θ,σ).
Proof.
  apply List.Forall_impl.
  intros []; try done. intros ?? Ha. exfalso.
  eapply IsAlloc_no_val in Ha. simpl in Ha. congruence.
Qed.


Lemma EveryAllocFits_enabled ms π θ σ :
  π < length θ ->
  EveryAllocFits sz ms (θ,σ) ->
  Enabled sz ms (Thread π) (θ,σ).
Proof.
  intros Hπ Hall.
  apply elem_of_list_lt in Hπ.
  destruct Hπ as ((t,g)&Hπ).
  eexists _,_. split_and !; eauto using AllWillWill.
Qed.

Lemma ended_no_val θ σ π t g :
  θ !! π = Some (t, g) ->
  Ended (Thread π) (θ, σ) ->
  is_val t.
Proof.
  intros ? (?&?&?&(?&?)&?). destruct t; naive_solver.
Qed.

Lemma not_all_outside_exists ms θ σ :
  ¬ AllOut θ ->
  Aapao (θ, σ) ->
  (∀ π, Enabled sz ms (Thread π) (θ, σ) → NotStuck ms (Thread π) (θ, σ)) ->
  ∃ c, step_main sz ms (θ, σ) c.
Proof.
  intros Hout Haaa Hall.
  apply neg_Forall_Exists_neg in Hout.
  2:{ destruct x. by right. by left. }
  apply Exists_exists in Hout.
  destruct Hout as (g&Hg&Hout).
  apply elem_of_list_fmap in Hg.
  destruct Hg as ((t&g')&Eq&Htg). simpl in Eq. subst g'. generalize Htg. intros X.
  apply elem_of_list_lookup in Htg. destruct Htg as (π&Hπ).
  assert (NotStuck ms (Thread π) (θ,σ)) as Hne.
  { apply Hall.
    apply Haaa in X.
    eexists _,_. split_and !; try done.
    { intros ??. naive_solver. }
    { naive_solver. } }
  destruct Hne. naive_solver. destruct H. eexists _. exists (Thread π). done.
Qed.

Lemma strongly_safe_globally_not_stuck ms θ σ :
  StronglySafe ms (θ, σ) ->
  ¬ Forall (λ t : tm, is_val t) θ.*1 ->
  exists c, step_main sz ms (θ,σ) c.
Proof.
  intros (X1&X2&X3) Hne.
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
    apply X3 in Hen. destruct Hen as [X|X].
    { exfalso. eauto using ended_no_val. }
    destruct X. eexists _, (Thread π). done. }
  destruct_decide (decide (AllOut θ)) as Hout.
  { edestruct X2 as (σ'&?&?); eauto.
    exists (θ,σ'). exists GC. assert (step_action GC (θ, σ) (θ, σ')).
    { constructor. done. naive_solver. }
    split. simpl. naive_solver. done. }
  { eauto using not_all_outside_exists. }
Qed.

End WithSize.
