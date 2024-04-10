From stdpp Require Import gmap fin_map_dom gmultiset.
From iris.algebra Require Import dfrac gset gmap auth.

From irisfit.lib Require Import qz qz_cmra smultiset disc.
From irisfit.spacelang Require Import predecessors hypotheses.
From irisfit.language Require Import language.
From irisfit.program_logic Require Import image more_maps_and_sets closed.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* linked *)

Definition valid_roots (r:gset loc) (τ :store) :=
  ∀ l, l ∈ r -> ¬ freed τ l.

Definition same_or_dead (θ τ:store) :=
  forall l b1 b2,
    θ !! l = Some b1 -> τ !! l = Some b2 -> (b1 = b2) ∨ b2 = BDeallocated.

Definition no_succ_freed (τ:store) :=
  forall l l', successor τ l l' -> ¬ freed τ l'.

Record linked (r:gset loc) (θ τ:store) :=
  { linked_dom : dom θ = dom τ;
    linked_inv : same_or_dead θ τ;
    linked_nrf : no_succ_freed τ;
    linked_roo : valid_roots r τ
  }.

Lemma linked_weak r1 r2 θ τ :
  r2 ⊆ r1 ->
  linked r1 θ τ ->
  linked r2 θ τ.
Proof.
  intros ? [??? C]. constructor; eauto. intros ? ?. eapply C. set_solver.
Qed.

Lemma linked_shift1 k η l1 l2 π L2 lk θ τ :
  l2 = dom L2 ->
  k !! π = Some (lk, l1 ∪ l2) ->
  linked (image_less η k) θ τ ->
  linked (image_less η (<[π:=(lk ⋅ L2, l1)]> k)) θ τ.
Proof.
  intros -> Hπ [E1 E2 E3 E4].
  constructor; eauto.
  intros l. rewrite elem_of_image_less.
  intros (π'&(lk'&ls')&H1&H2).
  rewrite lookup_insert_case in H1. case_decide; subst.
  2:{ eapply E4; eauto. eapply elem_of_image_less. eauto. }
  inversion H1; subst.  unfold xroot_less in *.
  rewrite dom_op in H2. simpl in *.
  eapply E4; eauto. eapply elem_of_image_less.
  do 2 eexists. split; first done. simpl.
  unfold xroot_less. simpl. set_solver.
Qed.


Lemma linked_shift2 η k θ τ lk l1 l2 π L2 :
  dom L2 = l2 ->
  k !! π = Some (lk ⋅ L2, l1) ->
  linked (image_less η k) θ τ ->
  linked (image_less η (<[π:=(lk, l1 ∪ l2)]> k)) θ τ.
Proof.
  intros <- Hk [E1 E2 E3 E4]. constructor; eauto.
  intros l. rewrite elem_of_image_less. intros (π'&(?&?)&Hl&?).
  eapply E4; eauto. eapply elem_of_image_less.
  rewrite lookup_insert_case in Hl. case_decide; eauto; subst.
  { inversion Hl; subst. do 2 eexists.
    split; first done. unfold xroot_less in *. simpl. rewrite dom_op.
    set_solver. }
Qed.

Lemma successor_not_freed τ l l' :
  successor τ l l' ->
  ¬ freed τ l.
Proof.
  intros E1 Hl.
  rewrite -successor_to_rstore // in E1.
  set_solver.
Qed.

Lemma closed_linked r θ τ :
  closed r θ ->
  linked r θ τ ->
  closed r τ.
Proof.
  intros [E1 E2] [X1 X2 X3 X4].
  split. set_solver.
  intros l l' Hs. rewrite -X1.
  apply E2 with l.
  assert (is_Some (τ !! l)) as (b1,H1).
  { apply elem_of_dom. eauto using successor_in_dom. }
  assert (is_Some (θ !! l)) as (b2,H2).
  { apply elem_of_dom. rewrite X1. eauto using successor_in_dom. }
  destruct b1.
  2:{ exfalso. by eapply successor_not_freed. }
  assert (b2 = BBlock l0) as ->.
  { unfold same_or_dead in *. naive_solver. }
  eapply successor_to_rstore in Hs; last done.
  by eapply successor_to_rstore.
Qed.

Lemma free_group_preserves_linked r locs θ τ :
  closed r θ ->
  locs ⊆ dom τ ->
  locs ∩ r = ∅ ->
  (∀ m m' : loc, m' ∈ successors τ m → m' ∈ locs → m ∈ locs) ->
  linked r θ τ ->
  linked r θ (hypotheses.deallocate locs τ).
Proof.
  intros Hclo Hd Hr Hfact Hl.
  destruct (closed_linked Hclo Hl) as [_ Hclo']; eauto.
  clear Hclo. destruct Hl as [X1 X2 X3 X4].
  constructor.
  { apply leibniz_equiv. rewrite dom_deallocate X1 //. }
  { intros l x1 x2 Hl Hl'.
    destruct_decide (decide (l∈ locs)).
    { rewrite /deallocate stdpp.gmap_lookup_mset_inside // in Hl'.
      { inversion Hl'. subst. destruct x1; eauto. }
      rewrite -X1 elem_of_dom //. }
    { rewrite /deallocate stdpp.gmap_lookup_mset_outside // in Hl'.
      eapply X2; eauto. } }
  { intros l l' Hl Hl'.
    destruct_decide (decide (l ∈ locs)).
    { exfalso. unfold successor in Hl.
      rewrite successors_deallocate_inside in Hl; set_solver. }
    apply successor_deallocate_outside in Hl; eauto.
    assert (l' ∉ locs) by naive_solver.
    apply freed_deallocate in Hl'. apply X3 in Hl. naive_solver. }
  { intros l Hl. assert (l ∉ locs) by set_solver.
    rewrite /freed /deallocate stdpp.gmap_lookup_mset_outside //.
    eauto. }
Qed.

Lemma use_successor θ x y :
  successor θ x y ->
  exists bs, θ !! x = Some (BBlock bs) /\ y ∈ locs bs.
Proof.
  intros Hx.
  assert (is_Some (θ !! x)) as (bs&Hbs).
  { apply elem_of_dom. eauto using successor_in_dom. }
  eapply successor_to_rstore in Hx; last done.
  destruct bs.
  2:{ exfalso. set_solver. }
  eexists. split; first done. by eapply pointers_locs.
Qed.

Lemma linked_reachable_not_freed l r τ :
  no_succ_freed τ ->
  valid_roots r τ ->
  reachable r τ l ->
  ¬ freed τ l.
Proof.
  intros X1 X2 (l0&Hl0&Hr).
  apply rtc_inv_r in Hr.
  destruct Hr as [->|(?&_&Hr)].
  { apply X2 in Hl0. naive_solver. }
  { apply X1 in Hr. naive_solver. }
Qed.

Lemma linked_preserves_reachable r θ τ :
  r ⊆ dom θ ->
  linked r θ τ ->
  (forall l, reachable r θ l <-> reachable r τ l).
Proof.
  intros Hr [E1 E2 E3 E4] l.
  split.
  { intros (l0&?&?). exists l0. split; first done.
    assert (reachable r τ l0).
    { exists l0. eauto using rtc_refl. }
    clear H.

    induction H0; eauto using rtc_refl.

    destruct (use_successor H) as (b1,(X1&X2)).
    assert (is_Some (τ !! x)) as (b2&X3).
    { apply elem_of_dom. rewrite -E1. eauto using successor_in_dom. }
    unfold same_or_dead in E2.
    eapply E2 in X1; last done. destruct X1 as [|]; subst; last first.
    { exfalso. eapply linked_reachable_not_freed; eauto. }

    eapply rtc_l with y.
    { eapply successor_to_rstore. done. by eapply pointers_locs. }
    apply IHrtc. destruct H1 as (l'&Hl'&?).
    eexists. split; first done.
    eapply rtc_r; first done.
    { eapply successor_to_rstore. done. by eapply pointers_locs. } }
  { intros (l0&?&?).
    exists l0. split; first done. clear H.
    induction H0. apply rtc_refl.
    eapply rtc_l; last done.
    assert (is_Some (τ !! x)) as (b2&X3).
    { apply elem_of_dom. eauto using successor_in_dom. }
    assert (is_Some (θ !! x)) as (b1&X4).
    { apply elem_of_dom. rewrite E1. eauto using successor_in_dom. }
    apply use_successor in H. destruct H as (?&?&?).
    edestruct E2; try done; subst; last naive_solver.
    rewrite H in X3. inversion X3. subst.
    eapply successor_to_rstore. done. by eapply pointers_locs. }
Qed.

Section WithSize.
Context (sz:nat -> nat).

Definition live_heap_size r σ := size_heap sz (collect r σ).

Lemma lookup_collect r σ l x:
  collect r σ !! l = Some x ->
  ∃ x', σ !! l = Some x' /\ x = if (decide (reachable r σ l)) then x' else BDeallocated.
Proof.
  rewrite /collect map_lookup_imap /collect_block.
  destruct (σ !! l) eqn:E; inversion 1. case_decide; eauto.
Qed.

Lemma linked_size_heap r θ τ :
  r ⊆ dom θ ->
  linked r θ τ ->
  live_heap_size r θ = live_heap_size r τ.
Proof.
  intros Hr Hlink.
  eapply stdpp.map_fold_ind_2 with (P:= fun x1 x2 _ _ => x1 = x2).
  all:intros; try lia.
  { rewrite -!not_elem_of_dom !dom_collect (linked_dom Hlink) //. }
  { subst. apply lookup_collect in H1,H2.
    destruct H1 as (?&H11&H12). destruct H2 as (?&H21&H22).
    case_decide as E.
    { rewrite decide_True in H12; subst.
      2:{ by eapply linked_preserves_reachable. }
      edestruct (linked_inv Hlink i) ; try done; subst. lia.
      subst. exfalso. destruct Hlink.
      eapply linked_reachable_not_freed; eauto. }
    { rewrite decide_False in H12; subst.
      2:{ intros X. apply E. eapply linked_preserves_reachable in Hlink. naive_solver. done. }
      done. } }
Qed.

End WithSize.
