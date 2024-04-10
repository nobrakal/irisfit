From stdpp Require Import sets mapset gmap relations gmultiset.
From iris.program_logic Require Import language.

From irisfit.spacelang Require Import stdpp hypotheses.
From irisfit Require Import successors store pointers.

Set Implicit Arguments.

(* This file defines garbage collection in irisfit.
   Most of the work is done in [successors.v]. *)

(* ------------------------------------------------------------------------ *)

(* XXX I should move store evolution here, rename it into "gc",
   and call this file "gc_more".
 *)
Definition gc : gset loc -> store -> store -> Prop :=
  store_evolution.

Local Hint Unfold gc : core.

(* ------------------------------------------------------------------------ *)
(* Basic lemmas about [gc] *)

(* The GC may have no effect. *)
Lemma gc_id r σ :
  gc r σ σ.
Proof. apply store_evolution_reflexive. Qed.

(* The GC is transitive. *)
Lemma gc_trans r σ1 σ2 σ3 :
  gc r σ1 σ2 ->
  gc r σ2 σ3 ->
  gc r σ1 σ3.
Proof. apply store_evolution_transitive. Qed.

(* gc preserves domain *)
Lemma gc_dom r σ1 σ2 :
  gc r σ1 σ2 ->
  dom σ1 = dom σ2.
Proof. by intros []. Qed.

Lemma gc_empty_inv r σ :
  gc r ∅ σ ->
  σ = ∅.
Proof.
  intros Hgc.
  apply gc_dom in Hgc. rewrite dom_empty_L in Hgc.
  apply dom_empty_iff.
  rewrite Hgc //.
Qed.

(* ------------------------------------------------------------------------ *)
(* We want to derive [gc_weak]. We have to work a bit. *)

Lemma rtc_successors_successor σ σ' r d :
  (forall l, successors σ l = successors σ' l) ->
  rtc (successor σ) r d ->
  rtc (successor σ') r d.
Proof.
  intros Hs.
  eapply rtc_subrel. intros.
  unfold successor in *.
  by rewrite -Hs.
Qed.

(* We can weaken a set of roots. *)
(* Order of arguments helps proof search *)
Lemma gc_weak r1 r2 σ σ' :
  gc r2 σ σ' ->
  r1 ⊆ r2 ->
  gc r1 σ σ'.
Proof.
  unfold gc, store_evolution.
  intros [? Hr] ?.
  split; try easy.
  intros ? Hl.
  destruct (Hr _ Hl) as [?|(?&?)];
    [by left|right; eauto using reachable_mono_roots].
Qed.

(* ------------------------------------------------------------------------ *)
(* GC does not increase size. *)

Lemma block_evolution_non_size_increasing sz unreachable (b b':block) :
  block_evolution unreachable b b' →
  size_block sz b' ≤ size_block sz b.
Proof.
  destruct 1 as [ | (? & ?) ]; subst; compute; lia.
Qed.

Lemma gc_non_size_increasing sz r σ σ' :
  gc r σ σ' ->
  size_heap sz σ' ≤ size_heap sz σ.
Proof.
  intros [Hdom Hl].
  rewrite /size_heap.
  eapply map_fold_ind_2 with (P := λ size1 size2 m1 m2, size1 ≤ size2); try lia.
  { intros. rewrite -!not_elem_of_dom Hdom //. }
  { intros l b1 b2 s1 s2 size1 size2 _ _ Hindom1 Hindom2 ?.
    assert (l ∈ dom σ) as Hlh.
    { erewrite elem_of_dom, Hindom2. eauto. }
    specialize (Hl l).
    specialize (Hl Hlh).
    apply block_evolution_non_size_increasing with (sz:=sz) in Hl.
    do 2 (erewrite lookup_total_correct in Hl; eauto).
    lia. }
Qed.

(* ------------------------------------------------------------------------ *)

Lemma gc_read_root l bs r σ σ' :
  l ∈ r ->
  gc r σ σ' ->
  σ !! l = Some (BBlock bs) ->
  σ' !! l = Some (BBlock bs).
Proof.
  intros Hl [Hr1 Hr2] Hb.
  assert (l ∈ dom σ) as Hlr.
  { apply elem_of_dom. rewrite Hb. easy. }
  apply Hr2 in Hlr.

  assert (reachable r σ l) as Hlr'.
  { eauto using roots_are_reachable. }

  destruct Hlr as [Hlr|]; try easy.
  rewrite !lookup_total_alt in Hlr.
  rewrite Hb in Hlr. simpl in Hlr.
  destruct (σ' !! l); naive_solver.
Qed.

Lemma gc_preserves_reachable σ r σ' l :
  gc r σ σ' ->
  reachable r σ' l ->
  reachable r σ l.
Proof.
  intros [].
  apply store_evolution_preserves_reachable; try easy.
Qed.

Lemma successor_to_rstore s l l' bs :
  s !! l = Some bs ->
  l' ∈ pointers bs <-> successor s l l'.
Proof.
  intros Hbs.
  rewrite /successors /successor /successors  Hbs.
  simpl. done.
Qed.

Lemma prove_not_reachable_group r locs σ :
  locs ⊆ dom σ ->
  locs ∩ r = ∅ ->
  (∀ m m' : loc, m' ∈ successors σ m → m' ∈ locs → m ∈ locs) ->
  forall l, l ∈ locs -> ¬ reachable r σ l.
Proof.
  intros ? ? Hc.
  eapply prove_unreachable_region; eauto; set_solver.
Qed.

Lemma prove_not_reachable r l σ :
  l ∈ dom σ ->
  l ∉ r -> (* l not a root *)
  (∀ m, l ∈ successors σ m → m = l) -> (* l is its only succ. *)
  ¬ reachable r σ l.
Proof.
  intros ? ? Hl.
  apply prove_not_reachable_group with (locs:={[l]} : gset loc).
  1,2,4:set_solver.
  intros ? l' E ?.
  assert (l' = l) by set_solver. subst.
  apply Hl in E. set_solver.
Qed.

Lemma gc_read_reachable l r σ σ' :
  closed r σ ->
  gc r σ σ' ->
  reachable r σ l ->
  σ' !! l = σ !! l.
Proof.
  intros Hclo Hgc Hl. generalize Hgc. intros [Hr1 Hr2].
  assert (l ∈ dom σ) as Hd.
  { eauto using closed_reachable_in_dom. }
  assert (l ∈ dom σ').
  { rewrite -Hr1 //. }

  apply Hr2 in Hd. destruct Hd as [Hd|Hd]; try easy.
  rewrite !lookup_total_alt in Hd.
  destruct (σ !! l) eqn:E1, (σ' !! l) eqn:E2; simpl in *; try easy.
  { naive_solver.  }
  { exfalso. by apply not_elem_of_dom in E2. }
  { apply not_elem_of_dom in E1. set_solver. }
Qed.

Lemma gc_free_group (r:gset loc) locs σ :
  locs ∩ r = ∅ ->
  locs ⊆ dom σ ->
  (∀ m m' : loc, m' ∈ successors σ m → m' ∈ locs → m ∈ locs) ->
  gc r σ (deallocate locs σ).
Proof.
  constructor.
  { apply leibniz_equiv. rewrite dom_gmap_mset. set_solver. }
  intros l'. intros Hl'. simpl.
  destruct (decide (l' ∈ locs)); subst.
  { right. split.
    { eapply prove_not_reachable_group; eauto. }
    { rewrite lookup_total_alt.
      rewrite gmap_lookup_mset_inside; eauto. } }
  left.
  do 2 rewrite lookup_total_alt.
  rewrite gmap_lookup_mset_outside; eauto.
Qed.

Lemma gc_free (r:gset loc) l σ :
  l ∉ r ->
  l ∈ dom σ ->
  (∀ m, l ∈ successors σ m → m = l) ->
  gc r σ (<[l:=BDeallocated]> σ).
Proof.
  intros Hl.
  constructor.
  { rewrite dom_insert_L. set_solver. }
  intros l'. intros Hl'. simpl.
  destruct (decide (l=l')); subst.
  { right.
    rewrite lookup_total_insert.
    eauto using prove_not_reachable. }
  left. by rewrite lookup_total_insert_ne.
Qed.

(* ------------------------------------------------------------------------ *)
(* GC basically preserves everything. *)

Lemma gc_preserves_valid_store sz maxsize r σ σ' :
  gc r σ σ' ->
  valid_store sz maxsize σ ->
  valid_store sz maxsize σ'.
Proof.
  unfold valid_store.
  intros Hgc. generalize Hgc. intros.
  intros. transitivity (size_heap sz σ); try easy.
  eauto using gc_non_size_increasing.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma gc_collect r σ :
  gc r σ (collect r σ).
Proof.
  unfold gc.
  apply store_evolution_collect.
Qed.

Lemma gc_preserves_reachable' σ r σ' l :
  gc r σ σ' ->
  reachable r σ l ->
  reachable r σ' l.
Proof.
  intros X. eapply store_evolution_preserves_reachable in X. naive_solver.
Qed.

Lemma reachable_collect r σ l :
  reachable r (collect r σ) l ->
  reachable r σ l.
Proof.
  apply gc_preserves_reachable. apply gc_collect.
Qed.

Lemma gc_collect_2 r σ σ' :
  gc r σ σ' ->
  gc r (collect r σ) (collect r σ').
Proof.
  intros E. generalize E. intros E'. destruct E as [Hd Hgc].
  constructor.
  { rewrite !dom_collect //. }
  { rewrite dom_collect => l Hl.
    assert (is_Some (σ !! l)) as (b&Hb).
    { by apply elem_of_dom. }
    assert (is_Some (σ' !! l)) as (b'&Hb').
    { apply elem_of_dom. set_solver. }
    apply Hgc in Hl. destruct Hl as [Hl|(X&Hl)].
    { left. rewrite !lookup_total_alt Hb Hb' in Hl. simpl in Hl. subst.
      rewrite /collect !lookup_total_alt !map_lookup_imap Hb Hb'. simpl.
      destruct_decide (decide ((reachable r σ' l))).
      { eapply gc_preserves_reachable in H; eauto. rewrite decide_True //. }
      { rewrite decide_False //.  intros ?. apply H. eauto using gc_preserves_reachable'. } }
    { right. split.
      { intros ?. apply X. eauto 15 using reachable_collect. }
      { rewrite lookup_total_alt /collect map_lookup_imap Hb'. simpl.
        rewrite decide_False //. intros ?. eauto using gc_preserves_reachable. } } }
Qed.

(* ------------------------------------------------------------------------ *)
(* GC has the diamond property. *)

Lemma gc_pursue_collect r σ1 σ2 :
  gc r σ1 σ2 ->
  gc r σ2 (collect r σ1).
Proof.
  intros ?.
  split; now apply store_evolution_collect_strong.
Qed.
