From stdpp Require Import gmap gmultiset.
From iris.prelude Require Import prelude.

From irisfit.spacelang Require Import stdpp hypotheses predecessors.

From irisfit Require Import syntax store.

(* ------------------------------------------------------------------------ *)
(* We will work with multiset. *)

Definition val_pointer_multiset v : gmultiset loc :=
  list_to_set_disj (val_pointer_list v).

(* ------------------------------------------------------------------------ *)
(* Immediate consequences of the definitions. *)

Lemma pointers_def b :
  pointers b = block_pointer_set b.
Proof.
  reflexivity.
Qed.

Lemma block_pointer_list_cons v vs :
  block_pointer_list (BBlock (v :: vs)) =
  val_pointer_list v ++ block_pointer_list (BBlock vs).
Proof.
  reflexivity.
Qed.

Lemma block_pointer_cons v vs :
  block_pointer_set (BBlock (v :: vs)) =
  val_pointer_multiset v ⊎ block_pointer_set (BBlock vs).
Proof.
  rewrite /block_pointer_set block_pointer_list_cons list_to_set_disj_app //.
Qed.

Lemma block_pointer_app vs vs' :
  block_pointer_set (BBlock (vs ++ vs')) =
    block_pointer_set (BBlock vs) ⊎ block_pointer_set (BBlock vs').
Proof.
  rewrite /block_pointer_set /block_pointer_set.
  revert vs'. induction vs; intros vs'; simpl.
  { multiset_solver. }
  { rewrite list_to_set_disj_app IHvs // list_to_set_disj_app.
    multiset_solver. }
Qed.

Lemma val_pointer_multiset_loc l :
  val_pointer_multiset (val_loc l) = {[+l+]}.
Proof.
  rewrite /val_pointer_multiset. simpl. multiset_solver.
Qed.

Lemma val_pointer_multiset_loc_membership l :
  l ∈ val_pointer_multiset (val_loc l).
Proof.
  rewrite val_pointer_multiset_loc. set_solver.
Qed.

Global Hint Resolve
  val_pointer_multiset_loc
  val_pointer_multiset_loc_membership
: pointers.

(* ------------------------------------------------------------------------ *)

(* The relation [alias v w] means that the values [v] and [w] are both
   pointers, and are the same pointer. This relation is stronger than
   [v = w]. For our purposes below, both relations would work. It is
   easier to show that [same_location] is decidable, though, which is
   why we use it. *)

Definition alias v w :=
  match v, w with
  | val_loc l, val_loc m => l = m
  | _, _ => False
  end.

Global Instance decide_alias v w :
  Decision (alias v w).
Proof.
  destruct v, w; simpl; solve_decision.
Qed.

Lemma alias_implies_eq v w :
  alias v w → v = w.
Proof.
  destruct v, w; simpl; solve [ tauto | congruence ].
Qed.

Lemma alias_implies_equal_locations v w :
  alias v w → ∃ l, v = val_loc l ∧ w = val_loc l.
Proof.
  destruct v, w; simpl; try solve [ tauto ].
  intros. subst. eauto.
Qed.

(* If [v] and [w] are not aliased, then their sets of pointers are
   disjoint. The stronger hypothesis [v ≠ w] would work, too. *)

Lemma nonaliased_values_have_disjoint_pointer_sets v w :
  ~ alias v w →
  val_pointer_multiset v ∩ val_pointer_multiset w = ∅.
Proof.
  intros. destruct v, w; rewrite /val_pointer_multiset; simpl;
  try solve [ multiset_solver ].
Qed.

(* ------------------------------------------------------------------------ *)

(* If [v] is a field of the block [b], then the pointers of [v]
   form a subset of the pointers of [b]. *)

Lemma pointers_lookup vs : ∀ ofs v,
  vs !! ofs = Some v ->
  val_pointer_multiset v ⊆ pointers (BBlock vs).
Proof.
  intros ? ?  Hn.
  rewrite <- (take_drop_middle _ _ _ Hn).
  rewrite pointers_def block_pointer_app block_pointer_cons.
  multiset_solver.
Qed.

(* If [v] is a field of the block [b], then, when [v] is overwritten with [w],
   the pointers of the updated block are those of the block [b], minus the
   pointers of [v], plus the pointers of [w]. *)

Lemma pointers_store_preliminary w vs : ∀ ofs v,
    vs !! ofs = Some v ->
    pointers (BBlock (<[ ofs := w ]> vs)) ⊎ val_pointer_multiset v =
      pointers (BBlock vs) ⊎ val_pointer_multiset w.
Proof.
  induction vs as [| v vs ]; simpl; intros ? ? Hv.
  { rewrite lookup_nil in Hv. easy. }
  apply lookup_cons_Some in Hv. destruct Hv as [(?&->) | (?&?)];
    subst; simpl; rewrite !block_pointer_cons.
  { multiset_solver. }
  replace ofs with (S (ofs - 1)) by lia.
  simpl; rewrite !block_pointer_cons.
  rewrite -assoc IHvs; try easy.
  multiset_solver.
Qed.

Lemma pointers_store v w vs ofs :
  vs !! ofs = Some v ->
  pointers (BBlock (<[ ofs := w ]> vs)) =
  pointers (BBlock vs) ∖ val_pointer_multiset v ⊎ val_pointer_multiset w.
Proof.
  intros  Hv.
  pose proof (pointers_lookup vs ofs v Hv).
  pose proof (pointers_store_preliminary w vs ofs v Hv).
  multiset_solver.
Qed.

(* Two ad hoc lemmas used below. *)

Lemma adhoc_multiset_lemma_1 `{Countable A} (B V W : gmultiset A) :
  V ⊆ B →
  V ∩ W = ∅ →
  V ⊆ B ∖ (B ∖ V ⊎ W).
Proof.
  multiset_solver.
Qed.

Lemma adhoc_multiset_lemma_2 `{Countable A} (B V W : gmultiset A) :
  V ∩ W = ∅ →
  W ⊆ (B ∖ V ⊎ W) ∖ B.
Proof.
  multiset_solver.
Qed.

(* If [v] is a field of the block [b], and if [v] and [w] are not
   aliased, then, when [v] is overwritten with [w], the pointers that
   disappear because of this update are exactly the pointers of [v]. *)

Lemma old_pointers_store_nonaliased w v vs ofs :
  (0 <= ofs < length vs)%nat ->
  vs !! ofs = Some v →
  ~ alias v w →
  let b  := BBlock vs in
  let b' := BBlock (<[ ofs := w ]> vs) in
  old_pointers b b' = val_pointer_multiset v.
Proof.
  intros ? Hv Hne ? ?.
  rewrite /b /b' /old_pointers (pointers_store v) //.
  eapply (anti_symm (⊆)).
  (* This inclusion is easy and does not need [v ≠ w]. *)
  { clear Hne. multiset_solver. }
  (* This inclusion is trickier. *)
  { eapply adhoc_multiset_lemma_1;
    eauto using pointers_lookup,nonaliased_values_have_disjoint_pointer_sets. }
Qed.

(* If [v] is a field of the block [b], and if [v] and [w] are not aliased,
   then, when [v] is overwritten with [w], the pointers that appear because
   of this update are exactly the pointers of [w]. *)

Lemma new_pointers_store_nonaliased w v vs ofs :
  (0 <= ofs < length vs)%nat ->
  vs !! ofs = Some v →
  ~ alias v w →
  let b  := BBlock vs in
  let b' := BBlock (<[ ofs := w ]> vs) in
  new_pointers b b' = val_pointer_multiset w.
Proof.
  intros ? Hv Hne ? ?.
  rewrite /b /b' /new_pointers (pointers_store v) //.
  eapply (anti_symm (⊆)).
  (* This inclusion is easy and does not need [v ≠ w]. *)
  { clear Hne. multiset_solver. }
  (* This inclusion is trickier. *)
  { eapply adhoc_multiset_lemma_2.
    eauto using nonaliased_values_have_disjoint_pointer_sets. }
Qed.

(* A newly-allocated block, filled with unit values, has no pointers. *)

Lemma block_no_pointers n v b :
  b = BBlock (replicate n v) →
  val_pointer_list v = [] →
  pointers b = ∅.
Proof.
  intros Hb Hv.
  rewrite pointers_def Hb {Hb} /block_pointer_set.
  rewrite -list_to_set_disj_nil. f_equal.
  induction n.
  - eauto.
  - simpl replicate.
    rewrite block_pointer_list_cons.
    rewrite IHn Hv //.
Qed.

Lemma pointers_locs l bs :
  l ∈ locs bs <-> l ∈ pointers (BBlock bs).
Proof.
  induction bs; first set_solver.
  auto_locs. rewrite /location_list /locs_list block_pointer_cons.
  simpl.
  rewrite elem_of_union gmultiset_elem_of_disj_union -IHbs.
  destruct a; set_solver.
Qed.

Lemma locs_insert n v (bs:list val) :
  locs (<[n:=v]> bs) ⊆ locs v ∪ locs bs.
Proof.
  auto_locs. rewrite /location_list /locs_list.
  rewrite list_fmap_insert /union_list.
  revert n. induction bs; try easy.
  intros []; set_solver.
Qed.

Lemma block_pointer_set_insert l n bs v :
  l ∈ pointers (BBlock (<[n:=v]> bs)) ->
  l ∈ locs v \/ l ∈ pointers (BBlock bs).
Proof.
  intros E.
  apply pointers_locs in E. rewrite -pointers_locs.
  apply locs_insert in E.
  set_solver.
Qed.

Lemma successor_to_rstore s l l' bs :
  s !! l = Some bs ->
  l' ∈ pointers bs <-> successor s l l'.
Proof.
  intros Hbs.
  rewrite /successors /successor /successors Hbs //.
Qed.
