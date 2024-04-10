From stdpp Require Import sets mapset gmap relations gmultiset.
From iris.program_logic Require Import language.

From irisfit.spacelang Require Import stdpp hypotheses.
From irisfit Require Import successors store pointers.

Set Implicit Arguments.

Lemma closed_init :
  closed ∅ ∅.
Proof.
  split; first set_solver. intros ??.
  rewrite /successor /successors lookup_empty. set_solver.
Qed.

Lemma closed_weak r1 r2 s :
  r1 ⊆ r2 ->
  closed r2 s ->
  closed r1 s.
Proof. intros ? []. split; set_solver. Qed.

Lemma free_group_preserves_closed r locs σ :
  locs ⊆ dom σ ->
  closed r σ ->
  closed r (deallocate locs σ).
Proof.
  unfold closed.
  pattern locs. eapply set_ind_L; clear locs;
    unfold deallocate.
  { intros. rewrite gmap_mset_empty. eauto. }
  { intros ? ? ? IH ? ?.
    rewrite gmap_mset_snoc'; last set_solver.
    eapply closed_weak.
    2:{ apply closed_insert_no_successors; last easy.
        apply IH; set_solver. }
    { set_solver. } }
Qed.

Lemma alloc_preserves_closed r l n σ :
  σ !! l = None ->
  closed r σ ->
  closed (r ∪ {[l]}) (<[l:=BBlock (replicate n val_unit)]> σ).
Proof.
  intros.
  unfold closed. simpl.
  apply closed_insert_no_successors; try easy. simpl.
  rewrite block_pointer_set_new_block //.
Qed.

Lemma closed_inline_root l bs r σ :
  σ !! l = Some (BBlock bs) ->
  closed r σ ->
  closed (r ∪ locs bs) σ.
Proof.
  intros Hl [? Hclo]. split; last done.
  assert (locs bs ⊆ dom σ); last set_solver.
  intros l' Hl'.
  specialize (Hclo l l'). apply Hclo.
  rewrite /successor /successors Hl -pointers_locs //.
Qed.

Lemma reachable_update r n v σ l l' bs :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  locs v ⊆ r ->
  reachable r (<[l:=BBlock (<[n:=v]> bs)]> σ) l' ->
  reachable r σ l'.
Proof.
  intros ? Hs ? Hl'.
  eapply analyze_reachable_after_heap_update in Hl'; try apply Hrl; try easy.
  apply Hs.
  intros x Hx ?.
  apply block_pointer_set_insert in Hx.
  destruct Hx; try easy.
  assert (x ∈ r) by set_solver.
  eauto using roots_are_reachable.
Qed.

Lemma update_preserves_closed r l n v w bs σ :
  l ∈ r ->
  σ !! l = Some (BBlock bs) ->
  bs !! n = Some w ->
  locs v ⊆ r ->
  closed r σ ->
  closed r (<[l:=BBlock (<[n:=v]> bs)]> σ).
Proof.
  intros ? Hl Hw ? (?&Hclo).
 apply closed_insert; try easy.
  rewrite (pointers_store w); try easy.
  intros l' Hl'.
  apply gmultiset_elem_of_disj_union in Hl'.
  destruct Hl'.
  { eapply Hclo. rewrite -successor_to_rstore; last apply Hl.
   multiset_solver. }
  assert (l' ∈ r) as Hl' by (destruct v; set_solver).
  set_solver.
Qed.
