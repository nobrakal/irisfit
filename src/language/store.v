From Coq Require Import ssreflect.
From stdpp Require Import base gmap gmultiset.

From irisfit.spacelang Require Import stdpp hypotheses.
From irisfit Require Export syntax successors.

(* This file defines stores and machine stores. *)

(* ------------------------------------------------------------------------ *)
(* Memory blocks *)

Inductive block :=
| BBlock : list val -> block
| BDeallocated : block.

Implicit Type b : block.

Global Instance block_inhabited : Inhabited block :=
  populate BDeallocated.

(* This is the list of pointers found in a memory block. *)
Definition block_pointer_list b : list loc :=
  match b with
  | BBlock bs =>
      foldr (fun v ps => val_pointer_list v ++ ps) [] bs
  | BDeallocated => [] end.

Lemma block_pointer_list_app xs ys :
  block_pointer_list (BBlock (xs ++ ys)) = block_pointer_list (BBlock xs) ++ block_pointer_list (BBlock ys).
Proof.
  revert ys. induction xs; try easy. intros ys.
  simpl. unfold block_pointer_list in *.
  rewrite IHxs. by rewrite app_assoc.
Qed.

Definition block_pointer_set b : gmultiset loc :=
  list_to_set_disj (block_pointer_list b).

Lemma elements_block_pointer_set bs :
  dom (block_pointer_set (BBlock bs)) = locs bs.
Proof.
  induction bs.
  { set_solver. }
  auto_locs.
  unfold location_list, block_pointer_set, locs_list in *.
  unfold block_pointer_list in *. simpl.
  rewrite list_to_set_disj_app.
  rewrite dom_union.
  rewrite IHbs. simpl.
  auto_locs.
  apply f_equal2; try easy.
  unfold locs_val. destruct a; simpl; try by rewrite dom_empty_L.
  rewrite right_id_L; try apply _.
  set_solver.
Qed.

Lemma block_pointer_set_block_elem bs l :
  l ∈ block_pointer_set (BBlock bs) <-> l ∈ locs bs.
Proof.
  rewrite <- gmultiset_elem_of_dom.
  rewrite elements_block_pointer_set.
  easy.
Qed.

Lemma block_pointer_set_new_block n :
  block_pointer_set (BBlock (replicate n val_unit)) = ∅.
Proof.
  induction n; set_solver.
Qed.

(* Block satisfies Hypotheses. *)
Global Instance lang_hypotheses : @Hypotheses loc _ _ block _.
Proof.
  exists block_pointer_set BDeallocated; try easy.
  intros []; [now right | now left].
Defined.

(* ------------------------------------------------------------------------ *)

(* A store is a map of locations to blocks.
   It represents the heap. *)
Notation store :=
  (gmap loc block).

(* ------------------------------------------------------------------------ *)

Section WithSize.
Context (sz:nat -> nat).

(* The size of a block in the heap is measured in sz. *)
Definition size_block b : nat :=
  match b with
  | BBlock vs => sz (length vs)
  | BDeallocated => 0
  end.

(* The size of a store is the sum of the sizes of its blocks.
   It is in fact the size of the heap. *)
Definition size_heap (σ:store) : nat :=
  map_fold (fun l b acc => acc + size_block b)%nat 0%nat σ.

(* ------------------------------------------------------------------------ *)

(* A store is valid if the limit on the size of the heap has not been
   exceeded. *)

Definition valid_store maxsize (σ : store) : Prop :=
  size_heap σ  <= maxsize.

(* ------------------------------------------------------------------------ *)

(* The available space in the heap is [maxsize] minus the current size of
   the heap. *)

Definition available maxsize σ :=
  maxsize - size_heap σ.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [size_block]. *)

(* The size of a block is preserved when a field is updated. *)

Lemma size_block_update vs ofs w :
  size_block (BBlock (<[ofs:=w]> vs)) = size_block (BBlock vs).
Proof.
  unfold size_block. rewrite insert_length. eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [size_heap]. *)

(* The empty heap has size 0. *)

Lemma size_empty_heap :
  size_heap ∅ = 0.
Proof.
  apply map_fold_empty.
Qed.

(* Allocating a block causes the size of the heap to grow by the size of
   that block. *)

Lemma size_heap_insert_new σ l b :
  σ !! l = None ->
  size_heap (<[l := b]> σ) = size_heap σ + size_block b.
Proof.
  intros Hfree.
  unfold size_heap in *.
  rewrite map_fold_insert; try (apply _); try easy.
  lia.
Qed.

(* Deleting a block causes the size of the heap to shrink by the size of
   that block. (The operational semantics actually never deletes a block,
   but this is still a useful lemma.) *)

Lemma size_heap_delete σ l b :
  σ !! l = Some b ->
  size_heap (delete l σ) + size_block b = size_heap σ.
Proof.
  symmetry.
  unfold size_heap in *.
  erewrite map_fold_delete_L; auto.
  lia.
Qed.

(* Updating a block from [b] to [b'] causes the size of the heap to grow
   by the difference between the size of [b'] and the size of [b]. *)

Lemma size_heap_insert_update σ l b b' :
  σ !! l = Some b ->
  size_heap (<[l := b']> σ) + size_block b = size_heap σ + size_block b'.
Proof.
  intros Hi.
  pose proof size_heap_insert_new (delete l σ) l b' (lookup_delete _ _).
  pose proof size_heap_insert_new (delete l σ) l b (lookup_delete _ _).
  pose proof size_heap_delete _ _ _ Hi.
  rewrite <-insert_delete_insert.
  lia.
Qed.

(* In particular, if [b] and [b'] have the same size, then the size of the
   heap is unaffected. *)

Lemma size_heap_insert_same_size σ l b b' :
  σ !! l = Some b ->
  size_block b = size_block b' ->
  size_heap (<[l := b']> σ) = size_heap σ.
Proof.
  intros Hi.
  pose proof size_heap_insert_update _ _ _ b' Hi.
  lia.
Qed.

(* Deallocating a block causes the size of the heap to shrink by the
   size of that block. *)

Lemma size_heap_dealloc σ l b :
  σ !! l = Some b ->
  size_heap (<[l := BDeallocated]> σ) + size_block b = size_heap σ.
Proof.
  intros Hl.
  pose proof (size_heap_insert_update σ l b BDeallocated Hl).
  simpl in *. lia.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [valid_store]. *)

(* The initial machine store [init maxsize] is valid. *)

Lemma valid_store_init maxsize :
  valid_store maxsize ∅.
Proof.
  unfold valid_store. simpl.
  rewrite size_empty_heap.
  lia.
Qed.

(* As stored earlier, updating a block from [b] to [b'] causes the size of
   the heap to grow by the difference between the size of [b'] and the size
   of [b]. Provided the size of the updated heap remains under [maxsize],
   the machine store remains valid. *)

Lemma valid_store_update maxsize σ l b b' :
  σ !! l = Some b ->
  size_block b' + size_heap σ <= maxsize + size_block b ->
  valid_store maxsize (<[l := b']> σ).
Proof.
  intros Hl Hbound.
  unfold valid_store; simpl.
  pose proof size_heap_insert_update _ l b b' Hl.
  lia.
Qed.

Lemma valid_store_update_tuple maxsize σ l vs ofs w :
  σ !! l = Some (BBlock vs) →
  0 <= ofs < length vs →
  valid_store maxsize σ →
  valid_store maxsize (<[l := BBlock (<[ofs := w]> vs)]> σ).
Proof.
  unfold valid_store. intros.
  eapply valid_store_update; eauto.
  rewrite size_block_update.
  lia.
Qed.

(* Deallocating a block preserves the validity of the machine store. *)

Lemma free_preserves_valid_store maxsize σ l :
  l ∈ dom σ →
  valid_store maxsize σ →
  valid_store maxsize (<[l:=BDeallocated]> σ).
Proof.
  intros Hb ?.
  apply elem_of_dom in Hb. destruct Hb.
  eapply valid_store_update.
  eauto.
  simpl. unfold valid_store in *. lia.
Qed.

Lemma free_group_preserves_valid_store maxsize σ locs :
  locs ⊆ dom σ →
  valid_store maxsize σ →
  valid_store maxsize (deallocate locs σ).
Proof.
  revert σ.
  pattern locs. eapply set_ind_L; clear locs; intros σ;
    unfold deallocate.
  { intros. rewrite gmap_mset_empty. eauto. }
  { intros ? ? IH ? ? ?. rewrite gmap_mset_snoc'.
    2:set_solver.
    apply free_preserves_valid_store; eauto.
    { rewrite dom_gmap_mset. set_solver. }
    { apply IH; eauto. set_solver. } }
Qed.

(* Provided there remains sufficient space in the heap, allocating a block
   preserves the validity of the machine store. *)

Lemma valid_store_alloc maxsize σ l b :
  σ !! l = None ->
  size_block b + size_heap σ <= maxsize ->
  valid_store maxsize (<[l := b]> σ).
Proof.
  intros Hfree Hbound.
  unfold valid_store; simpl.
  rewrite size_heap_insert_new; auto with lia.
Qed.

(* A reformulation of [valid_store_alloc]. *)

Lemma valid_store_alloc' maxsize σ l b :
  valid_store maxsize σ →
  size_block b <= available maxsize σ →
  σ !! l = None →
  valid_store maxsize (<[l:=b]> σ).
Proof.
  unfold valid_store, available.
  intros. eapply valid_store_alloc.
  - eauto.
  - lia.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [available]. *)

(* The available space in the initial store [init maxsize] is [maxsize]. *)

Lemma available_init maxsize :
  available maxsize ∅ = maxsize.
Proof.
  unfold available. simpl. rewrite size_empty_heap. lia.
Qed.

(* Allocating a block decreases the available space by the size of this
   block. *)

Lemma available_alloc maxsize σ l b :
  σ !! l = None →
  available maxsize (<[l:=b]> σ) = available maxsize σ - size_block b.
Proof.
  unfold available. intros. simpl.
  rewrite size_heap_insert_new; try easy.
  lia.
Qed.

(* Deallocating a block increases the available space by the size of this
   block. *)

Lemma available_dealloc maxsize σ l b :
  valid_store maxsize σ →
  σ !! l = Some b →
  available maxsize (<[l:=BDeallocated]> σ) =
  available maxsize σ + size_block b.
Proof.
  unfold valid_store, available. intros ? H. simpl.
  pose proof (size_heap_dealloc _ _ _ H). lia.
Qed.

(* Updating a block preserves the available space. *)

Lemma available_update maxsize σ l b b' :
  σ !! l = Some b →
  size_block b' = size_block b →
  available maxsize (<[l:=b']> σ) = available maxsize σ.
Proof.
  unfold available. simpl. intros.
  erewrite size_heap_insert_same_size by eauto.
  eauto.
Qed.

Lemma available_update_tuple maxsize σ l vs ofs w :
  (0 <= ofs < length vs)%nat ->
  σ !! l = Some (BBlock vs) →
  available maxsize (<[l:=BBlock (<[ofs:=w]> vs)]> σ) = available maxsize σ.
Proof.
  intros. erewrite available_update; eauto using size_block_update.
Qed.

End WithSize.
