From iris.algebra Require Import auth gset gmap.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import proofmode.

From irisfit Require Import hypotheses successors predecessors stdpp.
From irisfit.spacelang Require iris.
From irisfit Require Import more_maps_and_sets tied more_cmras.
From irisfit.language Require Import syntax store.

(* This is our view of the heap. *)

Class storeG (sz:nat -> nat) Σ := StoreG {
  (* The heap, a mapping of locations to list of values. *)
  storeG_heap : gen_heapGS loc (list val) Σ;
}.

#[export] Existing Instance storeG_heap.

(* ------------------------------------------------------------------------ *)

(* Assumptions and definitions. *)

Section ReasoningRules.

(* A heap [σ] is a finite map of locations to blocks. *)
Implicit Types σ : gmap loc block.

(* ------------------------------------------------------------------------ *)

(* Our store interpretation predicate includes: 1- the standard store
   interpretation predicate [gen_heap_interp σ]; 2- the assertion [auth π],
   which represents the authoritative ownership of the ghost cell γ and
   holds the predecessor map π; 3- an invariant that ties [σ] and [π]. *)

Context `{ fG : !storeG sz Σ }.

(* ------------------------------------------------------------------------ *)

Definition irisfit_nm : namespace := nroot.@"irisfit".

Definition sizeof (l:loc) (n:nat) := gen_heap.meta l irisfit_nm n.

Definition sizeofs θ : iProp Σ := [∗ map] l ↦ b ∈ θ, sizeof l b.

(* ------------------------------------------------------------------------ *)

(* Notation for various forms of the pointsto assertion. *)

Definition mapsto l dq vs : iProp Σ :=
  mapsto l dq vs ∗ sizeof l (sz (length vs)).

Local Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Local Notation "l ↦□ v" := (mapsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Local Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Global Instance mapsto_timeless l dq v : Timeless (l ↦{dq} v).
Proof. apply _. Qed.
Global Instance mapsto_fractional l v : fractional.Fractional (λ e, l ↦{#e} v)%I.
Proof. apply _. Qed.
Global Instance mapsto_as_fractional l e v :
  fractional.AsFractional (l ↦{#e} v) (λ e, l ↦{#e} v)%I e.
Proof. constructor. done. apply _. Qed.
Global Instance mapsto_persistent l v : Persistent (l ↦□ v).
Proof. apply _. Qed.

Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝%Qp.
Proof. iIntros "(?&_)". iApply (mapsto_valid with "[$]"). Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof. iIntros "(?&_) (?&_)". iApply (mapsto_valid_2 l dq1 with "[$][$]"). Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "(?&_) (?&_)". iApply (mapsto_agree l dq1 with "[$][$]"). Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof. iIntros "(?&?) (?&_)". iFrame. iApply (mapsto_combine l dq1 with "[$][$]"). Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. iIntros (?) "(?&_) (?&_)". by iApply (mapsto_frac_ne l1 with "[$][$]"). Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. iIntros "(?&_) (?&_)". by iApply (mapsto_ne l1 with "[$][$]"). Qed.

Lemma mapsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. iIntros "(?&?)". iFrame. iApply (mapsto_persist with "[$]"). Qed.

Lemma mapsto_extract_size l dq vs :
  l ↦{dq} vs -∗ sizeof l (sz (length vs)).
Proof.
  iIntros "(?&#?)". by iFrame.
Qed.

Local Lemma mapsto_extract_size_paper l dq vs :
  l ↦{dq} vs -∗ l ↦{dq} vs ∗ sizeof l (sz (length vs)).
Proof.
  iIntros "?". iDestruct (mapsto_extract_size with "[$]") as "#?".
  iFrame "∗#".
Qed.

Lemma sizeof_confront l n m :
  sizeof l n -∗ sizeof l m -∗ ⌜n=m⌝.
Proof.
  iIntros "H1 H2".
  iApply (meta_agree with "H1 H2").
Qed.

Global Instance sizeof_persist l n : Persistent (sizeof l n).
Proof. apply _. Qed.

(* ------------------------------------------------------------------------ *)

Definition store_interp σ : iProp Σ :=
  ∃ α, gen_heap_interp α ∗ sizeofs ((fun x => sz (length x)) <$> α)  ∗ ⌜σ = (BBlock <$> α)⌝.

Lemma store_alloc l b σ:
  l ∉ dom σ ->
  store_interp σ ==∗
  store_interp (<[l:=BBlock b]> σ) ∗ l ↦ b ∗ meta_token l (⊤∖↑irisfit_nm).
Proof.
  iIntros (Hl) "[%(?&#?&%Hcoh)]".
  iMod (gen_heap_alloc _ l b with "[$]") as "(Hh & Hlb & Hmeta)".
  { apply not_elem_of_dom. rewrite Hcoh dom_fmap // in Hl. }
  iFrame.

  iDestruct (meta_token_difference with "Hmeta") as "(?&?)"; last iFrame.
  { set_solver. }
  iMod (meta_set with "[$]") as "#?"; last iFrame "#".
  { set_solver. }
  iModIntro.
  iExists _. iFrame.
  rewrite !fmap_insert Hcoh. iSplitL; last done.
  iApply big_sepM_insert; eauto.
  rewrite lookup_fmap.
  replace (α !! l) with (@None (list val)); first done.
  symmetry. apply not_elem_of_dom. rewrite Hcoh dom_fmap // in Hl.
Qed.

(* LATER move to iris *)
Lemma meta_in_dom `{Countable A} α (l:loc) (N : namespace) (x : A) :
  meta l N x -∗ gen_heap_interp α -∗ ⌜l ∈ dom α⌝.
Proof.
  rewrite gen_heap.meta_unseal. iIntros "[% (?&?)]".
  iIntros "[% (%&?&?)]".
  iDestruct (ghost_map.ghost_map_lookup with "[$][$]") as "%X".
  iPureIntro. apply elem_of_dom_2 in X. set_solver.
Qed.

Lemma exploit_sizeof σ l n :
  store_interp σ -∗ sizeof l n -∗ ⌜exists b, σ !! l = Some (BBlock b) /\ sz (length b) = n⌝.
Proof.
  iIntros "[% (?&?&%)] ?".
  iDestruct (meta_in_dom with "[$][$]") as "%Hl".
  apply elem_of_dom in Hl. destruct Hl as (?,Hl).
  assert (σ !! l = Some (BBlock x)) as E.
  { rewrite H lookup_fmap Hl //. }
  iDestruct (big_sepM_lookup _ _ l (sz (length x)) with "[$]") as "#?".
  { rewrite lookup_fmap Hl //. }
  iDestruct (gen_heap.meta_agree with "[$][$]") as "%".
  iPureIntro. naive_solver. Unshelve. apply _.
Qed.

Lemma sizeof_in_dom σ l n :
  store_interp σ -∗ sizeof l n -∗ ⌜l ∈ dom σ⌝.
Proof.
  iIntros "[%(?&?&%)] ?".
  iDestruct (meta_in_dom with "[$][$]") as "%Hd".
  iPureIntro. rewrite H dom_fmap //.
Qed.

Lemma store_update l b b' σ:
  length b= length b' ->
  store_interp σ -∗ l ↦ b ==∗
  store_interp (<[l:=BBlock b']> σ) ∗ l ↦ b'.
Proof.
  iIntros (Eq) "[%(?&?&%)] (?&?)".
  iDestruct (gen_heap_valid with "[$][$]") as "%X".
  iMod (gen_heap_update _ l _ b' with "[$][$]") as "(?&?)".
  replace ((fun x => sz (length x)) <$> α) with ((fun x => sz (length x)) <$> <[l:=b']> α).
  2:{ rewrite fmap_insert insert_id //. rewrite lookup_fmap X -Eq //. }
  iModIntro. iFrame. rewrite Eq. iFrame. iExists _. iFrame.
  iPureIntro. rewrite fmap_insert H //.
Qed.

(* ------------------------------------------------------------------------ *)

(* Consequences of the [mapsto] assertion. *)

(* As usual, [l ↦{q} b] guarantees that the heap [σ] maps [l] to [b]. *)

Lemma exploit_mapsto σ l p b :
  store_interp σ -∗ l ↦{p} b -∗ ⌜σ!!l = Some (BBlock b)⌝.
Proof.
  iIntros "[%(?&?&%)] (?&?)".
  iDestruct (gen_heap_valid with "[$] [$]") as "%".
  iPureIntro. rewrite H lookup_fmap H0 //.
Qed.

End ReasoningRules.

(* ------------------------------------------------------------------------ *)

(* Notations for assertions. *)

Global Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Global Notation "l ↦□ v" := (mapsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Global Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Global Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

(* Predecessor set. *)

Module Initialization.
  Definition storeΣ : gFunctors := #[
    gen_heapΣ loc (list val)
  ].

  Class storePreG Σ := {
      storePreG_heap :: gen_heapGpreS loc (list val) Σ;
  }.

  Global Instance subG_storePreG {Σ} :
    subG storeΣ Σ → storePreG Σ.
  Proof. solve_inG. Qed.

  Lemma store_init `{!storePreG Σ} sz :
    ⊢ |==> ∃ _ : storeG sz Σ,
    store_interp (∅:store).
  Proof.
    iIntros. rewrite /store_interp.
    (* Allocate the ghost heap component. *)
    iMod (gen_heap_init ∅) as (ghG) "(Hh & _ & _)".

    (* Conclude. *)
    iExists (StoreG _ Σ _).
    iModIntro.
    iExists _. iFrame. rewrite !fmap_empty.
    iSplit; last done. by iApply big_sepM_empty.
  Qed.

End Initialization.
