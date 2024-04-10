From stdpp Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.

From irisfit.spacelang Require Import stdpp hypotheses predecessors.
From irisfit.lib Require Import qz smultiset fracset.
From irisfit Require Import more_maps_and_sets.

(* This file defines how we tie the store σ, the map of predecessors π,
   and a map of additional fracsets μ, through an invariant [tied σ π μ].

   Mainly:
   + The domain of μ is the one of σ
   + All fractions must be negative in μ (therefore all supports are negative)
   + Forall location in both π and μ, its "logical predecessors" from μ must
     be freed.

    The last property allows to generate at will assertions of the form
    [x ↤{0} {[-l-]}] for all freed l.
*)

Section Tied.
Context `{ Hypotheses L B }.

Definition all_neg (μ : gmap L (fracset L)) :=
  map_Forall (fun (_:L) x => frac x = 0%Qz) μ.

Definition all_freed (σ:gmap L B) (μ:gmap L (fracset L)) :=
  map_Forall (fun _ y => forall i, i ∈ supp y -> freed σ i) μ.

Record tied (σ:gmap L B) (μ:gmap L (fracset L)) :=
  { tied_dom : dom σ ⊆ dom μ;
    tied_neg : all_neg μ;
    tied_cov : all_freed σ μ }.

Lemma tied_init :
  tied (∅:gmap L B) ∅.
Proof. by constructor. Qed.

Lemma tied_alloc σ μ l b x :
  l ∉ dom σ →
  b <> deallocated ->
  frac x = 0 ->
  (supp x = ∅ \/ μ !! l = Some x) ->
  tied σ μ ->
  tied (<[l:=b]> σ) (<[l:=x]> μ).
Proof.
  intros ? ? ? X [Hd ? Hcovers].
  constructor.
  { do 2 rewrite dom_insert_L. set_solver. }
  { by apply map_Forall_insert_2. }
  { intros i. rewrite !lookup_insert_case. case_decide.
    { subst. simpl. intros ?. inversion 1. subst.
      destruct X as [->|X]. done. intros ??. apply Hcovers in X.
      apply not_freed_alloc_iff; try done. naive_solver. }
    { specialize (Hcovers i). simpl in *.
      intros. apply not_freed_alloc_iff; eauto. } }
Qed.

Lemma tied_dealloc σ μ l fr :
  l ∈ dom σ ->
  frac fr = 0%Qz ->
  (∀ i : L, i ∈ supp fr → freed σ i) ->
  tied σ μ ->
  tied σ (<[l:=fr]> μ).
Proof.
  intros Hin ? ? [Hd ? ?]. constructor.
  { rewrite dom_insert_L. set_solver. }
  { by apply map_Forall_insert_2. }
  { intros i x. rewrite lookup_insert_case. case_decide; naive_solver. }
Qed.

Lemma tied_add_freed1 nf σ l μ :
  frac nf = 0 ->
  (forall l, l ∈ supp nf -> freed σ l) ->
  μ !! l = None ->
  tied σ μ ->
  tied σ (<[l:=nf]> μ).
Proof.
  intros Hf Hl Hd [X1 X2 X3].
  constructor.
  { rewrite dom_insert_L //. set_solver. }
  all:intros ??; rewrite lookup_insert_case; case_decide; naive_solver.
Qed.

Lemma tied_add_freed2 σ μ (l:L) fr (ns:fracset L) :
  frac fr = 0%Qz ->
  μ !! l = Some ns ->
  (forall i, i ∈ supp fr -> freed σ i \/ i ∈ supp ns) ->
  tied σ μ ->
  tied σ (<[l:=fr]> μ).
Proof.
  intros ? Hμl Hfr [Hd Hneg Hco]. constructor.
   { rewrite dom_insert_L. set_solver. }
   { now apply map_Forall_insert_2. }
   { intros i x. rewrite lookup_insert_case. case_decide; naive_solver. }
Qed.

Lemma tied_store_deallocate σ μ locs :
  tied σ μ ->
  tied (deallocate locs σ) μ.
Proof.
  intros [Hd ? Hco]. constructor; try easy.
  { rewrite dom_deallocate //. }
  { intros ?????. apply freed_deallocate. eauto. }
Qed.

Lemma tied_update_store σ μ l b b' :
  b ≠ deallocated →
  b' ≠ deallocated →
  tied (<[l:=b]> σ) μ ->
  tied (<[l:=b']> σ) μ.
Proof.
  intros ? ? [Hd ? Hco]. constructor; try easy.
  { rewrite dom_insert_L. rewrite dom_insert_L in Hd. easy. }
  { intros ?????.
    eapply not_freed_update_iff. apply H2. all:naive_solver. }
Qed.

End Tied.
