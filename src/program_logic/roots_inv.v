From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import gset gmap frac.
From irisfit Require Import language more_maps_and_sets image.

Set Implicit Arguments.

Implicit Type η : gmap thread_id (option (gset loc)).

(* ------------------------------------------------------------------------ *)
(* mirror property *)

(* [mirror k ρ] asserts that if there is an edge in k, then its reverse is in ρ *)
Definition mirror (k:ctx) (η:gmap thread_id (option (gset loc))) (ρ:gmap loc (gset thread_id)) : Prop :=
  forall π l r x,
    k !! π = Some r ->
    η !! π = Some x ->
    l ∈ (dom r.1 ∪ r.2) ∖ set_of_option x ->
    π ∈ ρ !!! l.

Lemma mirror_extend S' k l η ρ g :
  ρ !! l = Some g ->
  mirror k η ρ ->
  mirror k η (<[l:=g ∪ S']> ρ).
Proof.
  intros Hg Hm.
  intros π' l' r x Hπ' Hr Hπ1.
  specialize (Hm π' l' _ x  Hπ' Hr).
  destruct_decide (decide (l=l')) as E; subst.
  { rewrite lookup_total_insert.
    rewrite lookup_total_alt Hg in Hm. set_solver. }
  { rewrite lookup_total_insert_ne; eauto. }
Qed.

Lemma mirror_clean k π l lt lk ρ g η :
  k !! π = Some (lk, lt) ->
  π ∈ dom η ->
  l ∉ lt ->
  l ∉ dom lk ->
  ρ !! l = Some g ->
  mirror k η ρ ->
  mirror k η (<[l:=g ∖ {[π]}]> ρ).
Proof.
  intros Hk Hη ? ? Hρ Hm. apply elem_of_dom in Hη. destruct Hη as (r,Hη).
  intros π' l' ? x Hπ' Hr' Hl'.
  specialize (Hm π' l' _ _ Hπ' Hr').
  destruct_decide (decide (l=l')); subst.
  { rewrite lookup_total_insert.
    rewrite lookup_total_alt Hρ in Hm. simpl in *.
    destruct_decide (decide (π=π')); subst.
    { exfalso. destruct r0. rewrite Hk in Hπ'. injection Hπ'.
      intros. subst. set_solver. }
    { set_solver. } }
  { rewrite lookup_total_insert_ne //; eauto. }
Qed.

Lemma mirror_weak k π lk lt lt' ρ η x :
  lt' ⊆ lt ->
  k !! π = Some (lk, lt) ->
  η !! π = Some x ->
  mirror k η ρ ->
  mirror(<[π:=(lk, lt')]> k) η ρ.
Proof.
  intros ? Hπ ? Hm.
  intros i l (r1,r2)  r'.
  destruct (decide (π=i)); subst.
  { rewrite lookup_insert. intros E Hl. injection E. intros. subst.
    eapply Hm; eauto. set_solver. }
  { rewrite !lookup_insert_ne //. eauto. }
Qed.

(* ------------------------------------------------------------------------ *)
(* ndom_lt *)

(* Each thread_id in [k] must be below [mt], to ensure freshness when using mt
   as a new thread id. *)
Definition ndom_lt (k:ctx) mt : Prop :=
  forall π, π ∈ dom k -> π < mt.

Lemma ndom_lt_insert π k mt r :
  π ∈ dom k ->
  ndom_lt k mt ->
  ndom_lt (<[π:=r]> k) mt.
Proof.
  unfold ndom_lt. set_solver.
Qed.

Lemma mirror_shift1 l2 L2 k π η lk l1 ρ x :
  l2 = dom L2 ->
  k !! π = Some (lk, l1 ∪ l2) ->
  η !! π = Some x ->
  mirror k η ρ ->
  mirror (<[π:=(lk ⋅ L2, l1)]> k) η ρ.
Proof.
  intros -> Hπ Hx Hm.
  intros π' l (lk',lt') x'. simpl.
  rewrite lookup_insert_case; case_decide; last eauto.
  inversion 1. subst. rewrite dom_op elem_of_difference !elem_of_union.
  specialize (Hm _ l _ _ Hπ Hx). simpl in *.
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* roots_inv *)

Record roots_inv (k:ctx) η (ρ:gmap loc (gset thread_id)) (mt:thread_id) :=
  { ri_mirror : mirror k η ρ;
    ri_ctx_dom : ndom_lt k mt;
    ri_dom : dom k = dom η;
  }.

Lemma roots_inv_extend S' k l  ρ g mt η :
  ρ !! l = Some g ->
  roots_inv k η ρ mt ->
  roots_inv k η (<[l:=g ∪ S']> ρ) mt.
Proof.
  intros Hl [].
  constructor; eauto using mirror_extend.
Qed.

Lemma roots_inv_weak k π lt' lt ρ mt lk η x :
  lt' ⊆ lt ->
  k !! π = Some (lk, lt) ->
  η !! π = Some x ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk, lt')]> k) η ρ mt.
Proof.
  intros ? ? ? [].
  constructor; eauto using mirror_weak,ndom_lt_insert.
  { rewrite !dom_insert_lookup_L //. }
Qed.

Lemma lookup_same_dom `{Countable A} {B C} i (k1 : gmap A B) (k2 : gmap A C) x :
  dom k1 = (dom k2 : gset A) ->
  k1 !! i = Some x ->
  is_Some (k2 !! i).
Proof. rewrite -!elem_of_dom => ? Hx. apply elem_of_dom_2 in Hx. set_solver. Qed.

Lemma roots_inv_shift1 k η mt l1 l2 π ρ L2 lk :
  l2 = dom L2 ->
  k !! π = Some (lk, l1 ∪ l2) ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk ⋅ L2, l1)]> k) η ρ mt.
Proof.
  intros ? Hk [? ? Hd].
  edestruct (lookup_same_dom π _ _ Hd Hk); eauto.
  constructor;  eauto using ndom_lt_insert, mirror_shift1.
  rewrite !dom_insert_lookup_L //.
Qed.

Lemma mirror_empty : mirror ∅ ∅ ∅.
Proof. intros ?. set_solver. Qed.

Lemma ndom_lt_empty : ndom_lt ∅ 0.
Proof. intros ?. set_solver. Qed.

Lemma roots_inv_init : roots_inv ∅ ∅ ∅ 0.
Proof. constructor; rewrite ?dom_empty_L; eauto using mirror_empty, ndom_lt_empty. Qed.

(* ------------------------------------------------------------------------ *)
(* add_thread *)

Definition add_thread π (S:gset loc) (ρ:gmap loc (gset thread_id)) : gmap loc (gset thread_id) :=
  set_fold (fun l ρ' => <[l := {[π]} ∪ ρ' !!! l]> ρ') ρ S.

Lemma elem_of_add_thread π ρ l lt mt :
  (π ∈ ρ !!! l) \/ (π = mt /\ l ∈ lt) ->
  π ∈ add_thread mt lt ρ !!! l.
Proof.
  unfold add_thread.
  pose (P:=fun (sf:gmap loc (gset thread_id)) (lt:gset loc) => (π ∈ ρ !!! l) \/ (π = mt /\ l ∈ lt) -> π ∈ sf !!! l).
  apply (set_fold_ind_L P); unfold P; clear P.
  { set_solver. }
  { intros x X r Hx IH E.
    destruct (decide (x=l)); subst.
    { rewrite lookup_total_insert. set_solver. }
    { rewrite lookup_total_insert_ne //.
      apply IH. set_solver. } }
Qed.

Lemma dom_add_thread mt lt ρ :
  lt ⊆ dom ρ ->
  dom (add_thread mt lt ρ) = dom ρ.
Proof.
  intros ?.
  unfold add_thread.
  pose (P:=fun (sf:gmap loc (gset thread_id)) (lt:gset loc) => lt ⊆ dom ρ -> dom sf = dom ρ ).
  apply (set_fold_ind_L P); unfold P; clear P; eauto.
  intros x X r ? IH ?.
  rewrite dom_insert_L.
  set_solver.
Qed.

Lemma roots_inv_fork mt k η ρ lt :
  mt ∉ dom k ->
  mt ∉ dom η ->
  roots_inv k η ρ mt ->
  roots_inv (<[mt:=(∅, lt)]> k) (<[mt:=None]> η) (add_thread mt lt ρ) (mt + 1).
Proof.
  intros ? ? [Hk Hmt].
  constructor; eauto.
  { intros π r l ? Hπ Hl ?.
    apply elem_of_add_thread.
    rewrite lookup_insert_case in Hπ; case_decide; subst.
    { set_solver. }
    { rewrite lookup_insert_ne // in Hl. eauto. } }
  { intros ?. rewrite dom_insert elem_of_union.
    intros [E|E].
    { apply elem_of_singleton in E. lia. }
    { apply Hmt in E. lia. } }
  { rewrite !dom_insert_L. set_solver. }
Qed.

Lemma roots_inv_delete l k ρ η mt :
  ρ !! l = Some ∅ ->
  roots_inv k η ρ mt ->
  roots_inv k η (delete l ρ) mt.
Proof.
  intros Hl [H2 H3].
  constructor; eauto.
  { intros ? l' ? ? R1 ? R2.
    destruct (decide (l=l'));subst.
    { exfalso. specialize (H2 π l' _ x R1).
      rewrite lookup_total_alt Hl in H2. set_solver. }
    rewrite lookup_total_delete_ne //. eauto. }
Qed.
