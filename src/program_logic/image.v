From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import gmap frac.
From irisfit Require Import language more_maps_and_sets.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* Notations. *)

(* thread_id are represented with nat. *)
Definition thread_id := nat.

(* A ctx is a map from thread_id to a set of invisible root (with a fraction)
   and a set of visible roots. *)
Notation ctx := (gmap thread_id (gmap loc Qp * gset loc)).

Definition set_of_option `{Countable A} (g:option (gset A)) : gset A :=
  match g with
  | None => ∅
  | Some g => g end.

(* ------------------------------------------------------------------------ *)
Definition xroot_less (r':option (gset loc)) (r:gmap loc Qp * gset loc) :=
  (dom r.1 ∪ r.2) ∖ set_of_option r'.

(* [image k] extracts all the locations of [k] *)
Definition image_less (η:gmap thread_id (option (gset loc))) (k:ctx) : gset loc :=
  map_fold (fun tid x acc => xroot_less (η !!! tid) x ∪ acc) ∅ k.

Lemma image_less_empty η : image_less η ∅ = ∅.
Proof. rewrite /image_less map_fold_empty //. Qed.

Lemma image_less_singleton η i r :
  image_less η ({[i:=r]}) = xroot_less (η !!! i) r.
Proof.
  rewrite -insert_empty.
  rewrite /image_less map_fold_insert; eauto.
  { rewrite map_fold_empty. set_solver. }
  intros i1 i2 ? ? ? ? Hi1 Hi2.
  destruct (decide (i1=i)); subst.
  { rewrite lookup_insert_ne // in Hi2. }
  { rewrite lookup_insert_ne // in Hi1. }
Qed.

Lemma image_less_insert1 tid r k η :
  k !! tid = None ->
  image_less η (<[tid:=r]> k) = xroot_less (η !!! tid) r ∪ image_less η k.
Proof.
  rewrite /image_less => ?.
  rewrite map_fold_insert; try easy.
  set_solver.
Qed.

Lemma image_less_insert2 tid r η k :
  tid ∈ dom k ->
  image_less η (<[tid:=r]> k) = xroot_less (η !!! tid) r ∪ (image_less η (delete tid k)).
Proof.
  intros ?.
  rewrite <- insert_delete_insert.
  rewrite image_less_insert1 //.
  rewrite lookup_delete //.
Qed.

Lemma elem_of_image_less l η k :
  l ∈ image_less η k <->  exists tid ls, (k !! tid = Some ls /\ l ∈ xroot_less (η !!! tid) ls).
Proof.
  unfold image_less.
  pose (P:=fun (b:gset loc) (k:ctx) => l ∈ b <->  exists tid ls, (k !! tid = Some ls /\ l ∈ xroot_less (η !!! tid) ls)).
  eapply (map_fold_ind P); unfold P; clear P.
  { set_solver. }
  { intros i x m r.
    intros Hmi Hlr.
    split.
    { intros Hr.
      apply elem_of_union in Hr. destruct Hr as [Hr|Hr].
      { exists i,x. rewrite lookup_insert. eauto. }
      { apply Hlr in Hr.
        destruct Hr as (tid,(ls,(E&?))).
        exists tid,ls. split; eauto.
        assert (i ≠ tid).
        { intros ?. subst. congruence. }
        rewrite lookup_insert_ne //. } }
    { intros (tid, (ls, (Hls & Hl))).
      apply elem_of_union.
      rewrite lookup_insert_case in Hls; case_decide; subst.
      { set_solver. }
      { right. apply Hlr. eauto. } } }
Qed.

Lemma image_less_delete_subseteq k tid η :
  image_less η (delete tid k) ⊆ image_less η k.
Proof.
  intros i. rewrite !elem_of_image_less.
  intros (tid',(ls,(E&?))).
  apply lookup_delete_Some in E. destruct E as (?&?).
  eauto.
Qed.

Definition sincl (x1 x2 : gmap thread_id (gset loc)) :=
  dom x1 = dom x2 /\ forall i r1 r2, x1 !! i =Some r1 -> x2 !! i = Some r2 -> r1 ⊆ r2.

Lemma image_less_elem_subset k tid r η :
  k !! tid = Some r ->
  xroot_less (η !!! tid) r ⊆ image_less η k.
Proof.
  intros ?.
  rewrite -(insert_id k tid r) //.
  rewrite image_less_insert2; eauto.
  set_solver.
Qed.

Lemma image_less_upd k tid r r' η :
  k !! tid = Some r ->
  xroot_less (η !!! tid) r =  xroot_less (η !!! tid) r' ->
  image_less η (<[tid:=r']> k) = image_less η k.
Proof.
  intros ? Htid.
  rewrite image_less_insert2; eauto.
  unfold xroot_less. simpl.
  setoid_rewrite <- (insert_id k tid ) at 2; eauto.
  rewrite <- insert_delete_insert.
  rewrite image_less_insert1.
  2:{ rewrite lookup_delete //. }
  unfold xroot_less in *. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)

(* [xroot] extracts the locations from a image of a ctx. *)
Definition xroot (r:gmap loc Qp * gset loc) := dom r.1 ∪ r.2.

Lemma xroot_empty : xroot (∅, ∅) = ∅.
Proof. set_solver. Qed.

Lemma image_less_upd' k tid r r' η :
  k !! tid = Some r ->
  xroot r =  xroot r' ->
  image_less η (<[tid:=r']> k) = image_less η k.
Proof.
  intros. eapply image_less_upd; try done.
  unfold xroot, xroot_less in *. set_solver.
Qed.

(* [image k] extracts all the locations of [k] *)
Definition image (k:ctx) : gset loc :=
  map_fold (fun _ x acc => xroot x ∪ acc) ∅ k.

Lemma image_empty : image ∅ = ∅.
Proof. rewrite /image map_fold_empty //. Qed.

Lemma image_singleton i r :
  image ({[i:=r]}) = xroot r.
Proof.
  rewrite -insert_empty.
  rewrite /image map_fold_insert; eauto.
  { rewrite map_fold_empty. set_solver. }
  intros i1 i2 ? ? ? ? Hi1 Hi2.
  destruct (decide (i1=i)); subst.
  { rewrite lookup_insert_ne // in Hi2. }
  { rewrite lookup_insert_ne // in Hi1. }
Qed.

Lemma image_insert1 tid r k :
  k !! tid = None ->
  image (<[tid:=r]> k) = xroot r ∪ image k.
Proof.
  intros Htid.
  unfold image.
  rewrite map_fold_insert; try easy.
  set_solver.
Qed.

Lemma image_insert2 tid r k :
  tid ∈ dom k ->
  image (<[tid:=r]> k) = xroot r ∪ (image (delete tid k)).
Proof.
  intros ?.
  rewrite <- insert_delete_insert.
  rewrite image_insert1 //.
  rewrite lookup_delete //.
Qed.

Lemma elem_of_image l k :
  l ∈ (image k) <->  exists tid ls, (k !! tid = Some ls /\ l ∈ xroot ls).
Proof.
  unfold image.
  pose (P:=fun (b:gset loc) (k:ctx) => l ∈ b <->  exists tid ls, (k !! tid = Some ls /\ l ∈ xroot ls)).
  eapply (map_fold_ind P); unfold P; clear P.
  { set_solver. }
  { intros i x m r.
    intros Hmi Hlr.
    split.
    { intros Hr.
      apply elem_of_union in Hr. destruct Hr as [Hr|Hr].
      { exists i,x. rewrite lookup_insert. eauto. }
      { apply Hlr in Hr.
        destruct Hr as (tid,(ls,(E&?))).
        exists tid,ls. split; eauto.
        assert (i ≠ tid).
        { intros ?. subst. congruence. }
        rewrite lookup_insert_ne //. } }
    { intros (tid, (ls, (Hls & Hl))).
      apply elem_of_union.
      rewrite lookup_insert_case in Hls; case_decide; subst.
      { set_solver. }
      { right. apply Hlr. eauto. } } }
Qed.

Lemma image_delete_subseteq k tid :
  image (delete tid k) ⊆ image k.
Proof.
  intros i. rewrite !elem_of_image.
  intros (tid',(ls,(E&?))).
  apply lookup_delete_Some in E. destruct E as (?&?).
  eauto.
Qed.

Lemma image_upd k tid r r' :
  k !! tid = Some r ->
  xroot r = xroot r' ->
  image (<[tid:=r']> k) = image k.
Proof.
  intros ? Htid.
  rewrite image_insert2; eauto.
  unfold xroot. simpl.
  setoid_rewrite <- (insert_id k tid ) at 2; eauto.
  rewrite <- insert_delete_insert.
  rewrite image_insert1.
  2:{ rewrite lookup_delete //. }
  set_solver.
Qed.

Lemma image_elem_subset k tid r :
  k !! tid = Some r ->
  xroot r ⊆ image k.
Proof.
  intros ?.
  rewrite -(insert_id k tid r) //.
  rewrite image_insert2; eauto.
  set_solver.
Qed.

Lemma image_fork k tid mt lk lt :
  mt ∉ dom k ->
  k !! tid = Some (lk,lt) ->
  (image (<[mt:=(∅, lt)]> (<[tid:=(lk, ∅)]> k))) = image k.
Proof.
  intros.
  assert (tid ∈ dom k); eauto.
  rewrite image_insert1.
  2:{ apply not_elem_of_dom. rewrite dom_insert.
      set_solver. }
  rewrite image_insert2 //.
  erewrite <- (image_upd k); eauto.
  rewrite image_insert2 //.
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma image_less_subseteq_image η k :
  image_less η k ⊆ image k.
Proof.
  intros l. rewrite elem_of_image_less elem_of_image.
  intros (π&(l1,l2)&?&?). do 2 eexists. split; first done.
  unfold xroot, xroot_less in *. set_solver.
Qed.
