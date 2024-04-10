From stdpp Require Import sets gmap.
From iris.algebra Require Import cmra.

Section More_gset.

Context `{Countable A}.
Context `{EqDecision A}.

Lemma difference_union (X Y : gset A) :
  X ∪ Y = (X ∖ Y) ∪ Y.
Proof.
  apply leibniz_equiv.
  split; intros.
  { destruct (decide (x ∈ Y)); set_solver. }
  { set_solver. }
Qed.

End More_gset.

Section More_gmap.

Context `{Countable K}.
Context `{A:Type}.

Implicit Type X : gmap K A.

Lemma lookup_insert_case X x y i :
  <[y:=i]> X !! x = if (decide (y=x)) then Some i else X !! x.
Proof.
  case_decide; subst;
    rewrite ?lookup_insert ?lookup_insert_ne //.
Qed.

Lemma gmap_equiv_singleton `{Equiv A} (k:K) (v1 v2:A):
  v1 ≡ v2 -> {[k:=v1]} ≡@{gmap K A} {[k:=v2]}.
Proof.
  intros X ?. rewrite !lookup_insert_case.
  case_decide; by constructor.
Qed.

Definition restrict X (d:gset K) :=
  filter (fun '(x,_) => x ∈ d) X.

Lemma lookup_restrict X d x :
  restrict X d !! x = if (decide (x ∈ d)) then X !! x else None.
Proof.
  unfold restrict.
  rewrite map_lookup_filter.
  destruct (X !! x); try easy.
  by case_decide.
Qed.

Lemma dom_restrict X d :
  dom (restrict X d) = dom X ∩ d.
Proof.
  apply leibniz_equiv. unfold restrict.
  rewrite dom_filter; try easy.
  intros ?.
  rewrite elem_of_intersection.
  split.
  { intros [E ?].
    apply elem_of_dom in E. destruct E as (?,?).
    by eexists. }
  { intros [? []].
    split; try easy.
    apply elem_of_dom.
    by eexists. }
Qed.

Lemma restrict_empty X :
  restrict X ∅ = ∅.
Proof.
  apply map_eq. intros i.
  rewrite /restrict lookup_empty.
  apply map_lookup_filter_None_2.
  right. set_solver.
Qed.

Lemma restrict_insert X k v d :
  X !! k = Some v ->
  restrict X ({[k]} ∪ d) = <[k:=v]> (restrict X d).
Proof.
  intros.
  apply map_eq. intros i.
  rewrite lookup_insert_case.
  case_decide.
  { subst. rewrite /restrict.
    apply map_lookup_filter_Some.  split; eauto. set_solver. }
  { rewrite !lookup_restrict. case_decide; eauto.
    all:case_decide; set_solver. }
Qed.

Lemma restrict_delete X k d :
  restrict (delete k X) d = delete k (restrict X d).
Proof.
  apply map_eq. intros i.
  rewrite lookup_restrict.
  destruct (decide (k=i)); subst.
  { rewrite !lookup_delete. case_decide; eauto. }
  { rewrite !lookup_delete_ne // -lookup_restrict //. }
Qed.

End More_gmap.

From iris.algebra Require Import cmra gmap.

Section More_gmap_cmra.

  Context `{Countable K}.
  Context `{A:cmra}.

  Lemma prove_gmap_valid (m:gmap K A) :
    (forall i x, m !! i = Some x -> ✓ x) -> ✓ m.
  Proof.
    intros Hv i.
    destruct (m !! i) eqn:E; try easy.
    eapply Hv, E.
  Qed.

  Lemma lookup_union_singleton (m1 m2:gmap K A) (k:K) (v:A) :
      {[ k := v ]} ≼ (m1 ∪ m2) ->
      {[ k := v ]} ≼ m1 \/ {[ k := v ]} ≼ m2.
  Proof.
    intros Hincl.
    apply singleton_included_l in Hincl.
    destruct Hincl as (y,(He&?)).
    apply Some_equiv_eq in He.
    destruct He as (y',(He&Hequiv)).
    apply lookup_union_Some_raw in He.
    destruct He as [He|(?&He)]; [left|right]; apply singleton_included_l;
      exists y'; now rewrite He Hequiv.
  Qed.

  Lemma split_map (X:gmap K A) (d:gset K) :
    d ⊆ dom X ->
    X = (restrict X d) ⋅ (restrict X (dom X ∖ d)).
  Proof.
    intros.
    apply map_eq.
    intros x.
    rewrite lookup_union_with.
    do 2 rewrite lookup_restrict.
    destruct (decide (x ∈ d)).
    { destruct (decide (x ∈ dom X ∖ d)).
      { exfalso. set_solver. }
      { rewrite right_id //. } }
    { rewrite left_id_L.
      destruct (decide (x ∈ dom X ∖ d)); try easy.
      destruct (decide (x ∈ dom X)).
      { exfalso. set_solver. }
      { apply not_elem_of_dom. eauto.  } }
  Qed.

  Lemma restrict_op (X1 X2:gmap K A) (d:gset K) :
    restrict (X1 ⋅ X2) d = restrict X1 d ⋅ restrict X2 d.
  Proof.
    rewrite /restrict. apply map_eq.
    intros l. rewrite lookup_op !map_lookup_filter lookup_op.
    destruct (X1 !!l) eqn:E1, (X2!!l) eqn:E2; rewrite ?E1 ?E2; simpl.
    { destruct_decide (decide (l∈d)).
      { rewrite !option_guard_True //. }
      { rewrite !option_guard_False //. } }
    all: rewrite ?right_id ?left_id //.
  Qed.

End More_gmap_cmra.

From iris.algebra Require Import gset local_updates.

Section More_gset_cmra.
  Context `{Countable A}.
  Implicit Type X Y : gset A.

Lemma gset_local_add X Y X' : (X,Y) ~l~> (X ∪ X',Y ∪ X').
Proof.
  rewrite local_update_unital_discrete => Z' _ /leibniz_equiv_iff ->.
  split; [done|]. set_solver.
Qed.

Lemma gset_local_rem X Y X' :
  X ∩ X' = ∅ ->
  (X,Y) ~l~> (X,Y ∖ X').
Proof.
  intros ?.
  rewrite local_update_unital_discrete => Z' ? /leibniz_equiv_iff.
  repeat (rewrite gset_op). intros E. subst.
  split; [done|]. set_solver.
Qed.

Lemma gset_local_rem_ex X Y Y' :
  (X,Y ⋅ Y') ~l~> (X,(Y ∖ Y') ⋅ Y').
Proof.
  rewrite local_update_unital_discrete => Z' ? /leibniz_equiv_iff.
  repeat (rewrite gset_op). intros E. subst.
  split; [done|].
  rewrite difference_union_L. set_solver.
Qed.

End More_gset_cmra.
