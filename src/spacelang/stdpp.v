From Coq.ssr Require Import ssreflect.
From stdpp Require Import base gmap gmultiset ssreflect.

(* If they are still present after a while, the lemmas in this file should be
   cleaned up and submitted for inclusion in stdpp. *)

(* ------------------------------------------------------------------------ *)

(* A database of rewriting rules for multisets. *)

Hint Rewrite
  @gmultiset_set_fold_empty
  @gmultiset_set_fold_singleton
  @gmultiset_set_fold_disj_union
: gmultiset.

Hint Rewrite
  @gmultiset_elem_of_disj_union
  @elem_of_singleton
  using solve [ typeclasses eauto ]
: gmultiset.

Hint Rewrite
  @multiplicity_empty
  @multiplicity_singleton
  @multiplicity_singleton_ne
  @multiplicity_disj_union
  @multiplicity_difference
  Nat.add_0_l
  Nat.add_0_r
  Nat.sub_0_r
  using solve [ eauto ]
: gmultiset.

Ltac multiset :=
  autorewrite with gmultiset.

(* ------------------------------------------------------------------------ *)

(* Lists. *)

(* The storement of this lemma could be made more general by letting [B] be
   a setoid (i.e., a type equipped with its own notion of equality) and by
   requiring the function [f] to be commutative only when applied to two
   elements of the list [xs]. *)

Lemma Permutation_foldr {A B} (f : A → B → B) (b : B) (xs ys : list A) :
  xs ≡ₚ ys →
  (∀ x y b, f x (f y b) = f y (f x b)) →
  foldr f b xs = foldr f b ys.
Proof.
  induction 1; intros Hcomm; simpl.
  (* Case: nil. *)
  { eauto. }
  (* Case: skip. *)
  { rewrite IHPermutation //. }
  (* Case: swap. *)
  { rewrite Hcomm. eauto. }
  (* Case: trans. *)
  { rewrite IHPermutation1 // IHPermutation2 //. }
Qed.

Class OrderInsensitive {A B} (f : A → B → B) : Prop :=
  order_insensitive x y b :
    f x (f y b) = f y (f x b).

Global Instance Permutation_fold_Proper
  {A B} (f : A → B → B) {_ : OrderInsensitive f} (b : B) :
  Proper ((≡ₚ) ==> (=)) (foldr f b).
Proof.
  repeat intro. eauto using Permutation_foldr.
Qed.

Global Instance CommAssocOrderInsensitive
  {A} (f : A → A → A) {_ : Comm (=) f} {_ : Assoc (=) f}
: OrderInsensitive f.
Proof.
  repeat intro. rewrite !(assoc f). rewrite (comm f x y). reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

(* Maps. *)

Section MyMaps.
Context `{Countable K}.
Implicit Types k : K.
Context {A : Type}.
Implicit Types m : gmap K A.

Lemma prove_in_dom k m a :
  m !! k = Some a →
  k ∈ dom m.
Proof.
  rewrite elem_of_dom. intros ->. eauto.
Qed.

Lemma prove_not_in_dom k m :
  m !! k = None →
  k ∉ dom m.
Proof.
  rewrite elem_of_dom. intros ->. eauto.
Qed.

Lemma in_dom_subseteq m m' k :
  m ⊆ m' →
  k ∈ dom m →
  k ∈ dom m'.
Proof.
  rewrite !elem_of_dom. eauto using lookup_weaken_is_Some.
Qed.

Lemma in_dom_equiv m m' k :
  dom m ≡@{gset K} dom m' →
  k ∈ dom m →
  k ∈ dom m'.
Proof.
  intros ->. eauto.
Qed.

Lemma in_dom_equiv_reverse m m' k :
  dom m ≡@{gset K} dom m' →
  k ∈ dom m' →
  k ∈ dom m.
Proof.
  intros ->. eauto.
Qed.

Lemma None_equiv m m' k :
  dom m ≡@{gset K} dom m' →
  m !! k = None →
  m' !! k = None.
Proof.
  intros Hdom. rewrite <- !not_elem_of_dom, Hdom. eauto.
Qed.

Lemma gmap_lookup_total_subseteq {_ : Inhabited A} m m' k :
  m ⊆ m' →
  k ∈ dom m →
  m !!! k = m' !!! k.
Proof.
  intros Hsub Hk.
  rewrite elem_of_dom in Hk.
  destruct Hk as (a & Hk).
  assert (m' !! k = Some a) by (eapply map_subseteq_spec; eauto).
  erewrite !lookup_total_correct by eauto.
  eauto.
Qed.

End MyMaps.

Global Hint Resolve
  prove_in_dom
  prove_not_in_dom
: core.

Global Hint Resolve
  in_dom_subseteq
  in_dom_equiv in_dom_equiv_reverse
  None_equiv
: in_dom.

Lemma in_dom_insert `{FinMapDom K M D} {A} (k : K) (m : M A) (a : A) :
  k ∈ dom (<[ k := a ]> m).
Proof.
  rewrite dom_insert. multiset_solver.
Qed.

Lemma in_dom_insert_ne `{FinMapDom K M D} {A} (k k' : K) (m : M A) (a : A) :
  k ∈ dom m →
  k ∈ dom (<[ k' := a ]> m).
Proof.
  rewrite dom_insert. multiset_solver.
Qed.

(* [map_fold f a m] is a fold operation on the finite map [m] with
   accumulator [a]. Inserting an element has the expected effect on
   [map_fold]: [map_fold f a (<[i:=x]> m) = f i x (map_fold f a m)].
   (assuming i is fresh and some commutativity condition).

   This result is proved in [map_fold_insert]:
   https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.fin_maps.html#map_fold_insert

   this is simply the same equation but for [delete]. Remark that this
   helps reasoning on [map_fold f a (<[i:=x]> m)] when i is already in
   the domain of m. *)

Lemma map_fold_delete `{FinMap K M} {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = Some x ->
  R (map_fold f b m) (f i x (map_fold f b (delete i m))).
Proof.
  intros Hf_proper Hf Hi.
  rewrite <-(insert_id _ _ _ Hi), <-insert_delete_insert at 1.
  apply map_fold_insert; auto.
  - by rewrite insert_delete_insert.
  - apply lookup_delete.
Qed.

Lemma map_fold_delete_L `{FinMap K M} {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = Some x ->
  map_fold f b m = f i x (map_fold f b (delete i m)).
Proof.
  apply map_fold_delete; apply _.
Qed.


Section MyFinMap.
Context `{FinMap K M}.

Lemma map_fold_ind_dom {A B}
  (P : B → M A → Prop)
  (f : K → A → B → B)
  (b : B)
  (f_comm: ∀ (j1 j2 : K) (z1 z2 : A) (y : B),
      f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) :
  ∀ m,
  P b ∅ →
  (∀ i x m' r,
      m' !! i = None →
      m !! i = Some x →
      P r m' →
      P (f i x r) (<[i:=x]> m')
  ) →
  P (map_fold f b m) m.
Proof.
  intros m Hempty IH.
  induction m using map_ind.
  { rewrite map_fold_empty. done. }
  { rewrite map_fold_insert //.
    { apply IH; eauto. rewrite lookup_insert //.
      apply IHm. intros. apply IH; eauto.
      rewrite lookup_insert_ne //. naive_solver. } }
Qed.

Tactic Notation "spec" hyp(H) :=
  match type of H with
  | ?x -> _ =>
    let H' := fresh in
    assert x as H'; [ | specialize (H H'); clear H' ]
  end.

Tactic Notation "spec" hyp(H) "by" tactic(t) :=
  spec H; [ solve [ t ] | ].

Tactic Notation "exact_eq" hyp(H) :=
  revert H; match goal with |- ?a -> ?b => assert (a = b); [ | congruence ] end.

Lemma map_fold_ind_2 {A1 A2 B1 B2}
  (P : B1 → B2 → M A1 → M A2 → Prop)
  (f1 : K → A1 → B1 → B1)
  (f2 : K → A2 → B2 → B2)
  (b1 : B1) (b2 : B2)
  (m1 : M A1) (m2 : M A2)
  (f1_comm: ∀ (j1 j2 : K) (z1 z2 : A1) (y : B1),
       f1 j1 z1 (f1 j2 z2 y) = f1 j2 z2 (f1 j1 z1 y))
  (f2_comm: ∀ (j1 j2 : K) (z1 z2 : A2) (y : B2),
      f2 j1 z1 (f2 j2 z2 y) = f2 j2 z2 (f2 j1 z1 y))
  (Hdom : forall i, m1 !! i = None <-> m2 !! i = None) :
  P b1 b2 ∅ ∅ →
  (∀ i x1 x2 m'1 m'2 r1 r2,
      m'1 !! i = None →
      m'2 !! i = None →
      m1 !! i = Some x1 →
      m2 !! i = Some x2 →
      P r1 r2 m'1 m'2 →
      P (f1 i x1 r1) (f2 i x2 r2) (<[i:=x1]> m'1) (<[i:=x2]> m'2)
  ) →
  P (map_fold f1 b1 m1) (map_fold f2 b2 m2) m1 m2.
Proof.
  pose (Q := fun (bb : B1 * B2) (mm : M (A1 * A2)) =>
               P (fst bb) (snd bb) (fst <$> mm) (snd <$> mm)).
  pose (f := fun k (aa : A1 * A2) (bb : B1 * B2) =>
               (f1 k (fst aa) (fst bb), f2 k (snd aa) (snd bb))).
  intros PO IH.
  pose (m := map_imap (fun (k : K) x1 => option_map (fun x2 : A2 => (x1, x2)) (m2 !! k)) m1).
  assert (E1 : m1 = fst <$> m). {
    apply map_eq; intros k; unfold m.
    rewrite lookup_fmap map_lookup_imap.
    destruct (m1 !! k) eqn:k1, (m2 !! k) eqn:k2; simpl; auto.
    apply Hdom in k2; congruence.
  }
  assert (E2 : m2 = snd <$> m). {
    apply map_eq; intros k; unfold m.
    rewrite lookup_fmap map_lookup_imap.
    destruct (m1 !! k) eqn:k1, (m2 !! k) eqn:k2; simpl; auto.
    apply Hdom in k1; congruence.
  }
  assert (∀ (j1 j2 : K)  z1 z2 y,
        f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) as f_comm.
  { unfold f. simpl. intros ?? (?,?) (?,?) (?,?). simpl. f_equal. naive_solver. naive_solver. }
  pose proof map_fold_ind_dom Q f (b1, b2) f_comm m as I.
  spec I.
  { unfold Q. simpl. rewrite !fmap_empty //. }
  spec I. {
    intros i (a1 & a2) mm' (b1' & b2') Hi mi Hmm'.
    specialize (IH i a1 a2 (fst <$> mm') (snd <$> mm') b1' b2').
    unfold Q.
    rewrite !fmap_insert; apply IH; auto.
    - rewrite lookup_fmap Hi; auto.
    - rewrite lookup_fmap Hi; auto.
    - revert mi. unfold m. rewrite map_lookup_imap.
      destruct (m1 !! i), (m2 !! i); simpl; congruence.
    - revert mi. unfold m. rewrite map_lookup_imap.
      destruct (m1 !! i), (m2 !! i); simpl; congruence.
  }
  exact_eq I.
  unfold Q.
  cut (map_fold f (b1, b2) m = (map_fold f1 b1 m1, map_fold f2 b2 m2)).
  { intros ->; simpl; congruence. }
  rewrite E1 E2.
  clearbody m. clear m1 m2 E1 E2 Hdom IH.
  revert f1_comm f2_comm.
  refine (map_fold_ind (fun b m => _ -> _ -> _ = _) f (b1, b2) _ _ m).
  - rewrite !fmap_empty !map_fold_empty. auto.
  - clear m.
    intros i (a1, a2) m (c1, c2) Hm IHm f1_comm f2_comm.
    rewrite !fmap_insert !map_fold_insert_L //.
    + rewrite IHm; auto.
    + rewrite lookup_fmap Hm; auto.
    + rewrite lookup_fmap Hm; auto.
Qed.

End MyFinMap.

Section MyFinMapDom.
Context `{FinMapDom K M D}.

Lemma dom_union_with {A} (m1 m2 : M A) g :
  let lift_g x1 x2 := Some (g x1 x2) in
  dom (union_with lift_g m1 m2) ≡@{D} dom m1 ∪ dom m2.
Proof.
  apply set_equiv. intros x.
  rewrite elem_of_union !elem_of_dom.
  (* This storement looks simple, but this proof is a bit painful. *)
  unfold is_Some.
  setoid_rewrite lookup_union_with_Some.
  split.
  { intros (a & Hx).
    destruct Hx as [ (?&?) | [ (?&?) | (?&?&?&?&?) ]]; eauto. }
  { intros [ (a & ?) | (a & ?) ];
    [ case_eq (m2 !! x) | case_eq (m1 !! x) ]; intros;
    eexists; eauto 8. }
Qed.

End MyFinMapDom.

Ltac if_decide :=
  match goal with |- context[decide (?P)] =>
    case (decide (P)); intro; try solve [ tauto | exfalso; set_solver ]
  end.

Section GMapMSet.

Context `{Countable K, A}.

Implicit Types k : K.
Implicit Types ks : gset K.
Implicit Types a x : A.

(* [gmap_mset ks a m] is the map [m] where all keys in [dom m ∩ ks] are
   mapped to [a], while all other keys retain their previous value. *)

Definition gmap_mset (ks : gset K) (a : A) (m : gmap K A) : gmap K A :=
  map_imap (λ k x, Some (if decide (k ∈ ks) then a else x)) m.

Lemma dom_gmap_mset ks a m :
 dom (gmap_mset ks a m) ≡@{gset K} dom m.
Proof.
  unfold gmap_mset.
  eapply dom_imap. intros k.
  rewrite elem_of_dom.
  split; intros (b & ?); exists b; [ eauto | tauto ].
Qed.

Lemma gmap_lookup_mset ks a m k :
  gmap_mset ks a m !! k =
  if decide (k ∈ dom m ∧ k ∈ ks) then Some a else m !! k.
Proof.
  unfold gmap_mset.
  rewrite map_lookup_imap.
  case_eq (m !! k).
  + intros b Hmk. simpl.
    assert (k ∈ dom m) by eauto.
    if_decide; if_decide.
  + intros Hmk. simpl.
    assert (k ∉ dom m) by eauto.
    if_decide.
Qed.

Lemma gmap_lookup_mset_inside ks a m k :
  k ∈ dom m →
  k ∈ ks →
  gmap_mset ks a m !! k = Some a.
Proof.
  intros Hdom ?. unfold gmap_mset.
  rewrite map_lookup_imap.
  rewrite elem_of_dom in Hdom. destruct Hdom as (b & Hmk).
  rewrite Hmk.
  simpl. if_decide.
Qed.

Lemma gmap_lookup_mset_outside ks a m k :
  k ∉ ks →
  gmap_mset ks a m !! k = m !! k.
Proof.
  intros. unfold gmap_mset.
  rewrite map_lookup_imap.
  case (m !! k).
  { intro b. simpl. if_decide. }
  { eauto. }
Qed.

Lemma gmap_lookup_mset_outside_dom ks a m k :
  k ∉ dom m →
  gmap_mset ks a m !! k = None (* = m !! k *).
Proof.
  intros Hdom. unfold gmap_mset.
  rewrite map_lookup_imap.
  rewrite not_elem_of_dom in Hdom.
  rewrite Hdom. eauto.
Qed.

Lemma gmap_lookup_mset_Some ks a m k b :
  gmap_mset ks a m !! k = Some b ↔
  m !! k = Some b ∧ k ∉ ks ∨
  b = a ∧ k ∈ ks ∧ k ∈ dom m.
Proof.
  split.
  + unfold gmap_mset.
    rewrite map_lookup_imap.
    case_eq (m !! k); simpl.
    { intros b' Hmk.
      assert (k ∈ dom m) by eauto.
      if_decide; intuition congruence. }
    { congruence. }
  + intros [ (? & ?) | (? & ? & ?) ].
    { rewrite gmap_lookup_mset_outside //. }
    { subst. rewrite gmap_lookup_mset_inside //. }
Qed.

Lemma gmap_lookup_total_mset_outside `{Inhabited A} ks a m k :
  k ∉ ks →
  gmap_mset ks a m !!! k = m !!! k.
Proof.
  intros. rewrite !lookup_total_alt.
  rewrite gmap_lookup_mset_outside //.
Qed.

Lemma gmap_mset_empty a m :
  gmap_mset ∅ a m = m.
Proof.
  intros. eapply map_eq; intros k'.
  rewrite gmap_lookup_mset_outside //.
Qed.

Lemma gmap_mset_cons k ks a m :
  k ∈ ks →
  k ∈ dom m →
  gmap_mset ks a m = gmap_mset (ks ∖ {[k]}) a (<[k := a]> m).
Proof.
  intros.
  eapply map_eq; intros k'.
  case (decide (k' ∈ dom m));
  case (decide (k' ∈ ks));
  case (decide (k = k'));
  intros; subst;
  rewrite !gmap_lookup_mset;
  rewrite ?lookup_insert //;
  rewrite ?lookup_insert_ne //;
  repeat if_decide.
Qed.

Lemma gmap_mset_cons' k ks a m :
  k ∈ dom m →
  gmap_mset ({[k]} ∪ ks) a m = gmap_mset ks a (<[k := a]> m).
Proof.
  intros.
  eapply map_eq; intros k'.
  case (decide (k' ∈ dom m));
  case (decide (k' ∈ ks));
  case (decide (k = k'));
  intros; subst;
  rewrite !gmap_lookup_mset;
  rewrite ?lookup_insert //;
  rewrite ?lookup_insert_ne //;
  repeat if_decide.
Qed.

Lemma gmap_mset_snoc' k ks a m :
  k ∈ dom m →
  gmap_mset ({[k]} ∪ ks) a m = <[k := a]> (gmap_mset ks a m).
Proof.
  intros.
  eapply map_eq; intros k'.
  case (decide (k' ∈ dom m));
  case (decide (k' ∈ ks));
  case (decide (k = k'));
  intros; subst;
  rewrite ?lookup_insert //;
  rewrite ?lookup_insert_ne //;
  rewrite !gmap_lookup_mset;
  repeat if_decide.
Qed.

Lemma gmap_mset_singleton k a m :
  k ∈ dom m →
  gmap_mset {[k]} a m = <[k := a]> m.
Proof.
  intros.
  eapply map_eq; intros k'.
  case (decide (k = k')); intro.
  + subst k'. assert (k ∈ ({[k]} : gset K)) by set_solver.
    rewrite lookup_insert.
    rewrite gmap_lookup_mset_inside //.
  + assert (k' ∉ ({[k]} : gset K)) by set_solver.
    rewrite lookup_insert_ne //.
    rewrite gmap_lookup_mset_outside //.
Qed.

End GMapMSet.

Section GMapMDelete.

Context `{Countable K, A}.

Implicit Types k : K.
Implicit Types ks : gset K.
Implicit Types a : A.

(* [gmap_mdelete ks m] is the map [m] where all keys in [ks] have been
   deleted. In other words, it is the corestriction of [m] to [ks]. *)

Definition gmap_mdelete (ks : gset K) (m : gmap K A) : gmap K A :=
  filter (λ '(k, a), k ∉ ks) m.

Lemma dom_gmap_mdelete ks m :
 dom (gmap_mdelete ks m) ≡ dom m ∖ ks.
Proof.
  unfold gmap_mdelete.
  eapply dom_filter. intros k.
  rewrite elem_of_difference.
  rewrite elem_of_dom.
  unfold is_Some.
  firstorder.
Qed.

Lemma gmap_lookup_mdelete ks m k :
  gmap_mdelete ks m !! k = (if decide (k ∈ ks) then None else m !! k).
Proof.
  unfold gmap_mdelete.
  case (decide (k ∈ ks)); intro.
  + rewrite map_lookup_filter_None.
    case (m !! k); eauto.
  + case_eq (m !! k).
    - intro a. rewrite map_lookup_filter_Some. eauto.
    - rewrite map_lookup_filter_None. eauto.
Qed.

Lemma gmap_mdelete_empty m :
  gmap_mdelete ∅ m = m.
Proof.
  eapply map_eq. intros k. rewrite gmap_lookup_mdelete. set_solver.
Qed.

Lemma gmap_mdelete_cons k ks m :
  k ∈ ks →
  gmap_mdelete ks m = gmap_mdelete (ks ∖ {[k]}) (delete k m).
Proof.
  intros. eapply map_eq. intros k'.
  rewrite !gmap_lookup_mdelete.
  case (decide (k' ∈ ks)); case (decide (k' = k)); intros; if_decide.
  - subst k'. rewrite lookup_delete. eauto.
  - rewrite lookup_delete_ne //.
Qed.

Lemma gmap_mdelete_cons' k ks m :
  k ∉ ks →
  gmap_mdelete ({[k]} ∪ ks) m = gmap_mdelete ks (delete k m).
Proof.
  intros.
  assert (fact: ks = ({[k]} ∪ ks) ∖ {[k]}) by set_solver.
  rewrite {2}fact .
  eapply gmap_mdelete_cons; set_solver.
Qed.

Lemma gmap_mdelete_singleton k m :
  gmap_mdelete {[k]} m = delete k m.
Proof.
  intros.
  eapply map_eq; intros k'.
  case (decide (k = k')); intro.
  + subst k'. assert (k ∈ ({[k]} : gset K)) by set_solver.
    rewrite lookup_delete.
    rewrite gmap_lookup_mdelete //. if_decide.
  + assert (k' ∉ ({[k]} : gset K)) by set_solver.
    rewrite lookup_delete_ne //.
    rewrite gmap_lookup_mdelete //. if_decide.
Qed.

End GMapMDelete.

(* ------------------------------------------------------------------------ *)

(* Lists *)

(* slight generalization of [stdpp.list.list_filter_iff] *)

Lemma list_filter_iff_dom {A} (P1 P2 : A → Prop)
      `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, x ∈ l -> P1 x ↔ P2 x) →
  filter P1 l = filter P2 l.
Proof.
  intros e.
  induction l as [ | a l IH]; auto.
  rewrite !filter_cons; do 2 destruct decide.
  - rewrite IH; auto. intros x i. apply e. now right.
  - cut (P2 a); try tauto. apply e; auto. left.
  - cut (P1 a); try tauto. apply e; auto. left.
  - apply IH. intros x i. apply e. now right.
Qed.

(* ------------------------------------------------------------------------ *)

(* Multisets. *)

Lemma list_to_set_disj_elements `{Countable A} (X : gmultiset A) :
  list_to_set_disj (elements X) ≡ X.
Proof.
  pattern X. eapply gmultiset_ind; clear X; [| intros x X ].
  - rewrite gmultiset_elements_empty. eauto.
  - rewrite gmultiset_elements_disj_union gmultiset_elements_singleton.
    multiset_solver.
Qed.

Lemma gmultiset_in_elements_in_set `{Countable A} (X : gmultiset A) x :
  x ∈ elements X → x ∈ X.
Proof.
  intros. rewrite <- gmultiset_elem_of_elements. eauto.
Qed.

Lemma gmultiset_in_set_in_elements `{Countable A} (X : gmultiset A) x :
  x ∈ X → x ∈ elements X.
Proof.
  intros. rewrite gmultiset_elem_of_elements. eauto.
Qed.

(* near [elem_of_multiplicity] *)

Lemma not_elem_of_multiplicity:
  ∀ `{Countable A} (x : A) (X : gmultiset A),
  x ∉ X ↔ multiplicity x X = 0.
Proof.
  intros. rewrite elem_of_multiplicity. lia.
Qed.

Lemma elem_of_difference_is_elem_of_lhs `{Countable A} (X Y : gmultiset A) x :
  x ∈ X ∖ Y → x ∈ X.
Proof.
  rewrite !elem_of_multiplicity multiplicity_difference. lia.
Qed.

(* currently unused *)

Lemma difference_when_not_elem `{Countable A} (X : gmultiset A) x :
  x ∉ X →
  X ∖ {[+x+]} ≡ X.
Proof.
  rewrite not_elem_of_multiplicity. intro.
  unfold equiv, gmultiset_equiv. intro y.
  rewrite multiplicity_difference.
  destruct (decide (y = x)); [ subst y |].
  - rewrite multiplicity_singleton. lia.
  - rewrite multiplicity_singleton_ne //. lia.
Qed.

Lemma difference_when_elem `{Countable A} (X : gmultiset A) x :
  x ∈ X →
  X = (X ∖ {[+x+]}) ⊎ {[+x+]}.
Proof.
  rewrite <- gmultiset_singleton_subseteq_l. multiset_solver.
Qed.

(* near [gmultiset_elem_of_disj_union] *)

Lemma gmultiset_elem_of_intersection `{Countable A} (X Y : gmultiset A) x :
  x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y.
Proof.
  rewrite !elem_of_multiplicity multiplicity_intersection. lia.
Qed.

(* This lemma exists in stdpp.gmultiset, but its type is too restrictive:
   it requires [f : A → A → A]. *)

Lemma gmultiset_set_fold_disj_union `{Countable A} {B}
  (f : A → B → B) {_ : OrderInsensitive f} (b : B) (X Y : gmultiset A) :
  set_fold f b (X ⊎ Y) = set_fold f (set_fold f b X) Y.
Proof.
  unfold set_fold. simpl.
  rewrite (comm (⊎)).
  rewrite gmultiset_elements_disj_union.
  rewrite foldr_app.
  reflexivity.
Qed.

(* The empty set is a unit for disjoint union. *)

Lemma gmultiset_disj_union_empty_r `{Countable A} (X : gmultiset A) :
  X ⊎ ∅ = X.
Proof.
  multiset_solver.
Qed.

(* The intersection of two singleton multisets can be computed as follows. *)

Lemma gmultiset_intersection_singletons `{Countable A} (x y : A) :
  {[+x+]} ∩ {[+y+]} = (if decide (x = y) then {[+x+]} else ∅ : gmultiset A).
Proof.
  eapply leibniz_equiv. intros z.
  rewrite multiplicity_intersection.
  destruct (decide (x = y)); [ subst y |].
  - lia.
  - rewrite multiplicity_empty.
    destruct (decide (z = x)); [ subst z |].
    + rewrite (multiplicity_singleton_ne x y) //. lia.
    + rewrite (multiplicity_singleton_ne z x) //.
Qed.

Lemma gmultiset_intersection_singletons_ne `{Countable A} (x y : A) :
  x ≠ y → {[+x+]} ∩ {[+y+]} = (∅ : gmultiset A).
Proof.
  intros Hne. rewrite gmultiset_intersection_singletons.
  destruct (decide (x = y)); tauto.
Qed.

Lemma commute_diff_union `{Countable A} (X Y Z : gmultiset A) :
  Y ∩ Z = ∅ →
  (X ∖ Y) ⊎ Z = (X ⊎ Z) ∖ Y.
Proof.
  multiset_solver.
Qed.

(* ------------------------------------------------------------------------ *)

(* Converting a multiset to a set. *)

Lemma gmultiset_dom_empty `{Countable A} :
  dom (∅ : gmultiset A) = (∅ : gset A).
Proof.
  unfold dom. apply dom_empty_L.
Qed.

Lemma dom_singleton `{Countable A} (x : A) :
  dom ({[+x+]} : gmultiset A) = ({[x]} : gset A).
Proof.
  unfold dom. apply dom_singleton_L.
Qed.

Lemma dom_union `{Countable A} (X Y : gmultiset A) :
  dom (X ⊎ Y) = dom X ∪ dom Y.
Proof.
  unfold dom.
  destruct X as [ mX ].
  destruct Y as [ mY ].
  simpl.
  apply leibniz_equiv. apply set_equiv. intros x.
  rewrite elem_of_union !elem_of_dom.
  (* This storement looks simple, but this proof is a bit painful. *)
  unfold is_Some.
  split.
  { intros (n & Hx).
    rewrite lookup_union_with_Some in Hx.
    destruct Hx as [ (?&?) | [ (?&?) | (?&?&?&?&?) ]]; eauto. }
  { intros [ (n & ?) | (n & ?) ];
    [ case_eq (mY !! x) | case_eq (mX !! x) ]; intros;
    eexists; rewrite lookup_union_with_Some; eauto 8. }
Qed.

Hint Rewrite
  @dom_empty
  @dom_singleton
  @dom_union
: dom.

Ltac dom :=
  autorewrite with dom.

(* ------------------------------------------------------------------------ *)

(* Multiset singleton with multiplicity *)

Definition repeatm `{Countable A} (x : A) (n : nat) : gmultiset A :=
  list_to_set_disj (replicate n x).

Lemma size_repeatm `{Countable A} (x : A) n : size (repeatm x n) = n.
Proof.
  induction n; auto; simpl.
  change (repeatm x (S n)) with ({[+x+]} ⊎ repeatm x n).
  rewrite gmultiset_size_disj_union gmultiset_size_singleton.
  lia.
Qed.

Lemma multiplicity_repeatm `{Countable A} (x y : A) n :
  multiplicity x (repeatm y n) = (if decide (x = y) then n else 0%nat).
Proof.
  induction n; auto.
  - change (repeatm y 0) with (∅ : gmultiset A).
    rewrite multiplicity_empty.
    destruct (decide _); auto.
  - change (repeatm y (S n)) with ({[+y+]} ⊎ repeatm y n).
    rewrite multiplicity_disj_union IHn multiplicity_singleton'.
    destruct (decide _); auto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Decidability. *)

Lemma decision_equiv (P Q : Prop) :
  (P <-> Q) →
  Decision Q →
  Decision P.
Proof.
  intros ? [ | ].
  - left. tauto.
  - right. tauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Reflexive-transitive closure. *)

Global Hint Constructors rtc : rtc.

Lemma rtc_snoc {A} (R : relation A) (x y z : A) :
  rtc R x y → R y z → rtc R x z.
Proof.
  induction 1; eauto with rtc.
Qed.

Global Hint Resolve rtc_snoc : rtc.
