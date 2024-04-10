From iris.algebra Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.
From irisfit.spacelang Require Import stdpp hypotheses.

(* This file contains mathematical results about the interplay between
   successors and predecessors in a heap. The physical heap σ is a map
   of locations to blocks, where each block contains a list of outgoing
   pointers. The ghost predecessor heap π is a map of locations to
   multisets of locations. We express the relationship between σ and π
   that we expect to hold. *)

(* ------------------------------------------------------------------------ *)

(* Tactics, hints, etc. *)

Local Hint Constructors elem_of_list    : in_list.
Local Hint Resolve elem_of_list_further : in_list.

Local Hint Resolve gmultiset_in_elements_in_set : dom.

(* ------------------------------------------------------------------------ *)

Section Predecessors.

(* We expect a countable type [L] of locations and an inhabited type [B]
   of blocks. *)

Context `{ Hypotheses L B }.

(* ------------------------------------------------------------------------ *)

(* Definitions. *)

(* A heap [σ] is a finite map of locations to blocks. *)

Implicit Types σ : gmap L B.

(* A predecessor map [π] is a finite map of locations to multisets
   of locations. *)

Implicit Types π : gmap L (gmultiset L).

(* We write [locs] for a set and [ls] for a multiset of locations. *)

Implicit Types locs : gset L.
Implicit Types ls : gmultiset L.

(* A location is said to be freed if it points to a deallocated block. *)

Definition freed σ l :=
  σ !! l = Some deallocated.

(* The predecessors of the location [l'], a multiset of locations,
   can be read off the map [π] as follows. *)

Definition predecessors π l' : gmultiset L :=
  match π !! l' with
  | None =>
      ∅
  | Some ls =>
      ls
  end.

(* TODO this is just [π !!! l']. Simplify? Also update [register]. *)

(* ------------------------------------------------------------------------ *)

(* We build three properties into our invariant: coincidence, mirror, and
   closure. *)

(* The coincidence property requires the domain of [π] to be the domain of
   [σ], deprived of the locations that have been freed. In other words, a
   location has a (ghost) [predecessors] field if and only if it has been
   allocated and not yet deallocated. *)

(* We intend to exploit this feature in the storement of the reasoning rule
   for memory allocation: the fact that every successor [l'] of the new block
   must come with a mapsfrom assertion [l' ↤ _] implies that [l'] is allocated
   and has not been freed, i.e., we are not creating a dangling pointer. *)

Definition coincidence_direct_freed σ π :=
  ∀ l, freed σ l → l ∉ dom π.

Definition coincidence_reverse σ π :=
  ∀ l, l ∈ dom π → l ∈ dom σ.

Definition coincidence σ π :=
  coincidence_direct_freed σ π ∧
  coincidence_reverse σ π.

(* The mirror property requires the predecessor edges to form a sound
   over-approximation of the successor edges. *)

(* Because an address [l'] that has been freed has no predecessors, this
   property implies that the set [successors σ l] cannot contain a freed
   location. This forbids the existence of dangling pointers in the heap. *)

Definition mirror σ π :=
  ∀ l l',
  multiplicity l' (successors σ l) ≤ multiplicity l (predecessors π l').

(* One could conceivably require a reverse mirror property, stating that if an
   edge between [l] and [l'] is recorded in the predecessor map, and if [l]
   has not been freed, then this edge exists in the heap. (The side condition
   that [l] has not been freed allows delayed destruction of predecessor
   edges.) The mirror property and the reverse property could then be stored
   together as follows:

Definition mirror σ π :=
  ∀ l l',
  ~ freed σ l →
  multiplicity l' (successors σ l) = multiplicity l (predecessors π l').

   However, the reverse mirror property is not technically necessary. We
   can live with over-approximated predecessor sets, and this gives us
   extra flexibility; e.g., it allows us to set up fractional (shared)
   ownership of predecessor sets and to update these sets even with a
   fraction that is less than 1. *)

(* We require a weak backward closure property: if an edge between [l] and
   [l'] is recorded in the predecessor map, then [l] is in the domain of [σ],
   that is, [l] has been allocated at some point in the past. (This would be
   a consequence of the reverse mirror property, if we required it.) *)

Definition closure σ π :=
  ∀ l l', l ∈ predecessors π l' → l ∈ dom σ.

(* The global invariant is the conjunction of the above properties. *)

Definition invariant σ π :=
  coincidence σ π ∧ mirror σ π ∧ closure σ π.

(* ------------------------------------------------------------------------ *)

(* [register l l' π] extends [π] so as to record the existence of an edge
   between [l] and [l']. *)

Definition register l l' π :=
  <[ l' := π!!!l' ⊎ {[+l+]} ]> π.

(* [unregister l l' π] deletes an edge between [l] and [l'] in [π]. *)

Definition unregister l l' π :=
  <[ l' := π!!!l' ∖ {[+l+]} ]> π.

(* ------------------------------------------------------------------------ *)

(* The invariant holds of an empty heap [σ] and an empty predecessor
   mapping [π]. *)

Lemma invariant_init :
  invariant ∅ ∅.
Proof.
  split; [| split ].
  { repeat split; intros l; repeat intros; multiset_solver. }
  { intros l l'.
    rewrite /successors /predecessors !lookup_empty. multiset. lia. }
  { intros l l'.
    rewrite /predecessors lookup_empty. multiset_solver. }
Qed.

(* ------------------------------------------------------------------------ *)

(* Lots of shallow lemmas that we group in hint databases. *)

Lemma Some_predecessors π l' ls :
  π !! l' = Some ls →
  predecessors π l' = ls.
Proof.
  rewrite /predecessors. intros ->. eauto.
Qed.

Lemma Some_in_dom π l' ls :
  π !! l' = Some ls →
  l' ∈ dom π.
Proof.
  rewrite elem_of_dom. intros ->. eauto.
Qed.

Lemma freed_in_dom σ l :
  freed σ l →
  l ∈ dom σ.
Proof.
  unfold freed. rewrite elem_of_dom. intros ->. eauto.
Qed.

Lemma use_coincidence_direct_freed σ π :
  coincidence σ π →
  ∀ l, freed σ l → l ∉ dom π.
Proof.
  intros (? & ?). unfold coincidence_direct_freed. eauto.
Qed.

Lemma use_coincidence_direct_freed_contrapositive σ π :
  coincidence σ π →
  ∀ l, l ∈ dom π → ~ freed σ l.
Proof.
  repeat intro.
  assert (l ∉ dom π) by eauto using use_coincidence_direct_freed.
  tauto.
Qed.

Lemma use_coincidence_reverse σ π :
  coincidence σ π →
  ∀ l, l ∈ dom π → l ∈ dom σ.
Proof.
  intros (? & ?). unfold coincidence_reverse. eauto.
Qed.

Lemma use_closure σ π :
  closure σ π →
  ∀ l l', l ∈ predecessors π l' → l ∈ dom σ.
Proof.
  unfold closure. eauto.
Qed.

Hint Resolve
  Some_in_dom
  freed_in_dom
  use_coincidence_direct_freed
  use_coincidence_reverse
  use_closure
: in_dom.

Lemma predecessors_in_dom_dst π l l' :
  l ∈ predecessors π l' →
  l' ∈ dom π.
Proof.
  rewrite elem_of_dom /predecessors.
  destruct (π !! l'); [| by multiset_solver ].
  eauto.
Qed.

Hint Resolve predecessors_in_dom_dst : in_dom.

Lemma predecessors_empty_outside_dom l' π :
  l' ∉ dom π →
  predecessors π l' = ∅.
Proof.
  rewrite not_elem_of_dom /predecessors. by intros ->.
Qed.

Lemma predecessors_empty_once_freed l' σ π :
  coincidence σ π →
  freed σ l' →
  predecessors π l' = ∅.
Proof.
  intros. rewrite predecessors_empty_outside_dom; [| eauto with in_dom ].
  reflexivity.
Qed.

Lemma no_predecessor_outside_dom l l' π :
  l' ∉ dom π →
  l ∈ predecessors π l' →
  False.
Proof.
  intro. rewrite predecessors_empty_outside_dom //. multiset_solver.
Qed.

Lemma successors_in_dom_src σ l l' :
  l' ∈ successors σ l →
  l ∈ dom σ.
Proof.
  rewrite elem_of_dom. unfold successors. intros.
  destruct (σ !! l); [| by multiset_solver ].
  eauto.
Qed.

Hint Resolve successors_in_dom_src : in_dom.

Lemma membership_in_predecessors π l' ls :
  π !! l' = Some ls →
  ∀ l, l ∈ ls → l ∈ predecessors π l'.
Proof.
  intro Hl'. rewrite /predecessors Hl'. eauto.
Qed.

Hint Resolve membership_in_predecessors : in_pred.

(* ------------------------------------------------------------------------ *)

(* By the mirror property, if [l'] is a successor of [l], then [l] is
   a predecessor of [l']. In other words, every forward edge is also
   recorded as a backward edge in the predecessor map [π]. *)

Lemma successors_predecessors σ π l l' :
  mirror σ π →
  l' ∈ successors σ l →
  l ∈ predecessors π l'.
Proof.
  unfold mirror. intros Hm Hs.
  (* Instantiate the mirror property for [l] and [l']. *)
  specialize (Hm l l') as Hm.
  (* State everything in terms of multiplicity, and conclude. *)
  revert Hs. do 2 rewrite elem_of_multiplicity. lia.
Qed.

Hint Resolve successors_predecessors : in_pred.

(* A freed location has no successors. *)

Lemma freed_no_successors σ l :
  freed σ l →
  successors σ l = ∅.
Proof.
  rewrite /successors. intros ->. rewrite pointers_deallocated //.
Qed.

(* ADDED *)
Lemma successors_predecessors_corollary σ π locs ls :
  invariant σ π →
  (forall l, l ∉ locs -> l ∈ ls -> freed σ l) ->
  (∀ l l', l' ∈ locs → l ∈ predecessors π l' → l ∈ locs \/ (l ∉ locs /\ l ∈ ls)) →
  (∀ l l', l' ∈ locs → l' ∈ successors σ l → l ∈ locs).
Proof.
  rewrite /invariant. intros (_ & Hmir & _) Hf Hpred.
  intros l l' Hl' Hl''.
  pose proof (successors_predecessors _ _ _ _ Hmir Hl'') as Hp.
  destruct (Hpred _ _ Hl' Hp) as  [Hl|Hl]; try easy.
  exfalso. destruct Hl as (?&Hl).
  apply Hf, freed_no_successors in Hl.
  rewrite Hl in Hl''. set_solver. done.
Qed.

(* ------------------------------------------------------------------------ *)

(* Because we have imposed the condition that a freed location has no
   predecessors, and because our predecessor information is sound, we
   can be assured that there is no dangling pointer in the heap --
   that is, no pointer of an allocated block to a freed location. *)

Lemma successors_not_freed_dst σ π l l' :
  coincidence σ π →
  mirror σ π →
  l' ∈ successors σ l →
  ~ freed σ l'.
Proof.
  (* Assume, by contradiction, that [l'] has been freed. *)
  intros ? Hmirror Hl' Hfreed.
  (* Because [l'] is a successor of [l], by the mirror property,
     [l] is a predecessor of [l']. *)
  assert (Hl: l ∈ predecessors π l') by eauto with in_pred.
  (* But a freed location has no predecessors. Contradiction. *)
  erewrite predecessors_empty_once_freed in Hl by eauto.
  multiset_solver.
Qed.

(* We have a forward closure property: if [l'] is a successor of [l]
   in the heap [σ], then [l'] is itself in the domain of the heap [σ].
   This is of course a property of the operational semantics; it is
   impossible to obtain a memory location that was never allocated. *)

Lemma successors_in_dom_dst σ π l l' :
  coincidence σ π →
  mirror σ π →
  l' ∈ successors σ l →
  l' ∈ dom σ.
Proof.
  intros.
  (* By a previous lemma, [l] is a predecessor of [l']. Thus, [l'] is in
     the domain of [π], and by the coincidence property, it is also in the
     domain of [σ]. *)
  eauto with in_dom in_pred.
Qed.

Hint Resolve successors_in_dom_dst : in_dom.

(* ------------------------------------------------------------------------ *)

(* Low-level lemmas about [freed]. *)

Lemma not_freed_alloc_iff σ l b l' :
  b ≠ deallocated →
  l ∉ dom σ →
  freed (<[l:=b]> σ) l' <-> freed σ l'.
Proof.
  intros Hb Hl.
  assert (Hlookup: σ !! l = None) by rewrite -not_elem_of_dom //.
  destruct (decide (l = l')); [ subst l' |]; rewrite /freed; intros.
  (* Case: [l' = l]. *)
  { rewrite lookup_insert Hlookup.
    (* The left-hand side is false because [b] is not deallocated.
       The right-hand side is false because of [None = Some _]. *)
    split; intros; simplify_eq. }
  (* Case: [l' ≠ l]. *)
  rewrite lookup_insert_ne //.
Qed.

Lemma not_freed_update_iff σ l b b' l' :
  b ≠ deallocated →
  b' ≠ deallocated →
  freed (<[l:=b']> σ) l' <-> freed (<[l:=b]> σ) l'.
Proof.
  intros.
  destruct (decide (l = l')); [ subst l' |]; rewrite /freed; intros.
  { rewrite !lookup_insert. split; intros; simplify_eq; tauto. }
  { rewrite !lookup_insert_ne //. }
Qed.

(* Interaction between [freed] and [deallocate]. *)

Lemma freed_deallocate_inside locs σ l :
  l ∈ dom σ →
  l ∈ locs →
  freed (deallocate locs σ) l.
Proof.
  intros. rewrite /freed /deallocate gmap_lookup_mset_inside //.
Qed.

Lemma freed_deallocate locs σ l :
  freed (deallocate locs σ) l ↔ (l ∈ locs ∧ l ∈ dom σ) ∨ freed σ l.
Proof.
  rewrite /freed /deallocate.
  rewrite gmap_lookup_mset_Some.
  split; intros [ ? | ? ]; try tauto.
  case (decide (l ∈ locs)); intro; try tauto.
  eauto with in_dom.
Qed.

(* ------------------------------------------------------------------------ *)

(* Coincidence is preserved by allocation. *)

Lemma coincidence_alloc σ π l b ls :
  coincidence σ π →
  b ≠ deallocated →
  l ∉ dom σ →
  coincidence (<[l:=b]> σ) (<[l:=ls]> π).
Proof.
  rewrite /coincidence
          /coincidence_direct_freed /coincidence_reverse.
  intros (? & ?) ? ?. repeat split; intros l'.
  (* [coincidence_direct_freed] *)
  - rewrite dom_insert elem_of_union elem_of_singleton.
    rewrite not_freed_alloc_iff //.
    intros ? [|].
    { subst l'. assert (l ∈ dom σ) by eauto with in_dom. multiset_solver. }
    { assert (l' ∉ dom π) by eauto. multiset_solver. }
  (* [coincidence_reverse] *)
  - do 2 rewrite dom_insert elem_of_union elem_of_singleton.
    intuition eauto.
Qed.

(* Coincidence is preserved when a block is updated. *)

Lemma coincidence_update σ l b b' π :
  coincidence (<[l:=b]> σ) π →
  b ≠ deallocated →
  b' ≠ deallocated →
  coincidence (<[l:=b']> σ) π.
Proof.
  rewrite /coincidence
          /coincidence_direct_freed /coincidence_reverse.
  intros (? & ?).
  assert (Hdo: dom (<[l:=b']> σ) ≡ dom (<[l:=b]> σ)) by rewrite !dom_insert //.
  repeat split; intros l'; rewrite ?Hdo ?(not_freed_update_iff _ _ b b') //;
  eauto.
Qed.

(* Coincidence is preserved by deallocation. *)

Lemma coincidence_free σ π locs :
  coincidence σ π →
  coincidence (deallocate locs σ) (gmap_mdelete locs π).
Proof.
  rewrite /coincidence
          /coincidence_direct_freed /coincidence_reverse.
  intros (? & ?). repeat split; intros l';
  (* Three subgoals: *)
  rewrite ?dom_deallocate ?dom_gmap_mdelete ?freed_deallocate //;
  multiset_solver.
Qed.

(* Coincidence depends only on the domain of [π], so cannot be broken
   by updates to predecessor fields. *)

Lemma coincidence_domain σ π π' :
  coincidence σ π →
  dom π' ≡ dom π →
  coincidence σ π'.
Proof.
  rewrite /coincidence
          /coincidence_direct_freed /coincidence_reverse.
  intros (? & ?) Hequiv.
  assert (∀ l, l ∈ dom π → l ∈ dom π').
  { intro. rewrite Hequiv. tauto. }
  assert (∀ l, l ∈ dom π' → l ∈ dom π).
  { intro. rewrite Hequiv. tauto. }
  assert (∀ l, l ∉ dom π → l ∉ dom π').
  { intro. rewrite Hequiv. tauto. }
  repeat split; eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Low-level properties of the functions [successors] and [predecessors]. *)

Lemma successors_insert σ l b :
  successors (<[l:=b]> σ) l = pointers b.
Proof.
  rewrite /successors lookup_insert //.
Qed.

Lemma successors_insert_ne σ l b l' :
  l ≠ l' →
  successors (<[l:=b]> σ) l' = successors σ l'.
Proof.
  intros. rewrite /successors lookup_insert_ne //.
Qed.

Lemma successors_deallocate_outside σ locs l :
  l ∉ locs →
  successors (deallocate locs σ) l = successors σ l.
Proof.
  intros. rewrite /successors /deallocate gmap_lookup_mset_outside //.
Qed.

Lemma predecessors_insert π l ls :
  predecessors (<[l:=ls]> π) l = ls.
Proof.
  intros. rewrite /predecessors lookup_insert //.
Qed.

Lemma predecessors_insert_ne π l ls l' :
  l ≠ l' →
  predecessors (<[l:=ls]> π) l' = predecessors π l'.
Proof.
  intros. rewrite /predecessors lookup_insert_ne //.
Qed.

Hint Rewrite
  predecessors_insert
  predecessors_insert_ne
  using solve [ eauto ]
: gmultiset.

Lemma predecessors_delete_ne π l m :
  l ≠ m →
  predecessors (delete l π) m = predecessors π m.
Proof.
  intros. rewrite /predecessors lookup_delete_ne //.
Qed.

Lemma predecessors_mdelete π locs m :
  predecessors (gmap_mdelete locs π) m =
  if decide (m ∈ locs) then ∅ else predecessors π m.
Proof.
  rewrite /predecessors gmap_lookup_mdelete.
  case (decide (m ∈ locs)); eauto.
Qed.

Lemma fresh_location_not_in_predecessors σ π l l' :
  closure σ π →
  l ∉ dom σ →
  l ∉ predecessors (<[l:=∅]> π) l'.
Proof.
  intros.
  destruct (decide (l = l')); [ subst l' |].
  - rewrite /predecessors lookup_insert. multiset_solver.
  - rewrite predecessors_insert_ne //. eauto with in_dom.
Qed.

(* ------------------------------------------------------------------------ *)

(* Low-level properties of the function [register]. *)

(* [register] is order-insensitive. That is, the order in which two edges
   are registered is irrelevant. *)

Global Instance order_insensitive_register l :
  OrderInsensitive (register l).
Proof.
  intros l'1 l'2 π. rewrite /register. eapply map_eq; intros l'.
  destruct (decide (l' = l'1)); destruct (decide (l' = l'2)); subst;
  repeat (first [
    rewrite lookup_insert
  | rewrite lookup_insert_ne; [| solve [ eauto ]]
  | rewrite lookup_total_insert_ne; [| solve [ eauto ]]
  ]);
  eauto.
Qed.

(* [register] does not affect the domain of the predecessor map. *)

Lemma dom_register l l' π :
  l' ∈ dom π →
  dom (register l l' π) ≡ dom π.
Proof.
  unfold register. rewrite dom_insert. multiset_solver.
Qed.

Lemma dom_foldr_register (ls' : list L) l π :
  (∀ l', l' ∈ ls' → l' ∈ dom π) →
  dom (foldr (register l) π ls') ≡ dom π.
Proof.
  induction ls' as [| l' ls' ]; simpl; intros Hdom.
  { reflexivity. }
  { assert (Heq: dom (foldr (register l) π ls') ≡ dom π).
    { eapply IHls'. eauto with in_list. }
    rewrite dom_register; [| by rewrite Heq; eauto with in_list ].
    exact Heq. }
Qed.

Hint Extern 1 (_ ∈ dom (set_fold (register _) _ _)) =>
  rewrite dom_foldr_register; eauto with dom
: dom.

(* The purpose of [register] is to update the predecessor map in the
   following way. *)

Lemma predecessors_register l l' π m' :
  predecessors (register l l' π) m' =
  if decide (l' = m') then predecessors π m' ⊎ {[+ l +]}
                      else predecessors π m'.
Proof.
  case_eq (π !! l'); [ intros ls |]; intros Hπl'; rewrite /register.
  (* Case: [l'] is in the domain of [π]. Its predecessors are [ls]. *)
  { erewrite lookup_total_correct by eauto.
    unfold predecessors.
    destruct (decide (l' = m')); [ subst m' |].
    - rewrite lookup_insert Hπl' //.
    - rewrite lookup_insert_ne //. }
  (* Case: [l'] is not in the domain of [π]. *)
  { rewrite lookup_total_alt Hπl'. simpl.
    destruct (decide (l' = m')); [ subst m' |].
    - rewrite predecessors_insert /predecessors Hπl' //.
    - rewrite predecessors_insert_ne //. }
Qed.

Lemma predecessors_foldr_register (ls' : list L) l π:
  ∀ m m',
  multiplicity m (predecessors (foldr (register l) π ls') m') =
  if decide (l = m) then
    multiplicity m' (list_to_set_disj ls') +
    multiplicity m (predecessors π m')
  else
    multiplicity m (predecessors π m').
Proof.
  (* Reason by induction over [ls']. *)
  induction ls' as [| l' ls' ]; simpl; intros m m'; multiset.
  (* Case: there are no outgoing pointers. *)
  { destruct (decide (l = m)); reflexivity. }
  (* Case: there is a list [l' :: ls'] of outgoing pointers. *)
  rewrite predecessors_register.
  destruct (decide (l' = m')); [ subst m' |]; multiset; rewrite IHls'.
  (* Subcase: [l' = m'], which means that we are looking at [l']. *)
  { destruct (decide (l = m)); [ subst m |]; multiset; lia. }
  (* Subcase: [l' ≠ m'], which means we are not looking at [l']. *)
  { reflexivity. (* yay. *) }
Qed.

(* ------------------------------------------------------------------------ *)

(* Properties of [unregister]. *)

Global Instance order_insensitive_unregister l :
  OrderInsensitive (unregister l).
Proof.
  intros l'1 l'2 π. rewrite /unregister. eapply map_eq; intros l'.
  destruct (decide (l' = l'1)); destruct (decide (l' = l'2)); subst;
  repeat (first [
    rewrite lookup_insert
  | rewrite lookup_insert_ne; [| solve [ eauto ]]
  | rewrite lookup_total_insert_ne; [| solve [ eauto ]]
  ]);
  eauto.
Qed.

Lemma dom_unregister l l' π :
  l' ∈ dom π →
  dom (unregister l l' π) ≡ dom π.
Proof.
  unfold unregister. rewrite dom_insert. multiset_solver.
Qed.

Lemma dom_foldr_unregister (ls' : list L) l π :
  (∀ l', l' ∈ ls' → l' ∈ dom π) →
  dom (foldr (unregister l) π ls') ≡ dom π.
Proof.
  induction ls' as [| l' ls' ]; simpl; intros Hdom.
  { reflexivity. }
  { assert (Heq: dom (foldr (unregister l) π ls') ≡ dom π).
    { eapply IHls'. eauto with in_list. }
    rewrite dom_unregister; [| by rewrite Heq; eauto with in_list ].
    exact Heq. }
Qed.

Hint Extern 1 (_ ∈ dom (set_fold (unregister _) _ _)) =>
  rewrite dom_foldr_unregister; eauto with dom
: dom.

(* In the following lemma, we avoid requiring [l ∈ predecessors π l'].
   This is important; we want to be able to unregister an edge without
   creating a proof obligation that this edge exists. *)

Lemma predecessors_unregister l l' π m' :
  predecessors (unregister l l' π) m' =
  if decide (l' = m') then predecessors π m' ∖ {[+ l +]}
                      else predecessors π m'.
Proof.
  case_eq (π !! l'); [ intros ls |]; intros Hπl'; rewrite /unregister.
  (* Case: [l'] is in the domain of [π]; it has some predecessors [ls]. *)
  { erewrite lookup_total_correct by eauto.
    (* Reason by cases. *)
    unfold predecessors.
    destruct (decide (l' = m')); [ subst m' |].
    - rewrite lookup_insert Hπl' //.
    - rewrite lookup_insert_ne //. }
  (* Case: [l'] is not in the domain of [π]. *)
  { rewrite lookup_total_alt Hπl' //. simpl.
    unfold predecessors.
    destruct (decide (l' = m')); [ subst m' |].
    - rewrite lookup_insert Hπl' //.
    - rewrite lookup_insert_ne //. }
Qed.

Lemma predecessors_foldr_unregister (ls' : list L) l π:
  ∀ m m',
  multiplicity m (predecessors (foldr (unregister l) π ls') m') =
  if decide (l = m) then
    multiplicity m (predecessors π m') -
    multiplicity m' (list_to_set_disj ls')
  else
    multiplicity m (predecessors π m').
Proof.
  (* Reason by induction over [ls']. *)
  induction ls' as [| l' ls' ]; simpl; intros m m'; multiset.
  (* Case: there are no outgoing pointers. *)
  { destruct (decide (l = m)); reflexivity. }
  (* Case: there is a list [l' :: ls'] of outgoing pointers. *)
  rewrite predecessors_unregister.
  destruct (decide (l' = m')); [ subst m' |]; multiset.
  (* Subcase: [l' = m'], which means that we are looking at [l']. *)
  { rewrite IHls'.
    destruct (decide (l = m)); [ subst m |]; multiset; lia. }
  (* Subcase: [l' ≠ m'], which means we are not looking at [l']. *)
  { rewrite IHls'. reflexivity. (* yay. *) }
Qed.

(* ------------------------------------------------------------------------ *)

(* The mirror property is preserved by allocation. *)

Lemma mirror_alloc σ π l b :
  coincidence σ π →
  mirror σ π →
  closure σ π →
  l ∉ dom σ →
  mirror (<[l:=b]> σ) (set_fold (register l) (<[l:=∅]> π) (pointers b)).
Proof.
  unfold mirror. intros Hco Hmirror Hclo Hl m m'.
  rewrite predecessors_foldr_register.
  rewrite list_to_set_disj_elements.
  destruct (decide (l = m)); [ subst m |].
  (* Case: [l = m]. *)
  - rewrite successors_insert.
    assert (multiplicity l (predecessors (<[l:=∅]> π) m') = 0).
    { rewrite -not_elem_of_multiplicity.
      eauto using fresh_location_not_in_predecessors. }
    lia.
  (* Case: [l ≠ m]. *)
  - rewrite successors_insert_ne //.
    specialize (Hmirror m m') as Hmirror.
    eapply Nat.le_trans; [ eauto | clear Hmirror ].
    destruct (decide (l = m')); [ subst m' |]; multiset.
    { cut (multiplicity m (predecessors π l) = 0). lia.
      rewrite -not_elem_of_multiplicity.
      eauto using no_predecessor_outside_dom with in_dom. }
    { lia. }
Qed.

(* The mirror property is preserved when a block is updated from [b]
   to [b']. Every pointer that is present in the block but not in the
   block [b'] must be unregistered; every pointer that is present in
   [b'] but not in [b] must be registered. The pointers present in
   the intersection need not be unregistered and registered again;
   this is important for the convenience of the end user. *)

Definition old_pointers b b' : gmultiset L :=
  pointers b ∖ pointers b'.

Definition new_pointers b b' : gmultiset L :=
  pointers b' ∖ pointers b.

Lemma mirror_update σ l b b' π :
  mirror (<[l:=b]> σ) π →
  (∀ l', l' ∈ new_pointers b b' → l' ∈ dom π) →
  let π'  := set_fold (unregister l) π (old_pointers b b') in
  let π'' := set_fold (register l) π' (new_pointers b b') in
  mirror (<[l:=b']> σ) π''.
Proof.
  (* This proof is surprisingly easy. Behold: *)
  rewrite /mirror. intros Hmirror Hnew m m'.
  rewrite predecessors_foldr_register list_to_set_disj_elements //.
  rewrite predecessors_foldr_unregister list_to_set_disj_elements //.
  rewrite /old_pointers /new_pointers. multiset.
  specialize (Hmirror m m'). revert Hmirror.
  destruct (decide (l = m)); [ subst m |].
  - rewrite !successors_insert. lia.
  - rewrite !successors_insert_ne //.
Qed.

Lemma mirror_update_weak σ l b b' π :
  mirror (<[l:=b]> σ) π →
  (∀ l', l' ∈ new_pointers b b' → l' ∈ dom π) →
  let π' := set_fold (register l) π (new_pointers b b') in
  mirror (<[l:=b']> σ) π'.
Proof.
  (* This proof is surprisingly easy. Behold: *)
  rewrite /mirror. intros Hmirror Hnew m m'.
  rewrite predecessors_foldr_register list_to_set_disj_elements //.
  rewrite /new_pointers. multiset.
  specialize (Hmirror m m'). revert Hmirror.
  destruct (decide (l = m)); [ subst m |].
  - rewrite !successors_insert. lia.
  - rewrite !successors_insert_ne //.
Qed.

(* ADDED *)
Global Instance freed_decision σ l : Decision (freed σ l).
Proof.
  rewrite /freed. destruct (σ !! l) as [b|]; try solve_decision.
  destruct (decision_deallocated b); subst.
  { by left. }
  { right. intros E. injection E. easy. }
Qed.

(* MODIFIED
   The mirror property is preserved by deallocation.  *)
Lemma mirror_free σ π locs ls :
  mirror σ π →
  locs ⊆ dom σ →
  (forall l, l ∉ locs -> l ∈ ls -> freed σ l) ->
  (∀ l l', l' ∈ locs → l ∈ predecessors π l' → l ∈ locs \/ l ∈ ls) →
  mirror (deallocate locs σ) (gmap_mdelete locs π).
Proof.
  unfold mirror. intros Hmirror Hlocs Hfreed Hclosed m m'.
  destruct (decide (m ∈ locs)).
  (* Case: [m ∈ locs]. *)
  - rewrite -> freed_no_successors by eauto using freed_deallocate_inside.
    multiset. lia.
  (* Case: [m ∉ locs]. *)
  - rewrite successors_deallocate_outside //.
    (* Decide if m is freed. *)
    destruct (decide (freed σ m)) as [f|].
    { rewrite (freed_no_successors _ _ f). rewrite multiplicity_empty. lia. }
    (* If m is not freed, yields a contradiction *)
    specialize (Hmirror m m') as Hmirror.
    eapply Nat.le_trans; [ eauto |].
    rewrite predecessors_mdelete.
    (* If [m] is not in [locs], then the result is immediate. *)
    case (decide (m' ∈ locs)); intro; [| eauto ].
    (* So, assume [m ∈ locs]. If the multiplicity of [m] in [predecessors π m']
       is zero then all is well. Otherwise, [m] is a predecessor of [m'], and
       because [locs] is closed under predecessors, [m] must be in [locs] as well;
       this yields a contradiction. *)
    case (decide (multiplicity m (predecessors π m') = 0)); intro; [ lia |].
    assert (m ∈ predecessors π m'). by (rewrite elem_of_multiplicity; lia).
    set_solver.
Qed.

(* The mirror property is preserved by cleanup -- that is, by the delayed
   removal of freed locations from a predecessor set. *)

Lemma mirror_cleanup σ π l' ls ms :
  mirror σ π →
  predecessors π l' = ls →
  (∀m, m ∈ ms → freed σ m) →
  mirror σ (<[ l' := ls ∖ ms ]> π).
Proof.
  unfold mirror. intros Hmirror Hls Hfreed m m'.
  destruct (decide (l' = m')); [ subst m' | rewrite predecessors_insert_ne //].
  multiset.
  destruct (decide (m ∈ ms)) as [ Hm | Hm ].
  (* Case [m ∈ ms]. Because [m] is in [ms], it must have been freed.
     Therefore, the set [successors σ m] must be empty. *)
  - clear Hmirror.
    assert (Hsucc: successors σ m = ∅) by eauto using freed_no_successors.
    rewrite Hsucc. multiset. lia.
  (* Case [m ∉ ms]. *)
  - specialize (Hmirror m l') as Hmirror.
    eapply Nat.le_trans; [ eauto | clear Hmirror ].
    rewrite Hls.
    revert Hm. rewrite not_elem_of_multiplicity. lia.
Qed.

(* ------------------------------------------------------------------------ *)

(* The closure property is preserved by allocation. *)

Lemma closure_alloc σ π l b :
  closure σ π →
  closure (<[l:=b]> σ) (<[l:=∅]> π).
Proof.
  unfold closure. intros ? m m'. rewrite dom_insert.
  destruct (decide (l = m')); [ subst m' |]; multiset; multiset_solver.
Qed.

Lemma closure_register σ π l l' :
  closure σ π →
  l ∈ dom σ →
  closure σ (register l l' π).
Proof.
  unfold closure. intros ? ? m m'.
  rewrite predecessors_register.
  destruct (decide (l' = m')); [ subst m' |].
  { multiset_solver. }
  { eauto. }
Qed.

Lemma closure_foldr_register (ls' : list L) σ π l :
  closure σ π →
  l ∈ dom σ →
  closure σ (foldr (register l) π ls').
Proof.
  induction ls'; eauto using closure_register.
Qed.

Lemma closure_unregister σ π l l' :
  closure σ π →
  closure σ (unregister l l' π).
Proof.
  unfold closure. intros ? m m'.
  rewrite predecessors_unregister //.
  destruct (decide (l' = m')); [ subst m' |];
  eauto using elem_of_difference_is_elem_of_lhs.
Qed.

Lemma closure_foldr_unregister (ls' : list L) σ π l :
  closure σ π →
  closure σ (foldr (unregister l) π ls').
Proof.
  induction ls'; eauto using closure_unregister.
Qed.

(* The closure property is preserved when a block is updated. *)

Lemma closure_domain σ σ' π :
  closure σ π →
  dom σ ≡ dom σ' →
  closure σ' π.
Proof.
  rewrite /closure. intros Hclo Heq l l' Hl. rewrite -Heq. eauto.
Qed.

Lemma closure_update σ l b b' π :
  closure (<[l:=b]> σ) π →
  let π'  := set_fold (unregister l) π (old_pointers b b') in
  let π'' := set_fold (register l) π' (new_pointers b b') in
  closure (<[l:=b']> σ) π''.
Proof.
  intros.
  eapply closure_foldr_register; [| eapply in_dom_insert ].
  eapply closure_foldr_unregister.
  eapply closure_domain; [ eauto |].
  rewrite !dom_insert //.
Qed.

Lemma closure_update_weak σ l b b' π :
  closure (<[l:=b]> σ) π →
  let π' := set_fold (register l) π (new_pointers b b') in
  closure (<[l:=b']> σ) π'.
Proof.
  intros.
  eapply closure_foldr_register; [| eapply in_dom_insert ].
  eapply closure_domain; [ eauto |].
  rewrite !dom_insert //.
Qed.

Lemma closure_semi_update σ l b b' π :
  closure (<[l:=b]> σ) π →
  let π'  := π in (* no unregistering at all! *)
  let π'' := set_fold (register l) π' (new_pointers b b') in
  closure (<[l:=b']> σ) π''.
Proof.
  intros.
  eapply closure_foldr_register; [| eapply in_dom_insert ].
  eapply closure_domain; [ eauto |].
  rewrite !dom_insert //.
Qed.

(* The closure property is preserved by deallocation. *)

Lemma closure_free σ π locs :
  closure σ π →
  closure (deallocate locs σ) (gmap_mdelete locs π).
Proof.
  rewrite /closure. intros Hclo m m'.
  rewrite predecessors_mdelete.
  rewrite dom_deallocate.
  case (decide (m' ∈ locs)).
  + set_solver.
  + eauto.
Qed.

(* The closure property is preserved by cleanup. *)

Lemma closure_cleanup σ π l' ls ms :
  closure σ π →
  predecessors π l' = ls →
  closure σ (<[ l' := ls ∖ ms ]> π).
Proof.
  rewrite /closure. intros Hclo Hls m m'.
  destruct (decide (l' = m')); [ subst m' |]; multiset.
  - rewrite -Hls. eauto using elem_of_difference_is_elem_of_lhs.
  - eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* The ordering relation [π1 ≾ π2] means that [π1] and [π2] have the same
   domain and the edges of [π1] form a subset of the edges of [π2]. *)

(* It is useful to define this relation, because we work with approximate
   information and there are cases where we do not know exactly in what
   way [π] is affected by an update; then, instead of an equality on [π],
   we get a lower bound and an upper bound on [π], which is good enough. *)

Definition approx π1 π2 :=
  dom π1 ≡ dom π2 ∧
  ∀l', predecessors π1 l' ⊆ predecessors π2 l'.

Infix "≾" := approx (at level 70, no associativity).

Lemma approx_reflexive π :
  π ≾ π.
Proof.
  split; eauto.
Qed.

Lemma approx_transitive π1 π2 π3 :
  π1 ≾ π2 → π2 ≾ π3 → π1 ≾ π3.
Proof.
  intros (Heq1 & ?) (Heq2 & ?). split.
  - rewrite Heq1 Heq2 //.
  - intros. eapply transitivity; eauto.
Qed.

Lemma register_approx l l' π1 π2 :
  π1 ≾ π2 →
  register l l' π1 ≾ register l l' π2.
Proof.
  intros (Heq & Hincl). split.
  - rewrite /register !dom_insert Heq //.
  - intros m'. specialize (Hincl m'). rewrite !predecessors_register.
    destruct (decide (l' = m')); multiset_solver.
Qed.

Lemma foldr_register_approx l (ls' : list L) π1 π2 :
  π1 ≾ π2 →
  foldr (register l) π1 ls' ≾ foldr (register l) π2 ls'.
Proof.
  induction ls' as [| l' ls' ]; [ eauto | intros ].
  simpl. eapply register_approx. eapply IHls'. eauto.
Qed.

Lemma unregister_approx l l' π1 π2 :
  π1 ≾ π2 →
  unregister l l' π1 ≾ unregister l l' π2.
Proof.
  intros (Heq & Hincl). split; [| intros m' ].
  - rewrite /unregister !dom_insert Heq //.
  - rewrite !predecessors_unregister.
    destruct (decide (l' = m')); [ subst m' |].
    + specialize (Hincl l'). multiset_solver.
    + eauto.
Qed.

Lemma approx_insert π1 π2 l' ls1 ls2 :
  π1 ≾ π2 →
  ls1 ⊆ ls2 →
  <[ l' := ls1 ]> π1 ≾ <[ l' := ls2 ]> π2.
Proof.
  rewrite /approx. intros (Hdom & Hcodom) ?. split.
  - rewrite ?dom_insert Hdom //.
  - intros m'.
    destruct (decide (l' = m')); [ subst m' |]; multiset; eauto.
Qed.

Lemma approx_delete π l' ps1 ps2 :
  π !! l' = Some ps1 →
  ps2 ⊆ ps1 →
  <[l':=ps2]> π ≾ π.
Proof.
  intros Hπl' ?.
  assert (l' ∈ dom π) by eauto with in_dom.
  apply Some_predecessors in Hπl'.
  split.
  - rewrite dom_insert. multiset_solver.
  - intros m'.
    destruct (decide (l' = m')); [ subst m' |]; multiset; multiset_solver.
Qed.

(* Coincidence and mirror are upward-closed, while closure is downward-closed.
   This allows us to store the following result: *)

Lemma invariant_closure_approx σ π1 π π2 :
  invariant σ π1 →
  closure σ π2 →
  π1 ≾ π → π ≾ π2 →
  invariant σ π.
Proof.
  intros (? & Hmirror & _) Hclo (? & Hcodom1) (_ & Hcodom2).
  split; [| split ].
  { eauto using coincidence_domain. }
  { intros l l'. specialize (Hmirror l l'). specialize (Hcodom1 l' l). lia. }
  { intros l l' Hl.
    specialize (Hclo l l'). eapply Hclo.
    revert Hl. rewrite !elem_of_multiplicity.
    specialize (Hcodom2 l' l). lia. }
Qed.

Lemma invariant_approx σ π1 π π2 :
  invariant σ π1 →
  invariant σ π2 →
  π1 ≾ π → π ≾ π2 →
  invariant σ π.
Proof.
  intros ? (_ & _ & ?) ? ?. eauto using invariant_closure_approx.
Qed.

(* ------------------------------------------------------------------------ *)

(* The invariant is preserved by allocation. *)

Hint Extern 1 (_ ∈ dom _) => multiset_solver : in_dom.

Lemma invariant_alloc σ π l b :
  invariant σ π →
  l ∉ dom σ →
  b ≠ deallocated →
  (∀ l', l' ∈ pointers b → l' ∈ dom π) →
  invariant (<[l:= b]> σ) (set_fold (register l) (<[l:=∅]> π) (pointers b)).
Proof.
  intros (? & ? & ?). split; [| split ].
  (* Coincidence. *)
  { eapply coincidence_domain.
    eauto using coincidence_alloc.
    rewrite dom_foldr_register; [ eauto |].
    intros l' Hl'. apply gmultiset_in_elements_in_set in Hl'.
    multiset_solver. }
  (* Mirror. *)
  { eauto using mirror_alloc. }
  (* Closure. *)
  { eauto using closure_foldr_register, closure_alloc with in_dom. }
Qed.

(* The invariant is preserved when a block is updated. *)

Lemma invariant_update_precise σ l b b' π :
  invariant (<[l:=b]> σ) π →
  b ≠ deallocated →
  b' ≠ deallocated →
  (∀ l', l' ∈ new_pointers b b' → l' ∈ dom π) →
  let π'  := set_fold (unregister l) π (old_pointers b b') in
  let π'' := set_fold (register l) π' (new_pointers b b') in
  invariant (<[l:=b']> σ) π''.
Proof.
  intros (? & Hmirror & ?). split; [| split ].

  (* The mirror property guarantees that every outgoing pointer of the
     block [b] is in the domain of [π]. *)
  assert (∀ l', l' ∈ old_pointers b b' → l' ∈ dom π).
  { rewrite /old_pointers. intros l' Hl'.
    apply elem_of_difference_is_elem_of_lhs in Hl'.
    specialize (Hmirror l l').
    rewrite successors_insert in Hmirror.
    eapply (predecessors_in_dom_dst _ l).
    revert Hl'. rewrite !elem_of_multiplicity. lia. }

  (* Coincidence. *)
  { eapply (coincidence_update _ _ b b'); eauto.
    eapply coincidence_domain; eauto.
    rewrite dom_foldr_register; [| eauto with dom ].
    rewrite dom_foldr_unregister; [| eauto with dom ].
    eauto. }
  (* Mirror. *)
  { eauto using mirror_update. }
  (* Closure. *)
  { eauto using closure_update. }
Qed.

Lemma invariant_update_precise_weak σ l b b' π :
  invariant (<[l:=b]> σ) π →
  b ≠ deallocated →
  b' ≠ deallocated →
  (∀ l', l' ∈ new_pointers b b' → l' ∈ dom π) →
  let π' := set_fold (register l) π (new_pointers b b') in
  invariant (<[l:=b']> σ) π'.
Proof.
  intros (? & Hmirror & ?). split; [| split ].

  (* Coincidence. *)
  { eapply (coincidence_update _ _ b b'); eauto.
    eapply coincidence_domain; eauto.
    rewrite dom_foldr_register; eauto with dom. }
  (* Mirror. *)
  { eauto using mirror_update_weak. }
  (* Closure. *)
  { eauto using closure_update_weak. }
Qed.

Lemma invariant_update_imprecise σ l b b' π π' :
  invariant (<[l:=b]> σ) π →
  b ≠ deallocated →
  b' ≠ deallocated →
  (∀ l', l' ∈ new_pointers b b' → l' ∈ dom π) →
  set_fold (unregister l) π (old_pointers b b') ≾ π' → π' ≾ π →
  invariant (<[l:=b']> σ) (set_fold (register l) π' (new_pointers b b')).
Proof.
  intros Hinv ? ? ? Hlo Hhi.
  eapply invariant_closure_approx; [ | |
    eapply foldr_register_approx; exact Hlo
  | eapply foldr_register_approx; exact Hhi ].
  - eapply invariant_update_precise; eauto.
  - eapply closure_semi_update. eapply Hinv.
Qed.

(* Same as invariant_update_imprecise but does not take into
   account predecessors. *)
Lemma invariant_update_imprecise_weak σ l b b' π :
  invariant (<[l:=b]> σ) π →
  b ≠ deallocated →
  b' ≠ deallocated →
  (∀ l', l' ∈ new_pointers b b' → l' ∈ dom π) →
  invariant (<[l:=b']> σ) (set_fold (register l) π (new_pointers b b')).
Proof.
  intros Hinv ? ? Hhi.
  eapply invariant_closure_approx; try apply approx_reflexive.
  - eapply invariant_update_precise_weak; eauto.
  - eapply closure_semi_update.
    eapply Hinv; apply approx_reflexive.
Qed.

(* The invariant is preserved by deallocation. *)

(* MODIFIED *)
Lemma invariant_free σ π locs ls :
  invariant σ π →
  locs ⊆ dom σ →
  (forall l, l ∉ locs -> l ∈ ls -> freed σ l) ->
  (∀ l l', l' ∈ locs → l ∈ predecessors π l' → l ∈ locs \/ l ∈ ls) →
  invariant (deallocate locs σ) (gmap_mdelete locs π).
Proof.
  intros (? & ? & ?). split; [| split ];
  eauto using coincidence_free, mirror_free, closure_free.
Qed.

(* The invariant is preserved by cleanup. *)

Lemma invariant_cleanup σ π l' ls ms :
  invariant σ π →
  l' ∈ dom π →
  predecessors π l' = ls →
  (∀m, m ∈ ms → freed σ m) →
  invariant σ (<[ l' := ls ∖ ms ]> π).
Proof.
  intros (? & ? & ?). split; [| split ].
  - eapply coincidence_domain; [ eauto |]. multiset_solver.
  - eauto using mirror_cleanup.
  - eauto using closure_cleanup.
Qed.

End Predecessors.

Infix "≾" := approx (at level 70, no associativity).

Global Hint Resolve approx_reflexive approx_insert approx_delete : approx.
Global Hint Extern 1 (_ ⊆ _) => multiset_solver : approx.
