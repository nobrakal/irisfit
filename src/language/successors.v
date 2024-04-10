From stdpp Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.
From irisfit.spacelang Require Import stdpp gset_fixpoint hypotheses.

(* This file contains mathematical results about the notions of successor,
   reachability, garbage collection, agreement between the physical store
   and the conceptual store, etc. *)

(* ------------------------------------------------------------------------ *)

Section Successors.

(* We expect a countable type [L] of locations and an inhabited type [B]
   of blocks. *)

Context `{ Hypotheses L B }.

(* ------------------------------------------------------------------------ *)

(* Basic definitions. *)

(* A store [s] is a finite map of locations to blocks. *)

Implicit Types s : gmap L B.

(* We write [locs] for a set of locations. *)

Implicit Types locs : gset L.

Implicit Types r : gset L.

(* With respect to the store [s], there is an edge of [l] to [l'] iff [l']
   is a successor of [l]. *)

Definition successor s l l' :=
  l' ∈ successors s l.

(* ------------------------------------------------------------------------ *)

(* Reachability. *)

(* An address [l] is reachable if and only there is a path from some
   root to [l]. *)

Definition reachable r s l :=
  ∃ x, x ∈ r ∧ rtc (successor s) x l.

(* The physical store and the conceptual stores are closed under successors.
   The physical store has no dangling pointers. The conceptual store can have
   dangling pointers, which means that a block can contain a deallocated
   location [l']; nevertheless, [l'] is still in the domain of the store. *)

Definition closed r s :=
  r ⊆ dom s /\
  ∀ l l',
  successor s l l' →
  l' ∈ dom s.

(* ------------------------------------------------------------------------ *)

(* Decidability of reachability. *)

(* In order to prove decidability of reachability, we build the reachability
   finite decidable set by iterating the function [add_successors] enough
   times on [roots] *)

Definition add_successors s (X : gset L) : gset L :=
  X ∪ ⋃ (map (fun l => dom (successors s l)) (elements X)).

Lemma add_successors_spec s X y :
  y ∈ add_successors s X <-> y ∈ X \/ exists x, x ∈ X /\ successor s x y.
Proof.
  rewrite elem_of_union.
  apply or_iff_compat_l.
  rewrite elem_of_union_list.
  split.
  - intros (Y & HY & Yy).
    apply elem_of_list_In, in_map_iff in HY.
    destruct HY as (x & <- & xX).
    exists x; split.
    + now apply elem_of_elements, elem_of_list_In.
    + now apply gmultiset_elem_of_dom.
  - intros (x & xX & xy).
    exists (dom (successors s x)); split.
    + rewrite elem_of_list_In in_map_iff.
      exists x; split; auto.
      now apply elem_of_list_In, elem_of_elements.
    + now apply gmultiset_elem_of_dom.
Qed.

(* We use the fixed point construction from our [gset_fixpoint], for which we
   require a upper bound on the iterated function and the starting set. We use
   the successors of the domain of [s] as our bound *)

Lemma add_successors_bounded s X r :
  X ⊆ r ∪ add_successors s (dom s) ->
  add_successors s X ⊆ r ∪ add_successors s (dom s).
Proof.
  intros HX y.
  rewrite !add_successors_spec.
  intros [ | (x & Hx & xy) ].
  - set_solver.
  - pose proof xy as xy'.
    unfold successor, successors in xy.
    destruct (s !! x) eqn:E; last inversion xy.
    destruct_decide (decide (y ∈ r)). set_solver.
    apply elem_of_union. right. apply add_successors_spec.
    right; exists x; split; auto.
    eapply prove_in_dom; eauto.
Qed.

(* We can now define the finite set of reachable locations *)

Definition reachable_gset s r : gset L :=
  gset_fixpoint
    (add_successors s)              (* iterated function *)
    r                               (* starting set *)
    (r ∪ add_successors s (dom s)) (* bound *).

(* The correspondance between [reachable] and [reachable_gset] is an induction
   on the reflexivity transitive closure of [successor] in one direction, and
   the induction principle for [gset_fixpoint] in the other direction *)

Lemma roots_reachable s r :
  r ⊆ reachable_gset s r.
Proof.
  eapply gset_fixpoint_upper with (n := 0).
  - intro. unfold add_successors. apply union_subseteq_l.
  - set_solver.
  - intros; now apply add_successors_bounded.
Qed.

Lemma succ_reachable s r x y :
  successor s x y ->
  x ∈ reachable_gset s r ->
  y ∈ reachable_gset s r.
Proof.
  intros xy Hx.
  unfold reachable_gset.
  erewrite <-(gset_fixpoint_limit _ _ _).
  - apply add_successors_spec. right. eauto.
  - intro. unfold add_successors. apply union_subseteq_l.
  - set_solver.
  - intros; now apply add_successors_bounded.
Qed.

Lemma rtc_succ_reachable s r x y :
  rtc (successor s) x y ->
  x ∈ reachable_gset s r ->
  y ∈ reachable_gset s r.
Proof.
  intros T Hl.
  eapply (rtc_ind_r (fun x => x ∈ reachable_gset s r)); eauto.
  intros; eapply succ_reachable; eauto.
Qed.

Lemma reachable_gset_spec s r l : reachable r s l <-> l ∈ reachable_gset s r.
Proof.
  split.
  - intros (x & Hr & S).
    eapply rtc_succ_reachable; eauto.
    eapply roots_reachable; eauto.
  - eapply gset_fixpoint_ind.
    + intro. unfold add_successors. apply union_subseteq_l.
    + set_solver.
    + intros; now apply add_successors_bounded.
    + intros x Hr. exists x. repeat constructor. apply Hr.
    + intros X IH e He.
      apply add_successors_spec in He.
      destruct He as [He | (x & Hx & xe)]; auto.
      destruct (IH x Hx) as (y & Hy & yx).
      exists y. eauto with rtc.
Qed.

(* Thanks to its characterization via decidable sets, reachability is
   decidable *)

Global Instance decision_reachable s r l :
  Decision (reachable r s l).
Proof.
  destruct (decide (l ∈ reachable_gset s r)); [ left | right ];
    now rewrite reachable_gset_spec.
Qed.

(* ------------------------------------------------------------------------ *)

(* Garbage collection. *)

(* The evolution of a memory block under the action of the GC is to possibly
   be replaced with a deallocated block. However, this is permitted only if
   this block is unreachable. The GC is nondeterministic: we do not require
   that every unreachable block be immediately deallocated. *)

Definition block_evolution unreachable b1 b2 :=
  b1 = b2 ∨
  unreachable ∧ b2 = deallocated.

(* The evolution of the store under the action of the GC is the pointwise
   extension of the relation that describes the evolution of a block. *)

Definition store_evolution r s1 s2 :=
  dom s1 = dom s2 ∧
  ∀ l, l ∈ dom s1 →
  let unreachable := ¬ reachable r s1 l in
  block_evolution unreachable (s1 !!! l) (s2 !!! l).

(* Whereas garbage collection is a relation (that is, it is nondeterministic),
   full garbage collection (which collects every unreachable block) is a
   function. *)

Definition collect_block r s l b : option B :=
  Some (if decide (reachable r s l) then b else deallocated).

Definition collect r s : gmap L B :=
  map_imap (collect_block r s) s.

(* ------------------------------------------------------------------------ *)

(* Miscellaneous little lemmas. *)

Lemma in_dom_insert_otherwise l m b s :
  l ∈ dom s →
  l ∈ dom (<[m := b]> s).
Proof.
  rewrite dom_insert. set_solver.
Qed.

Local Hint Resolve in_dom_insert_otherwise : in_dom closed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [successors] and [successor]. *)

Lemma prove_successor s l b l' :
  s !! l = Some b →
  l' ∈ pointers b →
  successor s l l'.
Proof.
  intros Hl ?. rewrite /successor /successors Hl //.
Qed.

Lemma successors_insert s l b :
  successors (<[l:=b]> s) l = pointers b.
Proof.
  rewrite /successors lookup_insert //.
Qed.

Lemma successors_insert_ne s l b l' :
  l ≠ l' →
  successors (<[l:=b]> s) l' = successors s l'.
Proof.
  intros. rewrite /successors lookup_insert_ne //.
Qed.

Lemma successor_insert s l b l' :
  successor (<[l:=b]> s) l l' <-> l' ∈ pointers b.
Proof.
  rewrite /successor successors_insert //.
Qed.

Lemma successor_insert_ne s l b l1 l2 :
  l ≠ l1 →
  successor (<[l:=b]> s) l1 l2 <-> successor s l1 l2.
Proof.
  intros. unfold successor. rewrite successors_insert_ne //.
Qed.

Lemma successor_deallocate_outside s locs l1 l2 :
  l1 ∉ locs →
  successor (deallocate locs s) l1 l2 <-> successor s l1 l2.
Proof.
  intros. unfold successor. rewrite successors_deallocate_outside //.
Qed.

Lemma successor_deallocate_implication s locs l1 l2 :
  successor (deallocate locs s) l1 l2 →
  successor s l1 l2.
Proof.
  pose proof (successors_deallocate_implication locs s l1).
  rewrite /successor. eauto using gmultiset_elem_of_subseteq.
Qed.

Lemma same_successors s s' l :
  dom s = dom s' →
  l ∈ dom s →
  s !!! l = s' !!! l →
  successors s l = successors s' l.
Proof.
  intros Hdom Hl Heq. unfold successors.
  rewrite Hdom in Hl.
  rewrite !lookup_lookup_total_dom //.
  rewrite Heq //. rewrite Hdom //.
Qed.

Lemma same_successor s s' l l' :
  dom s = dom s' →
  l ∈ dom s →
  s !!! l = s' !!! l →
  successor s l l' <-> successor s' l l'.
Proof.
  intros. unfold successor. rewrite (same_successors s s' l) //.
Qed.

Lemma successor_in_dom s l l' :
  successor s l l' →
  l ∈ dom s.
Proof.
  rewrite /successor /successors.
  rewrite elem_of_dom.
  destruct (s !! l).
  + eauto.
  + set_solver.
Qed.

Local Hint Resolve successor_in_dom : in_dom.

Lemma nonexistent_successor s l l' :
  s !! l = None →
  successor s l l' →
  False.
Proof.
  rewrite /successor /successors. intros ->. set_solver.
Qed.

Lemma closed_rtc_in_dom s r l l' :
  closed r s →
  rtc (successor s) l l' →
  l ∈ dom s → l' ∈ dom s.
Proof.
  intros (?&?).
  induction 1; eauto.
Qed.

Local Hint Resolve closed_rtc_in_dom : in_dom.

(* ------------------------------------------------------------------------ *)

(* A heap edge is an edge that does not lead to a stack cell. *)

Definition heap_edge r s l l' :=
  successor s l l' ∧ l' ∉ r.

Local Hint Unfold heap_edge : core.

(* A heap path is a path composed of heap edges. *)

(* A heap edge is (in particular) a successor edge. *)

Lemma heap_edge_implies_successor s r l l' :
  heap_edge r s l l' →
  successor s l l'.
Proof.
  destruct 1. eauto.
Qed.

Local Hint Resolve heap_edge_implies_successor : core.

Lemma prove_heap_edge_insert_eq r c cell s l :
  l ∈ pointers cell →
  c ∈ r →
  l ∉ r →
  heap_edge r (<[c:=cell]> s) c l.
Proof.
  constructor.
  + rewrite successor_insert //.
  + assert (l ≠ c) by (intros ->; tauto).
    eauto.
Qed.

Local Hint Resolve prove_heap_edge_insert_eq : core.

Lemma heap_path_implies_path s r l l' :
  rtc (heap_edge r s) l l' →
  rtc (successor s) l l'.
Proof.
  eauto using rtc_subrel.
Qed.

Local Hint Resolve heap_path_implies_path : core.


(* If there is a path from some root to [l], then there is also a heap path
   from some root to [l]. The intuition is to keep only the last part of the
   path, from the last root that is encountered along the way to [l]. *)

Lemma existence_of_heap_path_preliminary s r l l' :
  rtc (successor s) l l' →
  ∀ x,
  x ∈ r →
  rtc (heap_edge r s) x l →
  ∃ x,
  x ∈ r ∧
  rtc (heap_edge r s) x l'.
Proof.
  induction 1 as [| l m l' Hedge ? ? ]; [ eauto | intros ].
  destruct_decide (decide (m ∈ r)); eauto with rtc.
Qed.

Lemma existence_of_heap_path s r x l :
  x ∈ r →
  rtc (successor s) x l →
  ∃ x,
  x ∈ r ∧ rtc (heap_edge r s) x l.
Proof.
  eauto using existence_of_heap_path_preliminary with rtc.
Qed.

(* A memory location [l] is reachable (via an arbitrary path) if and
   only if it is reachable via a heap path. This gives us a tight
   characterization of reachability that can be useful when reasoning
   about updates to stack cells. *)

Lemma reachable_via_heap_path s r l :
  reachable r s l <->
  ∃ x, x ∈ r ∧ rtc (heap_edge r s) x l.
Proof.
  split; intros (x & ? & ?).
  - eauto using existence_of_heap_path.
  - exists x. eauto using rtc_subrel.
Qed.

(* A heap edge whose source is not [c] is preserved by an update to [c]. *)

Lemma heap_edge_cell_update c r cell s l l' :
  c ∈ r →
  l ≠ c →
  heap_edge r (<[c:=cell]> s) l l' <->
  heap_edge r s l l'.
Proof.
  intros ? ?. rewrite /heap_edge. split; intros (Hsucc & Hnroot).
  + rewrite -> successor_insert_ne in Hsucc by eauto.
    assert (c ≠ l') by (intros ->; tauto). eauto.
  + rewrite -> successor_insert_ne by eauto.
    assert (c ≠ l') by (intros ->; tauto).
    eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [reachable]. *)

Lemma reachable_snoc s r l l' :
  reachable r s l →
  successor s l l' →
  reachable r s l'.
Proof.
  intros (x & ? & ?) ?. exists x. eauto with rtc.
Qed.

Local Hint Resolve reachable_snoc : reachable.

Lemma reachable_path s r l l' :
  rtc (successor s) l l' →
  reachable r s l →
  reachable r s l'.
Proof.
  induction 1; eauto with reachable.
Qed.

Local Hint Resolve reachable_path : reachable.

Lemma reachable_heap_path s r l l' :
  rtc (heap_edge r s) l l' →
  reachable r s l →
  reachable r s l'.
Proof.
  induction 1; eauto with reachable.
Qed.

Local Hint Resolve reachable_heap_path : reachable.

Lemma roots_are_reachable s r l :
  l ∈ r →
  reachable r s l.
Proof.
  intros. exists l. eauto with rtc.
Qed.

Lemma reachable_mono_roots r1 r2 σ l :
  r1 ⊆ r2 ->
  reachable r1 σ l ->
  reachable r2 σ l.
Proof.
  intros ? (r,(?&?)).
  exists r. split; try done. set_solver.
Qed.

Lemma reachable_union r1 r2 x y :
  reachable (r1 ∪ r2) x y <-> (reachable r1 x y \/ reachable r2 x y).
Proof.
  split; last first.
  { intros [|]; eapply reachable_mono_roots; only 2,4:done; set_solver. }
  { intros (l,(Hl&?)). apply elem_of_union in Hl. destruct Hl; [left|right]; eexists; naive_solver. }
Qed.

Local Hint Resolve roots_are_reachable : reachable.

Lemma rtc_implies_reachable s r l l' :
  rtc (successor s) l l' →
  l ∈ r →
  reachable r s l'.
Proof.
  rewrite /reachable. eauto.
Qed.

Local Hint Resolve rtc_implies_reachable : reachable.

(* If two stores [s1] and [s2] have the same domain and agree on the content
   of the blocks that are reachable in [s1], then every block that is
   reachable in [s1] is also reachable in [s2]. *)

Lemma prove_reachable_implication s1 s2 r :
  dom s1 = dom s2 →
  (∀ l, l ∈ dom s1 -> reachable r s1 l → s1 !!! l = s2 !!! l) →
  ∀ l, reachable r s1 l → reachable r s2 l.
Proof.
  intros ? Hag l (x & Hroot1 & Hpath).
  assert (Hreach1: reachable r s1 x) by eauto with reachable.
  assert (Hreach2: reachable r s2 x) by eauto with reachable.
  clear Hroot1. revert Hreach1 Hreach2.
  induction Hpath as [ x | x x' l Hedge1 _ IH ]; [ eauto |]. intros.
  assert (Hedge2: successor s2 x x')
    by (rewrite -same_successor; eauto with in_dom).
  eauto with reachable.
Qed.

(* If two stores [s1] and [s2] have the same domain and agree on the content
   of the blocks that are reachable in [s1] or [s2], then they have the same
   reachable blocks. *)

Lemma prove_reachable_coincidence r s1 s2 :
  dom s1 = dom s2 →
  (∀ l, reachable r s1 l → s1 !!! l = s2 !!! l) →
  (∀ l, reachable r s2 l → s1 !!! l = s2 !!! l) →
  ∀ l, reachable r s1 l ↔ reachable r s2 l.
Proof.
  intros Hd ? ?. symmetry in Hd.
  split; eauto using prove_reachable_implication, eq_sym.
Qed.

(* Analogous storements for group deallocation. *)

Lemma rtc_successor_deallocate_direct x s locs l' :
  rtc (successor s) x l' →
  (∀ l, l ∈ locs → ¬ rtc (successor s) x l) →
  rtc (successor (deallocate locs s)) x l'.
Proof.
  induction 1 as [| r ? l' Hsucc Hrtc IH ]; intros Hunreachable; econstructor.
  - case (decide (r ∈ locs)); intro Hr.
    { exfalso. apply Hunreachable in Hr. eauto with rtc. }
    { rewrite successor_deallocate_outside //. }
  - eapply IH. repeat intro. eapply (Hunreachable l); [ eauto |].
    eauto using successor_deallocate_implication with rtc.
Qed.

Lemma rtc_successor_deallocate_reverse x s locs l' :
  rtc (successor (deallocate locs s)) x l' →
  rtc (successor s) x l'.
Proof.
  induction 1 as [| r ? l' Hsucc Hrtc IH ]; econstructor;
  eauto using successor_deallocate_implication.
Qed.

Lemma rtc_successor_deallocate x s locs l' :
  (∀ l, l ∈ locs → ¬ rtc (successor s) x l) →
  rtc (successor (deallocate locs s)) x l' ↔
  rtc (successor s) x l'.
Proof.
  split; eauto using rtc_successor_deallocate_direct,
  rtc_successor_deallocate_reverse.
Qed.

Local Lemma tautology1 (P Q : L → Prop) :
  (∀ x, P x ↔ Q x) →
  (∃ x, P x) ↔ (∃ x, Q x).
Proof.
  firstorder.
Qed.

Local Lemma tautology2 (A C1 C2 : Prop) :
 (A → (C1 ↔ C2)) →
  A ∧ C1 ↔ A ∧ C2.
Proof.
  tauto.
Qed.


Lemma reachable_deallocate s r locs l' :
  (∀ l, l ∈ locs → ¬ reachable r s l) →
  reachable r (deallocate locs s) l' <->
  reachable r s l'.
Proof.
  intro Hunreachable. rewrite /reachable. apply tautology1; intro.
  apply tautology2. intros.
  rewrite rtc_successor_deallocate //.
  repeat intro. eapply Hunreachable; eauto with reachable.
Qed.

(* If a region is closed under predecessors and contains no roots,
   then it is unreachable. *)

Lemma cannot_enter s locs :
  (∀ l l', l' ∈ locs → l' ∈ successors s l → l ∈ locs) →
  (∀ m m', rtc (successor s) m m' → m' ∈ locs → m ∈ locs).
Proof.
  unfold successor. induction 2; eauto.
Qed.

Lemma prove_unreachable_region s r locs :
  (∀ l, l ∈ locs → l ∉ r) →
  (∀ l l', l' ∈ locs → l' ∈ successors s l → l ∈ locs) →
  (∀ l, l ∈ locs → ¬ reachable r s l).
Proof.
  intros Hnoroot Hclosed ?? (x & ? & ?).
  assert (x ∉ r). eauto using cannot_enter.
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [closed] and [reachable]. *)

Lemma closed_reachable_in_dom s r l :
  closed r s →
  reachable r s l →
  l ∈ dom s.
Proof.
  intros Hclosed (x & ? & Hrtc).
  eapply closed_rtc_in_dom; eauto. destruct Hclosed. set_solver.
Qed.

Local Hint Resolve closed_reachable_in_dom : in_dom.

(* [closed_insert] is used both when a new block is allocated and when
   an existing block is deallocated. *)

(* We could allow [pointers b ⊆ dom s ∪ {[+l+]}], but that does not seem
   useful. *)

Lemma closed_insert s r l b :
  closed r s →
  (∀l, l ∈ pointers b → l ∈ dom s) →
  closed r (<[l:=b]> s).
Proof.
  intros (?&Hclosed) Hb. split.
  rewrite dom_insert_L. set_solver.
  intros x y. unfold successor. intros Hsucc.
  case (decide (x = l)); [ intros; subst x | intros Hx ].
  { rewrite successors_insert in Hsucc.
    apply Hb in Hsucc. set_solver. }
  { rewrite -> successors_insert_ne in Hsucc by eauto.
    unfold closed in Hclosed.
    eauto with in_dom. }
Qed.

Lemma closed_insert_no_successors s r l b :
  closed r s →
  pointers b = ∅ →
  closed (r ∪ {[l]}) (<[l:=b]> s).
Proof.
  intros (?&Hclosed) Hb. split.
  { rewrite dom_insert_L. set_solver. }
  intros x y. unfold successor. intros Hsucc.
  case (decide (x = l)); [ intros; subst x | intros Hx ].
  { rewrite successors_insert in Hsucc. exfalso.
    rewrite Hb in Hsucc. set_solver. }
  { rewrite -> successors_insert_ne in Hsucc by eauto.
    unfold closed in Hclosed.
    eauto with in_dom. }
Qed.

Local Hint Resolve
  closed_insert_no_successors
: closed.

(* If, after an update of the stack cell [c], the location [l] is accessible
   via a heap path from some root [r], and if [c] and [r] are distinct, then
   this heap path already existed before this update. *)

Lemma heap_path_cell_update_reverse c cell s r x l :
  rtc (heap_edge r (<[c:=cell]> s)) x l →
  c ∈ r →
  x ≠ c →
  rtc (heap_edge r s) x l.
Proof.
  induction 1 as [| x k l Hedge ? ? ]; intros.
  - eauto with rtc.
  - rewrite -> heap_edge_cell_update in Hedge by eauto.
    assert (c ≠ k).
    { intros ->. destruct Hedge. tauto. }
    eauto with rtc.
Qed.

(* The reciprocal storement. *)

Lemma heap_path_cell_update_direct c r cell s x l :
  rtc (heap_edge r s) x l →
  c ∈ r →
  x ≠ c →
  rtc (heap_edge r (<[c:=cell]> s)) x l.
Proof.
  induction 1 as [| x k l Hedge ? ? ]; intros.
  - eauto with rtc.
  - rewrite <- heap_edge_cell_update in Hedge by eauto.
    assert (c ≠ k).
    { intros ->. destruct Hedge. tauto. }
    eauto with rtc.
Qed.

(* The combined storement. *)

Lemma heap_path_cell_update c r cell s x l :
  c ∈ r →
  x ≠ c →
  rtc (heap_edge r (<[c:=cell]> s)) x l <->
  rtc (heap_edge r s) x l.
Proof.
  split; eauto using heap_path_cell_update_direct,
                     heap_path_cell_update_reverse.
Qed.

(* [reachable_from s P l] means that the [l] is reachable from some root [r]
   that satisfies [P r]. *)

Definition reachable_from r s P l :=
  ∃ x, x ∈ r ∧ rtc (heap_edge r s) x l ∧ P x.

Hint Unfold reachable_from : reachable.

Lemma reachable_from_reachable s r P l :
  reachable_from r s P l →
  reachable r s l.
Proof.
  destruct 1 as (x & ? & ? & ?). exists x.
  split; [ eauto |].
  eauto using heap_path_implies_path.
Qed.

Local Hint Resolve reachable_from_reachable : reachable.

(* If [c] is a root, then to be reachable is to be reachable from [c]
   or from some root other than [c]. *)

Lemma to_be_or_not_to_be s r l c :
  c ∈ r →
  reachable r s l ↔
    reachable_from r s (λ x : L, x ≠ c) l ∨
    rtc (heap_edge r s) c l.
Proof.
  split.
  { intros Hreach.
    rewrite -> reachable_via_heap_path in Hreach.
    destruct Hreach as (x & ? & ?).
    case (decide (x = c)); intro; subst.
    + right. eauto.
    + left. eauto with reachable. }
  { intuition eauto with reachable. }
Qed.

(* If, after writing [c := cell], a memory location [l] is reachable from
   some root [r] other than [c], then it was already reachable from [r]
   prior to this update, and vice-versa. *)

Lemma reachable_from_cell_update_ne s r c cell l :
  c ∈ r →
  reachable_from r (<[c:=cell]> s) (λ x, x ≠ c) l <->
  reachable_from r s (λ x, x ≠ c) l.
Proof.
  split; intros (x & ? & ? & ?); exists x; repeat split; eauto.
  - rewrite <- heap_path_cell_update; eauto.
  - rewrite -> heap_path_cell_update; eauto.
Qed.

(* If, after writing [c := cell], a memory location [l] is reachable from
   the root [c], then either [l] is [c] or [l] was already reachable from
   some successor [r] of [c] prior to this update, and vice-versa. *)

Lemma reachable_from_cell_update_eq s c r cell l :
  c ∈ r →
  rtc (heap_edge r (<[c:=cell]> s)) c l <->
  l = c ∨ ∃ x, x ∉ r  ∧ x ∈ pointers cell ∧ rtc (heap_edge r s) x l.
Proof.
  intros ?. split.
  { inversion 1 as [| ? x ? Hedge Hpath ]; [ eauto | right; subst ].
    destruct Hedge as [ Hedge ? ].
    assert (x ≠ c) by (intros ->; eauto).
    rewrite /successor /successors lookup_insert in Hedge.
    rewrite -> heap_path_cell_update in Hpath by eauto.
    eauto. }
  { intros [ ? | (x & ? & ? & Hpath) ].
    + subst l. eauto with rtc.
    + assert (heap_edge r (<[c:=cell]> s) c x) by eauto.
      assert (x ≠ c) by (intros ->; eauto).
      rewrite <- heap_path_cell_update in Hpath by eauto.
      eauto with rtc. }
  (* Ouf. *)
Qed.

(* A combination of the previous two lemmas. *)

(* The reachable memory locations after writing [c := cell] are those that
   were already reachable from some root other than [c], plus [c] itself,
   plus the locations that were already reachable from [cell]. *)

(* This very precise (hence painful) update lemma is required in order to
   show that [store_agreement] is preserved by an update to a cell. *)

Lemma reachable_cell_update s c r cell l :
  c ∈ r →
  reachable r (<[c:=cell]> s) l <->
    reachable_from r s (λ x, x ≠ c) l ∨
    l = c ∨
    ∃ x, x ∉ r ∧ x ∈ pointers cell ∧ rtc (heap_edge r s) x l.
Proof.
  intros .
  rewrite <- reachable_from_cell_update_eq by eauto.
  rewrite <- reachable_from_cell_update_ne by eauto.
  eapply to_be_or_not_to_be. eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* The above lemmas are true, but several of them are overkill. I have seen
   the light, midway through. Here is a simpler lemma, which stores that the
   set of reachable objects does not increase when a memory block is updated,
   provided of course that the new pointers that are written to the block are
   pointers to reachable objects. *)

(* We enter by proving that, if there is a path from [r] to [m] after a heap
   update, then either this path existed already before the update, or a path
   existed from some location that appears in [b'] to the location [m]. *)

Lemma analyze_path_after_heap_update s l b b' x m :
  s !! l = Some b →
  rtc (successor (<[l := b']> s)) x m →
    rtc (successor s) x m ∨
    ∃ x, x ∈ pointers b' ∧ x ∉ pointers b ∧ rtc (successor s) x m.
Proof.
  induction 2 as [| x r' m Hedge Hpath IH ]; [ eauto with rtc |].
  case (decide (l = x)); intro.
  (* Case: the path of interest goes through the block at [l]. *)
  { subst l.
    rewrite -> successor_insert in Hedge.
    destruct IH as [ IH | IH ]; [| right; eauto ].
    case (decide (r' ∈ pointers b)); intro.
    (* Subcase: the path of interest goes through an edge that exists
       both before and after the update. Easy. *)
    - left. eauto using prove_successor with rtc.
    (* Subcase: the path of interest goes through an edge that is
       destroyed by the update. *)
    - right. exists r'. eauto. }
  (* Case: the path of interest does not go through [l]. Easy. *)
  { rewrite -> successor_insert_ne in Hedge by eauto.
    intuition eauto with rtc. }
Qed.

(* Here is the promised lemma: if [m] is reachable after the heap update
   [l := b'], then [m] was reachable already before this update. The side
   conditions are that every new pointer in [pointers b' ∖ pointers b] is
   to a reachable object and that the location [l] is not magically turned
   into a stack cell. *)

Lemma analyze_reachable_after_heap_update s r l b b' m :
  s !! l = Some b →
  (∀ l, l ∈ pointers b' → l ∉ pointers b → reachable r s l) →
  reachable r (<[l := b']> s) m →
  reachable r s m.
Proof.
  intros Hl ? (x & Hroot & Hpath).
  eapply analyze_path_after_heap_update in Hpath; [| eauto ].
  destruct Hpath as [ ? | (r' & ? & ? & Hpath) ]; eauto with reachable.
Qed.

(* The following lemma is analogous to [analyze_path_after_heap_update], but
   concerns the case where a new heap block or stack cell is allocated. *)

(* If there is a path of [r] to [m] after this allocation, then either this
   path existed before, or there exists a path from the new block to [m]. *)

Lemma analyze_path_after_alloc s l b' x m :
  s !! l = None →
  rtc (successor (<[l := b']> s)) x m →
    rtc (successor s) x m ∨
    ∃ x, x ∈ pointers b' ∧ rtc (successor s) x m.
Proof.
  induction 2 as [| x r' m Hedge Hpath IH ]; [ eauto with rtc |].
  case (decide (l = x)); intro.
  (* Case: the path of interest goes through [l]. *)
  { subst l.
    rewrite -> successor_insert in Hedge.
    intuition eauto. }
  (* Case: the path of interest does not go through [l]. *)
  { rewrite -> successor_insert_ne in Hedge by eauto.
    intuition eauto with rtc. }
Qed.

(* The following lemma is analogous to [analyze_reachable_after_heap_update],
   but concerns the case where a new heap block or stack cell is allocated. *)

(* If [l ≠ m] and [m] is reachable after the allocation [l := b'], then [m]
   was reachable already before this update. The side condition is that every
   pointer in [pointers b'] is to a reachable object. *)

Lemma analyze_reachable_after_alloc s r l b' m :
  s !! l = None →
  (∀ l, l ∈ pointers b' → reachable r s l) →
  l ≠ m →
  reachable r (<[l := b']> s) m →
  reachable r s m.
Proof.
  intros Hl Hpointers ? (x & Hroot & Hpath).
  (* Proceeds by cases. *)
  eapply analyze_path_after_alloc in Hpath; [| eauto ].
  destruct Hpath as [ Hpath | (r' & ? & Hpath) ].
  (* Case: the path from [r] to [m] already existed before. *)
  (* Then, we must have [l ≠ r], as shown by the following argument. *)
  + case (decide (l = x)); intro.
    - subst x. exfalso.
      (* The address [l] was not initially allocated, and we have [l ≠ m],
         so we cannot possibly have a path from [l] to [m]. *)
      destruct Hpath as [| x r' m Hedge Hpath ];
      eauto using nonexistent_successor.
    - (* The hypothesis [l ≠ r] implies that [r] remains a root,
         which implies that [m] remains reachable. *)
      eauto with reachable.
  (* Case: there is a path from the block [b'] to [m]. *)
  + eauto with reachable.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [block_evolution]. *)

Lemma block_evolution_monotonic_in_unreachable (u1 u2 : Prop) b b' :
  (u1 → u2) →
  block_evolution u1 b b' →
  block_evolution u2 b b'.
Proof.
  unfold block_evolution. tauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [store_evolution]. *)

Lemma store_evolution_reflexive r s :
  store_evolution r s s.
Proof.
  split; [ eauto |].
  intros l _ ?.
  left. eauto.
Qed.

Lemma store_evolution_transitive r s1 s2 s3 :
  store_evolution r s1 s2 ->
  store_evolution r s2 s3 ->
  store_evolution r s1 s3.
Proof.
  intros [HE1 Hb1] [HE2 Hb2].
  split.
  { apply leibniz_equiv in HE1.
    by rewrite HE1. }
  intros l Hl1 Hu1.
  assert (l ∈ dom s2) as Hl2 by set_solver.
  specialize (Hb2 _ Hl2).
  destruct (Hb1 _ Hl1) as [->| (?&?)].
  { eapply block_evolution_monotonic_in_unreachable; try (apply Hb2).
    intros Hr2 Hr1.
    apply Hr2.
    eapply prove_reachable_implication with s1; try easy.
    intros l' Hl' ?.
    now destruct (Hb1 _ Hl'). }
  { right. split; try easy.
    by destruct Hb2 as [<-| (?&?)]. }
Qed.

Lemma store_evolution_preserves_closedness r s s' :
  closed r s →
  store_evolution r s s' →
  closed r s'.
Proof.
  unfold store_evolution.
  intros (?&Hclosed) (Hdom & Hevol).
  split; first set_solver.
  intros l l' Hsucc.
  assert (Hl: l ∈ dom s) by (rewrite Hdom; eauto with in_dom).
  specialize (Hevol l Hl).
  destruct Hevol as [ ? | (? & Hdealloc) ].
  { rewrite <- Hdom.
    assert (successor s l l') by rewrite same_successor // Hdom //.
    eauto with in_dom. }
  (* A deallocated block has no successor. *)
  { exfalso. unfold successor, successors in Hsucc.
    rewrite -> lookup_lookup_total_dom in Hsucc by eauto with in_dom.
    rewrite Hdealloc in Hsucc.
    rewrite -> pointers_deallocated in Hsucc by eauto.
    set_solver. }
Qed.

Lemma store_evolution_preserves_successor r s1 s2 l l' :
  store_evolution r s1 s2 →
  reachable r s1 l →
  successor s1 l l' <-> successor s2 l l'.
Proof.
  intros (Hdom & Hevol) Hreachable.
  split.
  { intros. assert (Hldom: l ∈ dom s1) by eauto using successor_in_dom.
    specialize (Hevol l Hldom).
    unfold block_evolution in Hevol.
    destruct Hevol as [ Hevol |]; [| tauto ].
    rewrite same_successor // -Hdom //. }
  { intros. assert (Hldom: l ∈ dom s1).
    { rewrite Hdom. eauto using successor_in_dom. }
    specialize (Hevol l Hldom).
    unfold block_evolution in Hevol.
    destruct Hevol as [ Hevol |]; [| tauto ].
    rewrite same_successor // -Hdom //. }
Qed.

Lemma store_evolution_preserves_rtc_successor x r s1 s2 l :
  store_evolution r s1 s2 →
  reachable r s1 x →
  rtc (successor s1) x l <-> rtc (successor s2) x l.
Proof.
  intros; split; induction 1 as [| x k l Hsucc Hrtc IH ]; eauto with rtc.
  { assert (successor s2 x k).
    { rewrite <- store_evolution_preserves_successor by eauto. eauto. }
    eauto with rtc reachable. }
  { assert (successor s1 x k).
    { rewrite -> store_evolution_preserves_successor by eauto. eauto. }
    eauto with rtc reachable. }
Qed.

Lemma store_evolution_preserves_reachable r s1 s2 l :
  store_evolution r s1 s2 →
  reachable r s1 l <-> reachable r s2 l.
Proof.
  intros. split; intros (x & Hroot & Hpath); exists x; split; try done.
  - rewrite -store_evolution_preserves_rtc_successor //.
    eauto with reachable.
  - rewrite store_evolution_preserves_rtc_successor //.
    eauto with reachable.
Qed.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [collect]. *)

Lemma dom_collect s r :
  dom (collect r s) = dom s.
Proof.
  apply leibniz_equiv.
  eapply dom_imap. intros l.
  rewrite elem_of_dom /is_Some.
  split; intros (b & ?); exists b; [ eauto | tauto ].
Qed.

(* ADDED *)
Lemma store_evolution_collect_strong r s1 s2 :
  store_evolution r s1 s2 ->
  store_evolution r s2 (collect r s1).
Proof.
  intros Hs. generalize Hs; intros [Hd He].
  split.
  { rewrite dom_collect //. }
  intros l Hl. generalize Hl. intros ?.
  symmetry in Hd. rewrite Hd in Hl.
  rewrite -> elem_of_dom in Hl.
  apply lookup_lookup_total in Hl.
  destruct (He l) as [Hel|(Hel&?)].
  { rewrite -Hd //. }
  { rewrite (lookup_total_alt (collect r s1)).
    rewrite /collect.
    rewrite map_lookup_imap.
    rewrite -Hel Hl. simpl.
    rewrite /block_evolution.
    case (decide (reachable r s1 l)); eauto.
    intros. rewrite store_evolution_preserves_reachable in n; eauto. }
  { right. rewrite -store_evolution_preserves_reachable; eauto.
    split; try easy. rewrite (lookup_total_alt (collect r s1)).
    rewrite /collect map_lookup_imap. rewrite Hl.
    simpl. rewrite decide_False //. }
Qed.

Lemma store_evolution_collect r s :
  store_evolution r s (collect r s).
Proof.
  eauto using store_evolution_collect_strong, store_evolution_reflexive.
Qed.

End Successors.

Global Hint Resolve prove_successor : closed.
