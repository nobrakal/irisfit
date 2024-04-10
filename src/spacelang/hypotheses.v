From stdpp Require Import gmap gmultiset.
From iris.proofmode Require Import proofmode.

From irisfit.spacelang Require Import stdpp.

(* This file defines a small set of hypotheses about locations and blocks.
   The files successors.v and predecessors.v depend on these hypotheses. *)

(* ------------------------------------------------------------------------ *)

Class Hypotheses `{Countable L} `{Inhabited B} := {

  (* We assume that a block contains a multiset of outgoing pointers. *)
  pointers: B → gmultiset L;

  (* We assume that a certain special value of type [B] represents a
     deallocated block. *)
  deallocated: B;

    (* MODIFIED added for predecessors *)
  decision_deallocated: ∀b, Decision (b = deallocated);

  (* We assume that a deallocated block has no outgoing pointers. *)
  pointers_deallocated:
    pointers deallocated = ∅;
  }.

(* ------------------------------------------------------------------------ *)

Section Definitions.

Context `{ Hypotheses L B }.

(* The successors of the location [l], a multiset of locations, can
   be read off the heap [σ] as follows. *)

Definition successors (σ : gmap L B) l : gmultiset L :=
  match σ !! l with
  | None =>
      ∅
  | Some b =>
      pointers b
  end.

(* [deallocate ls σ] is the heap [σ] where every location in the set [ls]
   has ben marked as deallocated. *)

Definition deallocate (locs : gset L) (σ : gmap L B) : gmap L B :=
  gmap_mset locs deallocated σ.

(* ------------------------------------------------------------------------ *)

(* Lemmas about [deallocate]. *)

Lemma dom_deallocate locs s :
   dom  (deallocate locs s) ≡ dom s.
Proof.
  rewrite /deallocate. eapply dom_gmap_mset.
Qed.

Lemma successors_deallocate_inside locs s l :
  l ∈ locs →
  successors (deallocate locs s) l = ∅.
Proof.
  intros. rewrite /successors /deallocate.
  case (decide (l ∈ dom s)); intro.
  + rewrite gmap_lookup_mset_inside //.
    eapply pointers_deallocated.
  + rewrite gmap_lookup_mset_outside_dom //.
Qed.

Lemma successors_deallocate_outside locs s l :
  l ∉ locs →
  successors (deallocate locs s) l = successors s l.
Proof.
  intros. rewrite /successors /deallocate gmap_lookup_mset_outside //.
Qed.

Lemma successors_deallocate_implication locs s l :
  successors (deallocate locs s) l ⊆ successors s l.
Proof.
  intros. rewrite /successors.
  case_eq (deallocate locs s !! l).
  { intros b.
    rewrite /deallocate gmap_lookup_mset_Some.
    intros [ (Hl & ?) | (Hl & ?) ].
    - rewrite Hl //.
    - rewrite Hl pointers_deallocated. multiset_solver. }
  { intros Hl. multiset_solver. }
Qed.

End Definitions.
