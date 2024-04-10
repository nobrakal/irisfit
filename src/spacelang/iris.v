From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.

(* A fancy update with access to the store interpretation predicate. *)

Definition supd `{!irisGS Λ Σ} E P Q : Prop :=
  ∀ σ ns κs nt,
  state_interp σ ns κs nt ∗ P ={E}=∗ state_interp σ ns κs nt ∗ Q.

Notation "P ={{ E }}=∗ Q" := (supd E P Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  '/' ={{ E }}=∗  Q ']'").

Lemma supd_True `{!irisGS Λ Σ} E P :
  P ={{E}}=∗ True.
Proof.
  iIntros (σ ns κs n) "[Hstore _]". iFrame "Hstore". eauto.
Qed.

(* The following lemma allows getting hold of the store interpretation
   predicate to help prove that it is permitted to transform [P] into
   [Q] when proving a Hoare triple about an expression [e]. Due to the
   manner in which [wp] is defined in Iris, it is necessary to impose
   the side condition that [e] is not a value. *)

Lemma wp_conseq `{!irisGS Λ Σ} s E e P Q Φ :
  language.to_val e = None →
  (P ={{E}}=∗ Q) →
  (Q -∗ wp s E e Φ) -∗ (P -∗ wp s E e Φ).
Proof.
  iIntros (Hnv Hentail) "H P".
  rewrite wp_unfold /wp_pre Hnv.
  iIntros (σ ns κ κs nt) "S".
  iMod (Hentail σ ns (κ ++ κs) nt with "[$]") as "[S Q]".
  iApply ("H" with "Q").
  iFrame.
Qed.

(* The following should be inserted in algebra/big_op.v under big_opM_union *)

From stdpp Require Import functions gmap gmultiset.
From iris.algebra Require Import monoid.
From iris.prelude Require Import options.
From iris.algebra Require Import big_op.
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

Section BigOp.

  Context `{Monoid M o}.
  Infix "`o`" := o (at level 50, left associativity).

  Section gmap.
    Context `{Countable K} {A : Type}.
    Implicit Types m : gmap K A.

  Lemma big_opM_union_with f (g : A -> A -> A) m1 m2 :
    (∀ i x1 x2, f i (g x1 x2) ≡ f i x1 `o` f i x2) →
    let lift_g x1 x2 := Some (g x1 x2) in
    ([^o map] k↦y ∈ union_with lift_g m1 m2, f k y)
    ≡ ([^o map] k↦y ∈ m1, f k y) `o` ([^o map] k↦y ∈ m2, f k y).
  Proof.
    intro Hfg. intros.
    revert m2. induction m1 as [|i x1 m1 Hm1 IH] using map_ind; intros.
    { by rewrite big_opM_empty !left_id. }
    case_eq (m2 !! i); [ intros x2 Hm2 | intros Hm2 ].
    (* Case: the key [i] is present in [m2]. *)
    { assert (Heq: m2 = <[i:=x2]>(delete i m2))
        by rewrite insert_delete_insert insert_id //.
      rewrite {1}Heq.
      erewrite <- insert_union_with by eauto.
      rewrite {2}Heq.
      rewrite !big_opM_insert; [
      | eapply lookup_delete
      | eauto
      | rewrite lookup_union_with Hm1 lookup_delete // ].
      rewrite IH.
      rewrite Hfg.
      (* Now only a matter of associativity and commutativity. *)
      rewrite !assoc.
      eapply monoid_proper; [| eauto ].
      rewrite -!assoc.
      eapply monoid_proper; [ eauto |].
      rewrite comm.
      eauto. }
    (* Case: the key [i] is not present in [m2]. *)
    { rewrite -insert_union_with_l //.
      rewrite !big_opM_insert; [
      | eauto
      | rewrite lookup_union_with Hm1 Hm2 // ].
      rewrite IH !assoc //. }
  Qed.

  End gmap.
End BigOp.

(* The following should be inserted in bi/big_op.v under big_sepM_union *)

From stdpp Require Import countable fin_sets functions.
From iris.algebra Require Import big_op.
From iris.algebra Require Import list gmap.
From iris.bi Require Import derived_laws_later.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

Section big_op.
Context {PROP : bi}.

Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_union_with (g : A → A → A) Φ m1 m2 :
    (∀ i x1 x2, Φ i (g x1 x2) ≡ (Φ i x1 ∗ Φ i x2)%I) →
    let lift_g x1 x2 := Some (g x1 x2) in
    ([∗ map] k↦y ∈ union_with lift_g m1 m2, Φ k y)
    ⊣⊢ ([∗ map] k↦y ∈ m1, Φ k y) ∗ ([∗ map] k↦y ∈ m2, Φ k y).
  Proof. apply big_opM_union_with. Qed.

End map.
End big_op.

(* The following could be inserted in gen_heap. *)

From stdpp Require fin_sets.
From iris.base_logic.lib Require Import gen_heap.
From irisfit Require Import stdpp.

Section GenHeap.
Context `{Countable L, hG : !gen_heapGS L V Σ}.

Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l ↦ v") : bi_scope.

Lemma gen_heap_valid_big σ ls :
  gen_heap_interp σ ∗
  ([∗ set] l ∈ ls, ∃ v, l ↦ v) -∗
  ⌜ ls ⊆ dom σ ⌝.
Proof.
  (* By induction on the set [ls]. *)
  pattern ls. eapply set_ind_L; clear ls.
  (* Case: ∅. *)
  { eauto. }
  (* Case: {[l]} ∪ ls. *)
  { intros l ls Hl IH.
    rewrite -> !big_sepS_union, !big_sepS_singleton by set_solver.
    iIntros "(Hh & Hl & Hls)".
    iDestruct "Hl" as (v) "Hl".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hone.
    assert (l ∈ dom σ) by eauto.
    iDestruct (IH with "[$]") as %Htwo.
    iPureIntro.
    set_solver. }
Qed.

Lemma gen_heap_update_big (ls : gset L) b : ∀ σ,
  gen_heap_interp σ ∗
  ([∗ set] l ∈ ls, (∃a, l ↦ a))
  ==∗
  gen_heap_interp (gmap_mset ls b σ) ∗
  ([∗ set] l ∈ ls, l ↦ b).
Proof.
  (* By induction on the set [ls]. *)
  pattern ls. eapply set_ind_L; clear ls.
  (* Case: ∅. *)
  { intros σ. rewrite !big_sepS_empty gmap_mset_empty. eauto. }
  (* Case: {[l]} ∪ ls. *)
  { intros l ls Hl IH σ.
    rewrite -> !big_sepS_union, !big_sepS_singleton by set_solver.
    iIntros "(Hh & Hl & Hls)".
    iDestruct "Hl" as (a) "Hl".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hlb.
    assert (l ∈ dom σ) by eauto.
    rewrite (gmap_mset_cons' l) //.
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]".
    iFrame "Hl".
    iApply IH. iFrame. }
Qed.

Lemma mapsto_persist_big ls v :
  ([∗ set] l ∈ ls, l ↦ v)
  ==∗
  ([∗ set] l ∈ ls, mapsto l DfracDiscarded v).
Proof.
  (* By induction on the set [ls]. *)
  pattern ls. eapply set_ind_L; clear ls.
  (* Case: ∅. *)
  { rewrite !big_sepS_empty. eauto. }
  (* Case: {[l]} ∪ ls. *)
  { intros l ls Hl IH.
    rewrite -> !big_sepS_union, !big_sepS_singleton by set_solver.
    iIntros "(Hl & Hls)".
    iMod (mapsto_persist with "Hl") as "Hl".
    iFrame "Hl".
    iApply IH. iFrame. }
Qed.

End GenHeap.
