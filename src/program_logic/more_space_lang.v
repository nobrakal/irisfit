From iris.proofmode Require Export proofmode.

From irisfit.language Require Import language.
From irisfit.spacelang Require Import predecessors.
From irisfit.lib Require Import qz smultiset.

From irisfit Require Import ph interp more_interp pbt.

(* ------------------------------------------------------------------------ *)
(* mapsfrom_set *)

Section Mapsfrom_set.
Context `{interpGS sz Σ}.

Lemma mapsfrom_of_mapsfrom_set_empty l q :
  mapsfrom_set l q ∅ -∗ l ↤{q} ∅.
Proof.
  iIntros "[% (?&%Hd)]".
  rewrite (smultiset.dom_empty_inv ps). iFrame.
  set_solver.
Qed.

Lemma mapsfrom_set_overapprox l q fs fs' :
  fs ⊆ fs' ->
  mapsfrom_set l q fs -∗
  mapsfrom_set l q fs'.
Proof.
  iIntros (?) "[% (?&%)]".
  iExists ps. iFrame. iPureIntro. set_solver.
Qed.

Lemma mapsfrom_set_join_mapsfrom l q1 q2 ms S :
  l ↤{q1} ms -∗ mapsfrom_set l q2 S -∗
  mapsfrom_set l (q1+q2) (dom ms ∪ S).
Proof.
  iIntros "H1 [% (?&%)]".
  iDestruct (mapsfrom_join with "H1 [$]") as "?".
  iExists _. iFrame. iPureIntro.
  etrans. apply smultiset.dom_disj_union.
  set_solver.
Qed.

Lemma mapsfrom_set_communicate q1 q2 ms1 ms2 fs l' :
  q1 ≠ 0%Qz -> q2 ≠ 0%Qz ->
  l' ↤{q1} (ms1 ⊎ ms2) -∗
  mapsfrom_set l' q2 fs -∗
  l' ↤{q1} ms1 ∗ mapsfrom_set l' q2 (dom ms2 ∪ fs).
Proof.
  iIntros (??) "H1 [% (H2&%)]".
  iDestruct (mapsfrom_join with "H1 H2") as "?".
  rewrite -assoc.
  iDestruct (mapsfrom_split with "[$]") as "(?&?)".
  3,4:eauto.
  1,2:naive_solver.
  iFrame. iExists _. iFrame.
  iPureIntro. etrans. apply smultiset.dom_disj_union.
  set_solver.
Qed.
End Mapsfrom_set.

(* ------------------------------------------------------------------------ *)

(* The predicate [vmapsfrom] takes a value [v] as its first argument,
   whereas [mapsfrom] takes a location [l']. *)

Definition vmapsfrom `{!interpGS sz Σ} v q ls : iProp Σ :=
  match v with
  | val_loc l' =>
      l' ↤{q} ls
  | _ =>
      True
  end.

Global Instance vmapsfrom_proper `{!interpGS sz Σ} v q : Proper ((≡) ==> (≡)) (vmapsfrom v q).
Proof.
  intros ? ? E.
  destruct v; try easy.
  rewrite E //.
Qed.

Notation "v ↤?{ q } ls" :=
  (vmapsfrom v%Qz q ls)
  (at level 20, format "v  ↤?{ q }  ls")
: bi_scope.

Notation "v ↤? ls" :=
  (vmapsfrom v 1%Qz ls)
  (at level 20, format "v  ↤?  ls")
: bi_scope.

Lemma vmapsfrom_join `{!interpGS sz Σ} v q1 q2 ls1 ls2 :
  v ↤?{q1} ls1 ∗ v ↤?{q2} ls2 ⊢ v ↤?{q1+q2} (ls1 ⊎ ls2) .
Proof.
  destruct v; simpl vmapsfrom; eauto.
  iIntros "[H1 H2]".
  iApply (mapsfrom_join with "H1 H2").
Qed.

Global Instance from_sep_vmapsfrom `{!interpGS sz Σ} v q1 q2 ls1 ls2 :
  FromSep (v ↤?{q1+q2} (ls1 ⊎ ls2)) (v ↤?{q1} ls1) (v ↤?{q2} ls2).
Proof.
  apply vmapsfrom_join.
Qed.

Global Instance timeless_vmapsfrom `{!interpGS sz Σ} v q ls :
  Timeless (vmapsfrom v q ls).
Proof. destruct v; apply _. Qed.

Lemma vmapsfrom_weak `{!interpGS sz Σ} ls1 ls2 v q :
  (is_loc v -> q = 0%Qz -> AllNeg ls2) ->
  (* NB this is not inclusion of signed multisets. *)
  (* TODO notation <= *)
  (forall x, smultiset.multiplicity x ls1 <= smultiset.multiplicity x ls2)%Z ->
  v ↤?{q} ls1 -∗ v ↤?{q} ls2.
Proof.
  iIntros. destruct v; try easy.
  iApply mapsfrom_weak; eauto.
Qed.

Lemma vmapsfrom_split `{!interpGS sz Σ} v q1 q2 ls1 ls2 :
  (is_loc v -> q1 = 0%Qz → AllNeg ls1) ->
  (is_loc v -> q2 = 0%Qz -> AllNeg ls2) ->
  v ↤?{q1+q2} (ls1 ⊎ ls2) -∗ v ↤?{q1} ls1 ∗ v ↤?{q2} ls2.
Proof.
  destruct v; simpl vmapsfrom; eauto.
  iIntros.
  iApply mapsfrom_split; eauto.
Qed.

Lemma vmapsfrom_correct `{!interpGS sz Σ} v q ls :
  v ↤?{q} ls -∗ ⌜¬ is_loc v \/ (q = 0%Qz -> AllNeg ls)⌝.
Proof.
  iIntros.
  destruct v; try naive_solver.
  simpl. iDestruct (mapsfrom_correct with "[$]") as "%Hq".
  naive_solver.
Qed.

Lemma vmapsfrom_split_empty `{!interpGS sz Σ} v q L :
  v ↤?{q} L -∗ v ↤?{q} L ∗ v ↤?{0} ∅.
Proof.
  iIntros. iDestruct (vmapsfrom_correct with "[$]") as "%".
  iApply vmapsfrom_split.
  { set_solver. }
  { smultiset_solver. }
  by do 2 rewrite right_id.
Qed.

Lemma vmapsfrom_no_loc `{!interpGS sz Σ} (v:val) (qz:Qz) (L:smultiset loc) :
  ¬ is_loc v ->
  (v ↤?{qz} L ⊣⊢ True)%I.
Proof. intros. by destruct v. Qed.

(* ------------------------------------------------------------------------ *)

Definition diff_loc v1 v2 : Prop :=
  match v1,v2 with
  | val_loc l1, val_loc l2 => l1 ≠ l2
  | _,_ => True end.

Lemma mapsfrom_vmapsfrom_confront `{!interpGS sz Σ} l1 q1 ls1 (l2:val) q2 ls2 :
  (1 < q1 + q2)%Qz -> l1 ↤{q1} ls1 -∗ l2 ↤?{q2} ls2 -∗ ⌜val_loc l1 ≠ l2⌝.
Proof.
  iIntros.
  destruct l2; eauto. simpl.
  iDestruct (mapsfrom_confront with "[$] [$]") as "%".
  { rewrite comm_L //. }
  { iPureIntro. injection 1. congruence. }
Qed.

Lemma vmapsfrom_cleanup `{!interpGS sz Σ} l l' q ls:
  ⊢ l ↤?{q} ls ∗ †l' =[#]=∗
  l ↤?{q} (ls ⊎ {[-l'-]}).
Proof.
  destruct_decide (decide (is_loc l)) as Eq.
  { apply is_loc_inv in Eq.  destruct Eq as (?,?). subst. apply mapsfrom_cleanup.  }
  { iIntros "(? & ?)". iIntros. destruct l; eauto. naive_solver. }
Qed.

(* ------------------------------------------------------------------------ *)

(* A technical lemma, for internal use. *)

Lemma interpret_val_pointer `{interpGS sz Σ} v q ls :
  (is_loc v -> q <> 0%Qz) ->
  interpret (map (λ l', (l', q, ls)) (val_pointer_list v)) ≡
  (v ↤?{q} ls)%I.
Proof.
  intros.
  destruct v; simpl; rewrite ?interpret_nil ?interpret_singleton //.
  eauto.
Qed.

(* ------------------------------------------------------------------------ *)

(* The following technical lemma describes the ghost store update that
   takes place at the level of [ph_interp] when a value [w] is stored
   in a memory block or a stack cell, overwriting a previous value [v]. *)

(* This lemma cannot be placed in the file ph.v (even though it may seem as
   though it belongs there) because it depends on several notions that are
   specific of SpaceLang, whereas ph.v is language-agnostic. *)

(* We assume that [b] is the old block and [b'] is the new block. They
   differ by just one field, so, if the values [v] and [w] are equal,
   then [b] and [b'] are equal. If the values [v] and [w] are not
   equal, then they are not aliased (not the same memory location), so
   the pointers present in [b] but not [b'] are the pointers found in
   [v], and the pointers present in [b'] but not in [b] are the
   pointers found in [w]. *)

(* We introduce a [precise] arguments allowing to distinguish the
   case where we do not need to track predecessors. *)

Lemma ph_update_1 `{!interpGS sz Σ} σ l v b w b' qw lsw :
  length b = length b' ->
  (is_loc w -> qw <> 0%Qz) ->
  σ !! l = Some (BBlock b) →
  (v = w → b = b') →
  (¬ alias v w → old_pointers (BBlock b) (BBlock b') = val_pointer_multiset v) →
  (¬ alias v w → new_pointers (BBlock b) (BBlock b') = val_pointer_multiset w) →
  let σ' := <[l := BBlock b']> σ in
  ph_interp σ  ∗ w ↤?{qw}  lsw ==∗
  ph_interp σ' ∗ w ↤?{qw} (lsw ⊎ {[+l+]}) ∗ v ↤?{0} {[-l-]}.
Proof.
  intros ? Hnw Hl ? Hold Hnew ?.
  destruct (decide (alias v w)) as [ Halias | Halias ].

  (* Case: [alias v w]. Then, the store instruction has no effect. *)
  { apply alias_implies_equal_locations in Halias.
    destruct Halias as (l' & ? & Hw).
    assert (w = v) by congruence. subst w.
    assert (b = b') by eauto. subst b'.
    assert (Hnop: σ' = σ) by (eapply insert_id; exact Hl).
    rewrite Hnop.
    subst v. simpl.
    iIntros "(? & Hmf1)". iFrame. iModIntro.
    iApply mapsfrom_split_neg; try easy.
    { intros. exfalso. apply Hnw; eauto. }
    { intros. apply AllNeg_nsingleton. }
    assert (lsw ≡ lsw ⊎ {[+ l +]} ⊎ {[-l-]}) as <-.
    { rewrite -assoc disj_union_singleton_opposite right_id //. }
    iFrame. }

  (* Case: [v] and [w] are not aliases, that is, not the same pointer. *)

  (* Define appropriate in and out triples. *)
  set (new_triples := map (λ l', (l', qw, lsw)) (val_pointer_list w)).

  (* Perform a ghost store update. *)
  iIntros "(Hh & Hmf1)".
  iMod (ph_update σ l b b' new_triples with "[Hh Hmf1]")
    as "(Hh & X & Hmf1)"; eauto.
  { rewrite /addresses /new_triples Hnew // map_map map_id //. }
  { rewrite /new_triples !interpret_val_pointer // insert_id //.
    iFrame. }

  (* There we are! *)
  rewrite Hold // /new_triples !map_map !interpret_val_pointer //.
  iFrame.
  rewrite /val_pointer_multiset /val_pointer_list.
  destruct v; simpl; try by iFrame.
  rewrite right_id gmultiset_elements_singleton interpret_unregister_cons.
  iDestruct "X" as "[? ?]". by iFrame.
Qed.

(* ------------------------------------------------------------------------ *)

(* The following technical lemma describes (part of) the ghost store update
   that takes place when a value [w] is stored in a memory block, overwriting
   a previous value [v]. It is a special case of [ph_update_1]. *)

(* We use a [precise] argument to indicate if we track predecessors. *)

Lemma ph_store_heap `{!interpGS sz Σ} σ l v vs ofs w qw lsw :
  (is_loc w -> qw <> 0%Qz) ->
  σ !! l = Some (BBlock vs) →
  (0 <= ofs < length vs)%nat →
  vs !! ofs = Some v →
  let σ' := <[l := BBlock (<[ ofs := w ]> vs)]> σ in
  ph_interp σ  ∗ w ↤?{qw}  lsw ==∗
  ph_interp σ' ∗ w ↤?{qw} (lsw ⊎ {[+l+]}) ∗ v ↤?{0} {[-l-]}.
Proof.
  intros.
  eapply ph_update_1.
  { rewrite insert_length //. }
  all:eauto using old_pointers_store_nonaliased, new_pointers_store_nonaliased.
  (* There remains to prove [v = w → b = b']. *)
  { intros <-. rewrite list_insert_id //. }
Qed.
