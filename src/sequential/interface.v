(* LATER
From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth excl.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import disc qz qz_cmra smultiset.
From irisfit.spacelang Require Import successors predecessors.
From irisfit.language Require Import language.

From iris.base_logic.lib Require Import ghost_map.

From irisfit.program_logic Require Import more_space_lang more_maps_and_sets.
From irisfit.program_logic Require Import interp more_interp pbt.

From irisfit.program_logic Require Import wp_alloc wp_load wp_store wp_call wp_call_prim wp_clean wp_free utils.
From irisfit.sequential Require Import wp_sequential.

Section Interface.
Context `{!interpGS Σ, !seqG Σ, !session}.

(********************************************)
(* Redefine shorthand for old assertions *)

Definition cmapsto l q b :=
  gen_heap.mapsto l q b.
Definition cmapsfrom l q S :=
  ph.mapsfrom l q S.
Definition cvmapsfrom v q S :=
  program_logic.more_space_lang.vmapsfrom v q S.

(********************************************)
(* mapsto *)

Lemma mapsto_of_seq l q b :
  l ↦{q} b -∗ cmapsto l q b.
Proof. iIntros "(?&_)". iFrame. Qed.

Definition forward_closed vs : iProp Σ := [∗ list] v ∈ vs, vregistered v.

Lemma mapsto_to_seq l q b :
  forward_closed b -∗
  cmapsto l q b -∗
  l ↦{q} b .
Proof. iIntros. by iFrame. Qed.

(********************************************)
(* mapsfrom *)

Lemma mapsfrom_of_seq l q S :
  l ↤{q} S -∗ cmapsfrom l q S.
Proof. iIntros "(?&_)". iFrame. Qed.

Lemma mapsfrom_to_seq l q S :
  registered l -∗
  cmapsfrom l q S -∗
  l ↤{q} S.
Proof. iIntros. by iFrame. Qed.

Lemma vmapsfrom_of_seq (v:val) q S :
  v ↤?{q} S -∗ cvmapsfrom v q S.
Proof. iIntros "(?&_)". iFrame. Qed.

Lemma vmapsfrom_to_seq v q S :
  vregistered v -∗
 cvmapsfrom v q S -∗
  v ↤?{q} S.
Proof. iIntros. by iFrame. Qed.

(********************************************)
(* pbt / Stackable *)

Lemma seq_rem_lu1 (τ:gmap loc Qp) l p :
  τ !! l = Some p ->
  (τ, {[l := p]}) ~l~> (delete l τ, ε).
Proof.
  intros Hl.
  apply local_update_unital_discrete.
  intros z ? Heq.
  split.
  { apply delete_valid; eauto. }
  rewrite left_id.
  intros l'. destruct (decide (l'=l)); subst.
  { rewrite lookup_delete. specialize (Heq l). rewrite Hl lookup_op lookup_singleton in Heq.
    destruct (z!!l) eqn:Hz.
    { exfalso. rewrite Hz in Heq. rewrite -Some_op in Heq.
      inversion Heq. subst. eapply Qp.add_id_free . eauto. }
    rewrite Hz //. }
  rewrite lookup_delete_ne //.
  rewrite (Heq l') lookup_op lookup_singleton_ne // left_id //.
Qed.

Lemma seq_rem1 (τ:gmap loc Qp) l p :
  τ !! l = Some p ->
  own γl (● τ) ∗
  seq l p%Qp ==∗
  own γl (● delete l τ).
Proof.
  iIntros (?) "(Ha&Hf)".
  iApply (own_update_2 with "Ha Hf").
  apply auth_update_dealloc.
  apply seq_rem_lu1. eauto.
Qed.

Lemma seq_rem_lu2 (τ:gmap loc Qp) l (p q:Qp) :
  τ !! l = Some (p+q)%Qp ->
  ✓q ->
  (τ, {[l := p]}) ~l~> (<[l:=q]>τ, ε).
Proof.
  intros Hl ?.
  apply local_update_unital_discrete.
  intros z ? Heq.
  split.
  { apply insert_valid; eauto. }
  rewrite left_id.
  intros l'. destruct (decide (l'=l)); subst.
  { rewrite lookup_insert. specialize (Heq l). rewrite Hl lookup_op lookup_singleton in Heq.
    destruct (z!!l) eqn:Hz.
    2:{ exfalso. rewrite Hz in Heq. rewrite right_id in Heq.
      inversion Heq. subst. eapply Qp.add_id_free . eauto. }
    rewrite Hz -Some_op in Heq. inversion Heq. subst.
    rewrite Hz. apply Qp.add_inj_r in H4. subst. eauto. }
  rewrite lookup_insert_ne //.
  rewrite (Heq l') lookup_op lookup_singleton_ne // left_id //.
Qed.

Lemma seq_rem2 (τ:gmap loc Qp) l p q :
  τ !! l = Some (p+q)%Qp ->
  own γl (● τ) ∗
  seq l p%Qp ==∗
  own γl (● <[l:=q]>τ).
Proof.
  iIntros (Hl) "(Ha&Hf)".
  iDestruct (own_valid with "Ha") as "%Hv".
  iApply (own_update_2 with "Ha Hf").
  apply auth_update_dealloc.
  apply seq_rem_lu2. eauto.
  rewrite auth_auth_valid in Hv. specialize (Hv l).
  rewrite Hl Some_valid in Hv.
  eapply cmra_valid_op_r. eauto.
Qed.

Lemma pbt_of_seq l p :
  no_seq_mode ∗
  Stackable l p%Qp ==∗
  no_seq_mode ∗ pbt l p%Qp {[session_tid]}.
Proof.
  iIntros "(HN1&(Hl1&?&?))".

  iDestruct "HN1" as "[% [% (%&_&?&?&Hτ)]]".
  iDestruct (seq_acc with "[$]") as "%Hv".
  destruct Hv as (q,(Hlq,Hpq)).
  rewrite /seq_locs big_sepM_delete. 2:eauto.
  iDestruct "Hτ" as "(Hl&Hback)".

  apply a_little_lemma in Hpq.
  assert (l ∈ dom τ).
  { rewrite elem_of_dom. eauto. }

  destruct_decide (decide (l∈μ)).
  { set_solver. }

  iDestruct "Hl" as "[?|Hl]".
  { iExFalso. iApply (confront_pbt_dag with "[$]"). }

  destruct_decide (decide (q=(p/2))%Qp) as Hq.
  { subst.
    iDestruct (pbt_join with "[$]") as "Hl".
    rewrite Qp.div_2 idemp_L.
    iFrame.
    iMod (seq_rem1 with "[$]") as "?". eauto.
    iModIntro.  iExists _. iFrame. iExists ({[l]} ∪ μ). rewrite dom_delete_L.
    iSplitR. { iPureIntro. set_solver. }
    replace ((dom τ ∖ {[l]} ∪ ({[l]} ∪ μ))) with (dom τ ∪ μ).
    2:{ rewrite assoc_L. f_equal. rewrite difference_union_L. set_solver. }
    iFrame. eauto. }

  { destruct (q - (p/2))%Qp as [q'|] eqn:Hq'.
    2:{ apply Qp.sub_None in Hq'. exfalso. apply Hq.
        eapply partial_order_anti_symm. Unshelve. 4:apply Qp.le_po.
        eauto. eauto. }
    apply Qp.sub_Some in Hq'. subst. clear Hq.
    iAssert (l ⟸{p/2} {[session_tid]} ∗ l ⟸{q'}{[session_tid]})%I with "[Hl]" as "(Hl2&Hl)".
    { iApply pbt_split. iApply (pbt_concl with "[$]"). easy. set_solver. }
    iDestruct (pbt_join with "[Hl1 Hl2]") as "?". iFrame.
    rewrite Qp.div_2 idemp_L. iFrame.

    iDestruct (big_sepM_insert with "[Hl Hback]") as "?". 2:iFrame.
    rewrite lookup_delete //.
    rewrite insert_delete_insert.
    iMod (seq_rem2 with "[$]") as "?". eauto.
    iModIntro. iExists _,_. iFrame. rewrite dom_insert_L.
    replace ({[l]} ∪ dom τ ∪ μ) with (dom τ ∪ μ) by set_solver. iFrame.
    iPureIntro. set_solver. }
Qed.

(* XXX move *)
Definition vStackable v p : iProp Σ :=
  match v with
  | val_loc l => Stackable l p
  | _ => True end.

Lemma vStackable_not_loc v p :
  ¬ (is_loc v) ->
  vStackable v p = True%I.
Proof.
  intros ?; destruct v; naive_solver.
Qed.

Lemma vpbt_of_seq v p :
  no_seq_mode ∗ vStackable v p%Qp ==∗
  no_seq_mode ∗ vpbt v p%Qp {[session_tid]}.
Proof.
  destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv as (l,->).
    apply pbt_of_seq. }
  { rewrite vpbt_not_loc //.
    iIntros "(?&?)". by iFrame. }
Qed.

Lemma pbt_to_seq l p :
  pbt l p%Qp {[session_tid]} =[#]=∗
  Stackable l p%Qp.
Proof.
  iIntros "(?&?)". iIntros.
  iMod (add_to_seq_inv with "[$]") as "(?&?&?&?)".
  by iFrame.
Qed.

Lemma vpbt_to_seq v p :
  vpbt v p%Qp {[session_tid]} =[#]=∗
  vStackable v p%Qp.
Proof.
  destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv as (l,->).
    apply pbt_to_seq. }
  { rewrite vStackable_not_loc //. iIntros "(?&?)". iIntros. by iFrame. }
Qed.
End Interface.

(*
From irisfit.examples Require Import list.

Section Examples.
Context `{interpGS Σ, !seqG Σ, !session}.

Fixpoint List_seq (xs : list (val * (Qp * Qz))) (l : loc) : iProp Σ :=
  match xs with
  | [] => l ↦ [ val_nat 0 ]
  | (v,(qp,qz)) :: xs =>
      ∃ l', l ↦ [ val_nat 1; v; val_loc l'] ∗ vStackable v qp ∗ v ↤?{qz} {[+l+]} ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ List_seq xs l'
end.

Lemma Stackable_registered l p :
  Stackable l p -∗ registered l.
Proof. iIntros "(?&?&?)". iFrame. Qed.

Lemma vStackable_vregistered v p :
  vStackable v p -∗ vregistered v.
Proof. iIntros. destruct v; try by iFrame. iApply Stackable_registered. iFrame. Qed.

Lemma vmapsfrom_registered v q L :
  v ↤{q} L -∗ vregistered v.
Proof. iIntros "(?&?)". iFrame. Qed.

Lemma List_to_seq xs l p :
  l ⟸{p} {[session_tid]} ∗ List xs l =[#]=∗
  Stackable l p ∗ List_seq xs l.
Proof.
  iStartProof.
  iRevert (l p).

  iInduction xs as [|(v,(?,?)) xs] "IH"; iIntros (l p); iIntros "(?&Hpbt&Hl)"; iIntros.
  { iMod (pbt_to_seq with "[$][$]") as "(?&?&?)". iFrame. iModIntro. iApply big_sepL_singleton. easy.  }
  iDestruct "Hl" as "[%l' (?&?&?&?&?&?)]". fold (List xs l').
  iMod (pbt_approx with "[$]") as "(?&?)". rewrite left_id_L.
  iMod ("IH" with "[$][$]") as "(?&?&?&?)". iClear "IH".
  iDestruct (Stackable_registered with "[$]") as "#?".

  (* XXX this should be a tupd *)
  iMod (vpbt_approx with "[$][$]") as "(?&?)". rewrite left_id_L.
  iMod (pbt_to_seq l with "[$][$]") as "(?&?&?)".
  iMod (vpbt_to_seq v with "[$][$]") as "(?&?&?)".
  iDestruct (vStackable_vregistered with "[$]") as "#?".
  iModIntro. iFrame.
  iExists l'. iFrame "∗ #". easy.
Qed.

Lemma List_of_seq l xs :
  no_seq_mode ∗ List_seq xs l =[true | session_tid | ∅]=∗
  no_seq_mode ∗ List xs l.
Proof.
  iRevert (l).
  iInduction xs as [|(v,(?,?)) xs] "IH"; iIntros (l); iIntros "(?&HL)"; iIntros.
  { iFrame. iApply mapsto_of_seq. by iFrame. }
  { iDestruct "HL" as "[%l' (?&?&?&?&?&?)]". fold (List_seq xs l').
    iMod ("IH" with "[$][%//][$]") as "(?&?&?)". iClear "IH".
    iDestruct (mapsto_of_seq with "[$]") as "?".
    iDestruct (mapsfrom_of_seq with "[$]") as "?".
    iDestruct (vmapsfrom_of_seq with "[$]") as "?".

    iMod (pbt_of_seq with "[$]") as "(?&?)".
    iMod (vpbt_of_seq with "[$]") as "(?&?)".
    iMod (supd_clean with "[$][%//][$]") as "(?&?)". set_solver.
    iMod (supd_vclean with "[$][%//][$]") as "(?&?)". set_solver.
    replace (({[session_tid]} ∖ {[session_tid]}) ) with (∅:gset thread_id) by set_solver.
    iFrame. iExists _. by iFrame. }
Qed.
End Examples.

*)

*)
