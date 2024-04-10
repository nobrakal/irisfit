From irisfit.examples Require Import proofmode.

Lemma VPBT_PBT `{!interpGS0 Σ} vs qs (S:gset thread_id) :
  ([∗ list] v;q ∈ vs;qs, v ⟸?{q} S) ==∗ ∃ (M:gmap loc Qp), ⌜dom M = locs vs⌝ ∗ PBT S M ∗ (PBT S M -∗ ([∗ list] v;q ∈ vs;qs, v ⟸?{q} S)) .
Proof.
  iRevert (qs). iInduction vs as [|v vs] "IH"; iIntros (qs) "Hvq".
  { iDestruct PBT_empty as "?". iExists ∅. iFrame. iModIntro. iSplitR.
    { iPureIntro. set_solver. }
    { iFrame "#". iIntros. done. } }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%q [% (->&?&?)]]".
  iMod ("IH" with "[$]") as "[%M (%HM&HM&Hback)]". iModIntro.

  destruct_decide (decide (is_loc v)) as Hv; last first.
  { iExists M. iFrame. iSplitR; first iPureIntro.
    { destruct v; set_solver. }
    iSmash. }

  apply is_loc_inv in Hv. destruct Hv as (l,->).
  simpl. rewrite {1}pbt_PBT. iDestruct (PBT_union with "[$]") as "?".
  iExists _. iFrame.
  iSplitR.
  { iPureIntro. rewrite gmap.dom_op. set_solver. }
  iIntros. iDestruct (PBT_split with "[$]") as "(?&?)".
  rewrite pbt_PBT. iSmash.
Qed.

Lemma wpc_ctxl vs qs `{!interpGS0 Σ} `{Enc A} E π r K t (Q:A -> iProp Σ) :
  locs K ⊆ locs vs ∪ r ->
  ([∗ list] v;q ∈ vs;qs, v ⟸?{q} {[π]}) -∗
  wpc E π (Some (r ∪ locs vs)) t (fun (v:val) => ([∗ list] v;q ∈ vs;qs, v ⟸?{q} {[π]}) -∗  wpc E π (Some r) (fill_item K v) Q) -∗
  wpc E π (Some r) (fill_item K t) Q.
Proof.
  iIntros.
  iMod (VPBT_PBT with "[$]") as "[%M (%HdM&?&?)]".
  iApply (wpc_bind with "[$]"). set_solver. rewrite HdM.
  iApply (wpc_mono with "[$]"). iSmash.
Qed.

Lemma wpc_ctx_2v `{!interpGS0 Σ} `{Enc A} K t v1 v2 q1 q2 E π r (Q:A -> iProp Σ) :
  locs K ⊆ locs v1 ∪ locs v2 ∪ r ->
  v1 ⟸?{q1} {[π]} -∗
  v2 ⟸?{q2} {[π]} -∗
  wpc E π (Some (locs v1 ∪ locs v2 ∪ r)) t (fun (v:val) => v1 ⟸?{q1} {[π]} -∗ v2 ⟸?{q2} {[π]} -∗ wpc E π (Some r) (fill_item K v) Q) -∗
  wpc E π (Some r) (fill_item K t) Q.
Proof.
  iIntros (?) "? ? Hwpc".
  iMod (VPBT_PBT  [v1;v2] [_;_] with "[-Hwpc]") as "[%M (%HdM&?&?)]".
  { by iFrame. }
  iApply (wpc_bind with "[$]"). set_solver. rewrite HdM.
  replace (r ∪ locs [v1; v2]) with (locs v1 ∪ locs v2 ∪ r) by set_solver.
  iApply (wpc_mono with "[$]"). iSmash.
Qed.

Lemma wpc_let_2v v1 v2 q1 q2 `{!interpGS0 Σ} `{Enc A} E π r x t1 t2 (Q:A -> iProp Σ) :
  locs t2 ⊆ locs v1 ∪ locs v2 ∪ r ->
  v1 ⟸?{q1} {[π]} -∗
  v2 ⟸?{q2} {[π]} -∗
  wpc E π (Some (locs v1 ∪ locs v2 ∪ r)) t1 (fun (v:val) => v1 ⟸?{q1} {[π]} -∗ v2 ⟸?{q2} {[π]} -∗ wpc E π (Some r) (subst x v t2) Q) -∗
  wpc E π (Some r) (tm_let x t1 t2) Q.
Proof.
  iIntros.
  iApply (wpc_ctx_2v (ctx_let x t2) t1 v1 v2 with "[$][$]"). set_solver.
  iApply (wpc_mono with "[$]"). iIntros.
  simpl. iApply wpc_let_val. iSmash.
Qed.

Lemma wpc_let_nv vs qs  `{!interpGS0 Σ} `{Enc A} E π r x t1 t2 (Q:A -> iProp Σ) :
  locs t2 ⊆ r ∪ locs vs ->
  ([∗ list] v;q ∈ vs;qs, v ⟸?{q} {[π]}) -∗
  wpc E π (Some (r ∪ locs vs)) t1 (fun (v:val) => ([∗ list] v;q ∈ vs;qs, v ⟸?{q} {[π]}) -∗ wpc E π (Some r) (subst x v t2) Q) -∗
  wpc E π (Some r) (tm_let x t1 t2) Q.
Proof.
  iIntros.
  iApply (wpc_ctxl vs qs _ _ _ (ctx_let x t2)  with "[$]"). set_solver.
  iApply (wpc_mono with "[$]"). iIntros. iApply wpc_let_val. iSmash.
Qed.
