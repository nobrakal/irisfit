From irisfit.examples Require Import proofmode spawn_join pair.

(* We define [par] as a macro, and instantiate later [par_code] and [par_clo]
   This implementation follows Birkedal's lecture notes.
 *)
Definition par t1 t2 : tm :=
    let: "h" := spawn t1 in
    let: "r2" := t2 in
    let: "r1" := join [["h"]] in
    pair [["r1", "r2"]].

Section Par.
Context `{!spawnG Σ,interpGS0 Σ}.

(* Very generic lemma of  the par'ed terms. See below for an instanciation
   with call and call_clo *)
Lemma par_spec i r (t1 t2:tm) M1 M2 q1 q2 Ψ1 Ψ2 p1 p2 :
  dom M1 ⊆ locs t1 -> locs t1 ⊆ dom M1 ∪ r ->
  dom M2 ⊆ locs t2 -> locs t2 ⊆ dom M2 ∪ r ->
  free_variables t1 = ∅ -> free_variables t2 = ∅ ->
  q1 ≠ 0%Qz -> q2 ≠ 0%Qz ->
  CODE (par t1 t2)
  TID i
  SOUV r
  PRE (♢4 ∗ PBT {[i]} M1 ∗ PBT {[i]} M2 ∗
    (∀ j, PBT {[j]} M1 -∗ wpc ⊤ j (Some r) t1 (fun v => Ψ1 v ∗ v ↤?{q1} ∅ ∗ v ⟸?{p1} {[j]}))%I ∗
    (∀ j, PBT {[j]} M2 -∗ wpc ⊤ j (Some r) t2 (fun v => Ψ2 v ∗ v ↤?{q2} ∅ ∗ v ⟸?{p2} {[j]}))%I)
  POST (fun l:loc => ∃ v1 v2, l ↦ [v1;v2] ∗ l ↤ ∅ ∗ l ⟸ {[i]} ∗ ♢2 ∗
     Ψ1 v1 ∗ v1 ↤?{q1} {[+l+]} ∗ v1 ⟸?{p1} ∅ ∗
     Ψ2 v2 ∗ v2 ↤?{q2} {[+l+]} ∗ v2 ⟸?{p2} ∅).
Proof.
  iIntros (????????) "(Hd & H1 & H2 & Hf1 & Hf2)".

  iApply wpc_split_ctx. iIntros (k Hk) "Hk".
  iApply (wpc_let with "H2"). set_solver.

  rewrite {1}(split_map k (locs t1 ∩ r)).
  2:{ set_solver. }
  iDestruct (PBT_split with "[$]") as "(H21&H22)".

  iDestruct (PBT_approx with "H21") as "H12". rewrite left_id_L.
  iDestruct (PBT_union _ M1 with "[$]") as "H11".

  mine 2.

  iApply wpc_apply.
  2:iApply (@spawn_spec _ _ _ nroot i p1 q1 (fun v => PBT ∅ k ∗ Ψ1 v)%I).
  5:iFrame "H11".
  { set_solver. }
  { eauto. }
  { rewrite gmap.dom_op !dom_restrict. apply leibniz_equiv. apply set_equiv_subseteq . split.
    set_solver. set_solver. }
  { eauto. }
  iFrame.
  iSplitL "Hf1 H22".
  { iIntros.
    iDestruct (PBT_split with "[$]") as "(Hl&Hr)".
    iSpecialize ("Hf1" with "[$]").
    iDestruct (PBT_approx with "H22") as "H22". rewrite left_id_L.
    iIntros. iDestruct (PBT_union _ (restrict k (locs t1 ∩ r)) with "[$]") as "?".
    rewrite -split_map. 2:set_solver.
    iApply wpc_postpone.
    iApply wpc_context. iFrame.
    iApply (wpc_weak r). set_solver.
    iApply (wpc_mono with "[$]").
    iIntros (?) "(?&?&?) ?". Unshelve. 2:apply _.
    iApply wpc_conseq. iApply vpbt_PBT_transfer. 3:iFrame. 1,2:set_solver.
    rewrite difference_diag_L. iSmash. }

  iIntros (c) "(Hc & ?) H2".

  iApply (wpc_let_vsingleton c with "[$]").
  set_solver.

  rewrite (subst_not_in "h"). 2:set_solver.

  iApply (wpc_mono with "[H2 Hf2]").
  { iApply wpc_weak. 2: iApply "Hf2". set_solver. iFrame. }
  iIntros (v1) "(? & ? & ?) ?". simpl.

  iApply wpc_postpone.

  iApply (wpc_context_vsingleton with "[$]").
  wpc_let_empty.

  wpc_apply join_spec. set_solver.

  iIntros (v2) "(? & ? & (?&?) & Hd2)". simpl.

  wpc_apply pair_spec. 1-3:set_solver.
  iIntros (l) "(?&?&?&?&?) ?".

  iDestruct (confront_pbt_vpbt _ v1 with "[$]") as "%".
  { apply Qp.not_add_le_l. }
  iDestruct (confront_pbt_vpbt _ v2 with "[$]") as "%".
  { apply Qp.not_add_le_l. }

  pclean v1 by ltac:(fun _ => destruct v1; set_solver).
  pclean v2 by ltac:(fun _ => destruct v2; set_solver).
  iSteps.
Qed.

End Par.

Definition par_code : val :=
  λ: [["f1", "f2"]], par ("f1" [[]]) ("f2" [[]]).

Definition par_clo : val :=
  λ: [["f1", "f2"]], par (call_clo "f1" [[]]) (call_clo "f2" [[]]).

Section ParDerived.
Context `{!spawnG Σ,interpGS0 Σ}.

Lemma par_code_spec i (f1 f2:val) q1 q2 Ψ1 Ψ2 p1 p2 r :
  q1 ≠ 0%Qz -> q2 ≠ 0%Qz ->
  locs f1 = ∅ -> locs f2 = ∅ ->
  CODE (par_code [[f1, f2]])
  TID i
  SOUV r
  PRE (♢4 ∗
    (∀ j, wpc ⊤ j (Some r) (f1 [[]])%T (fun v => Ψ1 v ∗ v ↤?{q1} ∅ ∗ v ⟸?{p1} {[j]}))%I ∗
    (∀ j, wpc ⊤ j (Some r) (f2 [[]])%T (fun v => Ψ2 v ∗ v ↤?{q2} ∅ ∗ v ⟸?{p2} {[j]}))%I)
  POST (fun l:loc => ∃ v1 v2, l ↦ [v1;v2] ∗ l ↤ ∅ ∗ l ⟸ {[i]} ∗ ♢2 ∗
     Ψ1 v1 ∗ v1 ↤?{q1} {[+l+]} ∗ v1 ⟸?{p1} ∅ ∗
     Ψ2 v2 ∗ v2 ↤?{q2} {[+l+]} ∗ v2 ⟸?{p2} ∅).
Proof.
  iIntros (Hq1 Hq2 ??) "(?&H1&H2)".
  wpc_call.
  iDestruct PBT_empty as "?".
  wpc_apply (par_spec _ r); try iFrame "#".
  1-6:set_solver. apply Hq1. apply Hq2.
  iSplitL "H1 H2".
  { iSplitL "H1"; iSmash. }
  iSmash.
Qed.

Lemma par_clo_spec i r (f1 f2:loc) pf1 pf2 q1 q2 Ψ1 Ψ2 p1 p2 :
  q1 ≠ 0%Qz -> q2 ≠ 0%Qz ->
  CODE (par_clo [[f1, f2]])
  TID i
  SOUV r
  PRE (♢4 ∗ f1 ⟸{pf1} {[i]} ∗ f2 ⟸{pf2} {[i]} ∗
    (∀ j, f1 ⟸{pf1} {[j]} -∗ wpc ⊤ j (Some r) (call_clo f1 [[]])%T (fun v => Ψ1 v ∗ v ↤?{q1} ∅ ∗ v ⟸?{p1} {[j]}))%I ∗
    (∀ j, f2 ⟸{pf2} {[j]} -∗ wpc ⊤ j (Some r) (call_clo f2 [[]])%T (fun v => Ψ2 v ∗ v ↤?{q2} ∅ ∗ v ⟸?{p2} {[j]}))%I)
  POST (fun l:loc => ∃ v1 v2, l ↦ [v1;v2] ∗ l ↤ ∅ ∗ l ⟸ {[i]} ∗ ♢2 ∗
     Ψ1 v1 ∗ v1 ↤?{q1} {[+l+]} ∗ v1 ⟸?{p1} ∅ ∗
     Ψ2 v2 ∗ v2 ↤?{q2} {[+l+]} ∗ v2 ⟸?{p2} ∅).
Proof.
  iIntros (??) "(?&H1&?&X1&X2)".
  wpc_call.
  wpc_apply (par_spec _ r).
  9:{ rewrite !pbt_PBT. iFrame "H1". iFrame. iSplitL.
       { iSplitL "X1"; iIntros; rewrite -pbt_PBT. by iApply "X1". by iApply "X2". }
       eauto. }
  eauto.
  1-6:set_solver.
  all:eauto.
Qed.

End ParDerived.
