From iris Require Import invariants.
From irisfit.examples Require Import proofmode.

Definition wait : val :=
  μ: "self", [["x"]],
    let: "vx" := "x".[0] in
    if: "x" '== "vx" then val_unit else "self" [["x"]].

Definition smallex : val :=
  λ: [],
    let: "x" := alloc 1 in
    let: "y" := alloc 1 in
    "x".[0] <- "y";;
    fork ("x".[0] <- "x");;
    wait [["x"]].

Section smallex.
Context `{!interpGS0 Σ}.

Lemma pbt_split_half l p S :
  l ⟸{p} S -∗ l ⟸{p/2} S ∗ l ⟸{p/2} S.
Proof.
  iIntros. iApply pbt_split. rewrite Qp.div_2 union_idemp_L //.
Qed.

Definition inv_content x y : iProp Σ :=
  †y ∨ x ↦ [val_loc y] ∨ (x ↦ [val_loc x] ∗ x ↤ {[+x+]} ∗ x ⟸{1/2} ∅ ∗ y ↤ ∅).

Lemma smallex_spec π:
  CODE (smallex [])
  TID π
  PRE (♢2)
  POST (fun _ => ♢2).
Proof.
  iIntros "HC".
  wpc_call.
  wpc_let_noclean.
  wpc_alloc. iIntros (x) "(Hx&X2&?&_)".
  wpc_let_noclean.
  wpc_alloc. iIntros (y) "(?&Y1&?&_)". simpl.
  wpc_let_noclean. wpc_store. iIntros "(Hx&Y1&_)". simpl. rewrite left_id.

  iDestruct (mapsto_ne with "[$][$]") as "%".

  iDestruct (pbt_split_half x with "[$]") as "(X1&?)". rewrite (pbt_PBT x).
  iApply (wpc_let with "[$]"). set_solver.

  iMod (inv_alloc nroot _ (inv_content x y) with "[Hx]") as "#I". iSmash.

  iApply (wpc_mono with "[X1 X2 Y1]").
  { iApply (wpc_fork with "[$]"). set_solver.
    iIntros (π') "_ ?". rewrite -pbt_PBT.
    iInv "I" as ">[?|[?|(?&?&?&HY)]]". solve_atomic.
    { iApply wpc_tconseq. iApply confront_mapsfrom_dag. 2:iFrame. compute_done. by iIntros. }
    2:{ iDestruct (mapsfrom_confront with "Y1 HY") as "%". by vm_compute. congruence. }

    iApply wpc_postpone.
    wpc_store. iIntros "(?&?&E)". simpl. pclean x. wpc_val. rewrite right_id. do 2 iModIntro.
    iDestruct (mapsfrom_join with "Y1 E") as "?". rewrite left_id right_id disj_union_singleton_opposite.
    iSmash. }


  iIntros (?) "-> ?". simpl. iClear "HC".
  pclean y.

  iLöb as "IH". wpc_call. wpc_let_noclean.

  iInv "I" as ">[?|[?|(?&?&?&?)]]". solve_atomic.
  { not_dead y. }
  { wpc_load. iIntros "(Hx&?)". iModIntro. iSplitL "Hx"; first iSmash. iIntros.
    iApply (wpc_bind_noclean (ctx_if _ _)).
    wpc_call_prim. simpl. rewrite bool_decide_eq_false_2. 2:naive_solver.
    wpc_if. pclean y. iApply ("IH" with "[$][$][$]"). }
  { iApply wpc_tconseq. iApply (interp_free y). 2:iFrame. set_solver.
    iIntros "(?&_&#?)".

    wpc_load. iIntros "(?&?)".  iFrame "#". iModIntro. iIntros.
    rewrite -pbt_PBT. iDestruct (pbt_join with "[$]") as "?".
    rewrite Qp.div_2 union_idemp_L.
    iApply (wpc_bind_noclean (ctx_if _ _)).
    wpc_call_prim. simpl. rewrite bool_decide_eq_true_2 //.
    wpc_if.
    pclean x.
    iApply wpc_tconseq. iApply (interp_free x). 2:iFrame.
    { rewrite dom_psingleton //. }
    iIntros "(?&_)". wpc_val. conclude_diamonds. }
Qed.

End smallex.
