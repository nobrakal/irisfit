From irisfit.examples Require Import proofmode seqproofmode list.

(* ------------------------------------------------------------------------ *)
(* rev_append with its two specifications. *)

Definition list_rev_append : val :=
  μ: "self", [["xs", "ys"]],
    let: "b" := list_is_nil [["xs"]] in
    if: "b" then "ys" else
    let: "hd" := list_head [["xs"]] in
    let: "tl" := list_tail [["xs"]] in
    let: "nys" := list_cons [["hd", "ys"]] in
    "self" [["tl", "nys"]].

Definition list_rev : val :=
  λ: [["xs"]],
    let: "n" := list_nil [[]] in
    list_rev_append [["xs", "n"]].

Section RevDestructive.
Import ListsOf.
Context `{interpGS0 Σ}.

(* We can express List.rev with ListOf only in the destructive case. *)
Lemma list_rev_append_spec {A} π (R:A -> val -> iProp Σ) L1 l1 L2 l2 :
  CODE (list_rev_append [[l1,l2]])
  TID π
  PRE (ListOf R L1 l1 ∗ l1 ⟸? {[π]} ∗ l1 ↤? ∅ ∗
       ListOf R L2 l2 ∗ l2 ⟸? {[π]} ∗ l2 ↤? ∅)
  POST (fun (l:val) => ListOf R (rev L1++L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ).
Proof.
  iStartProof.
  iRevert (l1 l2 L2).
  iInduction L1 as [|(x,(p,q)) L1] "IH"; iIntros (l1 l2 L2) "(Hxs1 & Hxs2 & Hxs3 & Hys1 & Hys2 & Hys3)".
  { wpc_call.
    iApply (@wpc_let_nv [l1;l2] [1;1]%Qp with "[Hxs2 Hys2]").
    { auto_locs. set_solver. }
    { by iFrame. }
    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%&?) (Hxs2&Hys2&_)".
    replace b with true by (destruct b; naive_solver).
    simpl. wpc_if. iSteps. }
  { wpc_call.
    iApply (@wpc_let_nv [l1;l2] [1;1]%Qp with "[Hxs2 Hys2]").
    { auto_locs. set_solver. }
    { by iFrame. }
    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%&?) (Hxs2&Hys2&_)".
    replace b with false by (destruct b; naive_solver).
    simpl. wpc_if.

    iApply (@wpc_let_nv [l1;l2] [1;1]%Qp with "[Hxs2 Hys2]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_head_spec. set_solver.
    iIntros (?) "(?&Hv&?) (Hxs2&Hys2&_)". simpl.

    iApply (@wpc_let_nv [l1;l2;v] [1;1;p]%Qp with "[Hxs2 Hys2 Hv]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_tail_spec. set_solver.
    iIntros (l') "[% (->&?&Hl'&?&?&?)] (Hxs2&Hys2&Hv&_)". simpl.

    iDestruct (confront_pbt_vpbt l0 l' with "[$]") as "%". by vm_compute.
    iDestruct (confront_pbt_vpbt l0 v with "[$]") as "%". by apply Qp.not_add_le_l.
    iDestruct (confront_pbt_vpbt l0 l2 with "[$]") as "%". by vm_compute.

    iDestruct (vmapsfrom_correct v with "[$]") as "%Hv".

    pclean l0.
    iApply wpc_tconseq. iApply (interp_free' l0). iFrame. iIntros "(?&?&#?)".
    iApply wpc_tconseq. iApply (vmapsfrom_cleanup l' l0). iFrame "#∗". iIntros "?".
    iApply wpc_tconseq. iApply (vmapsfrom_cleanup v l0). iFrame "#∗". iIntros "?".
    rewrite disj_union_singleton_opposite.

    iApply (@wpc_let_nv [l'] [1]%Qp with "[Hl']").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_cons_spec. set_solver.
    { intros. destruct Hv as [|Hv]; first done. intros ->. specialize (Hv eq_refl). smultiset_solver. }

    iFrame. iIntros (?) "(?&?&?) (?&_)". simpl.
    iSpecialize ("IH" with "[$]"). rewrite -assoc_L. iFrame. }
Qed.

Lemma list_rev_spec {A} π (R:A -> val -> iProp Σ) L l :
  CODE (list_rev [[l]])
  TID π
  PRE (ListOf R L l ∗ l ⟸? {[π]} ∗ l ↤? ∅)
  POST (fun l' => ListOf R (rev L) l' ∗ l' ⟸? {[π]} ∗ l' ↤? ∅).
Proof.
  iIntros "(?&Hl&?)".
  wpc_call.
  iApply (wpc_let_nv [l] [1]%Qp with "[Hl]"). set_solver. by iFrame.

  wpc_apply list_nil_spec. set_solver. rewrite left_id.
  iIntros (?) "(?&?&?) (?&_)".
  wpc_apply @list_rev_append_spec.
  rewrite right_id_L. iSteps.
Qed.

Import Lists.

Lemma list_rev_append_spec_ π L1 l1 L2 l2 :
  CODE (list_rev_append [[l1,l2]])
  TID π
  PRE (List L1 l1 ∗ l1 ⟸? {[π]} ∗ l1 ↤? ∅ ∗
       List L2 l2 ∗ l2 ⟸? {[π]} ∗ l2 ↤? ∅)
  POST (fun l => List (rev L1 ++ L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅).
Proof. apply list_rev_append_spec. Qed.

(* Then List.rev for List is a direct consequence. *)
Lemma list_rev_spec_ π L l :
  CODE (list_rev [[l]])
  TID π
  PRE (List L l ∗ l ⟸? {[π]} ∗ l ↤? ∅)
  POST (fun l => List (rev L) l ∗ l ⟸? {[π]} ∗ l ↤? ∅).
Proof. apply list_rev_spec. Qed.

End RevDestructive.

Section RevPreserving.
Import Lists.
Context `{interpGS0 Σ}.

Lemma list_rev_append_spec' π L1 l1 L2 l2 :
  CODE (list_rev_append [[l1,l2]])
  TID π
  SOUV (locs l1)
  PRE (♢ (2 * length L1) ∗ List L1 l1 ∗
       List L2 l2 ∗ l2 ⟸? {[π]} ∗ l2 ↤? ∅)
  POST (fun l => List (rev (halves L1) ++ L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ List (halves L1) l1).
Proof.
  iStartProof.
  iRevert (l1 l2 L2).
  iInduction L1 as [|(x,(p,q)) L1] "IH"; iIntros (l1 l2 L2) "(Hdiams & Hl1 & Hl21 & Hl22 & Hl23)".
  { wpc_call.
    iApply (@wpc_let_nv [l2] [1]%Qp with "[Hl22]").
    { auto_locs. set_solver. }
    { by iFrame. }
    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%&?) (?&_)".
    replace b with true by (destruct b; naive_solver).
    simpl. wpc_if. iSteps. }
  { wpc_call.
    iApply (@wpc_let_nv [l2] [1]%Qp with "[Hl22]").
    { auto_locs. set_solver. }
    { by iFrame. }
    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%&?) (Hl22&_)".
    replace b with false by (destruct b; naive_solver).
    simpl. wpc_if.
    mine 2.

    iApply (@wpc_let_nv [l2] [1]%Qp with "[Hl22]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_head_spec. set_solver.
    iIntros (?) "(->&Hv&?) (Hl22&_)". simpl.

    iApply (@wpc_let_nv [l2;v] [1;p]%Qp with "[Hl22 Hv]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_tail_spec. set_solver.
    iIntros (l') "[% (->&?&Hl'&?&?&?)] (Hl22&Hv&_)". simpl.

    iApply (@wpc_let_nv [l'] [1]%Qp with "[Hl']").
    { auto_locs. set_solver. }
    { by iFrame. }

    iDestruct (vmapsfrom_correct with "[$]") as "%Hq".

    assert (is_loc v -> q/2 ≠ 0)%Qz as Hdq.
    { intros ? E. apply Qz_div_eq_zero in E. destruct Hq as [|Hq]; eauto.
      apply Hq in E.
      smultiset_solver. }

    rewrite <- (Qz_div_2 q).
    assert ( {[+ l0 +]} ≡  {[+ l0 +]} ⊎ ∅) as -> by smultiset_solver.
    iDestruct (vmapsfrom_split with "[$]") as "(? & ?)".
    1,2:intros E; apply Hdq in E; intros; congruence.

    rewrite -{4}(left_id_L _ _ {[π]}) -(Qp.div_2 p).
    iDestruct (vpbt_split with "[$]") as "(?&?)".

    wpc_apply list_cons_spec. set_solver. exact (fun _ _ => True%I). done.
    iIntros (?) "(?&?&?) (?&_)". simpl.

    iApply (wpc_weak ∅). set_solver. iApply wpc_postpone.
    iApply (wpc_context_vsingleton l' with "[$]").
    replace ((length L1 + S (length L1 + 0) - 1)%nat) with (2*length L1) by lia.
    iSpecialize ("IH" with "[$]"). rewrite right_id_L.
    iApply (wpc_mono with "[$]"). iIntros (?) "(?&?&?&?) ?". iFrame.
    iDestruct (confront_vpbt_vpbt v1 l' with "[$]") as "%". by vm_compute.
    pclean l'.
    rewrite -app_assoc cons_middle. iFrame.
    rewrite Qz_div_2 Qp.div_2. rewrite right_id. iSteps. iExists _. iSteps.
    Unshelve. exact unit. }
Qed.

Lemma list_rev_spec' π L l :
  CODE (list_rev [[l]])
  TID π
  SOUV (locs l)
  PRE (♢ (2*length L) ∗ List L l)
  POST (fun l' => List (rev (halves L)) l' ∗ l' ⟸? {[π]} ∗ l' ↤? ∅ ∗ List (halves L) l).
Proof.
  iIntros "(? & ?)".
  wpc_call.
  iApply wpc_let_empty.
  { auto_locs. reflexivity. }
  { set_solver. }
  wpc_apply list_nil_spec. set_solver. rewrite left_id.
  iIntros.
  wpc_apply @list_rev_append_spec'.
  rewrite right_id_L.
  eauto.
Qed.

End RevPreserving.
