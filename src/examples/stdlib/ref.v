From irisfit.examples Require Import proofmode.

Definition ref : val :=
  λ: [["v"]],
    let: "x" := alloc 1 in
    "x".[0] <- "v";;
    "x".

Definition get : val :=
  λ: [["l"]],
    "l".[0].

Definition set : val :=
  λ: [["l", "v"]],
    "l".[0] <- "v".

Section Ref_spec.

Context `{!interpGS0 Σ}.

Definition isRef (v:val) (l:loc) := (l ↦ [v])%I.

Lemma ref_spec π q r (v:val) :
  q ≠ 0%Qz ->
  CODEFF (ref [[v]])
  TID π
  PRE  (♢ 1 ∗ v ↤?{q} r)
  POST (fun l => isRef v l ∗ v ↤?{q} (r ⊎ {[+l+]}) ∗ l ⟸ {[π]} ∗ l ↤ ∅ ∗ gen_heap.meta_token l (⊤ ∖ ↑irisfit_nm)).
Proof.
  iIntros (?) "(?&?)".
  wpc_call. wpc_let_noclean. wpc_alloc. iIntros (?) "(?&?&?)".
  wpc_let_noclean. simpl. wpc_store. simpl. iSmash.
Qed.

Lemma ref_spec_no_loc π (v:val) :
  is_loc v = false ->
  CODEFF (ref [[v]])
  TID π
  PRE  (♢ 1)
  POST (fun l => isRef v l ∗ l ⟸ {[π]} ∗ l ↤ ∅ ∗ gen_heap.meta_token l (⊤ ∖ ↑irisfit_nm)).
Proof.
  iIntros.
  replace ∅ with (locs v) by (destruct v; set_solver).
  wpc_apply (ref_spec _ 1 ∅ v); eauto.
  iSplitL. destruct v; try easy.
  iSteps.
Qed.

Lemma get_spec π l v qp :
  CODEFF (get [[l]])
  TID π
  PRE (isRef v l ∗ v ⟸?{qp} ∅)
  POST (fun w => ⌜v=w⌝ ∗ isRef v l ∗ v ⟸?{qp} {[π]}).
Proof.
  iIntros "(?&?)". wpc_call. wpc_load. iIntros. by iFrame.
Qed.

Lemma set_spec π l v w qw r :
  qw ≠ 0%Qz ->
  CODEFF (set [[l, w]])
  TID π
  PRE  (isRef v l ∗ w↤?{qw} r)
  POST (fun (_:unit) => isRef w l ∗ w ↤?{qw} (r ⊎ {[+ l +]}) ∗ v ↤?{0%Qz} {[-l-]}).
Proof.
  iIntros (?) "(?&?)". wpc_call. wpc_store. iSmash.
Qed.

Lemma set_spec_no_loc π l v (w:val):
  is_loc w = false ->
  CODEFF (set [[l, w]])
  TID π
  PRE  (isRef v l)
  POST (fun (_:unit) => isRef w l).
Proof.
  iIntros. wpc_call. wpc_apply (wpc_store _ _ _ 1 ∅).
  done. compute_done. iSplitR.
  { destruct w; done. }
  iIntros ([]) "(?&?&?)". iFrame.
Qed.

Lemma free_ref l v :
  l ⟸ ∅ ∗ l ↤ ∅ ∗ isRef v l =[#]=∗ ♢ 1 ∗ †l.
Proof.
  iIntros "(? & ? & ?)". iIntros. unfold isRef.
  iMod (interp_free with "[$] [$]") as "(?&?&?&?)"; try easy.
  simpl.  now iFrame.
Qed.

End Ref_spec.
