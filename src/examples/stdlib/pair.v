From irisfit.examples Require Import proofmode.

Definition pair : val :=
  λ: [["l","r"]],
    let: "p" := alloc ^2 in
    "p".[0] <- "l";;
    "p".[1] <- "r";;
    "p".

Section Pair.
Context `{interpGS0 Σ}.

Lemma pair_spec' r1 q1 r2 q2 tid :
  (is_loc r1 -> q1 ≠ 0%Qz) -> (is_loc r2 -> q2 ≠ 0%Qz) ->
  CODE (pair [[r1, r2]])
  TID tid
  PRE (♢2 ∗ r1 ↤?{q1} ∅ ∗ r2↤?{q2} ∅)
  POST (fun p => p ↦ [r1;r2] ∗ p ↤ ∅ ∗ p ⟸ {[tid]} ∗ r1 ↤?{q1} {[+p+]} ∗ r2↤?{q2} {[+p+]} ∗ gen_heap.meta_token p (⊤ ∖ ↑irisfit_nm) ).
Proof.
  iIntros (Hr1 Hr2) "(?&?&?)".
  wpc_call.
  wpc_let_noclean.
  wpc_alloc. iIntros (?) "(?&?&?&?)".

  wpc_let_noclean.
  iSteps.
  wpc_let_noclean.
  iSteps.
  rewrite !left_id.
  iSmash.
Qed.

Lemma pair_spec r1 q1 r2 q2 tid :
  (is_loc r1 -> q1 ≠ 0%Qz) -> (is_loc r2 -> q2 ≠ 0%Qz) ->
  CODE (pair [[r1, r2]])
  TID tid
  PRE (♢2 ∗ r1 ↤?{q1} ∅ ∗ r2↤?{q2} ∅)
  POST (fun p => p ↦ [r1;r2] ∗ p ↤ ∅ ∗ p ⟸ {[tid]} ∗ r1 ↤?{q1} {[+p+]} ∗ r2↤?{q2} {[+p+]}).
Proof.
  iIntros.
  wpc_apply pair_spec'. all:eauto.
  iSmash.
Qed.
End Pair.
