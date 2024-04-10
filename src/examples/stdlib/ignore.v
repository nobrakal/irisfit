From irisfit.examples Require Import proofmode.

Definition ignore : val :=
  λ: [["x"]], val_unit.

Lemma ignore_spec `{interpGS0 Σ} E π X t (Q:unit -> iProp Σ) :
  wpc E π X t (fun (_:val) => Q ()) ⊢
  wpc E π X (ignore [t]) Q.
Proof.
  iIntros.
  destruct X as [r|].
  { wpc_apply (wpc_bind (ctx_call2 ignore [] []) _ ∅ Q).
    { set_solver. }
    { iApply PBT_empty. }
    { rewrite dom_empty_L right_id_L.
      iSplitL; last iSteps.
      iApply (wpc_mono with "[$]"). iSteps. } }
  { wpc_apply (wpc_bind_noclean (ctx_call2 ignore [] []) _ Q).
    iSplitL; last iSteps. iApply (wpc_mono with "[$]"). iSteps. }
Qed.
