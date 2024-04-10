From irisfit.examples Require Import pair proofmode.

Definition option_none : val :=
  λ: [[]], pair [[false,val_unit]].
Definition option_some : val :=
  λ: [["x"]], pair [[true,"x"]].
Definition option_is_some : val :=
  λ: [["l"]], "l".[0].

Section Option.
Context `{interpGS0 Σ}.

Definition Option (l:loc) (o:option (Qp*Qz*val)) : iProp Σ :=
  match o with
  | None => l ↦ [val_bool false; val_unit]
  | Some (p,q,v) => l ↦ [val_bool true; v] ∗ v ⟸?{p} ∅ ∗ v ↤?{q} {[+l+]} end.

Lemma option_none_spec π :
  CODE (option_none [[]])
  TID π
  PRE (♢2)
  POST (fun l => Option l None ∗ l ⟸ {[π]} ∗ l ↤ ∅).
Proof.
  iIntros.
  wpc_call. wpc_apply (pair_spec _ 1 _ 1). 1,2:compute_done.
  iSplitR. easy. iIntros (?) "(?&?&?&_&_)".
  by iFrame.
Qed.

Lemma option_some_spec π v p q :
  (is_loc v → q ≠ 0%Qz) ->
  CODE (option_some [[v]])
  TID π
  PRE (♢2 ∗ v ⟸?{p} ∅ ∗ v ↤?{q} ∅)
  POST (fun l => Option l (Some (p,q,v)) ∗ l ⟸ {[π]} ∗ l ↤ ∅).
Proof.
  iIntros (?) "(?&?&?)".
  wpc_call. wpc_apply (pair_spec _ 1). 1,2:eauto.
  iIntros (?) "(?&?&?&_&?)". iFrame.
Qed.

Lemma option_is_some_spec π l o :
  CODE (option_is_some [[l]])
  TID π
  PRE (Option l o)
  POST (fun (b:bool) => ⌜b <-> is_Some o⌝ ∗ Option l o).
Proof.
  iIntros "Ho". wpc_call.
  destruct o as [((?,?),?)|].
  { iDestruct "Ho" as "(?&?&?)". wpc_load. iSmash. }
  { wpc_load. iIntros. iFrame.
    iPureIntro. split; first easy. intros (?,?). congruence. }
  Unshelve. all:exact inhabitant.
Qed.

Lemma option_free l o :
  Option l o ∗ l ⟸ ∅ ∗ l ↤ ∅ =[#]=∗
  ♢2 ∗ (match o with None => True | Some (p,q,v) => v ⟸?{p} ∅ ∗ v ↤?{q} ∅ end)%I.
Proof.
  iIntros "(Ho&?&?)". iIntros.
  destruct o as [((?,?),?)|].
  { iDestruct "Ho" as "(?&?&?)".
    iMod (interp_free' with "[$][$]") as "(?&?&_&?)".
    iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".
    rewrite smultiset.disj_union_singleton_opposite. by iFrame. }
  { iMod (interp_free' with "[$][$]") as "(?&?&?)". by iFrame. }
Qed.
End Option.
