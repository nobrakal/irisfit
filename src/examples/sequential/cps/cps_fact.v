From irisfit.examples Require Import proofmode.

(*
let rec fac_aux n k =
  if n <> 0
  then
    let k' = fun x -> k (n*x) in
    fac_aux (n-1) k'
  else
    k 1

let fac n = fac_aux n (fun x -> x)
 *)


(******************************************************************************)
(* First about the identity closure *)

Definition id_clo : tm :=
  mk_clo BAnon [["x"]]%binder ("x").

Section Id.
Context `{interpGS0 Σ}.

Definition id_spec  (_:loc) (args:list val) (t:tm) : iProp Σ :=
  ∀ π (A:Type) (EA:Enc A) (n:A),
  ⌜args = [enc n:val]⌝ -∗
  wpc ⊤ π (Some ∅) t (fun m => ⌜m=n⌝)%I.

Lemma clo_id_spec  π :
  CODE id_clo
  TID π
  PRE (♢ 1)
  POST (fun l => Spec 1 nil id_spec l ∗ l ↤ ∅ ∗ l ⟸ {[π]}).
Proof.
  iIntros.
  wpc_apply (wpc_mk_spec _ id_spec nil nil).
  1-4:compute_done.
  { iModIntro. iIntros. iIntros (?). iIntros. subst. simpl.
    by wpc_val. }
  rew_qz. iFrame. iSplitR.
  { unfold group_pointedbys. simpl. easy. }
  iSteps.
Qed.

Definition id_spec_autodestroy (l:loc) (args:list val) (t:tm) : iProp Σ :=
  ∀ π (A:Type) (EA:Enc A) (n:A) qp S,
  ⌜args = [enc n:val]⌝ -∗
  l ⟸ {[π]} ∗ l ↤ ∅ ∗ enc n ⟸?{qp} S -∗
  wpc ⊤ π (Some ∅) t (fun m => ⌜m=n⌝ ∗ enc n ⟸?{qp} S ∗ ♢1)%I.

Lemma clo_id_spec_autodestroy π :
  CODE id_clo
  TID π
  PRE (♢ 1)
  POST (fun l => Spec 1 nil id_spec_autodestroy l ∗ l ↤ ∅ ∗ l ⟸ {[π]}).
Proof.
  iIntros.
  wpc_apply (wpc_mk_spec _ id_spec_autodestroy nil nil).
  1-4:compute_done.
  { iModIntro. iIntros. iIntros (?????? ->) "(?&?&?)". subst. simpl.
    iDestruct (confront_pbt_vpbt with "[$]") as "%".
    { apply Qp.not_add_le_l. }
    pclean l by ltac:(fun _ => destruct (enc n); set_solver).

    iApply wpc_fconseq. iApply spec_free. iFrame "∗#".
    simpl. rew_qz. iIntros "(?&_)". wpc_val. by iFrame. }
  rew_qz. iFrame. iSplitR.
  { unfold group_pointedbys. simpl. easy. }
  iSteps.
Qed.
End Id.

(******************************************************************************)
(* The actual code of fac *)

Definition fac_aux : val :=
  μ: "self", [["n", "cont"]],
    let: "b" := ("n" '== 0) in
    if: "b"
    then call_clo "cont" [[1]]
    else
      let: "ncont" :=
        mk_clo BAnon [["r"]]%binder
          (let: "p" := "n" '* "r" in call_clo "cont" [["p"]]) in
      let: "m" := "n" '- 1 in
      "self" [["m", "ncont"]] .

Definition fac : val :=
  λ: [["n"]],
    let: "id" := id_clo in
    fac_aux [["n", "id"]].

Section Fac.
Context `{interpGS0 Σ}.

(* clo_cont_spec specifies [t] to return a natural [r] satisfying [Q r n]  *)
Definition clo_cont_spec (Q :Z -> nat -> Prop) pre (souv:list loc) (l:loc) (args:list val) (t:tm) : iProp Σ :=
  ∀ π (n:nat),
  ⌜args = [n:val]⌝ -∗
  pre -∗
  wpc ⊤ π (Some ({[l]} ∪ locs souv)) t (fun (r:Z) => ⌜Q r n⌝)%I.

(* Spec_clo_cont specifies the continuation l _and_ bundles what is needed to fire it. *)
Definition Spec_clo_cont (Q:Z -> nat -> Prop) (pre:iProp Σ) souv (env:list (val*Qz)) (l:loc) : iProp Σ :=
  pre ∗ Spec 1 env (clo_cont_spec Q pre souv) l.

Ltac subst_not_in x :=
  rewrite (subst_not_in x); only 2:now vm_compute.

(* The specification of [spec_aux] *)
Lemma fac_aux_spec π Q (n:nat) (cont:loc) inv souv env :
  locs env.*1 ∖ ({[cont]} ∪ locs souv) = ∅ ->
  CODE (fac_aux [[n,cont]])
  TID π
  SOUV ({[cont]} ∪ locs souv)
  PRE (♢ (3*n) ∗ cont ↤ ∅ ∗ Spec_clo_cont Q inv souv env cont)
  POST (fun (r:Z) => ⌜Q r (fact n)⌝ ∗ ♢ (3*n) ∗ cont ↤ ∅).
Proof.
  iStartProof.
  iRevert (cont inv souv env Q).
  iInduction (n) as [] "IH"; iIntros (cont inv souv env Q ?) "(Hdiams & Hcont)".
  { wpc_call.
    wpc_let_noclean. wpc_call_prim. simpl. wpc_if.
    rewrite !subst_call_clo. simpl. iDestruct "Hcont" as "(?&(?&Hcont))".
    iDestruct PBT_empty as "X".
    iApply (@wpc_call_spec_tac with "[$][$]").
    1,2:compute_done. set_solver.
    iModIntro. iIntros (?) "_ _ Hcont".
    iMod diamonds_zero. rew_qz.
    iSpecialize ("Hcont" with "[%//][$]").
    iApply (wpc_mono with "[$]"). iSmash. }

  wpc_call.
  wpc_let_noclean. wpc_call_prim. simpl. wpc_if.

  subst_not_in "self". subst_not_in "b".

  wpc_let_empty.
  mine 3. rewrite subst_subst_commut //.
  wpc_apply (wpc_mk_spec _ (clo_cont_spec (fun r m => Q r (S n * m)) (Spec_clo_cont Q inv souv env cont) (cont::souv))  [("cont", cont:val); ("n", (S n):val)] [1%Qz; 1%Qz] ).
  set_solver.
  1-4:compute_done.
  { iModIntro. simpl. iIntros (? ?) "Hspec".
    iIntros (?? ->).
    simpl. rewrite !subst_call_clo //. simpl.
    iIntros "(? & ?)".
    wpc_let_noclean. wpc_call_prim. simpl.

    rewrite subst_call_clo. simpl.
    iDestruct PBT_empty as "X".
    iApply( @wpc_call_spec_tac with "[$][$]").
    1-2:reflexivity. auto_locs. set_solver.
    iModIntro. iIntros (?) "_ _ Hspec_cont".
    iSpecialize ("Hspec_cont" with "[%] [$]").
    { rewrite -Nat2Z.inj_mul //. }
    iApply wpc_weak. shelve.
    iApply (wpc_mono with "[$]"). iSmash. Unshelve. auto_locs. set_solver. }
  iDestruct "Hcont" as "(?&?&?)".
  simpl. rew_qz. iFrame.
  iSplitR; first iSteps.
  iIntros (ncont) "(#Hspec&?&Henv&_)".

  (* LATER *)
  iApply wpc_let_noclean. simpl. wpc_call_prim. simpl.
  rewrite -Nat2Z.inj_sub; last lia. simpl.
  replace (n-0) with n by lia.
  iApply wpc_postpone. iApply (wpc_context_singleton with "[$]").

  iApply (wpc_mono with "[-]").
  { iSpecialize ("IH" $! ncont (Spec_clo_cont Q inv souv env cont) (cont::souv)).
    replace (({[cont]} ∪ locs souv)) with (locs (cont::souv)) by set_solver.
    iApply "IH". iPureIntro. shelve. iFrame "#∗". conclude_diamonds. Unshelve. auto_locs. set_solver. }


  iIntros (?) "(% & H1 & H2) ?".
  pclean ncont.
  iApply wpc_fconseq.
  { iApply spec_free. }
  iFrame "#∗". simpl.
  iIntros "(? & ((?&?&_) & _) )". simpl.
  wpc_val. iFrame. iFrame "%". conclude_diamonds.
Qed.

Lemma fac_spec π (n:nat) :
  CODE (fac [[n]])
  TID π
  PRE (♢ (3*n+1))
  POST (fun (m:Z) => ⌜m=fact n⌝ ∗ ♢(3*n+1)).
Proof.
  iIntros "Hdiams".

  wpc_call.
  wpc_let_empty. simpl. mine 1.
  wpc_apply (clo_id_spec). iIntros (l) "(#Hnl & ? & ?)".

  iApply wpc_postpone. iApply (wpc_context_singleton with "[$]").
  wpc_apply (fac_aux_spec _ (@eq Z) n l True%I nil nil). set_solver.
  iSplitR "Hnl".
  { iSplitL "Hdiams". conclude_diamonds.
    iSplitR; try easy.
    iApply spec_weak; last iFrame "#".
    iModIntro. iIntros (??) "H".
    iIntros (???) "_".
    iSpecialize ("H" $! _ Z with "[%]"). done.
    iApply wpc_weak. shelve.
    iApply (wpc_mono with "[$]"). iSmash.
    Unshelve. set_solver. }

  iIntros (?) "(%Hv & Hdiams & ?) ?". subst.
  pclean l.

  iApply wpc_fconseq.
  { iApply spec_free. }
  iFrame "#∗". iIntros "(?&_)".
  wpc_val. iSplitR; first done. conclude_diamonds.
Qed.

End Fac.
