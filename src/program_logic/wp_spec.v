From iris.proofmode Require Import base proofmode classes.
From iris Require Import gen_heap.
From iris.algebra Require Import agree gmap auth.
From stdpp Require Import gmap binders gmultiset stringmap.

From irisfit.lib Require Import qz.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.
From irisfit.language Require Export closure.

From irisfit.program_logic Require Import more_maps_and_sets more_space_lang pbt utils.
From irisfit.program_logic Require Import interp more_interp wp_alloc wp_store wp_load wp_call wp_closure.

(* This file presents [Spec], an abstract predicate for closures. *)
Local Notation tpred Σ := (loc -d> list val -d> tm -d> iPropO Σ).

Section ClosureMore.
Context `{interpGS sz Σ}.

Definition spec_nm := nroot.@"spec".

Definition Spec_pre
  (arity : nat) (env:list (val*Qz)) (l:loc)
  (Spec : tpred Σ -d> iPropO Σ) : tpred Σ -d> iPropO Σ := λ  P,
  (∃ P' self args code,
    Closure env self args code l ∗ ⌜arity = length args⌝ ∗
    let body vs :=
      let fv := fv_clo' self args code in
      (substs (zip fv env.*1)) (substs' (zip args vs) (subst' self l code)) in
    ▷ □(∀ vs, Spec P' -∗ P' l vs (body vs)) ∗
    ▷ □(∀ vs t, P' l vs t -∗ P l vs t))%I.

Local Instance Spec_pre_contractive arity env l : Contractive (Spec_pre arity env l).
Proof.
  rewrite /Spec_pre /=. intros n S S' ? ?.
  repeat (f_contractive || f_equiv).
Qed.

Definition Spec arity env P l : iProp Σ :=
  fixpoint (Spec_pre arity env l) P.

Lemma Spec_unfold P arity env l :
  Spec arity env P l ⊣⊢ Spec_pre arity env l (fun P => Spec arity env P l) P.
Proof. apply (fixpoint_unfold (Spec_pre _ _ _)). Qed.

Global Instance Spec_persistent arity env P l : Persistent (Spec arity env P l).
Proof.
  rewrite /Persistent !Spec_unfold.
  iIntros "[%[%[%[% #(?&?&?&?)]]]]".
  iModIntro. iExists _,_,_,_. iFrame "#".
Qed.

Lemma spec_weak n e R1 R2 l :
  □(∀ vs t, R1 l vs t -∗ R2 l vs t) -∗
  Spec n e R1 l -∗ Spec n e R2 l.
Proof.
  iIntros "#HR".
  iLöb as "IH".
  setoid_rewrite Spec_unfold at 3 4.
  iIntros "#[%P [%e1 [%e2 [%e3 (?&?&HW&Hpost)]]]]".
  iExists P,e1,e2,e3; iFrame. iFrame "#".
  do 2 iModIntro. iIntros. iApply "HR"; eauto.
  iApply ("Hpost" with "[$]"); eauto.
Qed.

Lemma wp_mk_spec tid P (env:list (string * val)) lq self args code:
  (* If self is not anonymous, then it should not appear in args. *)
  correct_name self args ->
  (* We must give non-zero fraction of pointed-by. *)
  Forall (λ q : Qz, q ≠ 0%Qz) lq ->
  (* The code must contain no locs. *)
  locs code = ∅ ->
  (* We require the "right" env *)
  env.*1 = fv_clo' self args code ->
  (* The meaning of "Spec" *)
  □(∀ l vs, Spec (length args) (zip env.*2 lq) P l -∗ P l vs (substs env (substs' (zip args vs) (subst' self l code)))) -∗
  ♢ (sz (1 + length env)) ∗ group_pointedbys ∅ env.*2 lq -∗
  outside tid -∗
  wp ⊤ true tid (substs env (mk_clo self args code))
  (fun v =>  outside tid ∗ ∃ l, ⌜v = val_loc l⌝ ∗ l ↤ ∅ ∗ l ⟸ {[tid]} ∗ Spec (length args) (zip env.*2 lq) P l ∗  meta_token l (⊤ ∖ ↑irisfit_nm)).
Proof.
  iIntros (? ? ? Henv) "#Hwp (? & ?) Hc".
  replace (substs env) with (substs (zip env.*1 env.*2)).
  2:{ f_equal. rewrite zip_fst_snd //. }
  rewrite Henv.
  iDestruct (big_sepL2_length with "[$]") as "%Hl".

  iApply wp_postpone.

  iApply (wp_mono with "[-]").
  iApply wp_noclean.
  iApply (wp_mk_clo with "[-Hc][$]"); eauto.
  { rewrite -Henv. do 2 rewrite fmap_length //. }
  { rewrite fmap_length //. iFrame. }
  iIntros (?) "(?&[%l (%Hv & Hclo & ? & ? & ?)])". subst.
  iSpecialize ("Hwp" $! l).

  iApply wp_val. iFrame.
  iExists l. iFrame.
  iSplitR; try easy.
  setoid_rewrite Spec_unfold at 2.
  iExists _,_,_,_. iFrame.
  iSplitR; first easy.

  iSplit.
  { do 2 iModIntro. iIntros.
    rewrite fst_zip.
    iApply ("Hwp" with "[$]"). lia.  }
  { do 2 iModIntro. iIntros. eauto. }
Qed.

Lemma wp_call_spec P E i b n env k l vals Q :
  length vals = n ->
  locs env.*1 ⊆ dom k ->
  Spec n env P l -∗
  PBT {[i]} k -∗
  outside i -∗
  ▷ (∀ t, £1 -∗ PBT {[i]} k -∗ outside i -∗ P l vals t -∗ wp E b i t (fun v => outside i ∗ Q v)) -∗
  wp E b i (call_clo l (tm_val <$> vals)) (fun v => outside i ∗ Q v).
Proof.
  setoid_rewrite Spec_unfold at 1.
  iIntros (??) "#[% [%self [%args [%code (?&%Hl&Hwp&Hpost)]]]] ? ? Hp".
  subst.
  iApply (wp_call_clo with "[$][$][$]"); eauto.
  iModIntro. iIntros.
  iApply ("Hp" with "[$][$][$]").
  iApply "Hpost"; eauto.
  iApply "Hwp"; eauto.
  iApply Spec_unfold.
  iExists _,_,_,_. iFrame "#". iSplitR; try easy.
  eauto.
Qed.

Lemma spec_free P n env l x1 x2 x3 :
  l ⟸ ∅ ∗ l ↤ ∅ ∗ Spec n env P l =[⊤|x1|x2|x3]=∗ ♢ (sz (1 + length env)) ∗ group_pointedbys ∅ env.*1 env.*2 ∗ †l.
Proof.
  iIntros "(?&?&Hspec)".
  rewrite Spec_unfold.
  iDestruct "Hspec" as "[% [%e0 [%e1 [%e2 (? & %Hn&_)]]]]".
  iIntros.
  iMod (closure_free with "[$][%//][$]") as "(?&?&?&?)"; try easy.
  by iFrame.
Qed.

End ClosureMore.

Global Opaque Spec.
