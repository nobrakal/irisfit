From iris Require Import invariants.
From iris.algebra Require Import excl dfrac_agree.

From irisfit.examples Require Import proofmode pair.

(* We define [spawn] as a macro, and instantiate later [spawn_code] and [spawn_clo] *)
Definition spawn t : tm :=
  let: "c" := pair [[0, ()]] in
  fork (let: "r" := t in
        (* We first set the value, _then_ the tag. *)
        "c".[1] <- "r";;
        "c".[0] <- ^1 );;
  "c".

Definition join : val :=
  μ: "self" , [["c"]] ,
      let: "tag" := "c".[0] in
      let: "b" := "tag" '== 1 in
      if: "b"
      then "c".[1]
      else "self" [["c"]].

Class spawnG Σ := SpawnG { spawn_tokG : inG Σ (exclR unitR); spawn_tokG' : inG Σ (dfrac_agreeR natO) }.
Local Existing Instance spawn_tokG.
Local Existing Instance spawn_tokG'.

Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO) ; GFunctor (dfrac_agreeR natR)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

Section SpawnJoin.
Context `{!spawnG Σ,interpGS0 Σ}.
Context (N : namespace).

Definition spawn_inv (γ γ':gname) (l:loc) (p:Qp) (q:Qz) (Ψ:val → iProp Σ) : iProp Σ :=
  ∃ tag lv,
    (* We have always either the pointsto & pointedby if l, or its proof of dealloc. *)
    (l ↦ [ ^tag; lv]%V) ∗
    (* q is not 0, as usual. *)
    ⌜q ≠ 0%Qz⌝ ∗
    (* Then we have 3-states transition system. *)
    ( (own γ' (to_frac_agree (1/2)%Qp 0) ∗ (⌜tag = 0 /\ lv = val_unit⌝)) ∨
      (own γ' (to_frac_agree (1/2)%Qp 1) ∗ ⌜tag = 0⌝ ∗ lv ↤?{q} {[+l+]} ∗ lv ⟸?{p} ∅ ∗ Ψ lv) ∨
      (* The final state *)
      (own γ' (to_dfrac_agree DfracDiscarded 2) ∗ ⌜tag = 1⌝ ∗
         (((lv ↤?{q} {[+l+]}) ∗ lv ⟸?{p} ∅ ∗ l ⟸{1 / 2} ∅ ∗ Ψ lv) ∨ own γ (Excl ())))).

Definition join_handle (l : loc) p q (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ γ', own γ (Excl ()) ∗ inv N (spawn_inv γ γ' l p q Ψ).

Global Instance spawn_inv_ne n γ γ' p q l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ γ' p q l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n p q l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle p q l).
Proof. solve_proper. Qed.

Lemma ownagf_valid2 γ p q (n m:nat) :
  (own γ (to_dfrac_agree p n)) -∗
  (own γ (to_dfrac_agree q m)) -∗
  ⌜n=m⌝.
Proof.
  iIntros.
  iDestruct (own_valid_2 with "[$] [$]") as %Hv.
  iPureIntro. apply dfrac_agree_op_valid in Hv.
  naive_solver.
Qed.

Lemma ownagf_update2 γ (r n m:nat) :
  own γ (to_frac_agree (1/2)%Qp n) -∗
  own γ (to_frac_agree (1/2)%Qp m) ==∗
  own γ (to_frac_agree (1/2)%Qp r) ∗ own γ (to_frac_agree (1/2)%Qp r).
Proof.
  iIntros.
  iMod (own_update_2 with "[$] [$]") as "(? & ?)". 2:by iFrame.
  apply dfrac_agree_update_2. compute_done.
Qed.

Lemma ownagdf_dup γ n :
  own γ (to_dfrac_agree DfracDiscarded n) ==∗
  own γ (to_dfrac_agree DfracDiscarded n) ∗ own γ (to_dfrac_agree DfracDiscarded n).
Proof.
  iIntros.
  iMod (own_update with "[$]") as  "(? & ?)". 2:by iFrame.
  rewrite -dfrac_agree_op.
  apply dfrac_agree_persist.
Qed.

Lemma ownagf_update_discard γ (r n m:nat) :
  own γ (to_frac_agree (1/2)%Qp n) -∗
  own γ (to_frac_agree (1/2)%Qp m) ==∗
  own γ (to_dfrac_agree DfracDiscarded r).
Proof.
  iIntros.
  iMod (ownagf_update2 _ r with "[$] [$]") as "(? & _)".
  iApply own_update. 2:iFrame.
  apply dfrac_agree_persist.
Qed.

Lemma spawn_spec i p q (Ψ:val → iProp Σ) t M :
  q ≠ 0%Qz ->
  dom M = locs t ->
  free_variables t = ∅ ->
  CODE (spawn t)
  TID i
  PRE (♢2 ∗ PBT {[i]} M ∗
       (∀ j, PBT {[j]} M -∗ wpc ⊤ j (Some ∅) t
             (fun v => Ψ v ∗ v ↤?{q} ∅ ∗ v ⟸?{p} {[j]}))%I)
  POST (fun l:loc => l ⟸{1/2} {[i]} ∗ l↤∅ ∗ join_handle l p q Ψ).
Proof.
  iIntros (? HM ?) "(?&?&Hf)".

  iApply (wpc_let with "[$]").
  { rewrite HM. set_solver. }

  wpc_apply (pair_spec _ 1%Qz _ 1%Qz). set_solver. 1,2:by compute_done.
  iSplitR. easy.
  iIntros (c) "(Hc1 & Hc2 & Hc3 & _) HM". rew_enc. simpl.

  iAssert (c ⟸{1/2} {[i]} ∗ c ⟸{1/2} {[i]})%I with "[Hc3]" as "(Hi & Hce)".
  { iApply pbt_split. rewrite Qp.div_2. rewrite union_idemp_L. iFrame. }

  iApply (wpc_context_singleton with "Hi").
  rewrite (subst_not_in "c"); last set_solver.
  wpc_let_empty. simpl.

  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (own_alloc ((to_frac_agree (1/2)%Qp 0) ⋅ (to_frac_agree (1/2)%Qp 0))) as (γ') "(Hn1 & Hn2)".
  { now apply dfrac_agree_op_valid. }
  iMod (inv_alloc N _ (spawn_inv γ γ' c p q Ψ) with "[Hc1 Hn1]") as "#Hinv".
  { iModIntro. iExists 0, val_unit. iSmash.  }

  iApply (wpc_mono with "[Hce Hf HM Hn2]").
  rewrite pbt_PBT.
  iDestruct (PBT_op _ M with "[$]") as "?".
  iApply (wpc_fork with "[$]").
  3:iSteps.
  { auto_locs. rewrite gmap.dom_op dom_insert_L dom_empty_L. set_solver. }
  iIntros.
  iDestruct (PBT_split with "[$]") as "(?&Hc)".
  iDestruct (PBT_insert1 with "Hc") as "(? & Hc)". eauto.
  iApply (wpc_let with "Hc").
  { rewrite dom_singleton_L. set_solver. }

  iApply (wpc_mono with "[-Hn2]").
  { iApply wpc_weak. 2:iApply "Hf"; iFrame. set_solver. }

  iIntros (?) "(HΨ & ? & ?) ?". simpl.

  simpl.
  iApply (wpc_let with "[$]"). set_solver.

  iInv N as (? ?) "(Hpt & Hq & Hsi)". solve_atomic.
  iApply fupd_wpc. iMod "Hpt".
  iDestruct "Hsi" as "[(>Hf & > %He) | [(>Hf & ?) | (>Hf & ?)] ]";
    iDestruct (ownagf_valid2 with "[$] [$]") as "%Hv"; try congruence.
  iMod (ownagf_update2 _ 1 with "[$][$]") as "(? & Hl)".
  iModIntro.

  iApply wpc_postpone.

  destruct He. subst. iStep 8. rewrite left_id.

  pclean v. simpl. wpc_val. iModIntro.
  iSplitR "Hl".
  { iSmash. }

  iIntros "?".
  iInv N as (? ?) "(>Hpt & Hq & Hsi)". solve_atomic.
  iDestruct "Hsi" as "[(>Hf & > %He) | [(>Hf & ?) | (>Hf & ?)] ]";
    iDestruct (ownagf_valid2 with "[$] [$]") as "%"; try congruence.

  iMod (ownagf_update_discard _ 2 with "[$] [$]").

  iApply wpc_postpone.
  iStep 6.
  rewrite -pbt_PBT.
  pclean c.
  iSmash.
Qed.

Lemma join_spec i l p q (Ψ : val → iProp Σ) :
  CODE (join [[l]])
  TID i
  PRE (l ⟸{1/2} {[i]} ∗ l ↤∅ ∗ join_handle l p q Ψ)
  POST (fun v => v ⟸?{p} {[i]} ∗ v ↤?{q} ∅ ∗ Ψ v ∗ ♢2).
Proof.
  iIntros "(Hl & Hmf &[% [% (Hexcl & #?)]])".

  iLöb as "IH".

  wpc_call.
  wpc_let_noclean.
  iInv N as (? ?) "(>Hpt & E)". solve_atomic.

  wpc_apply wpc_load_no_loc; eauto. simpl. lia.
  simpl.
  iIntros (?) "(% & Hpt)". subst.

  destruct_decide (decide (tag=0)) as Htag.
  { iModIntro. iSplitL "E Hpt".  iModIntro. iExists tag,lv. iFrame. iIntros.
    wpc_let_noclean. wpc_call_prim. wpc_if. simpl.
    rewrite bool_decide_eq_false_2; last naive_solver.
    iApply ("IH" with "[$][$][$]"). }

  iDestruct "E" as "(? & [ > (? & %Eq ) | [ (? & >% & ?) | (>? & (>%&?))]])".
  1-2:exfalso; apply Htag; try naive_solver.

  iMod (ownagdf_dup with "[$]") as "(He & ?)".

  iModIntro.
  iSplitR "He Hexcl Hmf Hl".
  { iSmash. }

  wpc_let_noclean. wpc_call_prim. wpc_if. subst. simpl.

  iInv N as (? ?) "(>Hpt & >% & Hsi)". solve_atomic.
  iDestruct "Hsi" as "[(>Hf & > %He) | [(>Hf & ?) | (>Hf & O)] ]";
     iDestruct (ownagf_valid2 with "[$] [$]") as "%Hv"; try congruence.
  iDestruct "O" as "( >% & [O | >O])". subst.
  2:{ iExFalso. iDestruct (own_valid_2 with "[$][$]") as %[]. }

  iDestruct "O" as "(>H & > Hpbt & >? & HΨ)".

  iApply wpc_postpone.
  iApply (wpc_frame_step with "[$]"). easy.
  iApply (wpc_mono with "[Hpt Hpbt]").
  { iApply wpc_load; eauto. 2:by iFrame. compute_done. }
  simpl. iIntros (?) "(% &?&?) ?". subst. rewrite left_id_L.

  iDestruct (pbt_join with "[$]") as "?".
  rewrite Qp.div_2 left_id_L.

  iDestruct (confront_pbt_vpbt with "[$]") as "%Hc".
  { now apply Qp.not_add_le_l. }

  pclean l.

  iApply wpc_tconseq.
  { iApply (interp_free' l). }
  iFrame. iIntros "(? &?& #Hd)".

  iApply wpc_tconseq.
  { iApply vmapsfrom_cleanup. }
  iFrame. iFrame "Hd".
  assert ({[+ l +]} ⊎ {[-l-]} ≡ (∅:smultiset loc)) as -> by smultiset_solver.
  iIntros.
  wpc_val. iModIntro. iFrame.
  iSmash.
Qed.
End SpawnJoin.

Definition spawn_code : val :=
  λ: [["f"]], spawn ("f" [[]]).
Definition spawn_clo : val :=
  λ: [["f"]], spawn (call_clo "f" [[]]).

Section SpawnDerived.
Context `{!spawnG Σ,interpGS0 Σ}.
Context (N : namespace).

Lemma spawn_code_spec i p q (Ψ : val → iProp Σ) (f : val) :
  q ≠ 0%Qz ->
  locs f = ∅ ->
  CODE (spawn_code [[f]])
  TID i
  PRE (♢2 ∗
       (∀ j, wpc ⊤ j (Some ∅) (f [[]])%T
             (fun v => Ψ v ∗ v ↤?{q} ∅ ∗ v ⟸?{p} {[j]}))%I)
  POST (fun l:loc => l ⟸{1/2} {[i]} ∗ l ↤∅ ∗ join_handle N l p q Ψ).
Proof.
  iIntros (? ?) "(? & Hf)".
  wpc_call.
  iDestruct PBT_empty as "?".
  iApply spawn_spec. 4:iFrame "#".
  eauto. set_solver. set_solver.
  iSmash.
Qed.

Lemma spawn_clo_spec i pv qv qf (Ψ : val → iProp Σ) (f : loc) :
  qv ≠ 0%Qz ->
  CODE (spawn_clo [[f]])
  TID i
  PRE (♢2 ∗ f ⟸{qf} {[i]} ∗
         (∀ j, f ⟸{qf} {[j]} -∗ wpc ⊤ j (Some ∅) (call_clo f [[]])%T
             (fun v => Ψ v ∗ v ↤?{qv} ∅ ∗ v ⟸?{pv} {[j]})))
  POST (fun l:loc => l ⟸{1/2} {[i]} ∗ l ↤∅ ∗ join_handle N l pv qv Ψ).
Proof.
  iIntros (?) "(?&Hcf&Hf)".
  wpc_call. rewrite pbt_PBT.
  iApply (spawn_spec with "[-]").
  4:{ iFrame. iIntros. iApply "Hf". rewrite pbt_PBT //. }
  eauto. set_solver. set_solver.
Qed.
End SpawnDerived.
