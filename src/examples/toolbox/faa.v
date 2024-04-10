From irisfit Require Import wpc_logatom.

From irisfit.examples Require Import proofmode.

Definition ifcas t1 t2 t3 t4 t5 t6 : tm :=
  tm_enter ;;
  if: (tm_cas t1 t2 t3 t4) then (tm_exit ;; t5) else (tm_exit ;; t6).

Definition faa : val :=
  μ: "self", [["l","i","n"]],
    let: "m" := "l".["i"] in
    let: "r" := "m" '+ "n" in
    ifcas "l" "i" "m" "r" "m" ("self" [["l","i","n"]]).

Lemma dig_debt_tupd `{!interpGS0 Σ} D' π D :
  D ⊆ D' ->
  inside π D =[#]=∗ inside π D'.
Proof.
  iIntros (?) "?". iIntros. by iApply (dig_debt with "[$][$]").
Qed.

Section Wp_faa.
Context `{!interpGS0 Σ}.

Lemma faa_spec E tid (l:loc) p (i n:Z) :
  (0 <= i)%Z ->
  ACODE (faa [[l,i,n]])%T
  TID tid
  WITH E
  SOUV ∅
  <<< l ⟸{p} {[tid]} | ∀∀ bs m, ⌜bs !! Z.to_nat i = Some (val_int m)⌝ ∗ l ↦ bs >>>
  <<< l ↦ (<[Z.to_nat i:=val_int (n+m)]> bs) ∗ l ⟸{p} ∅ ∗ £1 | (fun v => ⌜v=m⌝) >>>.
Proof.
  iIntros (?) "?". iIntros (Φ) "AU".
  iLöb as "IH".

  iApply @diaframe.wpc_call_tac. reflexivity. 1,2:compute_done. set_solver.
  iModIntro. iIntros. simpl.
  wpc_let_noclean.
  iMod "AU" as (bs m) "[(%Hm&Hl) [Hclose _]]". solve_atomic.
  iApply (@wpc_load_tac _ _ _ _ _ _ _ _ _ _ _ _ bs).
  { apply lookup_lt_Some in Hm. lia. }
  { rewrite list_lookup_total_alt Hm //. }
  iFrame. simpl. rewrite list_lookup_total_alt Hm. simpl. rewrite left_id right_id.
  iIntros "Hl". iMod ("Hclose" with "[Hl]") as "AU".
  { by iFrame. }
  iModIntro. wpc_let_noclean. wpc_call_prim. simpl.
  clear bs Hm.

  iApply @wpc_enter. iIntros (k) "%Ek Hk ?".

  iApply (wp_bind_noclean _ _ _ (ctx_if _ _)).

  iMod "AU" as (bs m') "[(%Hm&Hl) Hclose]". solve_atomic.
  destruct_decide (decide (m' = m)); subst.
  { iClear "IH".

    iApply wp_tconseq. iApply (dig_debt_tupd {[l]}). 2:iFrame. set_solver.
    iIntros "?".
    iApply wp_tconseq. iApply tupd_clean_debt. iFrame.
    rewrite difference_diag_L union_idemp_L. iIntros "(?&?)".

    iApply (wp_mono with "[Hl]").
    { iApply wp_cas.wp_cas_suc; last by iFrame. all:naive_solver. }
    iIntros (?) "(->&?&Hl&_&_)". iDestruct "Hclose" as "[_ Hclose]".
    rewrite Z.add_comm. iMod ("Hclose" with "[$]").
    simpl. iModIntro. iApply wp_if. iIntros "!> _".

    iApply @wpc_exit; last iFrame. set_solver.
    iSmash. }
  { iApply (wp_mono with "[Hl]").
    { iApply wp_cas.wp_cas_fail; naive_solver. }
    iIntros (?) "(->&_&Hl)". iDestruct "Hclose" as "[Hclose _]".
    iMod ("Hclose" with "[Hl]"). by iFrame. iModIntro. simpl.
    iApply wp_if. iIntros "!> _".
    iApply @wpc_exit; last iFrame. set_solver. rewrite Ek.
    iApply ("IH" with "[$][$]"). }
  Unshelve. all:exact inhabitant.
Qed.

Lemma faa_spec_weak E tid (l:loc) (i n:nat) :
  (0 <= i)%Z ->
  ACODE (faa [[l,i,n]])%T
  TID tid
  WITH E
  SOUV {[l]}
  <<< True | ∀∀ bs m, ⌜bs !! Z.to_nat i = Some (val_int m)⌝ ∗ l ↦ bs >>>
  <<< l ↦ (<[Z.to_nat i:=val_int (n+m)]> bs) ∗ £1 | (fun v => ⌜v=m⌝) >>>.
Proof.
  iIntros (?) "_". iIntros (Φ) "AU".
  iApply wpc_split_ctx. iIntros (X HX) "HPBT".
  assert (is_Some (X !! l)) as (p&Hp).
  { apply elem_of_dom. set_solver. }
  iDestruct (PBT_borrow_pbt with "[$]") as "(?&Hback)". done.
  iApply (wpc_weak ∅). set_solver.
  papprox l.
  iApply (faa_spec with "[$]"). done.
  iAuIntro.
  iApply (aacc_aupd with "[$]"). done.
  iIntros (xs m) "(%&Hl)".
  unshelve iAaccIntro with "[-Hback]".
  { by exists xs,m. }
  all:iSmash.
Qed.
End Wp_faa.
