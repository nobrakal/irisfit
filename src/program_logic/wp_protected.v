From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit Require Import more_maps_and_sets more_space_lang.
From irisfit Require Import interp.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

Set Implicit Arguments.

Section Wp_crit.
Context `{!interpGS sz Σ}.

Lemma inside_not_outside π T :
  inside π T ∗ outside π -∗ ⌜False⌝.
Proof.
  iIntros "(H1&H2)".
  iDestruct (ghost_map_elem_agree with "H1 H2") as "%".
  congruence.
Qed.

Lemma debt_enter (e:critsec) (π:nat) η :
  η !! π = Some None ->
  e !! π = Some Out ->
  debt e η ->
  debt (<[π:=In]> e) (<[π:=Some ∅]> η).
Proof.
  intros ? ? [].
  constructor; try rewrite !dom_insert_lookup_L //.
  intros ???. rewrite !lookup_insert_case. case_decide; naive_solver.
Qed.

Lemma debt_exit e π η :
  η !! π = Some (Some ∅) ->
  e !! π = Some In ->
  debt e η ->
  debt (<[π:=Out]> e) (<[π:=None]> η).
Proof.
  intros ? ? [].
  constructor; try rewrite !dom_insert_lookup_L //.
  intros ???. rewrite !lookup_insert_case. case_decide; naive_solver.
Qed.

Lemma roots_inv_no_debt x y η k ρ mt π:
  x = None \/ x = Some ∅ ->
  y = None \/ y = Some ∅ ->
  η !! π = Some x ->
  roots_inv k η ρ mt ->
  roots_inv k (<[π:=y]> η) ρ mt.
Proof.
  intros ??? []. constructor; eauto.
  { eapply mirror_dig_debt; try done. naive_solver. }
  { rewrite dom_insert_lookup_L //. }
Qed.

Lemma image_less_insert_same η π x1 x2 k:
  η !! π = Some x1 ->
  set_of_option x1 = set_of_option x2 ->
  image_less (<[π:=x2]> η) k = image_less η k.
Proof.
  intros E1 E2. apply leibniz_equiv. intros i.
  rewrite !elem_of_image_less.
  split; intros (a&b&?&X); exists a,b.
  all:rewrite lookup_total_alt ?lookup_insert_case.
  all:rewrite lookup_total_alt ?lookup_insert_case in X.
  all:case_decide; last naive_solver; subst; split; first done.
  all:rewrite ?E1 in X; rewrite ?E1.
  all:unfold xroot_less in *; set_solver.
Qed.

Lemma wp_enter E b π :
  outside π -∗
  wp E b π tm_enter (fun v => ⌜v=val_unit⌝ ∗ inside π ∅).
Proof.
  iIntros "?".
  iApply wp_unfold. intros_wp. intros_mod.
  destruct_interp "Hi".
  iDestruct (ghost_map_lookup with "Hinside [$]") as "%".
  assert (g=Out) as ->.
  { destruct Hdebt. naive_solver. }
  iSplitR; first eauto using reducible_enter.
  iIntros (????) "%Hstep Hcred".
  iModIntro.
  iMod (ghost_map_update (Some ∅) with "Hinside [$]") as "(Hinside&X1)".
  iMod "Hclose" as "_". apply invert_step_enter in Hstep.
  destruct Hstep as (?&?&?&?&?). subst. simpl.
  rewrite !right_id_L right_id (insert_id k).
  2:{ rewrite Htid. set_solver. }

  iModIntro.
  iSplitR "X1"; last first.
  { iApply wp_val. by iFrame. }
  iExists _,_,_,(<[π:=Some ∅]> η). iFrame "∗%".
  iPureIntro. inversion Hσ.
  split_and !; eauto using debt_enter.
  { eapply roots_inv_no_debt; try done. all:naive_solver. }
  { by erewrite image_less_insert_same. }
Qed.

Definition all_reg (R:gset loc) π (ρ:gmap loc (gset thread_id)) :=
  ∀ l, l ∈ R -> π ∈ ρ !!! l.

Local Definition PBT_precise S M : iProp Σ :=
  [∗ map] l ↦ q ∈ M, pbt_precise l q S.

Lemma pbt_pbt_precise l q S :
  l ⟸{q} S =[#]=∗ pbt_precise l q S.
Proof.
  iIntros "[% (%&?)]". iIntros.
  replace S with (S' ∪ (S ∖ S')).
  2:{ symmetry. by apply union_difference_L. }
  iMod (pbt_precise_approx with "[$]") as "(?&?)".
  by iFrame.
Qed.

Lemma PBT_PBT_precise S M :
  PBT S M =[#]=∗ PBT_precise S M.
Proof.
  iInduction M as [|] "IH" using map_ind.
  { iIntros "?". iIntros. rewrite /PBT_precise big_sepM_empty. by iFrame. }
  { iIntros "X". iIntros. rewrite /PBT /PBT_precise !big_sepM_insert //.
    iDestruct "X" as "(?&?)".
    iMod (pbt_pbt_precise with "[$][$]") as "(?&X)". iFrame "X".
    iApply ("IH" with "[$][$]"). }
Qed.

Lemma PBT_precise_PBT S M :
  PBT_precise S M -∗ PBT S M.
Proof.
  iIntros. iApply (big_sepM_impl with "[$]").
  iModIntro. iIntros. iExists _. iFrame. done.
Qed.

Local Lemma extract_all_reg r (π:thread_id) ρ L:
  auth_ctx ρ r -∗
  PBT_precise {[π]} L -∗
  ⌜all_reg (dom L) π ρ⌝.
Proof.
  iIntros "? X". iIntros (l Hl).
  apply elem_of_dom in Hl. destruct Hl as (q,Hl).
  iDestruct (big_sepM_lookup _ _ l with "X") as "?". done.
  iDestruct (pbt_precise_exploit with "[$]") as "%X".
  iPureIntro. destruct X as (?&?&?). rewrite lookup_total_alt H.
  set_solver.
Qed.

Lemma wp_exit E π b :
  inside π ∅ -∗
  wp E b π tm_exit (fun v => ⌜v=val_unit⌝ ∗ outside π).
Proof.
  iIntros "?".
  iApply wp_unfold. intros_wp. intros_mod.
  destruct_interp "Hi".
  iDestruct (ghost_map_lookup with "Hinside [$]") as "%".
  assert (g=In) as ->.
  { destruct Hdebt. assert (¬ g=Out) by naive_solver.
    by destruct g. }
  iSplitR; first eauto using reducible_exit.
  iIntros (????) "%Hstep _".
  iModIntro.
  iMod (ghost_map_update None with "Hinside [$]") as "(Hinside&X1)".
  iMod "Hclose" as "_". apply invert_step_exit in Hstep.
  destruct Hstep as (?&?&?&?&?). subst. simpl.
  rewrite !right_id_L right_id (insert_id k).
  2:{ rewrite Htid. set_solver. }

  iModIntro. iSplitR "X1"; last first.
  { iApply wp_val. by iFrame. }

  iExists _,τ,_,(<[π:=None]> η). iFrame "∗%".
  iPureIntro.
  split_and !; eauto using debt_exit.
  { eapply roots_inv_no_debt; try done. all:naive_solver. }
  { by erewrite image_less_insert_same. }
Qed.

Lemma roots_inv_change_dom k η ρ mt x1 x2 π :
  k !! π = Some x1 ->
  xroot x1 = xroot x2 ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=x2]> k) η ρ mt.
Proof.
  intros ?? [X1 X2 X3].
  constructor.
  { intros ??(?,?)?. rewrite lookup_insert_case.
    case_decide; last naive_solver. inversion 1. subst.
    destruct x1.
    intros. eapply X1. done. done. simpl in *. set_solver. }
  { intros ?. rewrite dom_insert_lookup_L //. apply X2. }
  { rewrite dom_insert_lookup_L //. }
Qed.

Lemma interp_borrow_inner_PBT1 mt e σ π lk lt k :
  k !! π = Some (lk,lt) ->
  interp mt true k e σ -∗
  PBT {[π]} (kdiv lk) ∗ interp mt true (<[π:=(kdiv lk, lt)]>k) e σ.
Proof.
  iIntros (?) "Hi". destruct_interp "Hi".
  iDestruct (big_sepM_insert_acc with "Hctx") as "(H1&H2)". done.
  rewrite {1}(kdiv_both lk) PBT_op. iDestruct "H1" as "(?&?)". simpl.
  iSpecialize ("H2" $! (kdiv lk,lt) with "[$]"). iFrame.
  iExists _,_,_,_. iFrame. iPureIntro.
  assert (xroot (lk, lt) = xroot (kdiv lk, lt)).
  { unfold xroot. simpl. rewrite dom_kdiv //. }
  split_and !; eauto using roots_inv_change_dom.
  { eapply closed_weak; first done. erewrite image_upd; done. }
  { eapply linked_weak; last done. erewrite image_less_upd'; done. }
Qed.

Lemma interp_borrow_inner_PBT2 mt e σ π lk lt k :
  k !! π = Some (lk,lt) ->
  PBT {[π]} (kdiv lk) ∗ interp mt true (<[π:=(kdiv lk, lt)]>k) e σ -∗
  interp mt true k e σ.
Proof.
  iIntros (?) "(?&Hi)". destruct_interp "Hi".
  iDestruct (big_sepM_insert_acc _ _ π with "Hctx") as "(H1&H2)".
  { rewrite lookup_insert //. }
  simpl. iDestruct (PBT_op with "[$]") as "?". rewrite -kdiv_both.
  iSpecialize ("H2" $! (lk,lt) with "[$]").
  rewrite insert_insert insert_id //.
  iFrame. iExists _,_,_,_. iFrame. iPureIntro.
  assert (xroot (kdiv lk, lt) = xroot (lk, lt)).
  { unfold xroot. simpl. rewrite dom_kdiv //. }
  split_and !; eauto.
  { eapply closed_weak; last done. erewrite image_upd; done. }
  { rewrite -(insert_id k π (lk,lt)) // -(insert_insert k π _ (kdiv lk, lt)).
    eapply roots_inv_change_dom; try done. rewrite lookup_insert //. }
  { eapply linked_weak; last done. erewrite image_less_upd'; done. }
Qed.

Lemma inside_clean π S V:
  inside π S =[true|π|V]=∗ inside π (S ∩ V).
Proof.
  iIntros "?". iIntros (??????) "Hi".

  iDestruct (interp_borrow_inner_PBT1 with "[$]") as "(?&?)". done.
  iMod (PBT_PBT_precise with "[$][$]") as "(Hi&HP)".
  destruct_interp "Hi".

  iDestruct (extract_all_reg with "[$][$]") as "%HS".

  iDestruct (ghost_map_lookup with "Hinside [$]") as "%X".
  iMod (ghost_map_update with "Hinside [$]") as "(?&X)". iFrame "X".

  iAssert (interp mt true (<[π:=(kdiv lk, V)]> k) e σ) with "[-HP]" as "?".
  2:{ iApply interp_borrow_inner_PBT2. done. iFrame. iApply (PBT_precise_PBT with "[$]"). }
  iExists _,_,_,(<[π:=Some (S ∩ V)]> η).
  iFrame "∗%". iPureIntro. split_and !.
  { inversion Hρ. constructor; eauto.
    { intros i l (?&?) ? ?. rewrite lookup_insert_case.
      case_decide; eauto. inversion 1. subst. simpl. intros Hl'.
      rewrite lookup_insert in H0. inversion H0. subst. specialize (HS l).
      destruct_decide (decide (l ∈ dom (kdiv lk))); eauto.
      eapply ri_mirror. rewrite lookup_insert. done. done. simpl. set_solver. }
    { rewrite !dom_insert_lookup_L // -ri_dom !dom_insert_lookup_L //. } }
  { inversion Hdebt. constructor; eauto. rewrite dom_insert_lookup_L //.
    intros. rewrite lookup_insert_case in H1. case_decide; last naive_solver.
    subst. eapply de_ok in X; try done. naive_solver. }
  { inversion Hτ. constructor; eauto.
    intros l. rewrite elem_of_image_less. intros (i&(?&?)&Hi&?).
    destruct_decide (decide (π=i)); subst.
    { rewrite lookup_total_insert in H0. rewrite lookup_insert in Hi. inversion Hi. subst.
      destruct_decide (decide (l ∈ dom (kdiv lk))) as Hl.
      { apply HS in Hl. intros Hf0. apply Htauro in Hf0.
        assert (l∉dom ρ) as Hf by naive_solver.
        apply not_elem_of_dom in Hf.
        rewrite lookup_total_alt Hf // in Hl. }
      { eapply linked_roo. eapply elem_of_image_less. exists i. eexists. rewrite lookup_insert.
        split; first done.
        unfold xroot_less in *. simpl in *. rewrite lookup_total_alt X. set_solver. } }
    { eapply linked_roo; eauto. eapply elem_of_image_less.
      do 2 eexists. split; first done. rewrite lookup_total_insert_ne // in H0. } }
Qed.

End Wp_crit.
