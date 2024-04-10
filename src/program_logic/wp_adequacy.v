From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap gset auth.
From stdpp Require Import gmap gmultiset.

From irisfit.language Require Import language.
From irisfit.lib Require Import qz qz_cmra.
From irisfit Require Import successors ph wp interp hypotheses.

From stdpp Require Import relations.

Global Instance status_eq_dec : EqDecision status.
Proof. solve_decision. Qed.

(* ------------------------------------------------------------------------ *)
(* [not_stuck] *)

Definition not_stuck t g σ := (is_Some (to_val t) /\ g = Out) \/ (reducible t g σ).

(* ------------------------------------------------------------------------ *)
(* Pre_adequacy *)

Section pre_adequacy.
Context `{iG:!interpGS sz Σ}.

Definition wptp b mt (ts:list (tm*status)) Qs := ([∗ list] i ↦ t;Q ∈ ts;Qs, wp ⊤ b (mt+i) (fst t) (fun v => outside (mt+i) ∗ Q v))%I.

(* cctx is the context of all threads. *)
Definition cctx i (t:tm) : (nat * (gmap loc Qp * gset loc)) := (i,(∅, locs t)).
Definition corr_ctx (ts:list (tm*status)) : ctx :=
  list_to_map (imap cctx (fst <$> ts)).

Lemma imap_cctx_nodup ts : NoDup (imap cctx ts).*1.
Proof.
  apply NoDup_alt.
  intros i j x.
  rewrite !list_lookup_fmap !list_lookup_imap.
  intros Hi Hj.
  destruct (ts !! i); inversion Hi. subst.
  destruct (ts !! j); inversion Hj. subst.
  eauto.
Qed.

Lemma corr_ctx_lookup ts i t (b:status) :
  ts !! i = Some (t,b) ->
  corr_ctx ts !! i = Some (∅,locs t).
Proof.
  intros Eq.
  apply elem_of_list_to_map_1. apply imap_cctx_nodup.
  apply elem_of_lookup_imap. do 2 eexists. split. done. rewrite list_lookup_fmap Eq //.
Qed.

Lemma wp_step mt b tid lk t1 σ1 k1 k2 t2 σ2 efs Q (g1 g2:status) e :
  atomic_step t1 g1 σ1 t2 g2 σ2 efs →
  k1 !! tid = Some (lk, locs t1) ->
  e !! tid = Some g1 ->
  k2 = ((<[tid:=(lk, locs t2)]> k1) ⋅ (ft mt efs)) ->
  interp mt b k1 e σ1 -∗
  £1 -∗
  wp ⊤ b tid t1 Q ={⊤,∅}=∗ ▷ |={∅,⊤}=> (interp (mt + length (opt_to_list efs)) b k2 (<[tid:=g2]> e ∪ et mt efs) σ2 ∗ wp ⊤ b tid t2 Q ∗
     match efs with None => True | Some t => wp ⊤ b mt t (fun _ => outside mt)%I end).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (??? ->) "Hσ ? Hstep".

  iMod ("Hstep" with "[%//] [$]") as "E".
  erewrite atomic_step_no_val; eauto.

  iModIntro.
  iDestruct "E" as "(% & E)". iSpecialize ("E" with "[%//][$]").
  iModIntro. iMod "E" as "(? & ? & ?)". by iFrame.
Qed.

Lemma correct_ctx_image_locs fs :
  locs (fst <$> fs) = image (corr_ctx fs).
Proof.
  apply leibniz_equiv.
  intros l.
  auto_locs.
  rewrite elem_of_union_list elem_of_image.
  split.
  { intros (E,(HE,?)).
    apply elem_of_list_fmap_2 in HE.
    destruct HE as (y,(HEy&Hl)).
    apply elem_of_list_lookup_1 in Hl.
    destruct Hl as (i,Hy). apply list_lookup_fmap_Some in Hy. destruct Hy as ((?&?)&?&?). subst. simpl.
     exists i, (∅, locs t). split; eauto using corr_ctx_lookup. set_solver. }
  { intros (i,(r, (T1,T2))).
    rewrite /corr_ctx in T1.
    apply elem_of_list_to_map_2 in T1.
    apply elem_of_lookup_imap_1 in T1.
    destruct T1 as (?,(y,(Eq&?))). inversion Eq. subst.
    exists (locs y). split; last set_solver.
    eauto using elem_of_list_fmap_1, elem_of_list_lookup_2. }
Qed.

Lemma corr_ctx_upd ts1 t1 ts2 t2 g2 :
  (<[length ts1:=(∅, locs t2)]> (corr_ctx (ts1 ++ t1 :: ts2))) =  corr_ctx (ts1 ++ (t2,g2) :: ts2).
Proof.
  rewrite /corr_ctx !fmap_app !imap_app !list_to_map_app insert_union_r; last first.
  { apply not_elem_of_list_to_map_1.
    intros E. apply elem_of_list_fmap_2 in E.
    destruct E as ([],(?&E)). simpl in *.
    apply elem_of_lookup_imap_1 in E.
    destruct E as (?,(?,(E&E'))). subst.
    inversion E. subst.
    apply lookup_lt_Some in E'. rewrite fmap_length in E'. lia. }
  f_equal.
  rewrite !imap_cons !list_to_map_cons Nat.add_0_r fmap_length insert_insert //.
Qed.

Lemma op_disj (x y:ctx) :
  dom x ## dom y ->
  x ⋅ y = x ∪ y.
Proof.
  intros.
  apply leibniz_equiv. intros ?.
  rewrite lookup_op lookup_union.
  destruct (x!!i) eqn:E.
  { assert (y!!i = None) as E'.
    { assert (i ∈ dom x) by eauto using elem_of_dom.
      apply not_elem_of_dom. eauto. }
    rewrite E E'. rewrite right_id //. }
  rewrite E !left_id //.
Qed.

Lemma corr_ctx_fork n ts tfs :
  n = length ts ->
  (corr_ctx ts) ⋅ (ft n tfs) =
  corr_ctx (ts ++ opt_to_list tfs).
Proof.
  intros ->.
  rewrite /corr_ctx fmap_app imap_app list_to_map_app op_disj.
  { f_equal. destruct tfs; try done. simpl. rewrite right_id fmap_length //. }

  intros i H1 H2.
  apply elem_of_dom in H1. destruct H1 as (x,H1).
  apply elem_of_list_to_map_2, elem_of_lookup_imap_1 in H1.
  destruct H1 as (n,(y,(H1&Hf))). injection H1. intros. subst.
  apply elem_of_dom in H2. destruct H2 as (x,H2).
  destruct tfs; simpl in *.
  { apply lookup_singleton_Some in H2. destruct H2.
    apply lookup_lt_Some in Hf. rewrite fmap_length in Hf. lia. }
  { rewrite lookup_empty // in H2. }
Qed.

Definition get_crit (i:nat) (x:tm*status) := (i,snd x).

Definition corr_critsec (ts:list (tm*status)) : gmap thread_id status :=
  list_to_map (imap get_crit ts).

Lemma imap_get_crit_nodup ts:
  NoDup (imap get_crit ts).*1.
Proof.
  apply NoDup_alt.
  intros i j x.
  rewrite !list_lookup_fmap !list_lookup_imap.
  intros Hi Hj.
  destruct (ts !! i); inversion Hi. subst.
  destruct (ts !! j); inversion Hj. subst.
  eauto.
Qed.

Definition all_out (e:critsec) := map_Forall (fun _ x => x =Out ) e.
Definition AllOut (ts:list (tm*status)) := Forall (fun x => x = Out) (snd <$> ts).

Lemma correct_corr_critsec ts :
  all_out (corr_critsec ts) <-> AllOut ts.
Proof.
  rewrite /AllOut /corr_critsec /all_out Forall_forall map_Forall_lookup.
  split.
  { intros X g Hg. apply elem_of_list_fmap in Hg. destruct Hg as ((?&?)&Eq&Hg).
    subst. apply elem_of_list_lookup in Hg. destruct Hg as (i,Hi).
    apply (X i). apply elem_of_list_to_map_1. apply imap_get_crit_nodup.
    assert ((i, (t, s).2) = (get_crit i (t,s))) as Eq by done. rewrite Eq.
    eauto using elem_of_lookup_imap_2. }
  { intros X i g Hi.
    apply elem_of_list_to_map_2 in Hi.
    apply elem_of_lookup_imap_1 in Hi. destruct Hi as (?&(?&?)&Eq&?). inversion Eq. subst.
    apply X. apply elem_of_list_fmap. exists (t,s). split; first done. apply elem_of_list_lookup.
    eauto. }
Qed.

Lemma correct_corr_decide_critsec {A:Type} ts (a b:A) :
  (if decide (all_out (corr_critsec ts)) then a else b) =
  if decide (AllOut ts) then a else b.
Proof.
  case_decide.
  { rewrite decide_True //. by eapply correct_corr_critsec. }
  { rewrite decide_False //. by rewrite -correct_corr_critsec. }
Qed.

Lemma corr_critsec_upd ts1 t1 ts2 t2 g2 :
  (<[length ts1:=g2]> (corr_critsec (ts1 ++ t1 :: ts2))) =  corr_critsec (ts1 ++ (t2,g2) :: ts2).
Proof.
  rewrite /corr_critsec !imap_app !list_to_map_app insert_union_r; last first.
  { apply not_elem_of_list_to_map_1.
    intros E. apply elem_of_list_fmap_2 in E.
    destruct E as ([],(?&E)). simpl in *.
    apply elem_of_lookup_imap_1 in E.
    destruct E as (?,(?,(E&E'))). subst.
    inversion E. subst.
    apply lookup_lt_Some in E'. lia. }
  f_equal.
  rewrite !imap_cons !list_to_map_cons Nat.add_0_r insert_insert //.
Qed.

Lemma corr_critsec_fork n ts tfs :
  n = length ts ->
  (corr_critsec ts) ∪ (et n tfs) =
  corr_critsec (ts ++ opt_to_list tfs).
Proof.
  intros ->.
  rewrite /corr_critsec imap_app list_to_map_app.
  f_equal. destruct tfs.
  { simpl. rewrite Nat.add_0_r //. }
  { reflexivity. }
Qed.

Lemma corr_critsec_same t' ts1 t g ts2 :
  corr_critsec (ts1 ++ (t,g) :: ts2) = corr_critsec (ts1 ++ (t',g) :: ts2).
Proof.
  rewrite /corr_critsec !imap_app !list_to_map_app //.
Qed.

Lemma corr_ctx_same t' g' ts1 t g ts2 :
  locs t = locs t' ->
  corr_ctx (ts1 ++ (t,g) :: ts2) = corr_ctx (ts1 ++ (t',g') :: ts2).
Proof.
  rewrite /corr_ctx !fmap_app !imap_app !list_to_map_app. simpl. intros ->. done.
Qed.

Lemma wptp_step b (ts1:list (tm*status)) σ1 ts2 σ2 Qs :
  step_oblivious (ts1,σ1) (ts2,σ2) →
  interp (length ts1) b (corr_ctx ts1) (corr_critsec ts1) σ1 -∗
  £1 -∗
  wptp b 0 ts1 Qs ={⊤,∅}=∗ ▷ |={∅,⊤}=>
  interp (length ts2) b (corr_ctx ts2) (corr_critsec ts2) σ2 ∗
  wptp b 0 ts2 (Qs ++ (replicate (length ts2 - length ts1) (fun _ => True)%I)).
Proof.
  iIntros (Hr) "Hi ? Ht".
  inversion_clear Hr. subst.
  (* Usual step. *)
  { iDestruct (big_sepL2_app_inv_l with "Ht") as (Qs1 Qs2 ->) "[Ht1 Ht]".
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Q Qs3 ->) "[Ht Ht2]".
    replace ((0 + (length ts0 + 0))) with (length ts0) by lia.
    iMod (@wp_step _ _ _  ∅ with "[$][$][$]") as "H".
    { done. }
    { rewrite /corr_ctx. apply elem_of_list_to_map_1. apply imap_cctx_nodup.
      simpl. assert ((length ts0, (∅, locs t1)) = cctx (length ts0) t1 ) as Eq. done.
      rewrite Eq. apply elem_of_lookup_imap_2. rewrite list_lookup_fmap.
      rewrite list_lookup_middle //. }
    { rewrite /corr_critsec. apply elem_of_list_to_map_1. apply imap_get_crit_nodup.
      assert ((length ts0, g1) = (get_crit (length ts0) (t1,g1))) as Eq by done. rewrite Eq.
      apply elem_of_lookup_imap_2. rewrite list_lookup_middle //. }
    { reflexivity. }

    do 2 iModIntro. iMod "H" as "(Hi & ? & ?)".

    iSplitL "Hi".
    { repeat (rewrite app_length; simpl).
      replace ((length ts0 + S (length ts3) + length (opt_to_list efs))) with (length ts0 + S (length ts3 + length (opt_to_list efs))) by lia.
      erewrite corr_ctx_upd.
      rewrite corr_ctx_fork.
      2:{ rewrite app_length. simpl. lia. }
      erewrite corr_critsec_upd.
      rewrite corr_critsec_fork.
      2:{ rewrite app_length. simpl. lia. }
      rewrite -!assoc. simpl. by iFrame. }

    simpl. iModIntro. rewrite -assoc.
    rewrite app_length. simpl.
    iApply (big_sepL2_app with "Ht1").
    iApply big_sepL2_cons. rewrite Nat.add_0_r. iFrame.
    replace (length (ts0 ++ (t2, g2) :: ts3 ++ opt_to_list efs) - (length ts0 + S (length ts3))) with (length (opt_to_list efs)).
    2:{ rewrite app_length cons_length app_length. lia.  }
    destruct efs; try done. simpl.
    replace (length ts0 + S (length ts3 + 0)) with (length ts0 + S (length ts3)) by lia.
    iFrame. rewrite right_id. iApply (wp_mono with "[$]"). iIntros. by iFrame. }
Qed.

Lemma step_grow_threads ts1 σ1 ts2 σ2 :
  step_oblivious (ts1, σ1) (ts2, σ2) ->
  length ts1 <= length ts2.
Proof.
  inversion_clear 1; subst.
  all:repeat (rewrite app_length; simpl); lia.
Qed.

Lemma steps_grow_threads n ts1 σ1 ts2 σ2 :
  nsteps step_oblivious n (ts1, σ1) (ts2, σ2) ->
  length ts1 <= length ts2.
Proof.
  revert ts1 σ1.
  induction n; intros ? ?; inversion_clear 1; first lia.
  destruct y. etrans.
  eapply step_grow_threads.
  all:eauto.
Qed.

Lemma wptp_steps b n ts1 σ1 ts2 σ2 Qs :
  nsteps step_oblivious n (ts1, σ1) (ts2, σ2) ->
  interp (length ts1) b (corr_ctx ts1) (corr_critsec ts1) σ1 -∗
  £n -∗
  wptp b 0 ts1 Qs ={⊤,∅}=∗ |={∅}▷=>^n |={∅,⊤}=>
  interp (length ts2) b (corr_ctx ts2) (corr_critsec ts2) σ2 ∗
  wptp b 0 ts2 (Qs ++ (replicate (length ts2 - length ts1) (fun _ =>  True)%I)).
Proof.
  revert ts1 σ1 ts2 σ2 Qs.
  induction n; intros ts1 σ1 ts2 σ2 Qs;
    inversion_clear 1; iIntros "Hi Hc Ht".
  { simpl. iApply fupd_mask_intro_subseteq; first eauto.
    replace (length ts2 - length ts2) with 0 by lia.
    rewrite app_nil_r. iFrame. }
  destruct y.
  rewrite -Nat.add_1_l lc_split. iDestruct "Hc" as "(?&?)".
  iDestruct (wptp_step with "[$][$]") as "Hs"; first eauto.
  iMod ("Hs" with "[$]") as "Hi".
  do 3 iModIntro.
  iMod "Hi" as "(? & ?)".
  iDestruct (IHn with "[$][$][$]") as "H"; first eauto.
  rewrite -assoc -replicate_add.
  assert (length ts1 <= length l) by (eauto using step_grow_threads).
  assert (length l <= length ts2) by (eauto using steps_grow_threads).
  replace (length l - length ts1 + (length ts2 - length l)) with (length ts2 - length ts1) by lia.
  by iFrame.
Qed.

Lemma big_sepL2_bupd1 `{Σ':gFunctors} {A B} (Φ : nat → A → B → iProp Σ') l1 l2 :
  ([∗ list] k↦x;y ∈ l1;l2, |==> Φ k x y) ==∗ [∗ list] k↦x;y ∈ l1;l2, Φ k x y.
Proof.
  rewrite !big_sepL2_alt.
  iIntros "(? & ?)". iFrame.
  by iApply big_sepL_bupd.
Qed.

Lemma big_sepL2_impl_aux {A B} I (Φ Ψ : nat → A → B → iProp Σ) l1 l2 i :
  I -∗
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ (i+k) y1 y2) -∗
  □ (∀ j x1 x2,
    ⌜l1 !! j%nat = Some x1⌝ → ⌜l2 !! j%nat = Some x2⌝ → I ∗ Φ (i+j) x1 x2 ={⊤}=∗ I ∗ Ψ (i+j) x1 x2) ={⊤}=∗
  I ∗ [∗ list] k↦y1;y2 ∈ l1;l2, Ψ (i+k) y1 y2.
Proof.
  rewrite !big_sepL2_alt. revert l2 i.
  induction l1; iIntros (l2 i) "HI (%E & Ht) #H".
  { destruct l2; simpl in *; try lia.  iFrame. eauto. }
  { destruct l2; simpl in *; try lia.
    iDestruct "Ht" as "(Hp & Ht)".
    iMod ("H" $! 0 with "[%] [%] [HI Hp]") as "(? & ?)".
    1-2:eauto.
    { rewrite Nat.add_0_r. iFrame. }
    rewrite Nat.add_0_r.
    iFrame "%".
    iMod (IHl1 l2 (S i) with "[$] [Ht] []") as "(? & ? & ?)".
    { iSplitR. iPureIntro. lia.
      iApply big_sepL_proper. 2:iFrame. intros. simpl. rewrite Nat.add_succ_r -Nat.add_succ_l //. }
    { iModIntro. iIntros.
      rewrite Nat.add_succ_l -Nat.add_succ_r.
      iApply "H"; try iFrame; iPureIntro; simpl; eauto. }
    iFrame.
    iApply big_sepL_proper. 2:iFrame. intros. simpl. rewrite Nat.add_succ_r -Nat.add_succ_l //. easy. }
Qed.

Lemma big_sepL2_impl  {A B} I (Φ Ψ : nat → A → B → iProp Σ) l1 l2 :
  I -∗
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
  □ (∀ j x1 x2,
    ⌜l1 !! j%nat = Some x1⌝ → ⌜l2 !! j%nat = Some x2⌝ → I ∗ Φ j x1 x2 ={⊤}=∗ I ∗ Ψ j x1 x2) ={⊤}=∗
  I ∗ [∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
Proof.
  iIntros "Hi Hl #E".
  iApply (big_sepL2_impl_aux _ _ _ _ _ 0 with "Hi [$] [-]").
  simpl. iModIntro. iIntros. iApply ("E" with "[%//] [%//] [$]").
Qed.

Lemma corr_critsec_lookup ts i t :
  ts !! i = Some t ->
  corr_critsec ts !! i = Some t.2.
Proof.
  intros Eq.
  apply elem_of_list_to_map_1. apply imap_get_crit_nodup.
  apply elem_of_lookup_imap. eauto.
Qed.


Lemma wptp_adequacy b n ts1 σ1 ts2 σ2 Qs :
  nsteps step_oblivious n (ts1, σ1) (ts2, σ2) ->
  interp (length ts1) b (corr_ctx ts1) (corr_critsec ts1) σ1 -∗
  £n -∗
  wptp b 0 ts1 Qs ={⊤,∅}=∗ |={∅}▷=>^n |={∅,⊤}=>
  interp (length ts2) b (corr_ctx ts2) (corr_critsec ts2) σ2 ∗ [∗ list] i ↦ e;Φ ∈ ts2;(Qs ++ (replicate (length ts2 - length ts1) (fun _ => True)%I)), from_option (fun v => outside i ∗ Φ v) True (to_val (fst e)).
Proof.
  iIntros (Hstep) "Hσ Hc He". iMod (wptp_steps with "Hσ Hc He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iIntros "E". iMod "E" as "(Hi & Ht)".
  iMod (big_sepL2_impl with "Hi Ht []") as "?". 2:by iFrame.
  iModIntro.
  iIntros (? e Q ? He) "(Hi & Hwp)". simpl.
  destruct (to_val _) as [v2|] eqn:E; last first.
  { by iFrame. }
  { rewrite wp_unfold /wp_pre. rewrite E.
    iMod ("Hwp" with "[%] [$]") as "hwp".
    { split.
      { destruct e. eapply corr_ctx_lookup. done. }
      { eauto using corr_critsec_lookup. } }
    by iFrame. }
Qed.

Lemma wp_not_stuck b lk mt (k:ctx) e t σ Q tid g :
  k !! tid = Some (lk, locs t) ->
  e !! tid = Some g ->
  interp mt b k e σ ∗ wp ⊤ b tid t (fun v => outside tid ∗ Q v) ={⊤, ∅}=∗
  ⌜not_stuck t g σ⌝.
Proof.
  iIntros (??) "[Hi Hwp]".
  rewrite wp_unfold /wp_pre.

  destruct (to_val t) eqn:?.
  { iMod ("Hwp" with "[%//][$]") as ">(?&?&?)".
    iDestruct (use_outside with "[$][$]") as "%".
    iMod (fupd_mask_subseteq ∅). set_solver. iModIntro. iPureIntro.
    left. naive_solver. }
  iMod ("Hwp" with "[%//] [$]") as "[%Hred Hwp]".
  iPureIntro. right. eauto.
Qed.

Lemma live_heap_size_le_heap_size sz0 r τ :
  live_heap_size sz0 r τ ≤ size_heap sz0 τ.
Proof.
  rewrite /size_heap /live_heap_size.
  eapply stdpp.map_fold_ind_2 with (P:= fun x1 x2 _ _ => x1 <= x2).
  all:try (intros; lia).
  { intros. rewrite -!not_elem_of_dom !dom_collect //. }
  { intros. unfold collect in *.
    rewrite !map_lookup_imap in H1,H2.
    destruct (τ !! i) eqn:E2; last inversion H2.
    unfold collect_block in *. simpl in *.
    inversion H1. inversion H2. subst.
    case_decide; simpl; lia. }
Qed.

Lemma interp_reasonable b ms0 e mt (k:ctx) σ :
  interp mt b k e σ ∗ own γmax (to_agree ms0) -∗
  ⌜all_out e -> live_heap_size sz (image k) σ <= ms0⌝.
Proof.
  iIntros "(Hi&Hag)" (Htrue).
  destruct_interp "Hi". iDestruct (own_valid_2 with "[$][$]") as "%Hv".
  apply to_agree_op_inv_L in Hv. subst.

  iPureIntro.
  rewrite /valid_store in Hθvalid.

  replace (image_less η k) with (image k) in Hτ; last first.
  { apply leibniz_equiv. apply set_equiv_subseteq.
    split. 2:eauto using image_less_subseteq_image.
    intros l. rewrite elem_of_image elem_of_image_less.
    intros (i&ls&?&?). exists i,ls. split; first done. destruct Hdebt.
    assert (η !! i = Some None) as X.
    { assert (is_Some (e !! i)) as (?&?).
      { apply elem_of_dom. destruct Hρ. rewrite de_dom -ri_dom. eauto using elem_of_dom. }
      assert (is_Some (η !! i)) as (?&?).
      { apply elem_of_dom. rewrite -de_dom. by eapply elem_of_dom. }
      specialize (Htrue _ _ H1). simpl in Htrue. subst x. naive_solver. }
    rewrite lookup_total_alt X. unfold xroot, xroot_less in *. set_solver. }

  assert (image k ⊆ dom σ).
  { destruct Hσ as (?&?). done. }

  apply linked_size_heap with (sz:=sz) in Hτ; eauto. rewrite Hτ.
  etrans; last done. apply live_heap_size_le_heap_size.
Qed.

Lemma wptp_not_stuck (x:bool) b n ms ts1 σ1 ts2 σ2 Qs t2 b2 :
  nsteps step_oblivious n (ts1, σ1) (ts2, σ2) ->
  (if x then True else (t2,b2) ∈ ts2) ->
  own γmax (to_agree ms) -∗ interp (length ts1) b (corr_ctx ts1) (corr_critsec ts1) σ1 ∗ £n ∗ wptp b 0 ts1 Qs
  ={⊤,∅}=∗ |={∅}▷=>^n |={∅}=> ⌜if x then AllOut ts2 → live_heap_size sz (locs (fst <$> ts2)) σ2 <= ms else not_stuck t2 b2 σ2⌝.
Proof.
  iIntros (Hstep Hel) "? (Hi & Hc & Ht)".
  iDestruct (wptp_steps with "[$][$][$]") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iIntros ">(? & Ht)".
  destruct x.
  { iDestruct (interp_reasonable with "[$]") as "%E".
    iApply fupd_mask_intro. set_solver. iIntros "_".
    iPureIntro.
    rewrite correct_ctx_image_locs //. unfold AllOut.
    intros. apply E. by eapply correct_corr_critsec. }
  { eapply elem_of_list_lookup in Hel as [i Hlook]. unfold wptp.
    destruct ((Qs ++ replicate (length ts2 - length ts1) (λ _, True)%I)!! i) as [Φ|] eqn: Hlook2; last first.
    { rewrite big_sepL2_alt. iDestruct "Ht" as "[%Hlen _]". exfalso.
      eapply lookup_lt_Some in Hlook. rewrite Hlen in Hlook.
      eapply lookup_lt_is_Some_2 in Hlook. rewrite Hlook2 in Hlook.
      destruct Hlook as [? ?]. naive_solver. }

    iDestruct (big_sepL2_lookup with "Ht") as "Ht". done. done.
    simpl. iApply (wp_not_stuck _ ∅ _ _ _ _ _ (fun _ => True)%I); simpl.
    eauto using corr_ctx_lookup.
    apply corr_critsec_lookup in Hlook. done.  iFrame.
    iApply (wp_mono with "[$]"). iIntros (?) "(?&?)". iFrame. }
Qed.

End pre_adequacy.

Import Initialization.

Definition steps := rtc step_oblivious.

Lemma corr_ctx_init e b :
  locs e = ∅ ->
  corr_ctx [(e,b)] = {[0:=(∅,∅)]}.
Proof.
  intros Hlt.
  rewrite /corr_ctx.
  simpl. rewrite Hlt. rewrite insert_empty //.
Qed.

Lemma fupdN_switch `{invGS Σ} (Q:iProp Σ) n:
  (|={∅}▷=>^n |={∅}=> Q) ⊢ (|={∅}=> |={∅}▷=>^n Q)%I.
Proof.
  iIntros "E".
  iInduction (n) as [] "IH"; iFrame.
  iMod "E". do 3 iModIntro. iMod "E". iApply "IH". iFrame.
Qed.

Lemma roots_inv_bump ρ :
  roots_inv ∅ ∅ ρ 0 ->
  roots_inv {[0 := (∅, ∅)]} {[0:=None]} ρ 1.
Proof.
  intros [Hk Hmt].
  constructor; eauto.
  { intros ? ? ? E Hl H1.
    apply lookup_singleton_Some in Hl,H1. destruct Hl,H1. subst.
    set_solver. }
  { intros ?. rewrite dom_singleton elem_of_singleton.
    intros ->. lia. }
Qed.

Lemma debt_bump i :
  debt {[i := Out]} {[i := None]}.
Proof.
  constructor; try rewrite !dom_insert_L //.
  intros ??? E1 E2. apply lookup_singleton_Some in E1,E2. naive_solver.
Qed.

Lemma linked_bump θ τ :
  linked (image_less ∅ ∅) θ τ ->
  linked (image_less {[0 := None]} {[0 := (∅, ∅)]}) θ τ.
Proof. intros []. by constructor. Qed.

Lemma interp_bump `{interpGS sz Σ} :
  interp 0 true ∅ ∅ ∅ ==∗
  outside 0 ∗ interp 1 true {[0 := (∅, ∅)]} {[0:=Out]} ∅.
Proof.
  iIntros "Hi".
  destruct_interp "Hi".

  destruct Hdebt as [X _]. rewrite !dom_empty_L in X. symmetry in X.
  apply dom_empty_inv_L in X. subst.

  iMod (ghost_map.ghost_map_insert 0 ∅ with "Hinside") as "(?&?)". compute_done.

  iDestruct PBT_empty as "X".
  iFrame. iExists _,_,_,_. iFrame.
  rewrite !big_sepM_singleton. iFrame "#∗". simpl.
  rewrite image_singleton xroot_empty.
  iFrame "%∗". rewrite insert_empty.
  iPureIntro. eauto 15 using roots_inv_bump, debt_bump, linked_bump.
Qed.

Lemma corr_critsec_init e b :
  corr_critsec [(e,b)] = {[0:=b]}.
Proof. done. Qed.

Lemma wp_adequacy_open `{!interpPreG Σ} (sz:nat -> nat) (ms:nat) t1 v ts2 σ2 Q g :
  locs t1 = ∅ ->
  steps ([(t1,Out)],∅) ((tm_val v,g)::ts2,σ2) ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t1 (fun v => outside π ∗ ⌜Q v⌝)) ->
  Q v.
Proof.
  intros Hlt Hsteps Hwp.

  apply rtc_nsteps in Hsteps.
  destruct Hsteps as (n,Hsteps).
  eapply uPred.pure_soundness.
  apply (step_fupdN_soundness_gen _ HasLc n n).
  iIntros.

  iMod (interp_init sz ms) as "[%HinterpGS (%He&(Hi&Hdia&#?))]".
  iDestruct (Hwp HinterpGS) as "Hwp".
  iMod (interp_bump with "[$]") as "(?&?)".

  iSpecialize ("Hwp" with "[$][$]").
  iDestruct (wptp_adequacy _ n [(t1,Out)] _ _ _ [(fun v => ⌜Q v⌝)]%I) as "Hadequate"; eauto.
  rewrite corr_ctx_init // corr_critsec_init. simpl.

  rewrite !He.
  iMod ("Hadequate" with "[$][$][Hwp]") as "H".
  { iApply big_sepL2_singleton. simpl. done. }
  iApply fupdN_switch.
  iApply (step_fupdN_wand with "[-]"). iFrame.
  iIntros ">(? & (?&?) & ?)". iFrame.
  iApply fupd_mask_intro. set_solver. iIntros. eauto.
Qed.

Definition all_not_stuck (es:list (tm*status)) σ :=
  ∀ e b, (e,b) ∈ es ->
    not_stuck e b σ.

Lemma wp_adequacy_not_stuck_open `{!interpPreG Σ} (sz:nat -> nat) (ms:nat) t1 ts2 σ2 Q :
  locs t1 = ∅ ->
  steps ([(t1,Out)],∅) (ts2,σ2) ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t1 (fun v => outside π ∗ Q v)) ->
  (AllOut ts2 -> live_heap_size sz (locs ts2.*1) σ2 <= ms ) /\ all_not_stuck ts2 σ2.
Proof.
  intros Hlt Hsteps Hwp.

  apply rtc_nsteps in Hsteps.
  destruct Hsteps as (n,Hsteps).

  split.
  { eapply uPred.pure_soundness, (step_fupdN_soundness_gen _ HasLc n n).
    iIntros.
    iMod (interp_init sz ms) as "[%HinterpGS (%He&(Hi&Hdia&Hok))]".
    iDestruct (Hwp HinterpGS) as "Hwp".
    iDestruct (wptp_not_stuck true true n ms [(t1,Out)] _ _ _ [Q]) as "Hadequate"; eauto. exact Out.
    rewrite corr_ctx_init //.
    iMod (interp_bump with "[$]") as "(?&?)".
    iSpecialize ("Hwp" with "[$][$]").
    iDestruct ("Hadequate" with "Hok") as "Hadequate'".
    rewrite -He corr_critsec_init. simpl. unfold wptp. simpl. rewrite right_id.
    iMod ("Hadequate'" with "[$]") as "?".
    rewrite !He.
    iApply fupdN_switch.
    iApply (step_fupdN_wand with "[-]"); eauto. }
  { intros ???.
    eapply uPred.pure_soundness, (step_fupdN_soundness_gen _ HasLc n n).
    iIntros.
    iMod (interp_init sz ms) as "[%HinterpGS (%He&(Hi&Hdia&Hok))]".
    iDestruct (Hwp HinterpGS) as "Hwp".
    iDestruct (wptp_not_stuck false true n ms [(t1,Out)] _ _ _ [Q]) as "Hadequate"; eauto.
    rewrite !corr_ctx_init // corr_critsec_init.
    iMod (interp_bump with "[$]") as "(?&?)".
    iSpecialize ("Hwp" with "[$][$]").
    rewrite -He. unfold wptp. simpl.
    iMod ("Hadequate" with "[$][$]").
    rewrite He. iApply fupdN_switch.
    iApply (step_fupdN_wand with "[-]"); eauto. }
Qed.

Import Initialization.

Lemma wp_adequacy b (sz:nat -> nat) (ms:nat) (t1:tm) v ts2 σ2 Q :
  locs t1 = ∅ ->
  steps ([(t1,Out)],∅) ((tm_val v,b)::ts2,σ2) ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t1 (fun v => outside π ∗ ⌜Q v⌝)) ->
  Q v.
Proof.
  intros.
  eapply wp_adequacy_open; eauto with typeclass_instances.
Qed.

Lemma wp_adequacy_not_stuck (sz:nat -> nat) (ms:nat) (t1:tm) ts2 σ2 Q:
  locs t1 = ∅ ->
  steps ([(t1,Out)],∅) (ts2,σ2) ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t1 (fun v => outside π ∗ ⌜Q v⌝)) ->
  (AllOut ts2 -> live_heap_size sz (locs ts2.*1) σ2 <= ms) /\ all_not_stuck ts2 σ2.
Proof.
  intros.
  eapply (wp_adequacy_not_stuck_open _ _ _ _ _ (fun v => ⌜Q v⌝)%I); eauto with typeclass_instances.
Qed.

Lemma wp_adequacy_core (sz:nat -> nat) (ms:nat) (t1:tm) θ σ :
  locs t1 = ∅ ->
  steps ([(t1,Out)],∅) (θ,σ) ->
  (∀ `{!interpGS sz Σ} π,
      ⊢ ♢ms -∗ outside π -∗ wp ⊤ true π t1 (fun _ => outside π)) ->
  (AllOut θ -> live_heap_size sz (locs θ.*1) σ <= ms) /\ all_not_stuck θ σ.
Proof.
  intros ?? Hwp.
  eapply wp_adequacy_not_stuck with (Q:=fun _ => True); eauto.
  iIntros.
  iDestruct (Hwp with "[$][$]") as "?".
  iApply (wp_mono with "[$]"). iIntros (?) "?". iFrame.
Qed.
