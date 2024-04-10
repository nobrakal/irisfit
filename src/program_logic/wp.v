From iris.proofmode Require Import base proofmode.
From iris.bi Require Import weakestpre.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import gset gmap frac.

From irisfit.language Require Import syntax substitution semantics reducible invert_step.
From irisfit Require Export more_maps_and_sets image roots_inv atomic.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* About [ft]. *)

(* Context of forked of threads. *)
Definition ft (mt:nat) (efs:option tm) : ctx :=
  match efs with
  | None => ∅
  | Some t => {[mt :=(∅,locs t)]} end.

Lemma ft_None mt : ft mt None = ∅.
Proof. done. Qed.

Lemma ft_Some mt t :
  ft mt (Some t) = {[mt :=(∅,locs t)]}.
Proof. done. Qed.

Lemma lookup_ft_notin tid mt efs :
  tid < mt ->
  ft mt efs !! tid = None.
Proof.
  revert mt. destruct efs; eauto.
  intros. simpl.
  rewrite lookup_insert_ne; last lia. done.
Qed.

Lemma fst_lookup_ft mt efs i :
  i ∈ dom (ft mt efs) ->
  fst <$> ft mt efs !! i = Some ∅.
Proof.
  destruct efs; try done. simpl.
  rewrite dom_singleton_L elem_of_singleton. intros ->.
  rewrite lookup_insert //.
Qed.

(* ------------------------------------------------------------------------ *)
(* About [et]. *)

(* Context of forked of threads. *)
Definition et mt (efs:option tm) : gmap thread_id status :=
  match efs with
  | None => ∅
  | Some t => {[mt := Out]} end.

Lemma et_None mt : et mt None = ∅.
Proof. done. Qed.

Lemma et_Some mt t :
  et mt (Some t) = {[mt := Out]}.
Proof. done. Qed.

Lemma lookup_et_notin tid mt efs :
  tid < mt ->
  et mt efs !! tid = None.
Proof.
  revert mt. destruct efs; eauto.
  intros. simpl.
  rewrite lookup_insert_ne; last lia. done.
Qed.

Lemma fst_lookup_et mt efs i :
  i ∈ dom (et mt efs) ->
  et mt efs !! i = Some Out.
Proof.
  destruct efs; try done. simpl.
  rewrite dom_singleton_L elem_of_singleton. intros ->.
  rewrite lookup_insert //.
Qed.

(* ------------------------------------------------------------------------ *)
(* About [upd]. *)

(* [upd] describes a valid update between two ctx:
   their domains are included and invisible roots were preserved. *)
Definition upd (k1 k2:ctx) : Prop :=
  (dom k1 ⊆ dom k2) /\
    (forall tid l1 l2, k1 !! tid = Some l1 -> k2 !! tid = Some l2 -> fst l1 = fst l2).

Lemma upd_refl k : upd k k.
Proof. constructor; naive_solver. Qed.

Lemma upd_trans : Transitive upd.
Proof.
  intros k1 k2 k3 [? U1] [? U2].
  constructor.
  { set_solver. }
  { intros.
    destruct (k2 !! tid) as [p|] eqn:E.
    2:{ apply not_elem_of_dom in E. assert (tid ∈ dom k1) by eauto. set_solver. }
    specialize (U1 tid l1 p).
    rewrite U1 //. eapply U2; eauto. }
Qed.

Lemma upd_fork k mt efs :
  ndom_lt k mt ->
  upd k (k ⋅ (ft mt efs)).
Proof.
  intros.
  constructor.
  { rewrite dom_op. set_solver. }
  intros i ? ? Hi1 Hi2.
  rewrite lookup_merge Hi1 lookup_ft_notin in Hi2; eauto.
  injection Hi2. now intros ->.
Qed.

Lemma upd_visible k tid lk l1 l2 :
  k !! tid = Some (lk,l1) ->
  upd k (<[tid:=(lk,l2)]> k).
Proof.
  intros Htid.
  constructor.
  { rewrite dom_insert. assert (tid ∈ dom k); eauto. set_solver. }
  { intros u ? ? Hu E.
    rewrite lookup_insert_case in E. case_decide; subst.
    all:naive_solver. }
Qed.

Lemma merge_fresh (k:ctx) tid v :
  tid ∉ dom k ->
  k ⋅ {[tid:=v]} = <[tid:=v]> k.
Proof.
  intros E.
  rewrite insert_singleton_op.
  2:{ apply not_elem_of_dom. eauto. }
  rewrite comm_L //.
Qed.

Lemma upd_step tid lk lt lt' k mt efs :
  tid ∈ dom k ->
  ndom_lt k mt ->
  upd (<[tid:=(lk, lt)]> k) (<[tid:=(lk, lt')]> k ⋅ ft mt efs).
Proof.
  intros.
  eapply upd_trans.
  1:apply upd_visible with (tid:=tid) (l1:=lt) (l2:=lt'); rewrite lookup_insert; eauto.
  rewrite insert_insert.
  eauto using upd_fork,ndom_lt_insert.
Qed.

Lemma upd_step' tid lk lt lt' k mt efs :
  k !! tid = Some (lk,lt) ->
  ndom_lt k mt ->
  upd k  (<[tid:=(lk, lt')]> k ⋅ ft mt efs).
Proof.
  intros.
  rewrite -{1}(insert_id k tid (lk,lt)) //.
  eauto using upd_step.
Qed.

(* ------------------------------------------------------------------------ *)
(* About [diff_empty] *)
Definition diff_empty (k k':ctx) :=
  forall i, i ∈ (dom k' ∖ dom k) -> fst <$> k' !! i = Some ∅.

Lemma diff_empty_refl k :
  diff_empty k k.
Proof. intros ?. set_solver. Qed.

Lemma diff_empty_ft k k' mt efs :
  dom k = dom k' ->
  diff_empty k (k' ⋅ ft mt efs).
Proof.
  intros Hd i. rewrite dom_op Hd. intros Hi.
  rewrite lookup_op.
  destruct (k'!!i) eqn:E'.
  { assert (i ∈ dom k') by eauto. set_solver. }
  rewrite E' left_id.
  apply fst_lookup_ft. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* We define WP w.r.t. an abstract [interp] axiomatized below. *)

Definition noclean (r:gset loc) : gmap loc Qp :=
  gset_to_gmap 1%Qp r.

Lemma dom_noclean r : dom (noclean r) = r.
Proof. apply dom_gset_to_gmap. Qed.

Definition critsec : Type := gmap thread_id status.
Implicit Type e : critsec.

Class irisfitGS (Σ : gFunctors) :=
  IrisFitGS {
      iinvgs :: invGS Σ;
      (* [interp maxthreadid ctx store] *)
      interp : thread_id -> bool -> ctx -> critsec -> store -> iProp Σ;
      (* Pointed By Threads *)
      PBT : gset thread_id -> gmap loc Qp -> iProp Σ;
      outside : thread_id -> iProp Σ;
      (* mt is indeed the max *)
      interp_valid : forall mt b k e σ,
        interp mt b k e σ -∗ ⌜ ndom_lt k mt ⌝;
      interp_shift : forall mt b k e tid σ lk l1 l2 M,
        (* The context of thread tid contains invisible roots lk, and visible l1 ∪ l2 *)
        k !! tid = Some (lk,l1 ∪ l2) ->
        l2 = dom M ->
        (interp mt b k e σ ∗ PBT {[tid]} M ==∗
          let k' := <[tid := (lk ⋅ M, l1)]> k in
          (* l2 is now in the context *)
          (interp mt b k' e σ) ∗
           (* The capacity to restore the old context. *)
            (∀ σ' k'' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k' k''⌝ -∗
                ⌜k'' !! tid = Some (lk ⋅ M, l1')⌝ -∗ (* The visible may change at will *)
                 interp mt' b k'' e' σ' ==∗
                 PBT {[tid]} M ∗ interp mt' b (<[tid:=(lk,l1' ∪ l2)]> k'') e' σ'));
      interp_shift_noclean : forall mt b k e tid σ lk l1 l2,
        k !! tid = Some (lk,l1 ∪ l2) ->
        (interp mt b k e σ ==∗
          let k' := <[tid := (lk ⋅ (noclean l2), l1)]> k in
          (* l2 is now in the context *)
          (interp mt false k' e σ) ∗
           (* The capacity to restore the old context. *)
            (∀ σ' k'' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k' k'' /\ diff_empty k' k''⌝ -∗
                ⌜k'' !! tid  = Some (lk ⋅ (noclean l2), l1')⌝ -∗ (* The visible may change at will *)
                 interp mt' false k'' e' σ' ==∗
                 interp mt' b (<[tid:=(lk,l1' ∪ l2)]> k'') e' σ'));
      interp_noclean : forall mt k e σ tid l lk,
        k !! tid = Some (lk,l) ->
        interp mt true k e σ -∗ interp mt false k e σ ∗
        (∀ σ' k' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k k' /\ diff_empty k k'⌝ -∗
           ⌜k' !! tid = Some (lk, l1')⌝ -∗
           interp mt' false k' e' σ' ==∗ interp mt' true k' e' σ')%I;
      interp_weak : forall tid lt' mt b k e lk lt σ,
        lt' ⊆ lt ->
        k !! tid = Some (lk,lt) ->
        interp mt b k e σ ==∗ interp mt b (<[tid:=(lk,lt')]> k) e σ;
    }.

Ltac intros_wp := iIntros (mt k lk σ e g (Htid&Hg)) "Hi".
Ltac intros_mod := iApply fupd_mask_intro; [set_solver| iIntros "Hclose"].

Section wp.
Context `{!irisfitGS Σ}.

(* ------------------------------------------------------------------------ *)
(* The actual wp. *)

Definition wp_pre
  (wp : coPset -d> bool -d> thread_id -d> tm -d> (val -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> bool -d> thread_id -d> tm -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E b tid t Q,
  (∀ mt k lk σ e g, ⌜k !! tid = Some (lk,locs t) /\ e !! tid = Some g⌝ -∗ interp mt b k e σ ={E,∅}=∗
  match to_val t with
  | Some v => |={∅,E}=> (interp mt b k e σ ∗ Q v)
  | None =>
      ⌜reducible t g σ⌝ ∗
      (∀ t' g' σ' efs, ⌜atomic_step t g σ t' g' σ' efs⌝ -∗
         £ 1 -∗ ▷ |={∅,E}=>
         let k' := (<[tid:=(lk, locs t')]> k) ⋅ (ft mt efs) in
         let e' := ((<[tid:=g']> e) ∪ et mt efs) in
       interp (mt + length (opt_to_list efs)) b k' e' σ' ∗ wp E b tid t' Q ∗
       (match efs with None => True | Some t => wp ⊤ b mt t (fun _ => outside mt) end))
  end)%I.

Local Instance wp_pre_contractive : Contractive wp_pre.
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp ? ? ? t Q.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

(* wp as the fixpoint of wp_pre *)
Definition wp : coPset -> bool -> thread_id -> tm -> (val -> iProp Σ) -> iProp Σ :=
  fixpoint wp_pre.

Lemma wp_unfold E b tid t Q :
  wp E b tid t Q ⊣⊢ wp_pre wp E b tid t Q.
Proof. apply (fixpoint_unfold wp_pre). Qed.

(* ------------------------------------------------------------------------ *)
(* Properties of wp. *)

Lemma wp_strong_mono E1 E2 b tid t Q Q' :
  E1 ⊆ E2 ->
  wp E1 b tid t Q -∗ (∀ v, Q v ={E2}=∗ Q' v) -∗ wp E2 b tid t Q'.
Proof.
  iIntros (?) "H HQ".
  iLöb as "IH" forall (t Q Q').
  rewrite !wp_unfold /wp_pre /=.
  iIntros (??????) "% Hσ".
  destruct (to_val t) as [v|] eqn:?.
  { iMod (fupd_mask_subseteq E1) as "H1". easy.
    iMod ("H" with "[% //] [$]") as ">[? ?]". iFrame.
    iFrame. iApply fupd_mask_intro. set_solver. iIntros "H2".
    iMod "H2". iMod "H1".
    by iApply "HQ". }
  { iMod (fupd_mask_subseteq E1) as "H1". easy.
    iMod ("H" with "[% //] [$]") as "[? H]". iFrame.
    iModIntro. iIntros.
    iSpecialize ("H" with "[% //][$]"). iModIntro.
    iMod "H" as "(? & ? & ?)".
    iMod "H1" as "_". iModIntro.
    iFrame.
    iApply ("IH" with "[$]"). iFrame. }
Qed.

Lemma wp_mono E b tid t Q Q' :
  wp E b tid t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wp E b tid t Q'.
Proof.
  iIntros "? H".
  iApply (wp_strong_mono with "[$]"). eauto.
  iIntros. by iApply "H".
Qed.

Lemma bupd_wp E b tid t Q :
  (|==> wp E b tid t Q) ⊢ wp E b tid t Q.
Proof.
  iIntros "Hwp".
  rewrite wp_unfold /wp_pre.
  destruct (to_val t); iMod "Hwp"; iFrame.
Qed.

Lemma fupd_wp E b tid t Q :
  (|={E}=> wp E b tid t Q) ⊢ wp E b tid t Q.
Proof.
  iIntros "Hwp".
  rewrite wp_unfold /wp_pre.
  iIntros. destruct (to_val t).
  all:iMod "Hwp"; iMod ("Hwp" with "[%//][$]"); by iFrame.
Qed.

Lemma wp_frame E b tid t Φ Ψ :
  Φ ∗ wp E b tid t Ψ ⊢ wp E b tid t (fun v => Φ ∗ Ψ v).
Proof.
  iIntros "[? Hwp]".
  iApply (wp_strong_mono with "Hwp"); eauto with iFrame.
Qed.

(* We can frame a proposition with a later, provided that the
   current term is not a value *)
Lemma wp_frame_step P E b i t Q :
  (to_val t = None) ->
  ▷ P -∗ wp E b i t (fun v => P -∗ Q v) -∗ wp E b i t Q.
Proof.
  iIntros (Ht) "Hp Hwp".
  rewrite !wp_unfold /wp_pre !Ht.
  iIntros. iMod ("Hwp" with "[%//] [$]") as "(?& Hwp)".
  iModIntro. iFrame.
  iIntros.
  iSpecialize ("Hwp" with "[%//][$]"). iModIntro.
  iMod "Hwp" as "(? & ? & ?)".
  iFrame. iModIntro.
  iApply (wp_mono with "[$]"). iIntros (?) "E". iApply "E". iFrame.
Qed.

(* A lemma to enable access to [state_interp] at the last step *)
Lemma wp_postpone E b tid t Q :
  wp E b tid t (fun v => wp E b tid v Q) -∗
  wp E b tid t Q.
Proof.
  iIntros "Hwp".
  iLöb as "IH" forall (t Q).
  rewrite !wp_unfold /wp_pre /=.
  iIntros. iMod ("Hwp" with "[%//] [$]") as "Hwp".
  destruct (to_val t) eqn:Eq; iIntros.
  { iModIntro. iMod "Hwp" as "(? & Hwp)".
    destruct t; try easy.
    injection Eq. intros. subst.
    rewrite wp_unfold /wp_pre. simpl.
    iMod ("Hwp" with "[%//] [$]") as ">(? & ?)".
    by iFrame. }
  { iDestruct "Hwp" as "(? & Hwp)".
    iFrame. iModIntro. iIntros.
    iSpecialize ("Hwp" with "[%//][$]"). iModIntro.
    iMod "Hwp" as "(? & ? & ?)".
    iFrame. by iApply "IH". }
Qed.

(* ------------------------------------------------------------------------ *)
(* Properties of WP on language constructs. *)

Lemma wp_bind E b tid K L t Q :
  locs K = dom L ->
  wp E b tid t (fun v => PBT {[tid]} L -∗ wp E b tid (fill_item K v) Q) -∗
     PBT {[tid]} L -∗ wp E b tid (fill_item K t) Q.
Proof.
  iIntros (HL) "H Hctx". iLöb as "IH" forall (t). rewrite wp_unfold /wp_pre.
  destruct (to_val t) as [v|] eqn:Et.
  { iClear "IH".
    setoid_rewrite wp_unfold at 2. rewrite /wp_pre.
    apply to_val_Some in Et. subst t.
    intros_wp.

    rewrite locs_fill_item union_comm_L in Htid.
    iMod (interp_shift with "[$]") as "[Hσ Hback]".
    1-3:eauto.

    rewrite to_val_fill_item.
    iMod ("H" with "[%] [$]") as ">(? & H)".
    { rewrite lookup_insert //. }
    iMod ("Hback" with "[%] [%] [$]") as "[Hctx Hσ]".
    { eauto using upd_refl. }
    { rewrite lookup_insert //. }

    rewrite wp_unfold /wp_pre.
    rewrite locs_fill_item to_val_fill_item insert_insert insert_id //.
    iApply ("H" with "[$] [%] [$]").
    split; last done.
    rewrite Htid. do 2 f_equal; eauto; set_solver. }
  { rewrite !wp_unfold /wp_pre. simpl.
    intros_wp.
    rewrite locs_fill_item union_comm_L in Htid.
    iDestruct (interp_valid with "[$]") as "%Hmt".

    iMod (interp_shift with "[$]") as "[Hσ Hback]".
    1-3:eauto.

    iMod ("H" with "[%][$]") as "[%Hred H]".
    { rewrite lookup_insert //. }
    iModIntro.
    rewrite to_val_fill_item.
    iSplitR.
    { eauto using reducible_context. }
    iIntros (t' σ' g' ? Hstep) "?".
    apply invert_step_context in Hstep; last done. destruct Hstep as (t1'&?&Hstep). subst.
    iSpecialize ("H" $! t1' σ' g' efs with "[%//][$]").
    iModIntro. iMod "H" as "(?&?&?)".
    iMod ("Hback" with  "[%] [%] [$]") as "[Hctx Hσ]".
    { rewrite insert_insert.
      eauto using atomic_step_grow_store, upd_step. }
    { rewrite lookup_merge lookup_insert. simpl.
      rewrite lookup_ft_notin; eauto. }
    iModIntro. iFrame.
    iDestruct ("IH" with "[$] [$]") as "?". iFrame.

    rewrite (insert_merge_l _ _ _ _ _ (lk, locs t1' ∪ locs K)).
    2:{ rewrite lookup_ft_notin //. eauto. }
    rewrite !insert_insert locs_fill_item union_comm_L.
    iFrame. }
Qed.

Lemma wp_val E b tid v Q :
  Q v ⊢ wp E b tid (tm_val v) Q.
Proof.
  iIntros.
  rewrite wp_unfold.
  iFrame. iIntros. iFrame.
  iApply fupd_mask_subseteq. set_solver.
Qed.

Lemma wp_let_val E b tid x (v:val) t Q :
  ▷(£1 -∗ wp E b tid (subst' x v t) Q) -∗
  wp E b tid (tm_let x v t) Q.
Proof.
  iIntros "Hwp". setoid_rewrite wp_unfold at 2.
  intros_wp. intros_mod.
  iSplitR; first eauto using reducible_let_val.
  iIntros (????) "%Hstep ?".
  apply invert_step_let_val in Hstep. destruct Hstep as (->&->&->&->).
  iModIntro. iSpecialize ("Hwp" with "[$]").
  rewrite Nat.add_0_r !right_id_L (insert_id e) //.
  iMod (interp_weak with "[$]"); last by iFrame.
  2:{ rewrite Htid //. }
  destruct x; first set_solver.
  apply locs_subst.
Qed.

Lemma wp_noclean E b tid t Q :
  wp E false tid t Q -∗ wp E b tid t Q.
Proof.
  destruct b; last (by iIntros).
  iIntros "Hwp".
  iLöb as "IH" forall (t tid E Q). rewrite !wp_unfold /wp_pre.
  intros_wp.
  iDestruct (interp_noclean with "[$]") as "(? & Hback)". eauto.
  destruct (to_val t).
  { iMod ("Hwp" with "[%//][$]") as "Hwp". iModIntro.
    iMod "Hwp" as "(?&?)". iFrame.
    iMod ("Hback" with "[%][%][$]"); eauto using upd_refl, diff_empty_refl. }
  { iDestruct (interp_valid with "[$]") as "%".
    iMod ("Hwp" with "[%//][$]") as "(? & Hwp)". iModIntro.
    iFrame. iIntros. iSpecialize ("Hwp" with "[%//][$]").
    iModIntro.  iMod "Hwp" as "(?&?&?)".
    iMod ("Hback" with "[%][%][$]").
    { assert (tid ∈ dom k) by eauto.
      split_and !; eauto using atomic_step_grow_store,upd_step'.
      eapply diff_empty_ft. rewrite dom_insert_L.
      set_solver. }
    { rewrite lookup_op lookup_insert lookup_ft_notin //. eauto. }
    iFrame.
    iModIntro. iDestruct ("IH" with "[$]") as "?". iFrame.
    destruct efs; last done. by iApply "IH". }
Qed.

Lemma wp_bind_noclean E b tid K t Q :
  wp E false tid t (fun v => wp E b tid (fill_item K v) Q) -∗
    wp E b tid (fill_item K t) Q.
Proof.
  iIntros "H". iLöb as "IH" forall (t). rewrite wp_unfold /wp_pre.
  destruct (to_val t) as [v|] eqn:Et.
  { iClear "IH".
    setoid_rewrite wp_unfold at 2. rewrite /wp_pre.
    apply to_val_Some in Et. subst t.
    intros_wp.

    rewrite locs_fill_item union_comm_L in Htid.
    iMod (interp_shift_noclean with "[$]") as "[Hσ Hback]".
    1-2:eauto.

    rewrite to_val_fill_item.
    iMod ("H" with "[%] [$]") as ">(? & H)".
    { rewrite lookup_insert //. }
    iMod ("Hback" with "[%] [%] [$]") as "Hσ".
    { split_and !; eauto using upd_refl.
      intros ?. rewrite dom_insert_L. set_solver. }
    { rewrite lookup_insert //. }

    rewrite wp_unfold /wp_pre.
    rewrite locs_fill_item to_val_fill_item insert_insert insert_id //.
    iApply ("H" with "[%] [$]").
    rewrite Htid. split; last done. do 2 f_equal; eauto; set_solver. }
  { rewrite !wp_unfold /wp_pre. simpl.
    intros_wp.
    rewrite locs_fill_item union_comm_L in Htid.
    iDestruct (interp_valid with "[$]") as "%Hmt".

    iMod (interp_shift_noclean with "[$]") as "[Hσ Hback]".
    1-2:eauto.

    iMod ("H" with "[%][$]") as "[%Hred H]".
    { rewrite lookup_insert //. }
    iModIntro.
    rewrite to_val_fill_item.
    iSplitR.
    { iPureIntro.
      eauto using reducible_context. }
    iIntros (t' σ' ? ? Hstep). iIntros.
    apply invert_step_context in Hstep; last done. destruct Hstep as (t1'&?&Hstep'). subst.
    iSpecialize ("H" $! t1' σ' _ efs with "[%//][$]").
    iModIntro. iMod "H" as "(? & ? & Hwp)".
    iMod ("Hback" with "[%] [%] [$]") as "Hσ".
    { rewrite insert_insert.
      split_and !; eauto using atomic_step_grow_store.
      { eapply upd_trans.
        1:apply upd_visible with (tid:=tid) (l1:=locs t) (l2:=locs t1'); rewrite lookup_insert; eauto.
        rewrite insert_insert.
        eauto using upd_fork,ndom_lt_insert. }
      { apply diff_empty_ft. rewrite !dom_insert_L //. } }
    { rewrite lookup_merge lookup_insert. simpl.
      rewrite lookup_ft_notin; eauto. }
    iModIntro. iDestruct ("IH" with "[$]") as "?". iFrame.

    rewrite (insert_merge_l _ _ _ _ _ (lk, locs t1' ∪ locs K)).
    2:{ rewrite lookup_ft_notin //. eauto. }
    rewrite !insert_insert locs_fill_item union_comm_L.
    iFrame. destruct efs; last done.
    destruct b; try easy.
    iApply wp_noclean. iFrame. }
Qed.

Lemma wp_let E b tid M x t1 t2 Q :
  locs t2 = dom M ->
  wp E b tid t1 (fun v => £1 -∗ PBT {[tid]} M -∗ wp E b tid (subst' x v t2) Q) -∗
     PBT {[tid]} M  -∗ wp E b tid (tm_let x t1 t2) Q.
Proof.
  intros. iIntros "H HL2".
  iApply (wp_bind _ _ _ (ctx_let x t2) with "[H]").
  { auto_locs. eauto. }
  2:{ iFrame. }
  iApply (wp_mono with "[$]").
  iIntros (?) "Hwp ?". simpl.
  iApply wp_let_val. iModIntro. iIntros. iApply ("Hwp" with "[$][$]").
Qed.

Lemma wp_let_noclean E b tid x t1 t2 Q :
  wp E false tid t1 (fun v => £1 -∗ wp E b tid (subst' x v t2) Q) -∗
  wp E b tid (tm_let x t1 t2) Q.
Proof.
  intros. iIntros "HL2".
  iApply (wp_bind_noclean _ _ _ (ctx_let x t2)).
  iApply (wp_mono with "[$]").
  iIntros (?) "Hwp". simpl.
  iApply wp_let_val. iModIntro. iIntros. by iApply "Hwp".
Qed.

Global Instance wp_ne E i b t n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp E b i t).
Proof.
  revert t. induction (lt_wf n) as [n _ IH]=> t Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  do 31 (f_contractive || f_equiv).
  apply IH. done. eapply dist_pointwise_lt. done.
  intros ?. apply dist_dist_later. done.
Qed.

Global Instance wp_contractive E i b t n :
  (to_val t) = None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp E b i t).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  repeat (f_contractive || f_equiv).
Qed.

Lemma wp_if E (b:bool) tid (c:bool) t1 t2 Q :
   ▷ (£1 -∗ if c then wp E b tid t1 Q else wp E b tid t2 Q)
   -∗ wp E b tid (tm_if c t1 t2) Q.
Proof.
  iIntros "Hif".
  iApply wp_unfold. rewrite /wp_pre.
  intros_wp. intros_mod.
  iSplitR; first eauto using reducible_if.
  iIntros (? ? ? ? Hstep) "?". iSpecialize ("Hif" with "[$]").
  apply invert_step_if in Hstep.
  destruct Hstep as (?&?&Hstep&?); subst. simpl.
  rewrite Nat.add_0_r !right_id_L (insert_id e) //.
  destruct c; iFrame; iModIntro.
  { iMod (interp_weak with "[$]"); last iFrame; last eauto.
    set_solver. }
  { iMod (interp_weak with "[$]"); last iFrame; last eauto.
    set_solver. }
Qed.

Lemma wp_atomic E1 E2 b i t Q :
  Atomic t ∨ is_Some (to_val t) ->
  (|={E1,E2}=> wp E2 b i t (fun v => |={E2,E1}=> Q v )) ⊢ wp E1 b i t Q.
Proof.
  iIntros (HA) "H". rewrite !wp_unfold /wp_pre.
  iIntros.
  iDestruct (interp_valid with "[$]") as "%Hvalid".
  destruct (to_val t) as [v|] eqn:He.
  { iMod ("H" with "[%//][$]") as ">> (? & >?)". iFrame.
    iApply fupd_mask_intro. set_solver. iIntros "E". iMod "E". by iFrame. }
  iMod ("H" with "[%//][$]") as "> (? & Hwp)". iFrame. iModIntro.
  iIntros (? ? ? ? Hstep) "?".
  iSpecialize ("Hwp" with "[%//][$]"). iModIntro. iMod "Hwp" as "(? & Hwp & Hf)". iFrame "Hf".
  destruct HA as [HA | HA]. 2:{ inversion HA. congruence. }
  apply Atomic_correct in Hstep; eauto. destruct Hstep as (?&->&->).
  rewrite wp_unfold /wp_pre. simpl.

  iMod ("Hwp" with "[%] [$]") as ">(? & > ?)".
  { destruct H. assert (i < mt).
    { apply Hvalid. eauto using elem_of_dom. }
    split.
    { rewrite lookup_op lookup_insert lookup_ft_notin //. }
    { rewrite lookup_union lookup_insert lookup_et_notin //. } }
  iModIntro. iFrame.
  iApply wp_val. iFrame.
Qed.
End wp.
