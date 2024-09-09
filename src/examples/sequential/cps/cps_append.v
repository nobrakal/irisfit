From irisfit.examples Require Import proofmode list stack ref cps_fact seqproofmode.

(* ------------------------------------------------------------------------ *)
(* cps_append with a recursive closure, and its two specifications. *)

Definition cps_append_aux ys self xs k : tm :=
    let: "b" := list_is_nil [[xs]] in
    if: "b"
    then call_clo k [[ys]]
    else
      let: "h" := list_head [[xs]] in
      let: "t" := list_tail [[xs]] in
      let: "nk" :=
        mk_clo BAnon [["r"]]%binder
          (let: "p" := list_cons [["h", "r"]] in call_clo k [["p"]]) in
      call_clo self [["t", "nk"]].

Definition cps_append : val :=
  λ: [["xs","ys"]],
    let: "id" := id_clo in
    let: "aux" := mk_clo "self" [["xs","k"]]%binder (cps_append_aux "ys" "self" "xs" "k") in
    call_clo "aux" [["xs", "id"]].

Section AppendDestruct.
Context `{interpGS0 Σ}.
Import ListsOf.

Definition clo_cont_spec M {A} π (R:A -> val -> iProp Σ) xs1 xs2 (Q:val -> iProp Σ) pre (ocont:loc) (args:list val) (t:tm) : iProp Σ :=
  ∀ p3,
    ⌜args = [p3:val]⌝ -∗
  PBT {[π]} M ∗
  pre ∗ ocont ⟸ {[π]} ∗ ocont ↤ ∅ ∗  p3 ⟸? {[π]} ∗ p3 ↤? ∅ ∗ ListOf R (xs1++xs2) p3 -∗
  wpc ⊤ π (Some ∅) t Q%I.

Definition Spec_clo_cont {A} π (R:A -> val -> iProp Σ) xs1 xs2 Q pre (env:list (val * Qz)) (l:loc) : iProp Σ :=
  ∃ M, ⌜dom M = locs env.*1⌝ ∗ PBT {[π]} M ∗ pre ∗ Spec 1 env (clo_cont_spec M π R xs1 xs2 Q pre) l.

Lemma prove_notin_locs_subst l x v t :
  l ∉ locs v ->
  l ∉ locs t ->
  l ∉ locs (subst x v t).
Proof.
  intros.
  intros E.
  apply locs_subst in E. set_solver.
Qed.


Definition cps_append_aux_spec_destructive {A} π (R:A -> val -> iProp Σ) L2 l2 (self:loc) (args:list val) t : iProp Σ :=
  ∀ L1 l1 Q (cont:loc) pre env,
  ⌜args = [l1:val;cont:val]⌝ -∗
 (♢(3*(length L1))%nat ∗ self ⟸ {[π]} ∗ self ↤ ∅ ∗ ListOf R L1 l1 ∗ l1 ⟸? {[π]} ∗ l1 ↤? ∅ ∗ ListOf R L2 l2 ∗ l2 ⟸? {[π]} ∗ cont ⟸ {[π]} ∗ cont ↤ ∅ ∗ Spec_clo_cont π R L1 L2 Q pre env cont) -∗
  wpc ⊤ π (Some ∅) t (fun v => Q v ∗ ♢ (3*(length L1) + 2))%I.

Definition Spec_cps_append_aux {A} π (R:A -> val -> iProp Σ) L2 (l2:loc) l : iProp Σ :=
  Spec 2 [(l2:val,1%Qz)] (cps_append_aux_spec_destructive π R L2 l2) l.

Lemma pbt_cov {l p} S S' :
  S ⊆ S' ->
  l ⟸{p} S ⊢ l ⟸{p} S'.
Proof.
  iIntros. rewrite (union_difference_L S S') //.
  by iApply pbt_approx.
Qed.

Lemma prove_cps_append_aux_spec {A} π self (R:A -> val -> iProp Σ) L1 (l1:val) L2 (l2:val) Q (cont:loc) pre env:
  CODE (subst "k" cont (cps_append_aux l2 self l1 "k"))
  TID π
  PRE ( ♢(3*(length L1))%nat ∗
        Spec 2 [(l2, 1%Qz)] (cps_append_aux_spec_destructive π R L2 l2) self ∗ self ⟸ {[π]} ∗ self ↤ ∅ ∗
        ListOf R L1 l1 ∗ l1 ⟸? {[π]} ∗ l1 ↤? ∅ ∗ ListOf R L2 l2 ∗ l2 ⟸? {[π]} ∗
        cont ⟸ {[π]} ∗ cont ↤ ∅ ∗ Spec_clo_cont π R L1 L2 Q pre env cont)
  POST (fun v => Q v ∗ ♢ (3*(length L1) + 2) ).
Proof.
  iStartProof.
  unfold cps_append_aux. simpl.
  rewrite subst_call_clo //. simpl.
  iIntros "(Hdiams & Hspec & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & (%M&%&HX&Hpre&Hclo))".
  destruct L1 as [|(x,(p,q)) L1].
  { iApply (@wpc_let_nv [l1; l2; val_loc cont; val_loc self] [1;1;1;1]%Qp with "[H1 H4 H7 H8]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%X&HL) (H4&H7&H8&H1&_)". simpl.
    replace b with true by (destruct b; naive_solver). clear X.
    wpc_if.
    rewrite subst_call_clo. simpl.

    iDestruct (confront_pbt_vpbt self l2 with "[$]") as "%". by vm_compute.
    iDestruct (confront_pbt_pbt self cont with "[$]") as "%". by vm_compute.
    assert (self ∉ locs l2) by (destruct l2; set_solver).
    pclean self.

    (* LATER *)
    rewrite (ListOf_eq _ _ l1). iDestruct "HL" as "%".

    iApply wpc_fconseq. iApply spec_free. iFrame. simpl.
    iIntros "(?&(?&_)&#?)".

    iApply (wpc_call_spec_tac with "[$][$]").
    1,2:compute_done. set_solver.

    iIntros "!>". iIntros (?) "_ ? Hspec". simpl. unfold clo_cont_spec.
    iSpecialize ("Hspec" with "[% //] [$]").
    iApply (wpc_mono with "[$]"). iIntros. iFrame. conclude_diamonds. }
  { iApply (@wpc_let_nv [l1; l2; val_loc cont; val_loc self] [1;1;1;1]%Qp with "[H1 H4 H7 H8]").
    { auto_locs. set_solver. }
    { simpl. rewrite right_id. by iFrame. }

    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%X&HL) (H4&H7&H8&H1&_)". simpl.
    replace b with false by (destruct b; naive_solver). clear X.
    wpc_if.

    iApply (@wpc_let_nv [l1; val_loc cont; val_loc self] [1;1;1]%Qp with "[H1 H4 H8]").
    { auto_locs. set_solver. }
    { simpl. iFrame. }

    wpc_apply (list_head_spec _ _ R l1). set_solver.
    iIntros (h) "(?&H10&?) (H1&H4&H8&_)". simpl.

    rewrite !subst_call_clo. simpl.
    iApply (@wpc_let_nv [val_loc cont; val_loc self; h] [1;1;p]%Qp with "[H4 H8 H10]").
    { auto_locs. set_solver. }
    { simpl. iFrame. }

    wpc_apply (list_tail_spec _ _ R). set_solver.
    iIntros (t) "[% (->&?&H11&?&?&Hh)]". rename l0 into l1.
    iIntros "(H4&H8&H10&_)". simpl.
    rewrite (subst_not_in "t"); last by vm_compute.
    rewrite (subst_not_in "b"); last by vm_compute.
    rewrite !subst_call_clo. simpl.

    iDestruct (confront_pbt_pbt l1 self with "[$]") as "%". by vm_compute.
    iDestruct (confront_pbt_pbt l1 cont with "[$]") as "%". by vm_compute.
    iDestruct (confront_pbt_vpbt l1 h with "[$]") as "%". apply Qp.not_add_le_l.
    iDestruct (confront_pbt_vpbt l1 t with "[$]") as "%". apply Qp.not_add_le_l.
    assert ({[l1]} ∩ (locs h ∪ locs t) = ∅) by (destruct h,t; set_solver).
    pclean l1.

    iApply wpc_tconseq. iApply (interp_free' l1). iFrame.
    iIntros "(?&_&#l1)".

    iDestruct (vmapsfrom_correct h with "[$]") as "%Hh".

    iApply wpc_tconseq. iApply (vmapsfrom_cleanup t l1). iFrame "#∗". iIntros "?".
    iApply wpc_tconseq. iApply (vmapsfrom_cleanup h l1). iFrame "#∗". iIntros "Hh".
    rewrite disj_union_singleton_opposite.

    iApply (@wpc_let_nv [val_loc self; t] [1;1]%Qp with "[H8 H11]").
    { auto_locs. set_solver. }
    { simpl. iFrame. }

    rewrite subst_subst_commut //.

    iMod (VPBT_PBT [cont:val;h:val] [_;_] with "[H4 H10]" ) as "[%M' (%&?&Hback)]".
    { simpl. by iFrame. }

    wpc_apply (wpc_mk_spec _ (clo_cont_spec M' π R L1 L2 (fun v => Q v ∗ ♢3)%I (♢2 ∗ R x h ∗ (PBT {[π]} M' -∗ [∗ list] v;q0 ∈ [(#cont)%V; h];[1%Qp; p], v ⟸?{q0} {[π]}) ∗  Spec_clo_cont π R ((x, (p,q)) :: L1) L2 Q pre env cont)%I) [("k",cont:val);("h",h:val)] [1%Qz;if is_loc h then q else 1%Qz]).
    { set_solver. }
    { compute_done. }
    { apply Forall_cons. split; first compute_done. apply Forall_singleton.
      destruct (is_loc h); try easy. destruct Hh. done.
      smultiset_solver. }
    { set_solver. }
    { by vm_compute. }
    { iModIntro. iIntros (ocont ?) "Hspec". simpl. iIntros (l) "->".
      iIntros "(?&(?&?&Hback&(%&%&?&?&?))&?&?&?&?&?)". simpl.
      iDestruct ("Hback" with "[$]") as "(H4&?&_)".
      iDestruct (confront_pbt_vpbt ocont l with "[$]") as "%". by vm_compute.
      iDestruct (confront_pbt_pbt ocont cont with "[$]") as "%". by vm_compute.
      iDestruct (confront_pbt_vpbt ocont h with "[$]") as "%".  apply Qp.not_add_le_l.
      assert (ocont ∉ (locs h ∪ locs l)) by (destruct h,l; set_solver).
      pclean ocont.

      (* Autodestruct ocont *)
      iApply wpc_fconseq. iApply (spec_free _ _ _ ocont). iFrame. simpl.
      iIntros "(?&(?&Hh&_)&_)".

      iAssert (h ↤?{q} ∅)%I with "[Hh]" as "?".
      { destruct h; eauto. }

      rewrite !subst_call_clo. simpl.

      iApply (@wpc_let_nv [val_loc cont] [1]%Qp with "[H4]"). set_solver. simpl. iFrame.

      wpc_apply list_cons_spec. set_solver.
      { intros. destruct (is_loc h); eauto. destruct Hh; eauto. smultiset_solver. }
      iIntros (h') "(?&?&?) (?&_)". simpl.
      rewrite subst_call_clo. simpl.

      iApply (wpc_call_spec_tac with "[$][$]"). done. done. set_solver.
      iModIntro. iIntros (?) "_ ? Hspec". simpl.
      iSpecialize ("Hspec" with "[%//] [$]").
      iApply (wpc_mono with "[$]"). iIntros.
      iFrame. }

    iAssert (♢3 ∗ ♢(3*(length L1)))%I with "[Hdiams]" as "(?&?)".
    { iApply diamonds_split. conclude_diamonds. }
    iFrame.
    iSplitL "Hh". simpl.
    { destruct h; eauto. }
    iIntros (?) "(? & ? & ?&_) (? & ?&_)".
    rewrite !subst_call_clo. simpl.
    iMod (VPBT_PBT [l2] [_] with "[H7]" ) as "[%M'' (%&?&Hback')]".
    { by iFrame. }

    iApply (wpc_call_spec_tac with "Hspec [$]"). done. done. set_solver.

    iModIntro. iIntros (?) "_ ? Hspec".

    iSpecialize ("Hspec" $! L1 t (λ v1, Q v1 ∗ ♢ 3)%I with "[% //] [-]").
    { rew_qz. iDestruct ("Hback'" with "[$]") as "(?&_)". iFrame.
      unfold Spec_clo_cont. iExists M'. iFrame. iSplitR. done. iExists _. by iFrame. }
    iApply (wpc_mono with "[$]").
    iIntros (?) "((? & ?) & ?)".
    iFrame. conclude_diamonds. }
Qed.

Lemma cps_append_spec_destructive {A} π (R:A -> val -> iProp Σ) L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  TID π
  PRE ( ♢ (3*(length L1) + 3) ∗ ListOf R L1 l1 ∗ l1 ⟸? {[π]} ∗ l1 ↤? ∅ ∗ ListOf R L2 l2 ∗ l2 ⟸? {[π]} ∗ l2 ↤? ∅)
  POST (fun l => ListOf R (L1++L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ ♢ (3*(length L1) + 3)).
Proof.
  iIntros "(HD &H1&H2&H3&H4&H5&H6)".
  wpc_call. simpl.

  rewrite (subst_not_in "xs"). 2:by vm_compute.
  rewrite (subst_not_in "ys"). 2:by vm_compute.

  iApply (@wpc_let_nv [l1;l2] [1;1]%Qp with "[H2 H5]").
  { auto_locs. rewrite mk_clo_eq. auto_locs. set_solver. }
  { simpl. by iFrame. }

  mine 1.
  wpc_apply (clo_id_spec_autodestroy). set_solver.
  iIntros (id) "(Hid&?&H7) (H2&H5&_)". simpl.
  rewrite !subst_call_clo. simpl. rewrite (subst_not_in "id"). 2: by vm_compute.

  iApply (@wpc_let_nv [val_loc id;l1] [1;1]%Qp with "[H7 H2]").
  { set_solver. }
  { by iFrame. }

  rewrite (subst_not_in "xs"). 2:by vm_compute.
  wpc_apply (wpc_mk_spec _ (cps_append_aux_spec_destructive π R L2 l2) [("ys",l2:val)] [1%Qz]).
  { set_solver. }
  { compute_done. }
  { by constructor. }
  { set_solver. }
  { compute_done. }
  { iModIntro.
    iIntros (??) "?". clear L1 l1. iIntros (L1 l1 ? ? ? ? ->).
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?&?&?)".

    simpl.
    iApply (@prove_cps_append_aux_spec _ _ l R L1 l1 L2 l2 Q cont pre env with "[$]"). }

  mine 2. iFrame.

  iIntros (?) "(?&?&?&_) (?&?&_)".
  rewrite subst_call_clo. simpl.

  iMod (VPBT_PBT [l2] [_] with "[H5]" ) as "[%M (%&?&Hback)]".
  { by iFrame. }

  iApply (wpc_call_spec_tac with "[$][$]"). done. done. set_solver.
  iModIntro. iIntros (?) "_ ? Hspec".
  iDestruct ("Hback" with "[$]") as "(?&_)". clear dependent M.

  replace ((length L1 + (length L1 + (length L1 + 0)) + 3 - 1 - 2)) with (3*length L1) by lia.
  unfold cps_append_aux_spec_destructive.

  iDestruct PBT_empty as "He".
  iAssert (Spec_clo_cont π R L1 L2 (λ (l:val), ListOf R (L1 ++ L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ ♢ 1)%I True [] id) with "[Hid]" as "?".
  { iExists ∅. iSplitR; eauto. iFrame "He". rewrite left_id.
    iApply (spec_weak with "[] [$]"); last first.
    iModIntro. iIntros (? ?) "Hid". iIntros (?) "->".
    iIntros "(_ & _ & ? & ? & ? & ? & ?)".
    iSpecialize ("Hid" with "[% //] [$]").
    iApply (wpc_mono with "[$]"). iIntros (?) "(->&?&?)". iFrame. }

  iSpecialize ("Hspec" $! L1 l1 (fun l => ListOf R (L1++L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ ♢1)%I id True%I nil with "[% //] [$]"). iFrame.
  iApply (wpc_mono with "[$]"). simpl.

  iIntros (?) "((? & ? & ? & ?) & ?)".
  iFrame.
  conclude_diamonds.
Qed.

(* A version with List. *)
Import Lists.

Lemma cps_append_spec_destructive_ π L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  TID π
  PRE ( ♢ (3*(length L1) + 3) ∗ List L1 l1 ∗ l1 ⟸? {[π]} ∗ l1 ↤? ∅ ∗ List L2 l2 ∗ l2 ⟸? {[π]} ∗ l2 ↤? ∅)
  POST (fun l => List (L1++L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ ♢ (3*(length L1) + 3)).
Proof. apply cps_append_spec_destructive. Qed.
End AppendDestruct.

Section Append.
Context `{interpGS0 Σ}.
Import Lists.

Definition cps_append_aux_spec' π L2 (l2:val) (self:loc) (args:list val) t  : iProp Σ :=
  ∀ L1 (l1:val) Q (cont:loc) pre env,
  ⌜args = [l1;cont:val]⌝ -∗
 (♢(3*(length L1) + 2*(length L1))%nat ∗ self ⟸ {[π]} ∗ self ↤ ∅ ∗ List L1 l1 ∗ List L2 l2 ∗ l2 ⟸? {[π]} ∗ cont ⟸ {[π]} ∗ cont ↤ ∅ ∗ Spec_clo_cont π (fun x y => ⌜x=y⌝)%I (halves L1) L2 (fun v => v ⟸? {[π]} ∗ Q v) pre env cont) -∗
  wpc ⊤ π (Some (locs l1)) t (fun v => v ⟸? {[π]} ∗ Q v ∗ List (halves L1) l1 ∗ ♢ (3*(length L1) + 2))%I.

Definition Spec_cps_append_aux' π L2 (l2:val) l : iProp Σ :=
  Spec 2 [(l2:val,1%Qz)] (cps_append_aux_spec' π L2 l2) l.

Lemma prove_cps_append_aux_spec' π self L1 l1 L2 (l2:val) Q (cont:loc) pre env :
  CODE (subst "k" cont (cps_append_aux l2 self l1 "k"))
  TID π
  SOUV (locs l1)
  PRE ( ♢ (3*(length L1) + 2*(length L1))%nat ∗ Spec 2 [(l2, 1%Qz)] (cps_append_aux_spec' π L2 l2) self ∗self ⟸ {[π]}  ∗ self ↤ ∅ ∗ List L1 l1 ∗ List L2 l2 ∗ l2 ⟸? {[π]} ∗
         cont ⟸ {[π]}  ∗ cont ↤ ∅ ∗ Spec_clo_cont π (fun x y => ⌜x=y⌝)%I (halves L1) L2 (fun v => v ⟸? {[π]} ∗ Q v) pre env cont)
  POST (fun v => v ⟸? {[π]} ∗ Q v ∗ List (halves L1) l1 ∗ ♢ (3*(length L1) + 2)).
Proof.
  iIntros "(Hdiams & Hspec & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hclo)". simpl.
  destruct L1 as [|(x,(p,q)) L1].
  { iApply (@wpc_let_nv [l2; val_loc cont; val_loc self] [1;1;1]%Qp with "[H5 H6 H1]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%X&HL) (H5&H6&H1&_)". simpl.
    replace b with true by (destruct b; naive_solver). clear X.
    wpc_if.
    rewrite subst_call_clo. simpl.

    iDestruct (confront_pbt_vpbt self l2 with "[$]") as "%". by vm_compute.
    iDestruct (confront_pbt_pbt self cont with "[$]") as "%". by vm_compute.
    assert (self ∉ locs l2) by (destruct l2; set_solver).
    pclean self.

    (* LATER *)
    rewrite /List (ListsOf.ListOf_eq _ _ l1). iDestruct "HL" as "%".

    iApply wpc_fconseq. iApply spec_free. iFrame. simpl.
    iIntros "(?&(?&_)&#?)".

    iDestruct "Hclo" as "(%&%&?&?&?)". rewrite subst_call_clo. simpl.
    iApply (wpc_call_spec_tac with "[$][$]").
    1,2:compute_done. set_solver.

    iIntros "!>". iIntros (?) "_ ? Hspec". simpl. unfold clo_cont_spec.
    iSpecialize ("Hspec" with "[% //] [$]").
    iApply (wpc_weak ∅). set_solver.
    iApply (wpc_mono with "[$]"). iIntros (?) "(?&?)". iFrame.
    iSplitR. done. conclude_diamonds. }
  { iApply (@wpc_let_nv [l2; val_loc cont; val_loc self] [1;1;1]%Qp with "[H5 H6 H1]").
    { auto_locs. set_solver. }
    { by iFrame. }

    wpc_apply list_is_nil_spec. set_solver.
    iIntros (b) "(%X&HL) (H5&H6&H1&_)". simpl. rewrite !subst_call_clo. simpl.
    replace b with false by (destruct b; naive_solver).
    wpc_if.

    iApply (@wpc_let_nv [val_loc cont; val_loc self] [1;1]%Qp with "[H1 H6]").
    { auto_locs. set_solver. }
    { simpl. iFrame. }

    wpc_apply (list_head_spec _ l1). set_solver.
    iIntros (h) "(->&H10&?) (H1&H6&_)". simpl.

    rewrite !subst_call_clo. simpl.
    iApply (@wpc_let_nv [val_loc cont; val_loc self; h] [1;1;p]%Qp with "[H1 H6 H10]").
    { auto_locs. set_solver. }
    { simpl. iFrame. }

    wpc_apply (list_tail_spec). set_solver.
    iIntros (t) "[% (->&E1&H11&E3&E2&Hh)]". rename l0 into l1.
    iIntros "(H1&H6&H10&_)". simpl.
    rewrite (subst_not_in "t"); last by vm_compute.
    rewrite (subst_not_in "b"); last by vm_compute.
    rewrite !subst_call_clo. simpl.

    iDestruct (vmapsfrom_correct h with "[$]") as "%Hh".
    assert (is_loc h -> (q/2)%Qz ≠ 0).
    { intros. destruct Hh; eauto.
      intros E. apply Qz_div_eq_zero in E.
      assert (AllNeg {[+ l1 +]}); smultiset_solver. }

    iAssert (h ↤?{q/2} {[+l1+]} ∗ h ↤?{q/2} ∅)%I with "[Hh]" as "(Hh' & Hh)".
    { iApply vmapsfrom_split.
      1,2:smultiset_solver.
      rewrite Qz_div_2 right_id. iFrame. }

    iApply (@wpc_let_nv [val_loc self; t] [1;1]%Qp with "[H6 H11]").
    { auto_locs. set_solver. }
    { simpl. iFrame. }

    iAssert (h ⟸?{p/2} {[π]} ∗ h ⟸?{p/2} ∅)%I with "[H10]" as "(H10&Hh'')".
    { iApply vpbt_split. rewrite Qp.div_2 right_id_L //. }

    iMod (VPBT_PBT [cont:val;h:val] [_;_] with "[H1 H10]" ) as "[%M' (%&Hm'&Hback)]".
    { simpl. by iFrame. }

    rewrite subst_subst_commut //.
    wpc_apply (wpc_mk_spec _ (clo_cont_spec M' π (fun x y => ⌜x=y⌝)%I (halves L1) L2 (fun v => v ⟸? {[π]} ∗ Q v ∗ ♢3)%I (♢ 2 ∗ Spec_clo_cont π (fun x y => ⌜x=y⌝)%I ((h, ((p/2)%Qp,(q/2)%Qz)) :: halves L1) L2 (fun v => v ⟸? {[π]} ∗ Q v) pre env cont ∗ (PBT {[π]} M' -∗ [∗ list] v;q0 ∈ [(#cont)%V; h];[1%Qp; (p/2)%Qp], v ⟸?{q0} {[π]}) )%I) [("k",cont:val);("h",h:val)] [1%Qz;if is_loc h then (q/2)%Qz else 1]).
    { set_solver. }
    { compute_done. }
    { apply Forall_cons. split; first done. apply Forall_singleton.
      destruct (is_loc h); eauto. }
    { set_solver. }
    { compute_done. }
    { iModIntro. iIntros (ocont ?) "Hspec". simpl.
      iIntros (l) "-> (?&(?&Hclo&Hback)&?&?&?&?&?)".
      simpl. rewrite !subst_call_clo. simpl.

      iDestruct ("Hback" with "[$]") as "(H4&X&_)".

      iDestruct (confront_pbt_vpbt ocont l with "[$]") as "%". by vm_compute.
      iDestruct (confront_pbt_pbt ocont cont with "[$]") as "%". by vm_compute.
      iDestruct (confront_pbt_vpbt ocont h with "[$]") as "%".  apply Qp.not_add_le_l.
      (* TODO: everywhere in this file, use a better confront_pbt_vpbt *)
      assert (ocont ∉ (locs h ∪ locs l)) by (destruct h,l; set_solver).
      pclean ocont.

      iApply wpc_fconseq. iApply (spec_free _ _ _ ocont). iFrame. simpl.
      iIntros "(? & (?&Hh&_) & ?)". simpl.

      iAssert (h ↤?{q/2} ∅)%I with "[Hh]" as "?".
      { destruct h; eauto. }

      iApply (@wpc_let_nv [val_loc cont] [1]%Qp with "[H4]"). set_solver. simpl. iFrame.
      wpc_apply list_cons_spec. set_solver. shelve.
      { intros. destruct (is_loc h); eauto. }

      iIntros (h') "(?&?&?) (?&_)". simpl.
      rewrite subst_call_clo. simpl.

      iDestruct "Hclo" as "[% (%&?&?&?)]".
      iApply (wpc_call_spec_tac with "[$][$]").
      1,2:done. set_solver.
      iModIntro. iIntros (?) "_ ? X". unfold List.
      iSpecialize ("X" with "[%//][$]").
      iApply (wpc_mono with "[$]"). iSteps. }

    rew_qz. iFrame. mine 3 as "Hd".
    iSplitL "Hh Hd".
    { destruct h; eauto. iFrame. }
    iIntros (?) "(Hgo & ? & ?&_) (? & ?&_)".
    rewrite !subst_call_clo. simpl.

    iApply wpc_postpone.
    iApply (wpc_context_vsingleton t with "[$]").
    iApply (@wpc_weak _ _ _ (locs t)). set_solver.

    iMod (VPBT_PBT [l2:val] [_] with "[H5]" ) as "[%M'' (%&HM''&Hback')]".
    { simpl. by iFrame. }

    iApply (wpc_call_spec_tac with "Hspec [$]"). done. done. set_solver.
    iModIntro. iIntros (?) "_ ? Hspec".
    iDestruct ("Hback'" with "[$]") as "(?&_)". clear dependent M''.
    iSpecialize ("Hspec" $! L1 _ (fun v => Q v ∗ ♢ 3)%I with "[%//] [-Hh' Hh'' E2 E3]").
    { simpl. mine 2 as "Hd2".
      iAssert (Spec_clo_cont π (λ x y : val, ⌜x = y⌝)%I (halves L1) L2 (λ v0, v0 ⟸? {[π]} ∗ Q v0 ∗ ♢ 3)%I _ _ v) with "[Hd2 Hgo Hback Hm' Hclo]" as "?".
      { iExists _. iFrame. iSplitR; first done. iFrame. }
      iFrame. conclude_diamonds. }
    iApply (wpc_mono with "[$]"). iIntros (?) "(?&(?&?)&?&?) ?". iFrame.
    iDestruct (diamonds_join with "[$]") as "Hd".
    iApply wpc_conseq.
    iApply (vpbt_transfer v0 t). 3:iFrame. set_solver. set_solver.
    iIntros "(?&?)". rewrite difference_diag_L.
    wpc_val. iFrame.
    iSplitR "Hd"; last conclude_diamonds. iExists _,_,_. by iFrame. }
  Unshelve. exact unit. done.
Qed.

Lemma cps_append_spec_preserving π L1 l1 L2 l2 :
  CODE (cps_append [[l1,l2]])
  TID π
  SOUV (locs l1)
  PRE ( ♢ (3*(length L1) + 2*(length L1) + 3)%nat ∗ List L1 l1 ∗ List L2 l2 ∗ l2 ⟸? {[π]} ∗ l2 ↤? ∅)
  POST (fun l => List (halves L1) l1 ∗ List (halves L1++L2) l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ ♢ (3*(length L1) + 3)).
Proof.
  iIntros "(HD & H2 & H3 & H4 & H5)".
  wpc_call.

  rewrite (subst_not_in "xs"). 2:by vm_compute.
  rewrite (subst_not_in "ys"). 2:by vm_compute.

  iApply (@wpc_let_nv [l2] [1]%Qp with "[H4]").
  { auto_locs. rewrite mk_clo_eq. auto_locs. set_solver. }
  { simpl. by iFrame. }

  mine 1.
  wpc_apply (clo_id_spec_autodestroy). set_solver.
  iIntros (id) "(Hid&?&H7) (H4&_)". simpl.
  rewrite !subst_call_clo. simpl. rewrite (subst_not_in "id"). 2: by vm_compute.
  iIntros.

  iApply (@wpc_let_nv [val_loc id] [1]%Qp with "[H7]").
  { auto_locs. set_solver. }
  { simpl. by iFrame. }

  rewrite (subst_not_in "xs"). 2:by vm_compute.
  wpc_apply (wpc_mk_spec _ (cps_append_aux_spec' π L2 l2) [("ys",l2:val)] [1%Qz]).
  { set_solver. }
  { compute_done. }
  { by apply Forall_singleton. }
  { set_solver. }
  { compute_done. }
  { iModIntro.
    iIntros (? ?) "?". clear L1 l1. iIntros (L1 l1 ? ? ? ? ->).
    simpl.
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iDestruct (@prove_cps_append_aux_spec' π l L1 l1 L2 l2 Q cont pre env with "[$]") as "?". iFrame. }

  mine 2. iFrame.

  iIntros (?) "(?&?&?&_) (?&_)".
  rewrite !subst_call_clo. simpl.

  iMod (VPBT_PBT [l2] [_] with "[H4]" ) as "[%M (%&?&Hback)]".
  { by iFrame. }

  iApply (wpc_call_spec_tac with "[$] [$]"). done. done. set_solver.

  iModIntro. iIntros (?) "_ ? Hspec".
  unfold cps_append_aux_spec'.

  iAssert (Spec_clo_cont π (λ x y : val, ⌜x = y⌝) (halves L1) L2
   (λ l : val, l ⟸? {[π]} ∗ List (halves L1 ++ L2) l ∗ l ↤? ∅ ∗ ♢ 1) True [] id)%I with "[Hid]" as "?".
  { iExists _. iDestruct PBT_empty as "?". iFrame "#". rewrite left_id.
    iSplitR; first easy.
    iApply (spec_weak with "[] [$]"); last first.

    iModIntro. iIntros (? ?) "Hid". iIntros (?) "->".
    iIntros "(_ & _ & ? & ? & ? & ? & ?)".
    iSpecialize ("Hid" with "[% //] [$]").
    iApply (wpc_mono with "[$]").
    iSteps. }

  iDestruct ("Hback" with "[$]") as "(?&_)".
  iSpecialize ("Hspec" $! L1 l1 (fun l => List (halves L1 ++ L2) l ∗ l ↤? ∅ ∗ ♢ 1)%I id True%I nil with "[% //] [-]"). iFrame. conclude_diamonds.
  iApply (wpc_mono with "[$]"). iSteps. conclude_diamonds.
Qed.
End Append.
