From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth gset.
From stdpp Require Import gmap gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit.lib Require Import qz qz_cmra.
From irisfit Require Import more_maps_and_sets.
From irisfit Require Import disc interp pbt wp_clean.

Section Wp_fork.
Context `{!interpGS sz Σ}.

Lemma pbt_fork S mt lt L u ρ :
   dom L = lt ->
   auth_ctx ρ u -∗
   PBT S L ==∗
   auth_ctx (add_thread mt lt ρ) u  ∗ PBT (S ∪ {[mt]}) L.
Proof.
  unfold add_thread.
  pose (P:= fun sf lt => forall L, dom L = lt
  → auth_ctx ρ u -∗
    PBT S L ==∗
    auth_ctx sf u ∗
    PBT (S ∪ {[mt]}) L).
  apply (set_fold_ind_L P); unfold P; clear P L lt.
  { intros L HL.
    assert (L=∅) by (apply dom_empty_inv; set_solver).
    subst. iIntros "? ?". iFrame. iApply PBT_empty. }
  { intros x lt sf Hx IH L HL.
    iIntros "? ?".
    destruct (L!!x) as [Lx|]eqn:E.
    2:{ apply not_elem_of_dom in E. exfalso. set_solver. }
    rewrite -(insert_id L x Lx) //.
    rewrite -insert_delete_insert.
    iDestruct (PBT_insert1 with "[$]") as "(? & ?)".
    { set_solver. }
    iMod (IH (delete x L) with "[$] [$]") as "(? & ?)".
    { set_solver. }
    iMod (PBT_update_fork with "[$] [$]") as "(? & ?)".
    iFrame.
    iApply PBT_insert2.
    { set_solver. }
    by iFrame. }
Qed.

Lemma debt_fork e η mt :
  debt e η ->
  debt (<[mt:=Out]> e) (<[mt:=None]> η).
Proof.
  intros []. constructor.
  { rewrite !dom_insert_L. set_solver. }
  { intros ???. rewrite !lookup_insert_case. case_decide; naive_solver. }
Qed.

Lemma linked_fork η k θ τ mt lt π lk :
  k !! π = Some (lk,lt) ->
  (forall l, l ∈ lt -> ¬ freed τ l) ->
  mt ∉ dom k ->
  linked (image_less η k) θ τ ->
  linked (lt ∪ image_less (<[mt:=None]> η) k) θ τ.
Proof.
  intros E1 E2 Hmt [X1 X2 X3 X4]. constructor; eauto.
  intros l'. rewrite elem_of_union. intros [|Hl]; first eauto.
  { eapply X4; apply elem_of_image_less. apply elem_of_image_less in Hl. destruct Hl as (?&?&?&?).
    do 2 eexists. split; try done.
    destruct_decide (decide (x=mt)).
    { subst. exfalso. eauto. }
    rewrite lookup_total_insert_ne // in H0. }
Qed.

Lemma interp_fork mt b (k:ctx) π L lk lt σ e:
  dom L = lt ->
  k !! π = Some (lk, lt) ->
  (PBT {[π]} L -∗ interp mt b k e σ  ==∗
   PBT {[π;mt]} L ∗ interp (mt+1) b (<[mt:=(∅,lt)]> k) (<[mt := Out]> e) σ ∗ outside mt ∗ ⌜e!!mt=None⌝).
Proof.
  iIntros (HL Htid) "Hpbt Hi".
  destruct_interp "Hi".

  iAssert (⌜forall l, l ∈ lt -> l ∈ dom ρ⌝)%I as "%".
  { iIntros (l Hl).
    rewrite -HL in Hl. apply elem_of_dom in Hl. destruct Hl.
    iDestruct (PBT_borrow_pbt with "Hpbt") as "(X&_)". done.
    iDestruct (pbt_exploit with "[$]") as "%". iPureIntro.
    apply elem_of_dom. naive_solver. }

  iMod (@pbt_fork _ mt lt with "[$] [$]") as "(? & ?)".
  { eauto. }

  assert (mt ∉ dom k).
  { destruct Hρ as [ ? Hmt].
    (* facto *)
    intros E. apply Hmt in E. lia. }
  assert (mt ∉ dom η).
  { destruct Hdebt. destruct Hρ. set_solver. }
  assert (mt ∉ dom e).
  { destruct Hdebt. set_solver. }

  iMod (ghost_map.ghost_map_insert mt with "Hinside") as "(?&Hc)".
  by eapply not_elem_of_dom.

  iDestruct PBT_empty as "Hnctx". rewrite -not_elem_of_dom.
  iFrame "∗%". iExists _,_,_,(<[mt:=None]> η).
  iFrame.

  assert (image (<[mt:=(∅, lt)]> k) = image k) as ->.
  { rewrite image_insert1 //. 2:apply not_elem_of_dom; eauto.
    erewrite <- (image_upd k ). 2-3:eauto.
    repeat rewrite image_insert2; eauto. set_solver. }

  iMod (if_update with "[-Hctx] [-]") as "?"; only 2,3:iFrame.
  { iIntros. iApply big_opM_insert. by eapply not_elem_of_dom.
    simpl. by iFrame. }

  iPureIntro.
  split_and !; eauto using roots_inv_fork,debt_fork.
  { rewrite image_less_insert1. 2:by eapply not_elem_of_dom.
    unfold xroot_less. rewrite lookup_total_insert difference_empty_L. simpl.
    rewrite dom_empty_L left_id_L.
    eapply linked_fork; try done. intros l Hl Hf. apply Htauro in Hf. naive_solver. }
  { intros l. rewrite dom_add_thread; eauto. }
Qed.

Lemma wp_fork_base E (b:bool) L t π :
  dom L = locs t ->
  outside π -∗
  PBT {[π]} L -∗
  ▷ (£1 -∗ ∀ π', (if b then PBT {[π']} L else PBT {[π;π']} L) -∗ outside π' -∗ wp ⊤ b π' t (fun _ => outside π')) -∗
  wp E b π (tm_fork t) (fun v => ⌜v=val_unit⌝ ∗ outside π).
Proof.
  iIntros (?) "Hπ HL Ht".
  rewrite wp_unfold /wp_pre.
  intros_wp. intros_mod.

  iDestruct (use_outside with "[$][$]") as "%Hg'".
  assert (g=Out) as ->. { rewrite Hg in Hg'. naive_solver. }

  iSplitR; first eauto using reducible_fork.
  iIntros (???? Hstep) "?". iModIntro. iMod "Hclose" as "_".

  apply invert_step_fork in Hstep. destruct Hstep as (?&?&?&?&?). subst.
  iFrame. simpl.

  iDestruct (interp_valid with "[$]") as "%Hmt".

  rewrite merge_fresh //.
  2:{ rewrite dom_insert. assert (π ∈ dom k) by eauto.
      replace ({[π]} ∪ dom k) with (dom k) by set_solver.
      intros Eq. apply Hmt in Eq. lia. }

  iMod (interp_fork with "[$] [$]") as "(?&?&?&%)".
  1-3:eauto.
  iSpecialize ("Ht" with "[$]").

  assert (mt ≠ π).
  { intros ?. eapply Nat.lt_irrefl. apply Hmt. subst. eauto. }

  iMod (@interp_weak _ _ _ π (locs val_unit) with "[$]").
  2:{ rewrite lookup_insert_ne //. }
  { set_solver. }

  destruct b.
  { iMod (wp_clean.supd_clean_iterated _ _ π with "[$] [%] [$]") as "(? & ?)".
    2:{ rewrite lookup_insert //.  }
    { set_solver. }
    replace (({[π; mt]} ∖ {[π]})) with ({[mt]} : gset thread_id) by set_solver.

    rewrite insert_commute // (insert_id e π) // -insert_union_singleton_r //.
    iSpecialize ("Ht" with "[$][$]"). iFrame.
    iApply wp_val. by iFrame. }
  {  rewrite insert_commute //.
     iSpecialize ("Ht" with "[$][$]"). iFrame.
     rewrite insert_commute // (insert_id e π) // -insert_union_singleton_r //.
     iFrame. iApply wp_val. by iFrame. }
Qed.

Lemma wp_fork E L t π :
  dom L = locs t ->
  outside π -∗
  PBT {[π]} L -∗
  (£1 -∗ ∀ π', PBT {[π']} L -∗ outside π' -∗ wp ⊤ true π' t (fun _ => outside π')) -∗
  wp E true π (tm_fork t) (fun v => ⌜v=val_unit⌝ ∗ outside π).
Proof.
  iIntros. iApply (wp_fork_base with "[$][$]"); eauto.
Qed.

End Wp_fork.
