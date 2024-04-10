From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.algebra Require Import gset gmap auth.
From stdpp Require Import gmap fin_map_dom gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit.lib Require Import qz smultiset.
From irisfit Require Import more_maps_and_sets.
From irisfit Require Import ph interp_base pbt wp_updates mapsto.

Section More_interp.
Context `{!interpGS sz Σ}.

(* ------------------------------------------------------------------------ *)
(* kdiv: divide a context by 2. *)

Definition kdiv (k:gmap loc Qp) : gmap loc Qp :=
  fmap (fun q => (q/2)%Qp) k.

Lemma dom_kdiv k : dom (kdiv k) = dom k.
Proof. by rewrite dom_fmap_L. Qed.

(* A context is the union of its two halves. *)
Lemma kdiv_both k :
  k = (kdiv k) ⋅ (kdiv k).
Proof.
  unfold kdiv.
  apply leibniz_equiv.
  intros x.
  rewrite lookup_op lookup_fmap.
  destruct (k !! x) eqn:E; rewrite E; simpl; try easy.
  rewrite -Some_op frac_op. by rewrite Qp.div_2.
Qed.

Lemma PBT_kdiv S k :
  PBT S k ⊣⊢ PBT S (kdiv k) ∗ PBT S (kdiv k).
Proof. rewrite {1}(kdiv_both k) PBT_op //. Qed.

(* ------------------------------------------------------------------------ *)
(* crit *)

Lemma use_outside mt b k e σ π :
  outside π -∗
  interp mt b k e σ -∗
  ⌜e !! π = Some Out⌝.
Proof.
  iIntros "Ha Hi". destruct_interp "Hi".
  iDestruct (ghost_map.ghost_map_lookup with "Hinside Ha") as "%X".
  iPureIntro. destruct Hdebt.
  assert (is_Some (e !! π)) as (?&?).
  { apply elem_of_dom . rewrite de_dom. eauto using elem_of_dom. }
  naive_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* inside *)

Lemma mirror_dig_debt k η ρ π D D' :
  mirror k η ρ ->
  η !! π = Some D ->
  set_of_option D ⊆ set_of_option D' ->
  mirror k (<[π:=D']> η) ρ.
Proof.
  intros Hm Hπ Hi π' l r x Hπ'.
  rewrite lookup_insert_case. case_decide; eauto.
  inversion 1. subst. intros. eapply Hm; eauto. set_solver.
Qed.

Lemma linked_dig_debt D η θ τ π k D' :
  η !! π = Some (Some D) ->
  D ⊆ D' ->
  linked (image_less η k) θ τ ->
  linked (image_less (<[π:=Some D']> η) k) θ τ .
Proof.
  intros HD ? [X1 X2 X3 X4].
  constructor; eauto.
  intros l. rewrite elem_of_image_less. intros (π'&(?&?)&?&?).
  eapply X4. eapply elem_of_image_less. do 2 eexists. split; first done.
  destruct_decide (decide (π=π')); subst.
  { rewrite lookup_total_insert in H1.
    rewrite lookup_total_alt HD. unfold xroot_less in *. set_solver. }
  { rewrite lookup_total_insert_ne // in H1. }
Qed.

Lemma dig_debt D' D mt b k e σ π :
  D ⊆ D' ->
  interp mt b k e σ -∗
  inside π D ==∗
  interp mt b k e σ ∗ inside π D'.
Proof.
  iIntros (?) "Hi D". destruct_interp "Hi".
  iDestruct (ghost_map.ghost_map_lookup with "Hinside D") as "%".
  iMod (ghost_map.ghost_map_update with "Hinside D") as "(?&?)".
  iFrame. iModIntro. iExists ms,τ,ρ,_. iFrame "∗%".
  iPureIntro. split_and !.
  { inversion Hρ.  constructor; eauto using mirror_dig_debt.
    rewrite dom_insert_lookup_L //. }
  { inversion Hdebt. constructor. rewrite dom_insert_lookup_L //.
    intros. rewrite lookup_insert_case in H2.
    case_decide; subst.
    { inversion H2; subst. split; try congruence. intros. exfalso. naive_solver. }
    { naive_solver. } }
  { eauto using linked_dig_debt. }
Qed.

(* ------------------------------------------------------------------------ *)
(* dagger *)

Definition dagger l : iProp Σ := pbt_dead l.
Global Instance timeless_dagger l : Timeless (dagger l).
Proof. apply _. Qed.
Global Instance persistent_dagger l : Persistent (dagger l).
Proof. apply _. Qed.

Local Notation "† l" := (dagger l)%Z%I (at level 20) : bi_scope.

Lemma dagger_eq l : dagger l = pbt_dead l%I.
Proof. easy. Qed.

Definition daggers (ls:gset loc) : iProp Σ := ([∗ set] l ∈ ls, dagger l)%I.
Local Notation "†† ls" := (daggers ls)%Z%I (at level 20) : bi_scope.

Lemma daggers_weak ls1 ls2:
  ls1 ⊆ ls2 ->
  ††ls2 -∗ ††ls1.
Proof.
  iIntros (?) "Hl".
  replace (ls2) with (ls2 ∪ ls1) by set_solver.
  rewrite -(difference_union_L) union_comm_L.
  rewrite /daggers big_sepS_union. 2:by set_solver.
  iDestruct "Hl" as "(?&?)". iFrame.
Qed.

Lemma daggers_extract l ls:
  l ∈ ls ->
  ††ls -∗ †l.
Proof.
  iIntros (?) "Hl".
  iDestruct (daggers_weak {[l]} with "[$]") as "?".
  set_solver.
  iApply big_opS_singleton. iFrame.
Qed.

Lemma confront_pbt_dag l q S :
  l ⟸{q} S ∗ †l ⊢ False.
Proof.
  iIntros "(? & ?)".
  iApply (confront_pbt_pbt_dead with "[$][$]").
Qed.

Lemma confront_mapsfrom_dag q l ls:
  q ≠ 0%Qz →
  l ↤{q} ls ∗ † l  =[#]=∗ False.
Proof.
  iIntros (?) "(?&?)". iIntros (?????) "Hi". destruct_interp "Hi".
  iDestruct (ph.exploit_mapsfrom_dag with "[$]") as "%E". eauto.
  destruct E as (?&?&?).
  iDestruct (pbt_dead_exploit with "[$]") as "%".
  exfalso. unfold synchro_dead in Htauro. apply Htauro in H0.
  naive_solver.
Qed.

Lemma confront_mapsfrom_set_dag q l ls :
  q ≠ 0%Qz →
  mapsfrom_set l q ls ∗ † l =[#]=∗ False.
Proof.
  iIntros (?) "([%(?&_)]&?)". iIntros.
  iApply (confront_mapsfrom_dag with "[$][$]").
  eauto.
Qed.

Definition vdagger (v:val) : iProp Σ :=
  match v with
  | val_loc l => †l
  | _ => True end.

Global Instance timeless_vdagger v : Timeless (vdagger v).
Proof. destruct v; apply _. Qed.

Lemma use_synchro_dead τ ρ l:
  synchro_dead τ ρ ->
  (l ∉ dom ρ) ->
  l ∈ dom τ ->
  freed τ l.
Proof.
  intros Htauro ? X2.
  apply elem_of_dom in X2. destruct X2 as (x,X2). destruct x; try done.
  apply Htauro in X2. naive_solver.
Qed.

Lemma no_dangling_pointer_aux V T l b i :
  l ∈ (V∖T) ->
  †l ∗ ((outside i ∗ ⌜T=∅⌝) ∨ inside i T )=[b|i|V]=∗ False.
Proof.
  iIntros (?) "(?&U)".
  iIntros (????? Htid) "Hi".
  destruct_interp "Hi".

  iDestruct (pbt_dead_exploit with "[$]") as "%X".
  assert (freed τ l).
  { erewrite linked_dom in X; last done. destruct X as (X1&X2).
    apply elem_of_dom in X2. destruct X2 as (x,X2). destruct x; try done.
    apply Htauro in X2. naive_solver. }

  iAssert (⌜exists X, η !! i = Some X /\ l ∈ (V ∖ set_of_option X)⌝ )%I as "%Hde".
  { iDestruct "U" as "[ (U&%) | U ]".
    { iDestruct (ghost_map.ghost_map_lookup with "Hinside U") as "%Hη".
      iPureIntro. exists None. set_solver. }
    { iDestruct (ghost_map.ghost_map_lookup with "Hinside U") as "%Hη".
      iPureIntro. exists (Some T). set_solver. } }
  exfalso.
  destruct Hτ as [_ _ _ X4].
  eapply (X4 l); last done. apply elem_of_image_less.
  exists i, (lk,V). split; first done. unfold xroot_less. simpl.
  destruct Hde as (?&Hη&?).
  rewrite lookup_total_alt Hη. set_solver.
Qed.

Lemma no_dangling_pointer l b i V :
  l ∈ V ->
  †l ∗ outside i =[b|i|V]=∗ False.
Proof.
  iIntros (?) "(?&?)". iApply (no_dangling_pointer_aux V ∅ l). set_solver.
  iFrame. iLeft. by iFrame.
Qed.

Lemma no_dangling_pointer_inside l b i V T :
  l ∈ (V ∖ T) ->
  †l ∗ inside i T =[b|i|V]=∗ False.
Proof.
  iIntros (?) "(?&?)". iApply (no_dangling_pointer_aux V T l). done.
  iFrame.
Qed.

Lemma no_dangling_pointer1 (l l':loc) b q tid (vs:list val) n V :
  vs !! n = Some (val_loc l') ->
  l ∈ V ->
  †l' ∗ l ↦{q} vs ∗ outside tid =[b|tid|V]=∗ False.
Proof.
  iIntros (Hvs ?) "(?&?&?)".
  iIntros (????? Htid) "Hi".
  iDestruct (use_outside with "[$]Hi") as "%He".
  destruct_interp "Hi".
  iDestruct (exploit_mapsto with "[$] [$]") as "%Hm".
  iDestruct (ghost_map.ghost_map_lookup with "Hinside [$]") as "%Hη".

  iDestruct (pbt_dead_exploit with "[$]") as "(%X1&%X2)".
  assert (freed τ l').
  { erewrite linked_dom in X2; last done. eauto using use_synchro_dead. }
  clear X1 X2. exfalso.

  destruct Hτ as [X1 X2 X3 X4].
  assert (is_Some (τ !! l)) as (b'&Hb').
  { apply elem_of_dom. rewrite -X1. eauto using elem_of_dom. }
  (* Is l deallocated in τ ? *)
  destruct (X2 _ _ _ Hm Hb') as [|]; subst.
  { eapply (X3 l); last done.
    eapply prove_successor. done.
      apply block_pointer_set_block_elem.
      apply locs_elem_subseteq in Hvs.
      set_solver. }
  { eapply (X4 l); last done. apply elem_of_image_less.
    do 2 eexists. split; first done. unfold xroot_less. simpl.
    rewrite lookup_total_alt Hη. set_solver. }
Qed.

(* ------------------------------------------------------------------------ *)
(* More cleanup *)

Lemma mapsfrom_cleanup0 l l' :
  †l =[#]=∗
  l' ↤{0} ({[-l-]}).
Proof.
  iIntros "?".  iIntros (?????) "Hi".
  destruct_interp "Hi".

  iDestruct (pbt_dead_exploit with "[$]") as "(%X1&%X2)".
  assert (freed τ l).
  { erewrite linked_dom in X2; last done. eauto using use_synchro_dead. }

  iMod (ph_cleanup_singleton _ l' l with "[$]") as "[? H0]". done.
  iFrame. iExists _,_,_,_. iFrame. by iFrame "%".
Qed.

Lemma mapsfrom_cleanup l l' q ls:
  l ↤{q} ls ∗ †l' =[#]=∗
  l ↤{q} (ls ⊎ {[-l'-]}).
Proof.
  iIntros  "(Hf & ?)".  iIntros (?????) "Hi".
  iMod (mapsfrom_cleanup0 with "[$][$]") as "(?&H0)". iFrame.
  iDestruct (mapsfrom_join with "Hf H0") as "?". rewrite right_id_L.
  by iFrame.
Qed.

Lemma PBT_update_fork S x Lx sf mt u :
  PBT S {[x := Lx]} -∗
  auth_ctx sf u ==∗
  PBT (S ∪ {[mt]}) {[x := Lx]} ∗ auth_ctx (<[x:={[mt]} ∪ sf !!! x]> sf) u.
Proof.
  iIntros "E1 [%(%&E2)]". rewrite /PBT big_sepM_singleton.
  iDestruct "E1" as "[% (%&E1)]".

  iDestruct (pbt_precise_exploit_core with "[$]") as "%Hv".
  { naive_solver. }
  destruct Hv as (Hv1&Hv2&(z,(Hz1&Hz2))).

  iMod (own_update_2 with "E2 E1") as "(E1&E2)".
  { apply auth_update.
    apply singleton_local_update_any.
    intros ?. rewrite lookup_op /map1 lookup_fmap Hv2 right_id Hz1.
    simpl. intros E. injection E. intros. subst.
    apply disc.live_local_update.
    apply prod_local_update_2. simpl.
    etrans. apply gset_local_add with (X':={[mt]}).
    rewrite union_comm //. }
  iModIntro. iSplitL "E2".
  { rewrite big_sepM_singleton. iExists _. iFrame. iPureIntro.
    clear dependent z μ. intros i. rewrite !elem_of_union !elem_of_singleton.
    destruct_decide (decide (i=mt)); set_solver. }
  iFrame.
  iExists μ. rewrite insert_op_l.
  2:{ apply not_elem_of_dom. easy. }
  rewrite /map1 fmap_insert lookup_total_alt Hz1. iFrame.
  iPureIntro.
  split.
  { rewrite dom_insert. assert (x ∈ dom sf) by eauto. set_solver. }
  naive_solver.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma mapsfrom_split_half_empty l q r :
  l ↤{q} r ⊢ l ↤{q/2} r ∗ l ↤{q/2} ∅.
Proof.
  iIntros.
  iDestruct (mapsfrom_correct with "[$]") as "%Hv".
  iApply (mapsfrom_split with "[$]").
  { intros Hq. apply Qz_div_eq_zero in Hq. eauto. }
  { smultiset.smultiset_solver. }
  { rewrite Qz_div_2 //. }
  { rewrite right_id //. }
Qed.

End More_interp.

Global Opaque dagger.
Global Notation "† l" := (dagger l)%Z%I (at level 20) : bi_scope.
Global Notation "†† ls" := (daggers ls)%Z%I (at level 20) : bi_scope.
Global Notation "†? v" := (vdagger v)%Z%I (at level 20) : bi_scope.


Global Instance is_except_0_wp `{!interpGS sz Σ} E tid b t (Q:val -> iProp Σ) :
  IsExcept0 (wp E tid b t Q).
Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

Global Instance elim_modal_bupd_wp `{!interpGS sz Σ} E b i t p P (Q:val -> iProp Σ) :
  ElimModal True p false (|==> P) P (wp E b i t Q) (wp E b i t Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim
    (bupd_fupd E) fupd_frame_r bi.wand_elim_r (@fupd_wp _ irisfit_irisfitGS) //.
Qed.

Global Instance elim_modal_fupd_wp `{!interpGS sz Σ} E b i t p P (Q:val -> iProp Σ) :
  ElimModal True p false
    (|={E}=> P) P
    (wp E b i t Q) (wp E b i t Q)%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  rewrite fupd_frame_r bi.wand_elim_r (@fupd_wp _ irisfit_irisfitGS) //.
Qed.

Global Instance elim_modal_fupd_wp_atomic `{!interpGS sz Σ} E1 E2 b i t p P (Q:val -> iProp Σ) :
  ElimModal (Atomic t ∨ is_Some (to_val t)) p false
    (|={E1,E2}=> P) P
    (wp E1 b i t Q) (wp E2 b i t (fun v => |={E2,E1}=> Q v ))%I | 100.
Proof.
  intros ?.
  rewrite bi.intuitionistically_if_elim
    fupd_frame_r bi.wand_elim_r (@wp_atomic _ irisfit_irisfitGS) //.
Qed.

Global Instance add_modal_fupd_wp `{!interpGS sz Σ}  E b i t P (Q:val -> iProp Σ) :
  AddModal (|={E}=> P) P (wp E b i t Q).
Proof. rewrite /AddModal fupd_frame_r bi.wand_elim_r (@fupd_wp _ irisfit_irisfitGS) //. Qed.

Global Instance elim_acc_wp_atomic `{!interpGS sz Σ} {X}  E1 E2 b i α β γ t (Q:val -> iProp Σ) :
  ElimAcc (X:=X) (Atomic t ∨ is_Some (to_val t))
    (fupd E1 E2) (fupd E2 E1)
    α β γ (wp E1 b i t Q)
    (λ x, wp E2 b i t (fun v => |={E2}=> β x ∗ (γ x -∗? Q v)))%I | 100.
Proof.
  iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iSpecialize ("Hinner" with "[$]").
  iApply (wp_mono with "[$]").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.
