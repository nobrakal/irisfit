From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import ghost_map.
From iris.algebra Require Import dfrac gset gmap auth.
From stdpp Require Export namespaces.
From stdpp Require Import gmap fin_map_dom gmultiset.

From irisfit.lib Require Import qz qz_cmra smultiset disc.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Export more_maps_and_sets wp ph mapsto image roots_inv linked closed.

Set Implicit Arguments.

Notation dfgR := (discR (prodR fracR (gsetUR thread_id)) unitR).

Class interpGS (sz:nat -> nat) (Σ : gFunctors) :=
  InterpG {
      #[global] iinvgs :: invGS Σ;
      #[global] iphg :: phG Σ; (* For the store *)
      #[global] istore :: storeG sz Σ;
      #[global] idiamonds :: inG Σ (authR ugfracUR); (* A camera for diamonds *)
      #[global] ictx :: inG Σ (authUR (gmapUR loc dfgR)); (* A camera for context *)
      #[global] imax :: inG Σ (agreeR natUR);
      #[global] icrit :: ghost_mapG Σ natUR (option (gset loc)); (* A cmra for crit. sec. *)
      γctx : gname; (* A name for the ghost cell of the context *)
      γdia : gname; (* A name for the ghost cell of the diamonds *)
      γmax : gname; (* A name for the ghost cell of the maximum live heap size *)
      γcri : gname;
    }.

Ltac destruct_interp H :=
  iDestruct H as "[%ms [%τ [%ρ [%η (%Hσ & %Hθvalid & %Hρ & %Hdebt & %Hτ & %Htauro & Hstore & Hph & Hinside & Hk & Hctx & Hmax & Hdiams)]]]]".

Section Interp.

Context `{iG:!interpGS sz Σ}.

Definition map1 (ρ:gmap loc (gset thread_id)) : gmapUR loc dfgR :=
  fmap (fun ls => live (1%Qp,ls)) ρ.

Definition auth_ctx (ρ:gmap loc (gset thread_id)) S : iProp Σ :=
  ∃ (μ:gmap loc dfgR),
    ⌜dom ρ ∪ dom μ ⊆ S /\ forall (l:loc) (x:discR _ unitR), μ !! l = Some x -> x = discarded tt⌝ ∗
    own γctx (auth_auth (DfracOwn 1) (map1 ρ ⋅ μ)).

Record debt (e:critsec) (η:gmap thread_id (option (gset loc))) :=
  { de_dom : dom e = dom η;
    de_ok : forall π g x, e !! π = Some g -> η !! π = Some x -> g=Out <-> x=None
  }.

Lemma debt_update_Some e η i x1 x2 :
  η !! i = Some (Some x1) ->
  debt e η ->
  debt e (<[i:=Some x2]> η).
Proof.
  intros X [E2 E3]. constructor.
  { rewrite dom_insert_lookup_L //. }
  { assert (is_Some (e!!i)) as (?&?).
    { apply elem_of_dom. rewrite E2. eauto using elem_of_dom. }
    intros ????. rewrite lookup_insert_case. case_decide; last naive_solver.
    eapply de_ok in X; try done. naive_solver. }
Qed.

Definition outside (π:thread_id) : iProp Σ := π ↪[γcri] None.
Definition inside (π:thread_id) (S:gset loc) : iProp Σ := π ↪[γcri] (Some S).

Definition synchro_dead (τ:store) (ρ:gmap loc (gset thread_id)) :=
  forall l x, τ !! l = Some x -> x = BDeallocated <-> l ∉ dom ρ.

Lemma synchro_dead_same_dom τ ρ' ρ:
  dom ρ = dom ρ' ->
  synchro_dead τ ρ ->
  synchro_dead τ ρ'.
Proof. intros Hd Hs l Hl. rewrite -Hd. by eapply Hs. Qed.

Definition pbt_precise (l:loc) (q:Qp) (S:gset thread_id) : iProp Σ :=
  own γctx (◯ ({[l:= live (q,S)]})).

Definition pbt (l:loc) (q:Qp) (S:gset thread_id) : iProp Σ :=
  ∃ S', ⌜S' ⊆ S⌝ ∗ pbt_precise l q S'.

Definition PBT (S:gset thread_id) (M:gmap loc Qp) : iProp Σ :=
  [∗ map] l ↦ q ∈ M, pbt l q S.

Definition interp (mt:thread_id) (b:bool) (k:ctx) (e:critsec) (σ:store) : iProp Σ :=
    ∃ ms τ ρ (η:gmap thread_id (option (gset loc))),

    ⌜closed (image k) σ⌝ ∗
    ⌜valid_store sz ms τ⌝ ∗
    ⌜roots_inv k η ρ mt⌝ ∗
    ⌜debt e η⌝ ∗
    ⌜linked (image_less η k) σ τ⌝ ∗
    ⌜synchro_dead τ ρ⌝ ∗

    (* [mapsto] *)
    store_interp σ ∗

    (* [mapsfrom] *)
    ph_interp τ ∗

    (* [inside] *)
    ghost_map_auth γcri 1%Qp η ∗

    (* The authoritative part of ρ *)
    auth_ctx ρ (dom σ) ∗

    (* For each context of each thread, hold its pointed-by thread. *)
    (if b then (big_opM bi_sep (fun (tid:thread_id) (p:gmap loc Qp * gset loc) => PBT {[tid]} (fst p)) k) else True) ∗

    own γmax (to_agree ms) ∗

    (* The number of space credits currently in circulation is (at most)
       [available θ], the available space in the conceptual machine store. *)
    own γdia (@auth_auth ugfracUR (DfracOwn 1) (nat_to_Qz (available sz ms τ)))
.

(* ------------------------------------------------------------------------ *)

Lemma if_update (b:bool) (Φ Φ':iProp Σ) :
  (Φ ==∗ Φ') -∗
  (if b then Φ else True) ==∗ if b then Φ' else True.
Proof.
  iIntros "Hp ?".
  destruct b; try by iFrame.
  by iApply "Hp".
Qed.

Lemma if_update' (b : bool) (Φ Φ' : iProp Σ):
  (Φ -∗ Φ') -∗ (if b then Φ else True) -∗ if b then Φ' else True.
Proof.
  iIntros "H X". destruct b; last done. by iApply "H".
Qed.

(* ------------------------------------------------------------------------ *)

Lemma roots_inv_weak k π lt' lt ρ mt lk η :
  lt' ⊆ lt ->
  k !! π = Some (lk, lt) ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk, lt')]> k) η ρ mt /\ image_less η (<[π:=(lk, lt')]> k) ⊆ image_less η k.
Proof.
  inversion 3.
  edestruct (lookup_same_dom π _ _ ri_dom H0); eauto.
  split; first eauto using roots_inv_weak.
  intros l. rewrite !elem_of_image_less.
  intros (π'&(lk',lt0)&Hπ'&Hl).
  rewrite lookup_insert_case in Hπ'.
  case_decide; subst; eauto.
  inversion Hπ'. simpl in *. subst.
  do 2 eexists. split; first done. unfold xroot_less in *.
  set_solver.
Qed.

Lemma interp_weak tid lt' mt b k e lk lt σ :
  lt' ⊆ lt ->
  k !! tid = Some (lk,lt) ->
  interp mt b k e σ ==∗ interp mt b (<[tid:=(lk,lt')]> k) e σ.
Proof.
  iIntros (? Htid) "Hi".
  destruct_interp "Hi".
  edestruct roots_inv_weak as (?&?); try done.

  iExists _,_,_,η. iFrame.

  assert (image (<[tid:=(lk, lt')]> k) ⊆ image k).
  { rewrite image_insert2; eauto.
    erewrite <- (image_upd k); eauto.
    rewrite image_insert2; eauto. set_solver. }

  iMod (if_update with "[] [$]") as "?"; last iFrame.
  { iIntros.
    iDestruct (big_sepM_insert_acc with "[$]") as "[Hctx Hback]".
    { eauto. }
    iSpecialize ("Hback" $! (lk,lt') with "[$]").
    by iFrame. }

  iPureIntro.
  split_and !; eauto using closed_weak, roots_inv_weak, linked_weak.
Qed.

(* ------------------------------------------------------------------------ *)
(* More lemmas on PBT *)

Lemma pbt_op l q1 q2 S1 S2 :
  pbt l (q1 + q2) (S1 ∪ S2) ⊣⊢ pbt l q1 S1 ∗ pbt l q2 S2.
Proof.
  unfold pbt, pbt_precise. iSplit.
  { iIntros "[% (%&X)]".
    assert ( live ((q1 + q2)%Qp, S') = live (q1, S' ∩ S1) ⋅ live (q2, S' ∩ S2)) as ->.
    { rewrite -live_op. f_equal. rewrite -pair_op. f_equal. set_solver. }
    iDestruct "X" as "(X1&?)". iSplitL "X1".
    all:iExists _; iFrame; iPureIntro; set_solver. }
  { iIntros "([%S1' (%&X1)]&[%S2' (%&X2)])".
    iExists (S1'∪S2'). iSplitR; first (iPureIntro;set_solver).
    rewrite -frac_op -gset_op pair_op live_op -singleton_op auth_frag_op own_op.
    iFrame. }
Qed.

Lemma PBT_op S k1 k2 :
  PBT S (k1 ⋅ k2) ≡ (PBT S k1 ∗ PBT S k2)%I.
Proof.
  unfold PBT. iStartProof.
  iRevert (k2). iInduction k1 as [|] "IH" using map_ind; iIntros (k2).
  { rewrite big_sepM_empty left_id_L left_id //. naive_solver. }
  destruct (k2 !! i) eqn:Hi.
  { rewrite -(insert_delete k2 i q) //.
    rewrite -insert_op !big_sepM_insert //; first last.
    { rewrite lookup_delete //. }
    { rewrite lookup_op H lookup_delete //. }
    rewrite -{4}(union_idemp_L S) frac_op pbt_op.
    iSplit.
    { iIntros "((?&?)&?)". iFrame. by iApply "IH". }
    { iIntros "((?&?)&?&?)". iFrame. iApply "IH". iFrame. } }
  { rewrite gmap_op. rewrite <- insert_merge_l with (x:=x).
    2:{ rewrite Hi //. }
    rewrite !big_sepM_insert //.
    2:{ rewrite lookup_merge H Hi //. }
    iSplit.
    { iIntros "(?&?)". iFrame. by iApply "IH". }
    { iIntros "((?&?)&?)". iFrame. iApply "IH". iFrame. } }
Qed.

Lemma PBT_union S k1 k2 :
  PBT S k1 ∗ PBT S k2 ⊢ PBT S (k1 ⋅ k2).
Proof. rewrite PBT_op. eauto. Qed.

Lemma PBT_split S k1 k2 :
  PBT S (k1 ⋅ k2) ⊢ PBT S k1 ∗ PBT S k2 .
Proof. rewrite PBT_op. eauto. Qed.

Lemma PBT_op_split (S1 S2:gset thread_id) k1 k2 :
  dom k1 = dom k2 ->
  (PBT (S1 ∪ S2) (k1 ⋅ k2) ⊣⊢ PBT S1 k1 ∗ PBT S2 k2)%I.
Proof.
  intros Hd. rewrite /PBT. iStartProof.
  iRevert (k2 Hd). iInduction k1 as [|] "IH" using map_ind; iIntros (k2 Hd).
  { rewrite dom_empty_L in Hd.  symmetry in Hd. apply dom_empty_inv_L in Hd. subst.
    rewrite left_id_L !big_sepM_empty left_id //. }
  { rewrite dom_insert_L in Hd.
    assert (i ∈ dom k2) as Hi by set_solver.
    apply elem_of_dom in Hi. destruct Hi as (q&?).
    rewrite -(insert_delete k2 i q) //.
    rewrite -insert_op !big_sepM_insert //; first last.
    { rewrite lookup_delete //. }
    { rewrite lookup_op H lookup_delete //. }
    rewrite frac_op pbt_op. apply not_elem_of_dom in H.
    iSplit.
    { iIntros "((?&?)&?)". iFrame. iApply "IH"; last done.
      iPureIntro. rewrite dom_delete_L. set_solver. }
    { iIntros "((?&?)&?&?)". iFrame. iApply "IH"; last iFrame.
      iPureIntro. rewrite dom_delete_L. set_solver. } }
Qed.

Lemma PBT_empty S : ⊢ PBT S ∅.
Proof. by iApply big_sepM_empty. Qed.

Lemma mirror_shift2 k η ρ lk l1 L2 π:
  k !! π = Some (lk ⋅ L2, l1) ->
  mirror k η ρ ->
  mirror (<[π:=(lk, l1 ∪ dom L2)]> k) η ρ.
Proof.
  intros Hk Hm.
  intros π' l (lk',lt') x. rewrite lookup_insert_case.
  case_decide; subst; eauto.
  injection 1. intros <- <- Hη. simpl.
  specialize (Hm π' l _ _ Hk Hη). simpl in *. rewrite dom_op in Hm.
  set_solver.
Qed.

Lemma roots_inv_shift2 k η mt l1 l2 π ρ L2 lk :
  l2 = dom L2 ->
  k !! π = Some (lk ⋅ L2, l1) ->
  roots_inv k η ρ mt ->
  roots_inv (<[π:=(lk, l1 ∪ l2)]> k) η ρ mt.
Proof.
  intros -> Hπ Hri . inversion Hri as [E1 E2 E3].
  edestruct (lookup_same_dom π _ _ E3 Hπ); eauto.
  econstructor; eauto using mirror_shift2,ndom_lt_insert.
  { rewrite !dom_insert_lookup_L //. }
Qed.

Lemma interp_shift_true mt (k:ctx) e tid (σ:store) lk l1 l2 (L2:gmap loc Qp) :
  k !! tid = Some (lk,l1 ∪ l2) ->
  l2 = dom L2 ->
  (interp mt true k e σ ∗ PBT {[tid]} L2 ==∗
   let k' := <[tid := (lk ⋅ L2, l1)]> k in
   (interp mt true k' e σ) ∗
   (∀ σ' k'' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k' k''⌝ -∗
   ⌜k'' !! tid = Some (lk ⋅ L2, l1')⌝ -∗ (* The visible may change at will *)
   interp mt' true k'' e' σ' ==∗
   PBT {[tid]} L2 ∗ interp mt' true (<[tid:=(lk,l1' ∪ l2)]> k'') e' σ')).
Proof.
  iIntros (? Hl2) "[Hi Hpbt]".
  assert (xroot (lk, l1 ∪ l2) = xroot (lk ⋅ L2, l1)).
  { rewrite /xroot dom_op. set_solver. }
  destruct_interp "Hi".
  iSplitL.
  { (* iDestruct (extract_all_reg _ _ _ L2 with "[$][$]") as "%". *)
    iExists _,_,_,η.
    replace (image (<[tid:=(lk ⋅ L2, l1)]> k)) with (image k) by (erewrite image_upd; eauto).
    iFrame "∗%".
    iDestruct (big_sepM_insert_acc with "Hctx") as "(? & Hback)" .
    done. simpl.
    iSplitR. { iPureIntro. eapply roots_inv_shift1; eauto. }
    iSplitR. { iPureIntro. eauto using linked_shift1. }
    iApply "Hback". iApply PBT_op. by iFrame. }

  { iModIntro.
    iIntros (? ? ? ? ? (?&?) ?) "[%ms' [%τ' [%ρ' [%η' (%Hσ' & %Hθvalid' & %Hρ' & %Hdebt' & %Hτ' & Hph' & Hstore' & Hk' & Hctx' & ? & ? & ?)]]]]".
    iDestruct (big_sepM_insert_acc with "[$]") as "(Hb & Hback)" .
    eauto. simpl.
    rewrite PBT_op. iDestruct "Hb" as "(? & ?)".
    iFrame.
    iSpecialize ("Hback" $! (lk, l1' ∪ l2) with "[$]").
    iModIntro.
    iExists _,_,_,_. iFrame.
    iPureIntro.
    assert (xroot (lk ⋅ L2, l1') = xroot (lk, l1' ∪ l2)).
    { rewrite /xroot dom_op. set_solver. }
    replace (image (<[tid:=(lk, l1' ∪ l2)]> k'')) with (image k'') by (erewrite image_upd; eauto).
    split_and!; eauto using roots_inv_shift2, linked_shift2. }
Qed.

(* XXX try to facto with true *)
Lemma interp_shift_false mt (k:ctx) tid (σ:store) lk l1 l2 e (L2:gmap loc Qp) :
  k !! tid = Some (lk,l1 ∪ l2) ->
  l2 = dom L2 ->
  (interp mt false k e σ ∗ PBT {[tid]} L2 ==∗
   let k' := <[tid := (lk ⋅ L2, l1)]> k in
   (interp mt false k' e σ) ∗
   (∀ σ' k'' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k' k''⌝ -∗
   ⌜k'' !! tid = Some (lk ⋅ L2, l1')⌝ -∗ (* The visible may change at will *)
   interp mt' false k'' e'  σ' ==∗
   PBT {[tid]} L2 ∗ interp mt' false (<[tid:=(lk,l1' ∪ l2)]> k'') e' σ')).
Proof.
  iIntros (? Hl2) "[Hi Hpbt]".
  assert (xroot (lk, l1 ∪ l2) = xroot (lk ⋅ L2, l1)).
  { rewrite /xroot dom_op. set_solver. }
  destruct_interp "Hi".
  iSplitR "Hpbt".
  { iExists _,_,_,_.
    replace (image (<[tid:=(lk ⋅ L2, l1)]> k)) with (image k) by (erewrite image_upd; eauto).
    iFrame "∗%". iPureIntro. split_and !.
    { eapply roots_inv_shift1; eauto. }
    { eauto using linked_shift1. } }
  { iModIntro.
    iIntros (? ? ? ? ? (?&?) ?) "[%ms' [%τ' [%ρ' [%η' (%Hσ' & %Hθvalid' & %Hρ' & %Hdebt' & %Hτ' & Hph' & Hstore' & Hk' & Hctx' & ? & ? & ?)]]]]".
    iModIntro. iFrame. iExists _,_,_,_. iFrame.
    iPureIntro.
    assert (xroot (lk ⋅ L2, l1') = xroot (lk, l1' ∪ l2)).
    { rewrite /xroot dom_op. set_solver. }
    replace (image (<[tid:=(lk, l1' ∪ l2)]> k'')) with (image k'') by (erewrite image_upd; eauto).
    eauto 15 using roots_inv_shift2, linked_shift2. }
Qed.

Lemma interp_shift mt b (k:ctx) e tid (σ:store) lk l1 l2 (L2:gmap loc Qp) :
  k !! tid = Some (lk,l1 ∪ l2) ->
  l2 = dom L2 ->
  (interp mt b k e σ ∗ PBT {[tid]} L2 ==∗
   let k' := <[tid := (lk ⋅ L2, l1)]> k in
   (interp mt b k' e σ) ∗
   (∀ σ' k'' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k' k''⌝ -∗
   ⌜k'' !! tid = Some (lk ⋅ L2, l1')⌝ -∗ (* The visible may change at will *)
   interp mt' b k'' e' σ' ==∗
   PBT {[tid]} L2 ∗ interp mt' b (<[tid:=(lk,l1' ∪ l2)]> k'') e' σ')).
Proof.
  destruct b; [apply interp_shift_true | apply interp_shift_false].
Qed.

Lemma big_sepM_init_empty (k:ctx) :
  (forall i, i ∈ dom k -> fst <$> k !! i = Some ∅) ->
  ⊢ [∗ map] tid↦p ∈ k, PBT {[tid]} p.1.
Proof.
  iIntros. iApply big_sepM_intro. iModIntro.
  iIntros (i ? X). assert (x.1 = ∅) as ->.
  { generalize X. intros E. apply stdpp.prove_in_dom in X. specialize (H i X).
    rewrite E in H. naive_solver. }
  iApply PBT_empty.
Qed.

Lemma upd_big_sepM k k':
  upd k k' ->
  (forall i, i ∈ (dom k' ∖ dom k ) -> fst <$> k' !! i = Some ∅) ->
  ([∗ map] tid↦p ∈ k, PBT {[tid]} p.1)%I ==∗
   [∗ map] tid↦p ∈ k', PBT {[tid]} p.1.
Proof.
  iIntros ((Hd & Hupd) Hext) "HM".
  rewrite (split_map k' (dom k)).
  2:{ set_solver. }
  iApply iris.big_sepM_union_with.
  { iIntros. rewrite PBT_op. naive_solver. }
  iSplitL; last first.
  { iApply big_sepM_init_empty.
    intros i Hi.
    rewrite dom_restrict in Hi.
    rewrite lookup_restrict.
    case_decide; set_solver. }
  clear Hext.

  iRevert (k' Hd Hupd).
  iInduction k as [] "IH" using map_ind; iIntros (k' Hd Hupd).
  { rewrite dom_empty_L restrict_empty.
    iApply big_sepM_empty. by iFrame. }
  { rewrite dom_insert_L in Hd.
    rewrite big_sepM_insert_delete.
    iDestruct ("HM") as "(? & ?)".

    destruct (k' !! i) eqn:E.
    2:{ apply not_elem_of_dom in E. set_solver. }
    rewrite dom_insert_L.
    erewrite restrict_insert. 2:eauto.

    rewrite (Hupd i x p) //.
    2:{ rewrite lookup_insert //. }

    iApply big_sepM_insert_delete. iFrame.
    rewrite delete_notin //.

    iSpecialize ("IH" with "[$]").
    iMod ("IH" $! (delete i k') with "[%] [%]") as "?".
    { rewrite dom_delete. apply not_elem_of_dom in H. set_solver. }
    { intros ? ? ? Hm Hk'.
      destruct (decide (i=tid)); subst.
      rewrite lookup_delete in Hk'. congruence.
      rewrite lookup_delete_ne // in Hk'.
      eapply Hupd; eauto.
      rewrite lookup_insert_ne //. }
    rewrite restrict_delete. by iFrame. }
Qed.

Lemma interp_shift_noclean mt b k e tid σ lk l1 l2 :
  k !! tid = Some (lk,l1 ∪ l2) ->
  (interp mt b k e σ ==∗
   let k' := <[tid := (lk ⋅ (noclean l2), l1)]> k in
   (* l2 is now in the context *)
   (interp mt false k' e σ) ∗
   (* The capacity to restore the old context. *)
    (∀ σ' k'' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k' k'' /\ diff_empty k' k''⌝ -∗
       ⌜k'' !! tid = Some (lk ⋅ (noclean l2), l1')⌝ -∗ (* The visible may change at will *)
       interp mt' false k'' e' σ' ==∗
       interp mt' b (<[tid:=(lk,l1' ∪ l2)]> k'') e' σ')).
Proof.
  iIntros (?) "Hi".
  assert (xroot (lk, l1 ∪ l2) = xroot (lk ⋅ (noclean l2), l1)).
  { rewrite /xroot dom_op dom_noclean. set_solver. }
  destruct_interp "Hi".
  iSplitR "Hctx".
  { iExists _,_,_,_.
    replace (image (<[tid:=(lk ⋅ (noclean l2), l1)]> k)) with (image k) by (erewrite image_upd; eauto).
    iFrame "∗%". iPureIntro.
    split_and !.
    { eapply roots_inv_shift1; eauto. rewrite dom_noclean //. }
    { eapply linked_shift1; eauto. rewrite dom_noclean //. } }
  { iModIntro.
    iIntros (? ? ? ? ? (?&Hupd) ?) "[%ms' [%τ' [%ρ' [%η' (%Hσ' & %Hθvalid' & %Hρ' & %Hdebt' & %Hτ' & Hph' & Hstore' & Hk' & Hctx' & ? & ? & ?)]]]]".

    assert (xroot (lk ⋅ (noclean l2), l1') = xroot (lk, l1' ∪ l2)).
    { rewrite /xroot dom_op dom_noclean. set_solver. }
    iExists _,_,_,_. iFrame.
    replace (image (<[tid:=(lk, l1' ∪ l2)]> k'')) with (image k'') by (erewrite image_upd; eauto).
    iFrame "%".
    destruct Hupd as ((? & ?) & He).
    iMod (if_update with "[] [$]"); last iFrame.
    { iIntros. iApply (upd_big_sepM with "[$]").
      { constructor.
        rewrite dom_insert_L. set_solver.
        intros tid' ? ? ? Hk''.
        destruct (decide (tid=tid')); subst.
        { rewrite lookup_insert in Hk''. injection Hk''. intros <-.
          simpl. rewrite H6 in H. injection H. intros ->. easy. }
        { rewrite lookup_insert_ne // in Hk''.
          eapply H5; eauto. rewrite lookup_insert_ne //. } }
      { intros i Hi. rewrite dom_insert in Hi.
        assert (tid ∈ dom k) by eauto.
        assert (i ≠ tid) by set_solver.
        rewrite lookup_insert_ne //.
        apply He. rewrite dom_insert. set_solver. } }
    iPureIntro. split.
    { eapply roots_inv_shift2; eauto. rewrite dom_noclean //. }
    { eapply linked_shift2; eauto. rewrite dom_noclean //. } }
Qed.

Lemma PBT_insert1 S l x i :
  i ∉ dom l ->
  PBT S (<[i:=x]> l) -∗ PBT S l ∗ PBT S {[i:=x]}.
Proof.
  iIntros (Hi) "H". apply not_elem_of_dom in Hi.
  rewrite /PBT big_sepM_insert // big_sepM_singleton comm //.
Qed.

Lemma PBT_insert2 S l x i :
  i ∉ dom l ->
  PBT S l ∗ PBT S {[i:=x]} -∗ PBT S (<[i:=x]> l).
Proof.
  iIntros (Hi) "H". apply not_elem_of_dom in Hi.
  rewrite /PBT big_sepM_insert // big_sepM_singleton comm //.
Qed.

Lemma interp_valid mt b k e σ :
  interp mt b k e σ -∗ ⌜ ndom_lt k mt ⌝.
Proof.
  iIntros "Hi".
  destruct_interp "Hi".
  destruct Hρ; eauto.
Qed.

Definition diamond (n : ugfrac) : iProp Σ :=
  own γdia (◯ n).

Lemma ugfrac_update_incr (γ : gname) (m k : ugfrac) :
  own γ (● m)%Qz -∗
  |==> own γ (● (m ⋅ k)%Qz) ∗ own γ (◯ k).
Proof.
  iIntros. rewrite -own_op.
  iApply (own_update with "[$]").
  apply auth_update_alloc.
  apply ugfrac_local_update.
  rewrite right_id ugfrac_op //.
Qed.

Local Notation "♢ n" := (diamond n)%I%Qz (at level 20) : bi_scope.

Lemma diamonds_split (n m : ugfrac) :
  ♢ (n + m) -∗ ♢ n ∗ ♢ m.
Proof.
  rewrite /diamond -own_op -auth_frag_op ugfrac_op //. by iIntros.
Qed.

Lemma diamonds_join n m :
  ♢ n ∗ ♢ m -∗ ♢ (n + m).
Proof.
  rewrite /diamond -own_op auth_frag_op //. by iIntros.
Qed.

Lemma diamond_split_iff n m  :
  (♢ (n + m))%I ≡ (♢ n ∗ ♢ m)%I.
Proof.
  iSplit.
  { iApply diamonds_split. }
  { iApply diamonds_join. }
Qed.

Lemma diamonds_zero :
  (⊢ |==> ♢ 0)%I.
Proof.
  iApply own_unit.
Qed.

Lemma exploit_mapsto mt b (l:loc) q (vs:list val) k e (σ:store) :
  interp mt b k e σ ∗ l ↦{q} vs ⊢ ⌜σ !! l = Some (BBlock vs)⌝.
Proof.
  iIntros "[Hi ?]".
  destruct_interp "Hi".
  iApply (exploit_mapsto with "[$] [$]").
Qed.

Lemma interp_noclean mt k e σ tid l lk :
  k !! tid = Some (lk,l) ->
  interp mt true k e σ -∗ interp mt false k e σ ∗
  (∀ σ' k' e' l1' mt', ⌜dom σ ⊆ dom σ' /\ upd k k' /\ diff_empty k k'⌝ -∗
     ⌜k' !! tid = Some (lk, l1')⌝ -∗
     interp mt' false k' e' σ' ==∗ interp mt' true k' e' σ')%I.
Proof.
  iIntros (?) "Hi".
  destruct_interp "Hi".
  iSplitR "Hctx".
  { iExists _,_,_,_. iFrame. eauto. }
  { iIntros (? ? ? ? ?) "(%&%&%) % [%ms' [%τ' [%ρ' [%η' (%Hσ' & %Hθvalid' & %Hρ' & %Hdebt' & %Hτ' & Hph' & Hstore' & Hk' & Hctx' & ? & ? & ?)]]]]".
    iExists _,_,_,_. iFrame "∗%".
    iApply (upd_big_sepM with "[$]"); eauto. }
Qed.
End Interp.

Global Notation "♢ n" := (diamond n)%I%Qz (at level 20) : bi_scope.

Global Instance irisfit_irisfitGS `{interpGS sz Σ} : irisfitGS Σ.
Proof.
  apply (IrisFitGS _ interp PBT outside).
  { eapply interp_valid. }
  { eapply interp_shift. }
  { eapply interp_shift_noclean. }
  { eapply interp_noclean. }
  { eapply interp_weak. }
Defined.

Module Initialization.

  Definition interpΣ : gFunctors :=
    #[ invΣ;
       Initialization.phΣ;
       GFunctor (authR ugfracUR);
       GFunctor (authUR (gmapUR loc dfgR));
       GFunctor (agreeR natUR);
       ghost_mapΣ nat (option (gset loc));
       Initialization.storeΣ
      ].

  (* The difference between the *PreG and *G is the presence of the names
     of ghost cells. (ie. gname) *)
  Class interpPreG (Σ : gFunctors) :=
  { piinvgs :: invGpreS Σ;
    piphg :: Initialization.phPreG Σ;
    pidiamonds :: inG Σ (authR ugfracUR);
    pictx :: inG Σ (authUR (gmapUR loc dfgR));
    pimax :: inG Σ (agreeR natUR);
    pide :: ghost_mapG Σ nat (option (gset loc));
    pstore :: Initialization.storePreG Σ
    }.

  Instance subG_interpPreG Σ :
    subG interpΣ Σ → interpPreG Σ.
  Proof. solve_inG. Qed.

  Instance interpPreG_interpΣ : interpPreG interpΣ.
  Proof. eauto with typeclass_instances. Qed.

  Lemma auth_ctx_init `(interpGS sz Σ):
    own γctx  (● (∅:gmap loc dfgR)) -∗
    auth_ctx ∅ ∅.
  Proof.
    iIntros.
    iExists ∅.
    rewrite /map1 fmap_empty left_id.
    iFrame. iPureIntro. set_solver.
  Qed.

  Lemma debt_empty : debt ∅ ∅.
  Proof. constructor; set_solver. Qed.

  Lemma linked_empty :
    linked (image_less ∅ ∅) ∅ ∅.
  Proof.
    rewrite image_less_empty.
    constructor; eauto.
    { intros ???. rewrite lookup_empty //. }
    { intros ??. rewrite /successor /hypotheses.successors lookup_empty //. }
    { intros ?. set_solver. }
  Qed.

  Lemma synchro_dead_empty :
    synchro_dead ∅ ∅.
  Proof. intros ?. set_solver. Qed.


  Lemma interp_init `{!interpPreG Σ, hinv:!invGS Σ} (sz:nat -> nat) (ms:nat) :
    ⊢ |==> ∃ hi : interpGS sz Σ, ⌜@iinvgs sz Σ hi = hinv⌝ ∗
    interp 0 true ∅ ∅ ∅ ∗ ♢ms ∗ @own Σ (agreeR natUR) (@imax _ _ hi) γmax (to_agree ms).
  Proof.
    intros.
    iIntros. rewrite /interp.
    iMod Initialization.ph_init as "[%Iph ?]".

    iMod (own_alloc (● (∅:gmapUR loc dfgR))) as (γctx) "Hctx".
    { rewrite auth_auth_valid. done. }
    Unshelve.
    iMod (@own_alloc _ (authR ugfracUR) _ (● (nat_to_Qz (available sz ms ∅):ugfrac) ⋅ ◯ (nat_to_Qz (available sz ms ∅):ugfrac))) as (γdia) "[? Hdia]".
    { rewrite auth_both_valid. done. }

    iMod (own_alloc (to_agree ms)) as "[%γmax #Hmax]". done.
    iMod (@ghost_map_alloc_empty _ _ (option (gset loc)) _ _ pide) as "[%γcri Hcri]".

    iMod Initialization.store_init as "[% ?]".
    iExists (@InterpG _ Σ hinv _ _ _ _ _ _ γctx γdia γmax γcri). iFrame "#".
    iSplitR; try easy.
    iSplitR "Hdia".
    2:{ rewrite available_init /diamond //. }

    iDestruct (@auth_ctx_init _ _ (@InterpG _ Σ hinv _ _ _ _ _ _ γctx γdia γmax γcri) with "[$]") as "?".
    iExists ms,∅,∅,∅. iFrame. rewrite !big_sepM_empty. simpl.
    iFrame "∗#".
    iPureIntro. rewrite image_empty.
    eauto 15 using valid_store_init,closed_init,roots_inv_init, debt_empty, linked_empty,synchro_dead_empty.
  Qed.

End Initialization.
