From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gset gmap auth.
From iris Require Import ghost_map.
From stdpp Require Import gmap fin_map_dom gmultiset.

From irisfit.lib Require Import qz qz_cmra smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets wp ph image disc interp pbt.

Section Wp_clean.

Context `{!interpGS sz Σ}.

(* ------------------------------------------------------------------------ *)
(* Toward [interp_clean]. *)

Local Lemma a_set_eq (X Y Z:gset thread_id):
  Y ⊆ Z ->
  X ∖ Y ∪ Z = X ∪ Z.
Proof.
  intros ?. apply leibniz_equiv.
  intros i. rewrite elem_of_union elem_of_union elem_of_difference.
  split.
  { intros [[]|]; set_solver. }
  intros []; try set_solver.
  destruct (decide (i ∈ Y)); set_solver.
Qed.

Lemma gmap_disj_valid_op `{Countable K} {A : cmra} (g1 g2: gmap K A) :
  dom g1 ## dom g2 ->
  ✓ (g1 ⋅ g2) <-> ✓g1 /\ ✓g2.
Proof.
  split.
  { eauto using cmra_valid_op_l, cmra_valid_op_r. }
  { intros (E1,E2).
    intros i.
    specialize (E1 i). specialize (E2 i).
    rewrite lookup_op.
    destruct (g1 !! i) eqn:?; destruct (g2 !! i) eqn:?; eauto.
    assert (i ∈ dom g1) by eauto.
    assert (i ∈ dom g2) by eauto.
    set_solver. }
Qed.

Local Lemma not_black (A:gmapUR loc dfgR) X l q' x :
  ¬ ✓ (● A ⋅ ◯ {[l := live X]} ⋅ View (Some q') x).
Proof.
  intros Hz.
    rewrite -assoc (comm _ _ (View (Some q') x)) assoc in Hz.
    apply cmra_valid_op_l in Hz.
    destruct Hz as (Hz,_). simpl in *.
    apply dfrac_valid_own_l in Hz.
    apply irreflexivity in Hz; eauto; apply _.
Qed.

Local Lemma valid1 ρ l g μ π :
  l ∈  dom ρ ->
  dom ρ ## dom μ ->
  ✓ (map1 ρ ⋅ μ) ->
  ✓ (map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ).
Proof.
  intros ?? Hv.
  apply gmap_disj_valid_op.
  { rewrite /map1 dom_fmap dom_insert. set_solver. }
  apply gmap_disj_valid_op in Hv.
  2:{ rewrite /map1 dom_fmap //. }
  destruct Hv. split; eauto.
  unfold map1 in *. rewrite fmap_insert.
  by apply insert_valid; eauto.
Qed.

Local Lemma valid2 ρ μ l q S x q' c π :
  ✓ (map1 ρ ⋅ μ) ->
  (∀ i, ({[l := live (q, S)]} ⋅ x) !! i ≼ (map1 ρ ⋅ μ) !! i) ->
  x !! l = Some (csum.Cinl (q', c)) ->
  π ∈ c ->
  ✓ (● (map1 ρ ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]} ⋅ View None x).
Proof.
  intros Hv Hz Hl ?.
  rewrite -assoc -auth_frag_op.
  apply auth_both_valid_discrete.
  split; eauto.
  apply lookup_included. intros l'.
  etrans. 2:apply Hz.
  do 2 rewrite lookup_op.

  rewrite lookup_insert_case. case_decide; subst.
  { rewrite lookup_insert Hl -!Some_op.
    apply Some_included. left.
    constructor. split; simpl; eauto.
    rewrite !gset_op. rewrite a_set_eq //. set_solver. }
  rewrite !lookup_insert_ne //.
Qed.

Local Lemma valid3 g ρ μ l q S x q' c π :
  dom ρ ## dom μ ->
  ρ !! l = Some g ->
  ✓ (map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ) ->
  (∀ i, ({[l := live (q, S)]} ⋅ x) !! i ≼ (map1 ρ ⋅ μ) !! i) ->
  x !! l = Some (csum.Cinl (q', c)) ->
  π ∉ c ->
  ✓ (● (map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]}
     ⋅ View None x).
Proof.
  intros ? Hl Hv Hz E' ?.
  rewrite -assoc -auth_frag_op.
  apply auth_both_valid_discrete.
  split; eauto.
  { rewrite -(insert_id x l (csum.Cinl (q', c))) //.
    apply lookup_included. intros l'.
    rewrite !lookup_op /map1 lookup_fmap.
    rewrite lookup_insert_case; case_decide; subst.
    { repeat rewrite lookup_insert. simpl.

      assert (μ !! l' = None) as El'.
      { rewrite -not_elem_of_dom. intros ?.
        eapply elem_of_dom_2 in Hl. set_solver. }
      rewrite El' right_id  -Some_op.
      specialize (Hz l').
      rewrite !lookup_op lookup_insert /map1 lookup_fmap E' Hl El' right_id in Hz.
      rewrite -Some_op Some_included in Hz. simpl in *.

      rewrite Some_included.
      destruct Hz as [Hz|Hz]; [left|right].
      { inversion Hz. subst. inversion H3. simpl in *.
        do 2 constructor; eauto.
        simpl. set_solver. }
      { rewrite -live_op in Hz. rewrite live_included in Hz.
        apply pair_included in Hz. destruct Hz as (Hz1,Hz2).
        rewrite -live_op live_included.
        apply pair_included. split; eauto.
        apply gset_included in Hz2.
        apply gset_included. intros i. rewrite elem_of_union elem_of_difference elem_of_difference.
        intros [[]|]; set_solver. } }
    { rewrite !lookup_insert_ne // !lookup_empty left_id.
      specialize (Hz l'). rewrite lookup_op !lookup_insert_ne // !lookup_empty left_id // in Hz.
      etrans. eauto. rewrite lookup_op /map1 !lookup_fmap //. } }
Qed.

Local Lemma valid4 g ρ μ l q S x π :
  dom ρ ## dom μ ->
  ρ !! l = Some g ->
  ✓ (map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ) ->
  (∀ i, ({[l := live (q, S)]} ⋅ x) !! i ≼ (map1 ρ ⋅ μ) !! i) ->
  l ∉ dom x ->
  ✓ (● (map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]}
     ⋅ View None x).
Proof.
  intros ? Hl Hv Hz ?.
  rewrite -assoc -auth_frag_op.
  apply auth_both_valid_discrete.
  split; eauto.

  apply lookup_included. intros l'.
  destruct (decide (l=l')); subst.
  { assert (μ !! l' = None) as El'.
    { rewrite -not_elem_of_dom. intros ?. apply elem_of_dom_2 in Hl. set_solver. }
    rewrite !lookup_op /map1 lookup_fmap !lookup_insert El' right_id.
    rewrite not_elem_of_dom in H0. rewrite H0 right_id.
    apply Some_included.

    specialize (Hz l').
    rewrite !lookup_op /map1 lookup_fmap lookup_insert H0 El' Hl !right_id in Hz.
    apply Some_included in Hz.

    destruct Hz as [E|E].
    { left. inversion E. subst. inversion H3. simpl in *.
      constructor. split; eauto. set_solver. }
    { right. rewrite live_included pair_included in E.  destruct E as [? E].
      apply gset_included in E.
      rewrite live_included.
      apply pair_included; split; eauto.
      apply gset_included. set_solver. } }
  { rewrite !lookup_op /map1 lookup_fmap !lookup_insert_ne // lookup_empty left_id.
    specialize (Hz l').
    rewrite !lookup_op /map1 lookup_fmap !lookup_insert_ne // lookup_empty left_id in Hz.
    eauto. }
Qed.

Local Lemma hard_update k η π r l q S g ρ μ :
  k !! π = Some r ->
  dom k ⊆ dom η ->
  l ∉ xroot r ->
  mirror k η ρ ->
  ρ !! l = Some g ->
  dom ρ ## dom μ ->
  ● (map1 ρ ⋅ μ) ⋅ ◯ {[l := live (q, S)]} ~~>:
    (λ x, ∃ ρ', x = ● (map1 ρ' ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]} ∧ mirror k η ρ' /\ dom ρ = dom ρ').
Proof.
  intros ? Hη ? ? Hl Hd.
  apply cmra_discrete_updateP.

  (* We reason over a possible frame [z] *)
  intros z Hz.
  destruct z as [z x].
  destruct z as [q'|].
  (* If z is a black one, not possible. *)
  { exfalso. by eapply not_black. }
  (* if z is a white one *)
  { rewrite -assoc -auth_frag_op in Hz.
    apply auth_both_valid_discrete in Hz.
    destruct Hz as (Hz,Hv).

    assert (l∈dom ρ) by eauto.

    assert (✓(map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ)) by eauto using valid1.
    rewrite lookup_included in Hz.

    destruct_decide (decide (l ∈ dom x)).
    { destruct (x!!l) as [|] eqn:E'.
      2:{ rewrite -not_elem_of_dom in E'. set_solver. }

      destruct c as [ (q',c) | | ]; [ | exfalso | exfalso ].
      2,3:specialize (Hz l); apply cmra_valid_included in Hz; [ | apply Hv].
      2,3: rewrite lookup_op E' lookup_insert in Hz; inversion Hz.

      destruct_decide (decide (π ∈ c)).
      { eauto 15 using valid2. }

      { exists (● (map1 (<[l:=(g ∖ {[π]})]>ρ)  ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]}).
        split; eauto using valid3.
        eexists _. split; eauto. destruct r. split; eauto.
        eapply  mirror_clean; eauto; set_solver.
        rewrite dom_insert_L.  set_solver. } }
    { exists (● (map1 (<[l:=(g ∖ {[π]})]>ρ) ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]}).
      split; eauto using valid4.
      eexists _. split; eauto. destruct r.
      split; eauto.
      eapply  mirror_clean; eauto; set_solver.
      rewrite dom_insert_L; set_solver. } }
Qed.

(* The supd version should be preferred *)
Local Lemma interp_clean mt (k:ctx) e (σ:store) S l q π lk lt :
  k !! π = Some (lk,lt) ->
  l ∉ lt ->
  interp mt true k e σ ∗ l ⟸{q} S ==∗ interp mt true k e σ ∗ l ⟸{q} (S ∖ {[π]}).
Proof.
  iIntros (? ?) "[Hi Hn]".
  destruct_interp "Hi".

  (* is l an invisible root ? *)
  destruct_decide (decide (l ∈ dom lk)) as Hlk.
  { iDestruct (big_sepM_lookup_acc _ k with "[$]") as "[X Hback]".
    { eauto. }
    simpl.

    destruct (lk !! l) as [q'|] eqn:E'.
    2:{ apply not_elem_of_dom in E'. set_solver. }

    iDestruct (big_sepM_lookup_acc with "X") as "(?& Hback')". done.
    iDestruct (pbt_join with "[$]") as "?".
    replace ({[π]} ∪ S) with ({[π]} ∪ (S ∖{[π]})).
    2:{ rewrite (comm_L _ {[π]}) -(difference_union). set_solver. }
    iDestruct (pbt_split with "[$]") as "(?&?)".
    iFrame.

    iSpecialize ("Hback'" with "[$]").
    iSpecialize ("Hback" with "[$]").

    iExists _,τ,ρ,η. iFrame. iPureIntro. eauto 15. }
  { (* We need to analyse whether or not we remove the binding (loc,π) in ρ *)
    iDestruct "Hk" as "[% (%&Ha)]".
    iDestruct "Hn" as "[% (%&Hn)]".
    iDestruct (pbt_precise_exploit_core with "[$]") as "%Hv". naive_solver.
    iDestruct (own_op with "[Ha Hn]") as "?".
    { iFrame "Ha". iFrame. }
    iMod (@own_updateP _ _ _ (fun x => exists ρ', x = (● (map1 ρ' ⋅ μ) ⋅ ◯ {[l := live (q, S' ∖ {[π]})]})/\  mirror k η ρ' /\ dom ρ = dom ρ') γctx with "[$]") as "Hk".
    { destruct Hv as (?&?&(?,(?&?))).
      destruct Hρ as [Hm _]. destruct Hdebt.
      eapply hard_update; eauto; set_solver. }

    destruct Hρ as [? ?].

    iDestruct "Hk" as "[% [%E' Hk]]".
    destruct E' as (ρ',(->&?&Eq)).
    iDestruct "Hk" as "(? & Hl)".
    iSplitR "Hl".
    2:{ iExists _. iFrame. iPureIntro. set_solver. }
    iExists _,τ,ρ',_. iFrame.
    iAssert (auth_ctx ρ' (dom σ)) with "[-]" as "?".
    { iExists _. iFrame. rewrite -Eq. iFrame "%". }
    iFrame. iPureIntro.
    split_and !; eauto using synchro_dead_same_dom.
    constructor; eauto. }
Qed.

Local Lemma another_hard_update π l q S ρ μ g D k lk lt η :
  k !! π = Some (lk,lt) ->
  η !! π = Some (Some D) ->
  ρ !! l = Some g ->
  μ !! l = None ->
  mirror k η ρ ->
  dom ρ ## dom μ ->
  ● (map1 ρ ⋅ μ) ⋅ ◯ {[l := live (q, S)]} ~~>:
    (λ x, ∃ ρ', x = ● (map1 ρ' ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]} /\ mirror k (<[π:=Some (D ∪ {[l]})]> η) ρ' /\ dom ρ = dom ρ').
Proof.
  intros Hk HD H1 H2 Hm Hd.
  apply cmra_discrete_updateP.

  (* We reason over a possible frame [z] *)
  intros z Hz.
  destruct z as [z x].
  destruct z as [q'|].
  (* If z is a black one, not possible. *)
  { exfalso. by eapply not_black. }
  (* if z is a white one *)
  { rewrite -assoc -auth_frag_op in Hz.
    apply auth_both_valid_discrete in Hz.
    destruct Hz as (Hz,Hv).

    assert (l∈dom ρ) by eauto.

    assert (✓(map1 (<[l:=g ∖ {[π]}]> ρ) ⋅ μ)) by eauto using valid1.

    rewrite lookup_included in Hz.

    destruct_decide (decide (l ∈ dom x)).
    { destruct (x!!l) as [|] eqn:E'.
      2:{ rewrite -not_elem_of_dom in E'. set_solver. }

      destruct c as [ (q',c) | | ]; [ | exfalso | exfalso ].
      2,3:specialize (Hz l); apply cmra_valid_included in Hz; [ | apply Hv].
      2,3: rewrite lookup_op E' lookup_insert in Hz; inversion Hz.

      destruct_decide (decide (π ∈ c)).
      { exists (● (map1 ρ ⋅ μ) ⋅ ◯ {[l :=live (q, S ∖ {[π]})]}).
        split; eauto 15 using valid2.
        eexists. split_and !; try done.
        { intros π' l' r' x'. rewrite lookup_insert_case.
          case_decide; subst; eauto.
          { intros Hk'. rewrite Hk in Hk'. inversion Hk'. inversion 1. subst.
            intros. eapply Hm; try done. set_solver. } } }
      { exists (● (map1 (<[l:=(g ∖ {[π]})]>ρ) ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]}).
        split; eauto using valid3.
        eexists _. split_and !; eauto.
        { intros π' l' r' x'. rewrite lookup_insert_case. case_decide; subst.
          { rewrite Hk. do 2 inversion 1. subst.
            destruct_decide (decide (l=l')); subst.
            { rewrite lookup_total_insert. set_solver. }
            simpl. rewrite lookup_total_insert_ne //.
            intros. eapply Hm; try done. simpl. set_solver. }
          { intros. destruct_decide (decide (l=l')); subst.
            { rewrite lookup_total_insert. apply elem_of_difference.
              split; last set_solver.
              specialize (Hm π' l' _ _ H6 H7).
              rewrite lookup_total_alt H1 in Hm. eauto. }
            { rewrite lookup_total_insert_ne //. eauto. } } }
        rewrite dom_insert_lookup_L //. } }
    { exists (● (map1 (<[l:=(g ∖ {[π]})]>ρ) ⋅ μ) ⋅ ◯ {[l := live (q, S ∖ {[π]})]}).
      split; eauto using valid4.
      eexists _. split_and !; eauto.
      { intros π' l' (lk',lt') x'. rewrite lookup_insert_case.
        case_decide; subst.
        { rewrite Hk. do 2 inversion 1. subst. simpl.
          destruct_decide (decide (l=l')); subst.
          { rewrite lookup_total_insert. set_solver. }
          { rewrite lookup_total_insert_ne //. intros.
            eapply Hm; try done. simpl. set_solver. } }
        { intros. simpl in *.
          destruct_decide (decide (l=l')); subst.
          { rewrite lookup_total_insert. apply elem_of_difference.
            split; last set_solver.
            specialize (Hm π' l' _ _ H5 H6).
            rewrite lookup_total_alt H1 in Hm. eauto.  }
          { rewrite lookup_total_insert_ne //. intros.
            eapply Hm; try done. } } }
      { rewrite !dom_insert_lookup_L //. } } }
Qed.

(* The supd version should be preferred *)
Local Lemma interp_clean_debt b mt (k:ctx) e (σ:store) S l q π D :
  interp mt b k e σ ∗ l ⟸{q} S ∗ inside π D ==∗ interp mt b k e σ ∗ l ⟸{q} (S ∖ {[π]}) ∗ inside π (D ∪ {[l]}).
Proof.
  iIntros "(Hi&[% (%&Hn)]&?)".
  destruct_interp "Hi".

  iDestruct (ghost_map_lookup with "Hinside [$]") as "%".
  iMod (ghost_map_update with "Hinside [$]") as "(?&Hde)".
  iFrame "Hde".

  assert (∃ x, k !! π = Some x) as ((lk,lt),?).
  { apply elem_of_dom. destruct Hρ as [_ _ ->]. eauto using elem_of_dom. }

  iDestruct "Hk" as "[% (%E&Ha)]".
  iDestruct (pbt_precise_exploit_core with "[$]") as "%Hv".
  { naive_solver. }
  iDestruct (own_op with "[Hn Ha]") as "?". by iFrame.
  destruct Hv as (?&?&?&?&?&_).
  iMod (@own_updateP _ _ _ (fun x => exists ρ', x = (● (map1 ρ' ⋅ μ) ⋅ ◯ {[l := live (q, S' ∖ {[π]})]}) /\ mirror k (<[π:=Some (D ∪ {[l]})]> η) ρ' /\ dom ρ = dom ρ') γctx with "[$]") as "Hk".
  { destruct Hρ. eapply another_hard_update; eauto. }

  iDestruct "Hk" as "[% (%X&Hk)]". destruct X as [ρ' (->&?&?)].
  iDestruct "Hk" as "(Ha&E)".
  iSplitR "E".
  2:{ iExists _. iFrame. iPureIntro. set_solver. }
  iAssert (auth_ctx ρ' (dom σ)) with "[Ha]" as "?".
  { iExists _.  iFrame. iPureIntro. split. set_solver. naive_solver. }
  iModIntro. iExists _,_,ρ',_. iFrame "∗%".
  iPureIntro. split_and !; eauto using debt_update_Some, synchro_dead_same_dom.
  { inversion Hρ. constructor; eauto.
    rewrite dom_insert_lookup_L //. }
  { eapply linked_dig_debt; eauto. set_solver. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Derived lemmas. *)

Lemma supd_clean l q S i V :
  l ∉ V ->
  l ⟸{q} S =[true|i|V]=∗ l ⟸{q} (S ∖ {[i]}).
Proof.
  iIntros (?) "?". iIntros.
  iMod (interp_clean with "[$]") as "(? & ?)"; eauto.
  by iFrame.
Qed.

Lemma supd_clean_iterated M S i V :
  dom M ∩ V = ∅ ->
  PBT S M =[true|i|V]=∗ PBT (S ∖ {[i]}) M.
Proof.
  pattern M. eapply map_ind.
  { iIntros (?) "?". iIntros. iFrame. iApply PBT_empty. }
  { iIntros (? ? ? ? IH Hd) "HBPT".
    iIntros.
    iDestruct (PBT_insert1 with "[$]") as "(? & ?)".
    { eauto using not_elem_of_dom. }
    rewrite /PBT big_sepM_singleton.
    iMod (supd_clean with "[$] [%//] [$]") as "(? & ?)".
    { set_solver. }
    iMod (IH with "[$] [%//] [$]") as "(? & ?)". set_solver.
    iFrame. iModIntro.
    iApply PBT_insert2.
    { eauto using not_elem_of_dom. }
    iFrame. by iApply big_sepM_singleton. }
Qed.

Lemma supd_vclean v q S i V :
  (locs v) ∩ V = ∅ ->
  v ⟸?{q} S =[true|i|V]=∗ v ⟸?{q} (S ∖ {[i]}).
Proof.
  intros Hv.
  destruct_decide (decide (is_loc v)) as Eq.
  { apply is_loc_inv in Eq. destruct Eq as (?,?). subst. apply supd_clean. set_solver. }
  { iIntros "?". iIntros. rewrite !vpbt_not_loc //. by iFrame. }
Qed.

Lemma tupd_clean_debt l q S D π:
  l ⟸{q} S ∗ inside π D =[#]=∗ l ⟸{q} (S ∖ {[π]}) ∗ inside π (D ∪ {[l]}).
Proof.
  iIntros "(?&?)". iIntros.
  iMod (interp_clean_debt with "[$]") as "(?&?&?)".
  by iFrame.
Qed.

Lemma tupd_vclean_debt v q S D π :
  v ⟸?{q} S ∗ inside π D =[#]=∗ v ⟸?{q} (S ∖ {[π]}) ∗ inside π (D ∪ locs v).
Proof.
  iIntros "(?&?)". iIntros.
  destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv. subst.
    iMod (tupd_clean_debt with "[$][$]"). auto_locs. by iFrame. }
  rewrite locs_no_loc // right_id_L. rewrite !vpbt_not_loc //. by iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* Transfers *)

Lemma pbt_transfer π V S1 S2 k1 l q :
  π ∈ S1 -> V ⊆ dom k1 ->
  PBT S1 k1 ∗ pbt l q S2 =[true | π | V ]=∗ PBT S1 k1 ∗ pbt l q (S2∖{[π]}) .
Proof.
  iIntros (??) "(?&?)". iIntros.
  destruct_decide (decide (l ∈ V)).
  { assert (l ∈ dom k1) as Hl by set_solver.
    apply elem_of_dom in Hl. destruct Hl as (q',Hl).
    iDestruct (PBT_borrow_pbt _ k1 with "[$]") as "(?&Hback)". eauto.
    iDestruct (pbt_exchange with "[$][$]") as "(?&?)". eauto. iFrame.
    iApply "Hback". by iFrame. }
  { iMod (interp_clean with "[$]") as "(?&?)"; last by iFrame. eauto. eauto. }
Qed.

Lemma PBT_transfer k1 k2 π V S1 S2  :
  π ∈ S1 -> V ⊆ dom k1 ->
  PBT S1 k1 ∗ PBT S2 k2 =[true | π | V ]=∗ PBT S1 k1 ∗ PBT (S2∖{[π]}) k2.
Proof.
  pattern k2. apply map_ind.
  { iIntros (??) "(?&?)". iIntros. iFrame. iApply PBT_empty. }
  { iIntros (l ??? IH ??) "(H1&?)". iIntros.
    iDestruct (PBT_insert1 with "[$]") as "(?&H2)".
    { by apply not_elem_of_dom. }
    rewrite -pbt_PBT.
    iMod (pbt_transfer with "[H1 H2][%//][$]") as "(?&?&?)". 3:iFrame "H1". 3:iFrame.
    eauto. eauto.
    iMod (IH with "[$][%//][$]") as "(?&?&?)"; eauto. iFrame.
    iApply  PBT_insert2. { by apply not_elem_of_dom. }
    rewrite -pbt_PBT. by iFrame. }
Qed.

Lemma vpbt_PBT_transfer π V v p S1 S2 k2 :
  π ∈ S1 -> V ⊆ locs v ->
  v ⟸?{p} S1 ∗ PBT S2 k2 =[true | π | V ]=∗ v ⟸?{p} S1 ∗ PBT (S2∖{[π]}) k2.
Proof.
  iIntros (??) "(X1&X2)". iIntros.
  destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv as (l,?). subst. simpl.
    rewrite pbt_PBT.
    iMod (PBT_transfer {[l:=p]} k2 with "[$][%//][$]") as "(?&?&?)". eauto. set_solver.
    by iFrame.  }
  { iMod (supd_clean_iterated with "[$][%//][$]") as "(?&?)". apply locs_no_loc in Hv. subst. set_solver.
    by iFrame. }
Qed.

Lemma PBT_vpbt_transfer v p k1 S1 S2 π V :
  π ∈ S1 -> V ⊆ dom k1 ->
  PBT S1 k1 ∗ v ⟸?{p} S2 =[true | π | V ]=∗ PBT S1 k1 ∗ v ⟸?{p} (S2∖{[π]}).
Proof.
  iIntros (??) "(?&?)". iIntros (??????) "Hi".
  destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv as (l,->).
    simpl. rewrite !pbt_PBT.
    iApply (PBT_transfer k1 {[l:=p]} with "[$][%//][$]"); eauto. }
  { iFrame. destruct v; eauto. exfalso. naive_solver. }
Qed.

Lemma vpbt_transfer  v1 v2 p1 p2 S1 S2 π V :
  π ∈ S1 -> V ⊆ locs v1 ->
  v1 ⟸?{p1} S1 ∗ v2 ⟸?{p2} S2 =[ true | π | V ]=∗ v1 ⟸?{p1} S1 ∗ v2 ⟸?{p2} (S2 ∖ {[π]}).
Proof.
  iIntros (? HV) "(?&?)". iIntros.
  destruct_decide (decide (is_loc v2)) as Hv.
  2:{ do 2 rewrite (vpbt_not_loc _ _ v2) //. by iFrame. }
  apply is_loc_inv in Hv. destruct Hv. subst.
  destruct_decide (decide (is_loc v1)) as Hv'.
  { apply is_loc_inv in Hv'. destruct Hv'. subst.
    simpl. rewrite pbt_PBT.
    iApply (pbt_transfer _ _ _ _ {[ x0 := p1 ]} with "[$][%//][$]"). all:set_solver. }
  { rewrite locs_no_loc // in HV. assert (V = ∅) by set_solver. subst.
    iMod (interp_clean _ _ _ _ _ x with "[$]") as "(?&?)"; last by iFrame. done. set_solver. }
Qed.

Lemma debt_transfer l p S π D:
  inside π D ∗ l ⟸{p} S =[#]=∗ inside π (D ∖ {[l]}) ∗ l ⟸{p} (S ∪ {[π]}).
Proof.
  iIntros "(D&[% (%HS&Hn)])". iIntros (?????) "Hi".
  iMod (pbt_precise_approx {[π]} with "[$]") as "(Hi&Hn)".
  destruct_interp "Hi".
  iDestruct (pbt_precise_exploit with "[$]") as "%X".
  destruct X as (x&Hl1&Hl2).
  iDestruct (ghost_map.ghost_map_lookup with "Hinside D") as "%".
  iMod (ghost_map.ghost_map_update with "Hinside D") as "(?&?)".
  iFrame. iModIntro. iSplitR "Hn".
  2:{ iExists _. iFrame. iPureIntro. set_solver. }
  iExists ms,τ,ρ,_. iFrame "∗%".
  iPureIntro. split_and !.
  { inversion Hρ. constructor; eauto.
    { intros i l' (?&?) o Hi. simpl. rewrite lookup_insert_case.
      case_decide; eauto. subst.
      inversion 1. subst. destruct_decide (decide (l=l')); subst.
      { intros _. rewrite lookup_total_alt Hl1. set_solver. }
      { intros. eapply ri_mirror; eauto. set_solver. } }
    { rewrite dom_insert_lookup_L //. } }
  { inversion Hdebt. constructor; try done. rewrite dom_insert_lookup_L //.
    intros ????. rewrite lookup_insert_case. case_decide; last naive_solver.
    subst. eapply de_ok in H; try done. naive_solver. }
  { inversion Hτ. constructor; eauto.
    intros l'. rewrite elem_of_image_less. intros (i&o&Hi&Hr). unfold xroot_less in *. simpl in *.
    destruct_decide (decide (l'=l)); subst.
    { intros X. apply Htauro in X. assert (l ∉ dom ρ) as X0 by naive_solver.
      apply not_elem_of_dom in X0. congruence. }
    eapply linked_roo. apply elem_of_image_less. exists i,o. split; first done.
    unfold xroot_less in *.
    destruct_decide (decide (i=π)); subst.
    { rewrite lookup_total_insert in Hr. rewrite lookup_total_alt H. set_solver. }
    { rewrite lookup_total_insert_ne // in Hr. } }
Qed.

Lemma debt_vtransfer v p S π D:
  inside π D ∗ v ⟸?{p} S =[#]=∗  inside π (D ∖ locs v) ∗ v ⟸?{p} (S ∪ {[π]}).
Proof.
  iIntros "(?&?)". iIntros. destruct_decide (decide (is_loc v)) as Hv.
  { apply is_loc_inv in Hv. destruct Hv as (?&?). subst.
    auto_locs. iApply (debt_transfer with "[$][$]"). }
  rewrite locs_no_loc // difference_empty_L. iFrame. destruct v; done.
Qed.

End Wp_clean.
