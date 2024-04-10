From iris.algebra Require Import auth gset gmap.
From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import proofmode.

From irisfit Require Import hypotheses successors predecessors stdpp.
From irisfit.spacelang Require iris.
From irisfit.lib Require Import qz qz_cmra smultiset fracset.
From irisfit Require Import more_maps_and_sets tied more_cmras.

(* This module sets-up the machinery needed for the store.
   It provides traditional points-to assertions through the Iris gen_heap:
   https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.gen_heap.html

   Moreover, a ghost mapping [π] of each memory location to its predecessors is maintained.
   In the user's eyes, this is done via "mapsfrom" assertion [l' ↤{q} ls]. The file's name,
   [ph], stands for "predecessor heap".

   These mapsfrom assertion are non-standard in two points:
   + First, predecessors are represented as signed multisets.
   + They can come with a null fraction, in that case with only a negative multiset.
     This property is enforced by fracset. *)

(* Suppose [L] is the type of memory locations, and [B] is the type of blocks
   stored in the heap, so the heap is a finite map of [L] to [B]. *)

(* ------------------------------------------------------------------------ *)

(* We want every memory location [l] to carry a ghost field [predecessors]
   that contains a multiset of locations: the predecessors of the location
   [l] in the heap. *)

(* Furthermore, we want to be able to split the ownership of this field,
   so that partial ownership of the [predecessors] field yields partial
   knowledge of the predecessors (and still allows updates), while full
   ownership of the [predecessors] field yields full knowledge of the
   predecessors. *)

(* Moreover, we want to generate some "permission to remove a location l
   from the multiset of predecessors". This is made possible using signed multisets
   with fraction zero. *)

(* These considerations lead us to using the following CMRA: *)

Notation predR L :=
  (authUR (gmapUR L (fracsetUR L))).

(* ------------------------------------------------------------------------ *)
From irisfit.language Require Import syntax store.

(* This is our view of the heap. *)

Class phG Σ := PhG {
  (* The predecessor resource, described above. *)
  phG_pred : inG Σ (predR loc);
  (* A ghost memory location that holds the predecessor mapping. *)
  phG_pred_name : gname;
}.

(* Make only the last argument explicit. *)
Arguments phG_pred      {Σ} _ : assert.
Arguments phG_pred_name {Σ} _ : assert.

#[export] Existing Instance phG_pred.

(* ------------------------------------------------------------------------ *)

(* Assumptions and definitions. *)

Section ReasoningRules.

  (* A heap [σ] is a finite map of locations to blocks. *)
Implicit Types σ : gmap loc block.

(* A logical heap [α] is a finite map of locations to list of values. *)
Implicit Types α : gmap loc (list val).

Implicit Types ρ : gset loc.

(* A predecessor map [π] is a finite map of locations to multisets
   of locations. *)
Implicit Types π : gmap loc (gmultiset loc).

(* A signed predecessor map [μ] is a finite map of locations to signed
   multisets of locations. *)

Implicit Types μ : gmap loc (fracset loc).

(* We write [ls] and [ps] for signed multisets of locations. *)

Implicit Types ls ps : smultiset loc.

(* We write [fs] for fracset. *)
Implicit Types fs : fracset loc.

(* We write [fs] for gmultiset. *)
Implicit Types gs : gmultiset loc.

(* We use [p] for non-null fractions *)
Implicit Types p : dfrac.
(* We use [q] for possibly null fractions *)
Implicit Types q : Qz.

(* ------------------------------------------------------------------------ *)
(* A helper lemma *)
Lemma invariant_dom σ π :
  invariant σ π ->
  dom π ⊆ dom σ.
Proof. intros [[] ]. eauto. Qed.

(* ------------------------------------------------------------------------ *)

(* Our store interpretation predicate includes: 1- the standard store
   interpretation predicate [gen_heap_interp σ]; 2- the assertion [auth π],
   which represents the authoritative ownership of the ghost cell γ and
   holds the predecessor map π; 3- an invariant that ties [σ] and [π]. *)

Context `{ fG : !phG Σ }.

Notation γ      := (phG_pred_name fG).

(* ------------------------------------------------------------------------ *)

(* [pred σ π] asserts authoritatively the existence of all predecessors in π, plus
   some other fracsets in μ. All of these fracsets are tied, see tied.v . *)
Definition pred σ π : iProp Σ :=
  ∃ μ, ⌜tied σ μ⌝ ∗ @own _ _ (phG_pred fG) γ (● ((full_gmultiset <$> π) ⋅ μ)).

(* The interpretation of the store: defines the authoritative assertions
   for mapsto (via gen_heap_interp) and mapsfrom (via pred) and links the two
   (via invariant) *)
Definition ph_interp σ : iProp Σ :=
(∃ π, pred σ π ∗ ⌜invariant σ π⌝).

(* ------------------------------------------------------------------------ *)

(* The predicate [mapsfrom l q ls] represents partial ownership of the
   ghost field [l.predecessors], and stores that the signed multiset [ls] is one
   share of the multiset [l.predecessors].
   As "one share" of a signed multiset is unclear, see [exploit_mapsfrom]
   for its formal meaning. *)

Definition mapsfrom l q ls : iProp Σ :=
  ∃ alln,
  own γ (◯ {[l := mk_nf q ls alln]}).

Notation "l ↤{ q } ls" :=
  (mapsfrom l q%Qz ls)
  (at level 20, format "l  ↤{ q }  ls")
: bi_scope.

Notation "l ↤ ls" :=
  (mapsfrom l 1%Qz ls)
  (at level 20, format "l  ↤  ls")
: bi_scope.

(* An abstraction of the previous assertion: in [mapsfrom_set l q ls],
   [ls] is a set, as opposed to a multiset. Thus, the multiplicity of
   each predecessor is unknown. *)

(* TODO propose a notation *)

Definition mapsfrom_set l q locs : iProp Σ :=
  ∃ ps, l ↤{q} ps ∗ ⌜ dom ps ⊆ locs ⌝.

(* ------------------------------------------------------------------------ *)

(* The mapsfrom assertion is proper with respect to signed multisets. *)
Global Instance proper_mapsfrom x q : Proper (equiv ==> equiv) (mapsfrom x q).
Proof.
  intros X Y HXY.
  eapply bi.equiv_entails_2; iIntros "H"; iDestruct "H" as (pi) "H".
  - assert ({[x := mk_nf q X pi ]} ≡ {[x := mk_nf q Y (alln_upd HXY pi) ]}) as ->.
    { apply gmap_equiv_singleton.
      now constructor. }
    iExists _; iFrame.
  - symmetry in HXY.
    assert ({[x := mk_nf q Y pi ]} ≡ {[x := mk_nf q X (alln_upd HXY pi) ]}) as ->.
    { apply gmap_equiv_singleton.
      now constructor. }
    iExists _. iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* Combining two [mapsfrom] assertions. *)

Lemma mapsfrom_join l' q1 q2 ls1 ls2 :
  l' ↤{q1} ls1 -∗ l' ↤{q2} ls2 -∗
  l' ↤{q1+q2} (ls1 ⊎ ls2).
Proof.
  iIntros "[%a1 H1] [%a2 H2]".
  iCombine "H1 H2" as "H".
  iExists _. iFrame.
Qed.

(* Splitting a [mapsfrom] assertion.
   The precondition is richer, remember that we are working with fracset:
   if the fraction is null, then the support must be negative *)

Lemma mapsfrom_split l q ls q1 q2 ls1 ls2 :
  (q1 = 0%Qz -> AllNeg ls1) ->
  (q2 = 0%Qz -> AllNeg ls2) ->
  (q = q1 + q2)%Qz →
  ls ≡ ls1 ⊎ ls2 →
  l ↤{q} ls -∗
  l ↤{q1} ls1 ∗ l ↤{q2} ls2.
Proof.
  intros Hq1 Hq2 ? ->. intros. subst. iIntros "[%a H]".

  assert ({[l := mk_nf (q1 + q2)%Qz (ls1 ⊎ ls2) a]} ≡
            ({[l := mk_nf q1 ls1 Hq1]} ⋅ ({[l := mk_nf q2 ls2 Hq2]}))) as ->.
  { rewrite singleton_op.
    apply gmap_equiv_singleton.
    now constructor. }
  rewrite auth_frag_op own_op.
  iDestruct "H" as "[H1 H2]".
  iSplitL "H1"; iExists _; iFrame.
Qed.

(* A special case, when splitting a negative part *)
Lemma mapsfrom_split_neg ls1 ls2 l q ls :
 (q = 0%Qz -> AllNeg ls1) ->
  AllNeg ls2 ->
  ls ≡ ls1 ⊎ ls2 →
  l ↤{q} ls -∗
  l ↤{q} ls1 ∗ l ↤{0} ls2.
Proof.
  intros ? ? ->. apply mapsfrom_split; eauto.
  by rewrite right_id.
Qed.

(* The combination of the previous two lemmas. *)
Lemma mapsfrom_join_equiv l' q q1 q2 ls ls1 ls2 :
  (q1 = 0%Qz -> AllNeg ls1) ->
  (q2 = 0%Qz -> AllNeg ls2) ->
  (q1+q2)%Qz = q →
  ls1 ⊎ ls2 ≡ ls →
  l' ↤{q1} ls1 ∗ l' ↤{q2} ls2 ⊣⊢ l' ↤{q} ls.
Proof.
  intros ? ? ? <-. subst. iSplit.
  { iIntros "[H1 H2]".
    iDestruct (mapsfrom_join with "H1 H2") as "H". iFrame. }
  { iApply mapsfrom_split; eauto. }
Qed.

(* The special case where all multisets are empty. *)

Lemma mapsfrom_split_empty l q1 q2 :
  l ↤{q1} ∅ ∗ l ↤{q2} ∅ ⊣⊢ l ↤{q1 + q2} ∅.
Proof.
  now apply mapsfrom_join_equiv.
Qed.

(* We can always weaken a mapsfrom assertion. *)
Lemma mapsfrom_weak ls1 ls2 l q :
  (q = 0%Qz -> AllNeg ls2) ->
  (* NB this is not inclusion of signed multisets. *)
  (* TODO notation <= *)
  (forall x, multiplicity x ls1 <= multiplicity x ls2)%Z ->
  l ↤{q} ls1 ⊢
    l ↤{q} ls2.
Proof.
  iIntros (? ?) "?".
  iDestruct (mapsfrom_split_neg ls2 (ls1 ⊎ opposite ls2) with "[$]") as "[? ?]"; eauto.
  all:smultiset_solver.
Qed.

Local Lemma mapsfrom_weak_paper l l' q ls :
  q ≠ 0%Qz ->
  l ↤{q} ls ⊢
  l ↤{q} (ls ⊎ {[+l'+]}).
Proof.
  intros.
  apply mapsfrom_weak. naive_solver.
  intros x.
  rewrite multiplicity_disj_union multiplicity_psingleton_case.
  case_decide; lia.
Qed.

Lemma mapsfrom_correct l q ls :
  l ↤{q} ls -∗ ⌜q = 0%Qz -> AllNeg ls⌝.
Proof.
  iIntros "[%E ?]". easy.
Qed.

(* ------------------------------------------------------------------------ *)

(* Exploiting an exact [mapsfrom] assertion. *)

Lemma option_included_Some_l_unital `{A:ucmra} (x:A) (y:option A) :
  Some x ≼ y -> exists y', y = Some y' /\ x ≼ y'.
Proof.
  intros Hx.
  apply option_included in Hx. destruct Hx as [|(a,(b,(Ha&?&Ho)))]; subst; try easy.
  injection Ha; intros ->.
  eexists. split; try easy.
  destruct Ho; try easy.
  exists ε. rewrite right_id //.
Qed.

Lemma exploit_frac_null μ fs q l :
  q = frac fs ->
  all_neg μ ->
  Some fs ≼ μ !! l ->
  q = 0%Qz.
Proof.
  intros ? Hn Hleq; subst.
  apply (@option_included_Some_l_unital (nfracUR (@smultisetUR loc _ _))) in Hleq.
  destruct Hleq as (nfr,(Hin&Hleq)).
  assert (frac nfr = 0%Qz) as Hq' by eauto.
  apply nfrac_frac_le in Hleq.
  apply Qz_le_zero.
  rewrite -Hq' //.
Qed.

(* This is a very precise storement, unveiling μ. Use it at your own risk. *)
Lemma exploit_mapsfrom_precise σ π q l ls :
  dom π ⊆ dom σ ->
  q <> 0%Qz ->
  pred σ π -∗
  mapsfrom l q ls -∗
  ∃ μ gs ns,
    ⌜ tied σ μ /\ π !! l = Some gs /\ μ !! l = Some ns /\
      (q = 1%Qz -> (of_gmultiset gs ⊆ (ls ⊎ opposite (supp ns)))) ⌝
     ∗ own γ (● ((full_gmultiset <$> π) ⋅ μ)) ∗ mapsfrom l q ls.
Proof.
  iIntros (Hinv Hq) "[%μ [%Hμ Hauth]] Hfrag".
  iDestruct "Hfrag" as (pr) "Hfrag".
  iDestruct (own_valid_2 with "Hauth Hfrag") as "%Hv".

  assert (exists gs ns, π !! l = Some gs /\ μ !! l = Some ns
                   /\ (q=1%Qz -> of_gmultiset gs ⊆ (ls ⊎ opposite (supp ns)))) as (ps,(ns,?)).
  2:{ iExists _, _,_. iFrame. iSplitR "Hfrag"; try iExists _; eauto. }

  (* Confront the authoritative element and the fragmentary element. *)
  apply auth_both_valid_discrete in Hv. destruct Hv as [Hv _].

  (* Perform lots of destruction. *)
  rewrite singleton_included_l in Hv.
  destruct Hv as [y [Hlookup Hord]].

  rewrite Some_included_total in Hord.
  rewrite lookup_op lookup_fmap in Hlookup.

  destruct Hμ as [Hdμ Hneg Hcovers].

  (* We can only be in π, therefore in μ *)
  destruct (π !! l) as [|] eqn:Hπl.
  { assert (l ∈ dom π) by (eauto with in_dom).
    assert (exists ns, μ !! l = Some ns) as (ns,Hμl).
    { apply elem_of_dom. set_solver. }
    rewrite Hμl.
    eexists _,_. do 2 (split; try easy).

    rewrite Hμl -Some_op in Hlookup.
    rewrite inj_iff in Hlookup.

    specialize (Hcovers l).
    rewrite Hμl in Hcovers.
    specialize (Hneg l _ Hμl).
    simpl in *.

    assert (frac y = 1%Qz) as Hy.
    { apply nfrac_equiv_frac in Hlookup.
      simpl in Hlookup. rewrite Hneg right_id // in Hlookup. }

    apply nfrac_equiv_supp in Hlookup. simpl in *.
    intros ->.
    apply from_full in Hord; last easy.
    destruct Hord as (z,(Hz1&Hz2&Hz3)).
    rewrite Hz1 in Hlookup. simpl in *.
    smultiset_solver. }
  { exfalso. simpl in Hlookup. rewrite left_id in Hlookup.
    apply Hq.
    eapply (exploit_frac_null μ) with (fs:={| frac := q; supp := ls; neglz := pr |}) (l:=l); try easy.
    rewrite Hlookup.
    apply (@Some_included_2). naive_solver. }
Qed.

(* [freeds σ gs] asserts that all the locations in gs are freed in σ *)
Definition freeds σ gs :=
  forall l, l ∈ gs -> freed σ l.

Lemma abstract_all_freeds σ π μ l gs ns ls:
  μ !! l = Some ns ->
  all_freed σ μ ->
  of_gmultiset gs ⊆ ls ⊎ opposite (supp ns) ->
  ∃ gs', gs ⊆ to_gmultiset ls ⊎ gs' ∧ freeds σ gs'.
Proof.
  intros Hμl Hco ?.
  exists (to_gmultiset (opposite (supp ns))).
  split.
  { smultiset_solver. }
  { intros i Hi.
    specialize (Hco l).
    rewrite Hμl in Hco. smultiset_solver. }
Qed.

(* When confronted with the authoritative assertion [pred σ π], the assertion
   [mapsfrom_exact l' q ls] guarantees that [l'] is in the domain of [π].
   Furthermore, if [q] is 1, then it guarantees that [predecessors π l'] is a subset
   of [ls] plus some deallocated locations. *)
Lemma exploit_mapsfrom σ π l q ls :
  q <> 0%Qz ->
  dom π ⊆ dom σ ->
  pred σ π -∗
  mapsfrom l q ls -∗
  ⌜ ∃ gs, π !! l = Some gs
      ∧ (q = 1%Qz → ∃ gs', gs ⊆ to_gmultiset ls ⊎ gs' ∧ freeds σ gs') ⌝.
Proof.
  iIntros (Hq Hinv) "? ?".
  iDestruct (exploit_mapsfrom_precise with "[$] [$]") as "[%μ [%gs [%ns [%Hmf ?]]]]".
  1,2:easy.
  iPureIntro.
  destruct Hmf as ([]&?&?&?).
  eauto using abstract_all_freeds.
Qed.

(* A simplified corollary of the previous lemma. *)

Local Lemma exploit_mapsfrom_dom_pre σ π l' q ls :
  q <> 0%Qz ->
  dom π ⊆ dom σ ->
  pred σ π -∗
  l' ↤{q} ls -∗
  ⌜ l' ∈ dom π ⌝.
Proof.
  iIntros.
  iDestruct (exploit_mapsfrom with "[$] [$]") as %(? & Heq & ?);
    rewrite ?elem_of_dom ?Heq; eauto.
Qed.

Lemma exploit_mapsfrom_dom σ l' q ls :
  q ≠ 0 ->
  ph_interp σ -∗
  l' ↤{q} ls -∗
  ⌜ l' ∈ dom σ ⌝.
Proof.
  iIntros (?) "[%π [[%μ [%Htied Hμ]] %Hinv]] [%a ?]".
  assert (dom π ⊆ dom σ) by (eauto using invariant_dom).
  destruct Htied as [Hd Hn _].
  iDestruct (own_valid_2 with "Hμ [$]") as "%Hv".
  iPureIntro.
  destruct (decide (l' ∈ dom σ)); try easy.
  exfalso.
  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv&_).
  rewrite lookup_included in Hv.
  specialize (Hv l').
  assert (π !! l' = None) as Hπ.
  { apply not_elem_of_dom. set_solver. }
  rewrite lookup_op lookup_singleton lookup_fmap  Hπ left_id_L in Hv.
  eapply exploit_frac_null in Hv; try done.
Qed.

(* ------------------------------------------------------------------------ *)

(* Confronting a [mapsfrom] assertion and a deallocation witness. *)

Lemma exploit_mapsfrom_dag σ l' q ls :
  q <> 0%Qz ->
  ph_interp σ ∗ l' ↤{q} ls ⊢ ⌜∃ b, σ!!l'=Some b /\ b ≠ deallocated⌝.
Proof.
  intros Hq.
  iIntros "(Hh & Hmapsfrom)".
  (* Unfold [ph_interp] to obtain [pred π]. *)
  unfold ph_interp.
  iDestruct "Hh" as (π) "(Hpred & %Hinv)".
  (* Exploit the [mapsfrom] hypothesis. *)
  iDestruct (exploit_mapsfrom _ π l' q ls with "Hpred Hmapsfrom") as %Hm; try easy.
  { eauto using invariant_dom. }
  destruct Hm as (ps & Hπl' & _).
  (* Conclude. [l'] has been freed, so cannot be in the domain of [π].
     Contradiction. *)
  iPureIntro.
  destruct Hinv as (Hco & Hm & _).
  unfold coincidence in Hco.
  destruct Hco as (Hco1 & Hco2).
  assert (l' ∈ dom π) as Hl by eauto with in_dom.
  apply Hco2 in Hl. apply elem_of_dom in Hl. destruct Hl as (b&Hb).
  destruct b; first naive_solver. exfalso. eapply Hco1; eauto with in_dom.
Qed.

(* ------------------------------------------------------------------------ *)
(* More lemmas on mapsfrom *)

Lemma mapsfrom_confront l1 q1 ls1 l2 q2 ls2 :
  (1 < q1 + q2)%Qz -> l1 ↤{q1} ls1 -∗ l2 ↤{q2} ls2 -∗ ⌜l1 ≠ l2⌝.
Proof.
  iIntros (Hlt) "[% ?] [% ?]". rewrite Qz_lt_nge in Hlt.
  iDestruct (own_valid_2 with "[$] [$]") as "%Hv".
  iPureIntro. intros ?. apply Hlt. subst.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
  destruct Hv as (Hv & ?). simpl in *.
  rewrite gfrac_valid in Hv.
  rewrite comm_L. easy.
Qed.

(* ------------------------------------------------------------------------ *)

(* Helper lemma for [pred_alloc]*)
Lemma alloc_fracset_local_update π μ l fs :
  frac fs = 1%Qz ->
  supp fs = ∅ ->
  (<[l:=fs]> ((full_gmultiset <$> π) ⋅ μ), ε : gmap loc (fracset loc)) ~l~>
  ((full_gmultiset <$> <[l:=∅]> π) ⋅ <[l:=ε]> μ, ε).
Proof.
  intros ? Hfs.
  apply local_update_unital_discrete.
  intros z Hv Hz.
  split.
  { apply prove_gmap_valid. intros ? ?.
    rewrite lookup_union_with lookup_fmap lookup_insert_case.
    case_decide.
    { subst. rewrite !lookup_insert. simpl. injection 1. intros <-. easy. }
    { specialize (Hv i). rewrite !lookup_insert_ne //.
      rewrite !lookup_insert_ne // lookup_op lookup_fmap in Hv.
      intros Eq. rewrite -Some_valid -Eq. easy. } }
  rewrite left_id in Hz.
  rewrite -Hz left_id.
  intros x.
  rewrite lookup_union_with lookup_fmap.
  destruct (decide (x=l)); subst; simplify_map_eq.
  { do 2 constructor; simpl.
    { rewrite right_id //. }
    { rewrite ?Hfs; easy. } }
  { by rewrite lookup_union_with lookup_fmap. }
Qed.

(* The authoritative assertion [pred σ π] allows allocation: provided [l] is
   fresh, it can be changed to [pred σ (<[l:=∅]> π)], while producing [l ↤ ∅],
   which witnesses the fact that a newly allocated location has no
   predecessors. *)
Lemma pred_alloc σ π l b :
  l ∉ dom σ →
  b <> deallocated ->
  dom π ⊆ dom σ ->
  pred σ π ==∗
  pred (<[l:=b]> σ) (<[l:=∅]> π) ∗ l ↤ ∅.
Proof.
  intros.
  assert (Hπl: π !! l = None) by (eapply not_elem_of_dom; eauto).
  iIntros "[%μ [%Hμ Hauth]]".

  pose (nf :=  mk_nf 1 (∅:smultiset loc) (fun _ => AllNeg_empty)).
  destruct (μ !! l) as [fs|] eqn:Hμl; last first.
  { iMod (own_update with "Hauth") as "[Hauth Hfrag]".
    { apply auth_update_alloc.
      eapply alloc_singleton_local_update with (i := l) (x := nf); try easy.
      apply not_elem_of_dom. rewrite dom_op dom_fmap_L.
      rewrite not_elem_of_union !not_elem_of_dom //. }
    iSplitL "Hauth"; last first.
    { iExists _. eauto. }
    iExists _. iSplitR.
    { iPureIntro. apply tied_alloc with (x:=ε); try done. left. naive_solver. }
    iApply (own_update with "[$]").
    eapply auth_update_auth.
    now apply alloc_fracset_local_update. }
  { iMod (own_update with "Hauth") as "[Hauth Hfrag]".
    { apply auth_update_alloc with (a':= {[l:=nf]} ⋅ ((full_gmultiset <$> π) ⋅ μ)) (b':={[l:=nf]} ⋅ ∅).
      apply op_local_update_discrete. intros HM.
      assert (((full_gmultiset <$> π) ⋅ μ) !! l = Some fs) as X.
      { rewrite lookup_op lookup_fmap Hπl Hμl //. }
      apply prove_gmap_valid. intros l' x.
      { rewrite lookup_op lookup_insert_case lookup_empty. case_decide.
        { subst l'. rewrite X. simpl. rewrite -Some_op.
          inversion 1. subst. subst nf. destruct Hμ as [X1 X2 X3].
          apply nfrac_valid_alt. simpl. rewrite left_id.
          specialize (HM l). rewrite X Some_valid in HM.
          apply X2 in Hμl. rewrite Hμl //. }
        { rewrite left_id. intros Eq. rewrite -Some_valid -Eq. apply HM. } } }
    rewrite right_id. iModIntro. iSplitR "Hfrag".
    2:{ iExists _. iFrame. }
    assert ({[l := nf]} ⋅ ((full_gmultiset <$> π) ⋅ μ) ≡ (full_gmultiset <$> <[l:=∅]> π) ⋅ μ) as ->.
    { intros l'.
      rewrite !lookup_op !lookup_fmap !lookup_insert_case. case_decide.
      { subst l'. simpl. rewrite Hπl Hμl. simpl. rewrite left_id -!Some_op.
        apply Some_Forall2. constructor. done. simpl. rewrite left_id //. }
      { rewrite lookup_empty left_id //. } }
    iExists _. iFrame. iPureIntro.
    { rewrite -(insert_id μ l fs) //. generalize Hμ. intros.
      apply tied_neg in Hμ.
      apply tied_alloc; eauto. } }
Qed.


(* An interesting lemma. Under the right hypotheses,
   we can delete a location from π and transfer the negative part in μ *)
Lemma dealloc_fracset_update π μ l fs gs (ns:fracset loc) :
  all_neg μ ->
  frac fs = 1%Qz ->
  π !! l = Some gs ->
  μ !! l = Some ns ->
  of_gmultiset gs ⊆ supp fs ⊎ opposite (supp ns) ->
  ((full_gmultiset <$> π) ⋅ μ, {[l := fs]}) ~l~>
  ((full_gmultiset <$> delete l π) ⋅ <[l:=null_neg_part (opposite (supp fs ⊎ opposite (supp ns) ⊎ opposite (of_gmultiset gs))) ]> μ, {[l := ε]}).
Proof.
  intros Hμ Hffs Hns Hπl ?.
  apply local_update_unital_discrete.
  intros z Hv Hz.
  split.
  { apply prove_gmap_valid. intros ? ?.
    rewrite lookup_op lookup_fmap.
    destruct (decide (l=i)); subst.
    { rewrite lookup_delete lookup_insert. injection 1. intros <-. easy. }
    { rewrite lookup_delete_ne // lookup_insert_ne //.
      intros Hv'. rewrite -Some_valid -Hv'.
      specialize (Hv i). rewrite lookup_op lookup_fmap // in Hv. } }
  intros x.
  specialize (Hz x).
  do 2 rewrite lookup_op in Hz. rewrite lookup_fmap in Hz.
  do 2 rewrite lookup_op. rewrite lookup_fmap.
  destruct (decide (l=x)); subst.
  { rewrite lookup_insert lookup_delete. simpl.

    rewrite lookup_insert Hπl Hns in Hz. simpl in Hz.
    rewrite -Some_op in Hz.
    rewrite lookup_singleton.

    assert (frac ns = 0%Qz) as Hfracns by eauto.

    destruct (z !! x) as [zx|] eqn:E; rewrite E.
    { rewrite -Some_op. constructor. rewrite left_id.
      rewrite E -Some_op inj_iff in Hz.

      inversion Hz as [Hf Hs]. simpl in *. clear Hz.
      rewrite Hffs Hfracns right_id in Hf.
      apply  Qz_add_eq_same in Hf.
      constructor; try easy; simpl.
      assert (supp zx ≡ opposite (supp fs ⊎ opposite (supp ns) ⊎ opposite (of_gmultiset gs) )) as Hs'.
      { smultiset_solver. }
      rewrite negative_part_AllNeg.
      { smultiset_solver. }
      { rewrite -Hs'. now apply neglz. } }
    { rewrite E right_id inj_iff in Hz.
      rewrite right_id left_id inj_iff.
      inversion Hz as [? Hs].
      constructor; try easy; simpl in *.
      rewrite negative_part_AllNeg; smultiset_solver. } }
  { rewrite lookup_delete_ne //.
    rewrite lookup_insert_ne // lookup_singleton_ne // left_id.
    rewrite lookup_singleton_ne // left_id in Hz.
    easy. }
Qed.

(* Conversely, the conjunction [pred σ π ∗ l ↤ ls] allows deallocation,
   and produces a witness that the predecessors of [l] form a subset
   of [ls] plus some deallocated locations [gs]. *)
Lemma pred_free_singleton σ π l ls :
  dom π ⊆ dom σ ->
  (forall l, l ∈ ls -> freed σ l) ->
  pred σ π -∗ l ↤ ls ==∗
  pred σ (delete l π) ∗ ⌜ exists gs, predecessors π l ⊆ to_gmultiset ls ⊎ gs /\ freeds σ gs ⌝.
Proof.
  iIntros (??) "Hauth Hpred".
  iDestruct (exploit_mapsfrom_precise _ π with "Hauth Hpred")
    as "[%μ [%ps [%ns [%Hpre [Hauth Hpred]]]]]"; try easy.

  destruct Hpre as (Hti&Hπl&Hμl&Hincl).
  specialize (Hincl eq_refl).
  assert (predecessors π l = ps) as -> by rewrite /predecessors Hπl //.
  iSplitL; last (destruct Hti; eauto using abstract_all_freeds).
  iDestruct "Hpred" as (alln) "Hpred".

  iExists _. iSplitR; last first.
  { iAssert (|==> @own _ _ (phG_pred fG) γ (● ((full_gmultiset <$> delete l π) ⋅ <[l:=null_neg_part (opposite (ls ⊎ opposite (supp ns) ⊎ opposite (of_gmultiset ps)))]> μ)) ∗ @own _ _ (phG_pred fG) γ (◯ {[l := ε]}))%I with "[Hauth Hpred]" as ">[? ?]"; last by iFrame.

    rewrite -own_op.
    iApply (own_update_2 with "[Hauth] [Hpred]"). 2,3:iFrame.
    apply auth_update.
    destruct Hti.
    now eapply dealloc_fracset_update. }
  { iPureIntro. eapply  tied_dealloc; try done.
    { apply H. by apply elem_of_dom. }
    { simpl. intros l'. rewrite !opposite_disj_union !opposite_opposite.
      intros Hl'.
      apply elem_of_negative_part_disj_union in Hl'. destruct Hl' as [Hl'|Hl'].
      2:{ exfalso. rewrite negative_part_of_positive in Hl'; smultiset_solver. }
      apply elem_of_negative_part_disj_union in Hl'. destruct Hl' as [Hl'|Hl'].
      all:apply elem_of_negative_part_weak in Hl'.
      { rewrite elem_of_opposite in Hl'. eauto. }
      { destruct Hti. by eapply tied_cov. } } }
Qed.

(* An iterated version of the previous lemma. *)

Lemma pred_free_group antecedents locs : ∀ σ π,
  dom π ⊆ dom σ ->
  (forall l, l ∈ antecedents -> freed σ l) ->
  pred σ π ∗
  ([∗ set] l ∈ locs, mapsfrom_set l 1%Qz antecedents)
  ==∗
  pred σ (gmap_mdelete locs π) ∗
  ⌜ exists gs, freeds σ gs /\ (∀ l l', l' ∈ locs → l ∈ predecessors π l' → l ∈ antecedents \/ (l ∉ antecedents /\ l ∈ gs)) ⌝.
Proof.
  (* By induction on the set [locs]. *)
  pattern locs. eapply set_ind_L; clear locs.
  (* Case: ∅. *)
  { intros. rewrite gmap_mdelete_empty.
    iIntros "[Hauth _]". iFrame "Hauth".
    iPureIntro. exists ∅. set_solver. }
  (* Case: {[l]} ∪ locs. *)
  { intros l locs ? IH σ π ??.
    rewrite -> big_sepS_union by set_solver.
    rewrite big_sepS_singleton.
    rewrite -> gmap_mdelete_cons' by set_solver.
    iIntros "(Hauth & Hl & Hlocs)".
    rewrite /mapsfrom_set.
    iDestruct "Hl" as (ps) "[Hl %Hps]".
    iMod (pred_free_singleton with "Hauth Hl") as "[Hauth %Hl]"; first easy.
    { intros. apply H1. apply Hps. apply smultiset_elem_of_dom. done. }
    iMod (IH with "[$]") as "[Hauth %Hlocs]".
    { rewrite dom_delete_L. set_solver. }
    { done. }
    iFrame "Hauth". iPureIntro.
    destruct Hl as (ls', (Hincl&Hls')).
    destruct Hlocs as (ls'', (Hls''&?)).
    exists (ls' ⊎ ls'').
    split.
    { intros ?. rewrite gmultiset_elem_of_disj_union. naive_solver. }
    intros m m'. rewrite elem_of_union elem_of_singleton.
    destruct 1.
    + subst. intros Hm.
      eapply gmultiset_elem_of_subseteq in Hm.
      2:apply Hincl.
      apply gmultiset_elem_of_disj_union in Hm.
      destruct_decide (decide (m ∈ antecedents)). left. done.
      right. destruct Hm as [Hm|Hm].
      { exfalso. apply H3.  apply Hps, dom_to_gmultiset, gmultiset_elem_of_dom. easy. }
      { multiset_solver. }
    + rewrite <- (predecessors_delete_ne _ l) by set_solver.
      multiset_solver. }
Qed.

(* If the predecessor set of [l'] is [gs1] and if we hold a share
   [ls1] of it, then we can update this to [gs2] and [ls2], provided
   [gs1 ⊎ ls2 = gs2 ⊎ ls1] holds. This expresses the fact that the
   share that we do not hold remains unchanged. *)

(* [gs2] is determined: it is [(gs1 ⊎ ls2) ∖ ls1]. *)

Lemma pred_update σ π l' q gs1 gs2 ls1 ls2 :
  π !! l' = Some gs1 →
  dom π ⊆ dom σ ->
  (q=0%Qz -> AllNeg ls2) ->
  (of_gmultiset gs1) ⊎ ls2 ≡ (of_gmultiset gs2) ⊎ ls1 →
  pred σ π -∗ mapsfrom l' q ls1 ==∗
  pred σ (<[ l' := gs2 ]> π) ∗ mapsfrom l' q ls2.
Proof.
  iIntros (Hπl' ? Hls2 ?) "[%μ [%Hμ Hauth]] [%J Hfrag]".

  assert (l' ∈ dom π).
  { now apply elem_of_dom. }

  assert (exists ns, μ !! l' = Some ns) as (ns,Hns).
  { destruct Hμ as [Hd]. apply elem_of_dom.  set_solver. }

  iAssert (|==> @own _ _ (phG_pred fG) γ (● ((full_gmultiset <$> <[l':=gs2]> π) ⋅ μ)) ∗ own γ (◯ {[l' := {| frac := q; supp := ls2; neglz := Hls2 |}]}))%I with "[Hauth Hfrag]" as ">[Hauth Hfrag]".
  { rewrite -own_op.
    iApply (own_update_2 with "[Hauth //] [$]").
    eapply auth_update.
    rewrite fmap_insert.

    setoid_rewrite <- (insert_id _ _ _ Hns) at 2.
    setoid_rewrite gmap_op at 2.
    erewrite <- (insert_merge _ _ _ l').
    2:{ rewrite -Some_op. easy. }
    eapply singleton_local_update.
    { rewrite lookup_merge lookup_fmap Hπl' Hns. simpl. rewrite -Some_op //. }
    { apply local_update_unital_discrete.
      intros z Hv Hz.
      split; try easy.
      inversion_clear Hz as [? ?]. constructor; try easy. simpl in *.
      smultiset_solver. } }
  iSplitL "Hauth"; iExists _; eauto.
Qed.

(* We can always allocate an empty fracset. *)
Lemma fracset_local_alloc_unit l μ :
  l ∈ dom μ ->
  (μ, ε) ~l~> (μ, {[l := ε]}).
Proof.
  intros ?.
  apply local_update_unital_discrete.
  intros z Hv Hz.
  split; try easy.
  intros x. rewrite left_id in Hz.
  specialize (Hz x).
  rewrite Hz lookup_op.
  destruct (decide (x=l)); subst.
  { rewrite lookup_singleton.
    destruct (z !! l) eqn:E; rewrite E.
    { by rewrite -Some_op left_id. }
    { exfalso.
      rewrite E in Hz. inversion Hz as [|Hz'].
      symmetry in Hz'.
      by apply not_elem_of_dom in Hz'. } }
  { by rewrite lookup_singleton_ne // left_id. }
Qed.

Lemma insert_op_r `{Countable K} {A : cmra} l (u:A) (k1 k2:gmap K A)  :
  l ∉ dom k1 ->
  <[l:=u]> (k1 ⋅ k2) = k1 ⋅ <[l:=u]> k2.
Proof.
  intros Hl2. apply not_elem_of_dom in Hl2.
  apply map_eq. intros l'. rewrite lookup_op. destruct (decide (l=l')); subst.
  { rewrite lookup_insert Hl2 lookup_insert // right_id //. }
  { rewrite !lookup_insert_ne // lookup_op //. }
Qed.

Local Lemma get_empty_mapsfrom_inner l' σ π :
  dom π ⊆ dom σ ->
  pred σ π ==∗
  ∃ μ, own γ (● ((full_gmultiset <$> π) ⋅ μ)) ∗ ⌜tied σ μ /\ l' ∈ dom μ⌝ ∗  mapsfrom l' 0%Qz ∅.
Proof.
  iIntros (?) "[%μ [%Hμ Hauth]]".
  destruct_decide (decide (l' ∈ dom μ)).
  { iMod (own_update with "[$]") as "(Hauth&?)".
    { eapply auth_update_alloc.
      apply fracset_local_alloc_unit with (l:=l').
      destruct Hμ as [Hd ? ?].
      rewrite dom_union_with dom_fmap_L.
      set_solver. }
    iModIntro. iExists _. iFrame. iSplitR. eauto. iExists _. done. }
  { destruct Hμ as [X1 X2 X3].
    assert (l' ∉ dom π) by set_solver.
    assert (((full_gmultiset <$> π) ⋅ μ) !! l' = None).
    { rewrite lookup_op lookup_fmap !not_elem_of_dom_1 //. }
    iMod (own_update with "[$]") as "(Hauth&?)".
    { eapply auth_update_alloc.
      by eapply alloc_singleton_local_update with (i := l') (x := ε). }
    rewrite insert_op_r //.
    2:{ rewrite dom_fmap //. }
    iModIntro. iExists _. iFrame. iSplitR; last iExists _; iFrame.
    iPureIntro. split; last set_solver.
    apply tied_add_freed1; try done.
    by apply not_elem_of_dom. }
Qed.

(* We can get an empty mapsfrom from every allocated location. *)
Lemma get_empty_mapsfrom l' σ π :
  dom π ⊆ dom σ ->
  pred σ π ==∗
  pred σ π ∗ mapsfrom l' 0%Qz ∅.
Proof.
  iIntros.
  iMod (get_empty_mapsfrom_inner with "[$]") as "[% (?&(%&%)&?)]".
  done.
  iFrame. iExists _. by iFrame.
Qed.

Lemma pred_update_no_mapsfrom σ π l' (ps1 ps2 : gmultiset loc) (ls2 : smultiset loc):
  π !! l' = Some ps1 →
  dom π ⊆ dom σ ->
  (of_gmultiset ps1) ⊎ ls2 ≡ (of_gmultiset ps2) →
  AllNeg ls2 ->
  pred σ π ==∗
  pred σ (<[ l' := ps2 ]> π) ∗ l' ↤{0} ls2.
Proof.
  iIntros (Hπl' ? Hls2 ?) "Hpred".
  iMod (get_empty_mapsfrom l' with "[$]") as "[? ?]".
  { assert (l' ∈ dom π) by now apply elem_of_dom. set_solver. }
  iMod (pred_update with "[$] [$]"); eauto.
  by rewrite right_id.
Qed.

Lemma pred_update_freed σ π l' ms :
  dom π ⊆ dom σ ->
  (∀m, m ∈ ms → freed σ m) →
  pred σ π ==∗
  pred σ π ∗ l' ↤{0} (of_gmultiset_neg ms).
Proof.
  iIntros (??) "Hpred".
  iMod (get_empty_mapsfrom_inner l' with "[$]") as "[%μ (Hauth&(%Hμ&%)&Hf)]".
  { done. }

  generalize Hμ. intros [Hdμ Hneg Hco].

  assert (exists ns, μ !! l' = Some ns) as (ns,Hns).
  { apply elem_of_dom. set_solver. }

  assert (AllNeg (of_gmultiset_neg ms)) as Halln.
  { smultiset_solver. }
  assert (AllNeg (of_gmultiset_neg ms ⊎ supp ns)) as Halln'.
  { specialize (Hneg _ _ Hns).
    assert (AllNeg (supp ns)) by (now apply neglz).
    smultiset_solver. }

  iAssert (|==> @own _ _ (phG_pred fG) γ (● ((full_gmultiset <$> π) ⋅ (<[l':=mk_nf 0%Qz (of_gmultiset_neg ms ⊎ supp ns) (fun _ => Halln')]>)μ)) ∗ own γ (◯ {[l' := {| frac := 0%Qz; supp := of_gmultiset_neg ms; neglz := fun _ => Halln |}]}))%I with "[Hauth Hf]" as ">[Hauth ?]".
  { rewrite -own_op.
    iDestruct "Hf" as "[%X ?]".
    iApply (own_update_2 with "[Hauth] [$]"); last iFrame.
    apply auth_update.

    setoid_rewrite gmap_op at 2.

    destruct (π !! l') eqn:E.
    { setoid_rewrite <- (insert_id _ _ _ E) at 2.
      rewrite fmap_insert.
      erewrite <- (insert_merge op (full_gmultiset <$> π) μ l').
      2:{ rewrite -Some_op //. }
      eapply singleton_local_update.
      { rewrite lookup_merge lookup_fmap E Hns. simpl. rewrite -Some_op //. }

      apply local_update_unital_discrete.
      intros z _ Hz.
      split; try easy.
      constructor.
      { specialize (Hneg _ _ Hns).
        apply nfrac_equiv_frac in Hz. simpl in *.
        rewrite Hneg in Hz. easy. }
      { apply nfrac_equiv_supp in Hz. simpl in *.
        smultiset_solver. } }

    (* Not in π. Why not. *)
    { erewrite <- (insert_merge_r op _ μ l').
      2:{ rewrite lookup_fmap E. simpl. rewrite left_id //. }
      eapply singleton_local_update.
      { rewrite lookup_merge lookup_fmap E Hns. simpl. rewrite left_id //. }

      (* LATER facto *)
      apply local_update_unital_discrete.
      intros z _ Hz.
      split; try easy.
      constructor.
      { specialize (Hneg _ _ Hns).
        apply nfrac_equiv_frac in Hz. simpl in *.
        rewrite Hneg in Hz. easy. }
      { apply nfrac_equiv_supp in Hz. simpl in *.
        smultiset_solver. } } }

  iSplitL "Hauth"; iExists _; iFrame; eauto.
  iPureIntro.
  eapply tied_add_freed2; eauto. intros ? Hi.
  apply smultiset_elem_of_disj_union in Hi.
  destruct Hi; eauto. smultiset_solver.
Qed.

(* When confronted with the authoritative assertion [pred dσ π], the assertion
   [l' ↤{q} ls] allows registering [l] as a new predecessor of [l']. The
   authoritative predecessor map is updated from [π] to [register l l' π],
   while the mapsfrom assertion becomes [l' ↤{q} (ls ⊎ {[l]})]. It is worth
   noting that the fraction [q] is not required to be 1. *)

Lemma pred_register σ π l l' q ls :
  dom π ⊆ dom σ ->
  q <> 0%Qz ->
  pred σ π -∗ l' ↤{q} ls ==∗
  pred σ (register l l' π) ∗ l' ↤{q} (ls ⊎ {[+l+]}).
Proof.
  iIntros (? ?) "Hauth Hmapsfrom".
  iDestruct (exploit_mapsfrom with "Hauth Hmapsfrom")
    as %(ps & Hπl' & _).
  1,2:easy.
  rewrite /register.
  erewrite lookup_total_correct by eauto.
  iMod (pred_update σ π l' q ps (ps ⊎ {[+ l +]}) ls (ls ⊎ {[+ l +]}) Hπl'
         with "Hauth Hmapsfrom") as "[? ?]"; try easy.
  { rewrite of_gmultiset_disj_union of_gmultiset_singleton. smultiset_solver. }
  by iFrame.
Qed.

(* The reverse of the previous lemma. Because this is a decreasing update,
   the storement is more complex, and the final store [π'] is not known
   exactly; we get a lower bound and an upper bound on it. *)

Lemma pred_unregister σ π l l' :
  dom π ⊆ dom σ ->
  l ∈ predecessors π l' ->
  pred σ π ==∗
  ∃π',
  pred σ π' ∗ l' ↤{0} {[-l-]} ∗ ⌜ unregister l l' π ≾ π' ∧ π' ≾ π ⌝.
Proof.
  iIntros (? Hl') "Hauth".

  assert (exists gs, π !! l' = Some gs /\ l ∈ gs) as (gs,(?&?)).
  { rewrite /predecessors in Hl'. destruct (π !! l'); set_solver. }

  rewrite /unregister.
  erewrite lookup_total_correct; last eauto.
  iMod (pred_update_no_mapsfrom σ π l' gs (gs ∖ {[l]}) with "[$]") as "[Hauth Hfrag]"; eauto.
  { assert ({[+ l +]} ⊆ gs ) by multiset_solver.
    rewrite of_gmultiset_difference //. }
  { apply AllNeg_of_gmultiset_neg. }
   rewrite of_gmultiset_neg_singleton.
  iModIntro. iExists _. iFrame.
  iPureIntro.
  split; eauto with approx.
Qed.

(* We now wish to iterate the above lemma so as to register an address [l] as
   a new predecessor of [l'], for every address [l'] in a certain list.

   For each address [l'] in the list, we must require [l' ↤{q} ls], for a
   certain fraction [q] and a certain list [ls] of pre-existing predecessors.

   This leads us to parameterizing the lemma with a list of triples, where
   each triple is of the form [(l', q, ls)], and is interpreted as a
   description of the assertion [l' ↤{q} ls].

   The fact that we allow fractional ownership seems crucial here. Indeed,
   because a newly-allocated block may have two fields that contain the same
   pointer, we must allow two triples in this list to concern the same address
   [l']. If we required full ownership of every triple in the list, then the
   iterated conjunction of these triples would be unsatisfiable. *)

(* That said, considering our current needs, working with lists of triples of
   arbitrary length is slightly overkill. The lemma [ph_alloc] is applied to a
   list of length 0, because we initialize every memory block with unit
   values. The lemma [ph_update] is applied to lists of length at most 1,
   because our store instruction updates only one field at a time, so destroys
   at most one edge and creates at most one edge. *)

Implicit Types triple :      (loc * Qz * smultiset loc).

Implicit Type triples : list (loc * Qz * smultiset loc).

(* interpret1 & interpret are used for points to of the new value.
   As we will register a new predecessor, they cannot be empty. *)
Definition interpret1 triple : iProp Σ :=
  let '(l', q, ls) := triple in ⌜q<>0%Qz⌝ ∗ l' ↤{q} ls.

Definition interpret triples : iProp Σ :=
  [∗ list] triple ∈ triples, interpret1 triple.

Definition interpret_unregister1 l l' : iProp Σ :=
  l' ↤{0%Qz} {[- l -]}.

Definition interpret_unregister l xs : iProp Σ :=
  [∗ list] l' ∈ xs, interpret_unregister1 l l'.

Definition address triple :=
  let '(l', q, ls) := triple in l'.

Definition addresses triples : gmultiset loc :=
  list_to_set_disj (map address triples).

Definition update l triple :=
  let '(l', q, ls) := triple in (l', q, ls ⊎ {[+l+]}).

Lemma interpret_nil :
  interpret [] = True%I.
Proof. reflexivity. Qed.

Lemma interpret_unregister_nil l :
  interpret_unregister l [] = True%I.
Proof. reflexivity. Qed.

Lemma interpret_unregister_cons l x xs :
  interpret_unregister l (x::xs) = (interpret_unregister1 l x ∗ interpret_unregister l xs)%I.
Proof. by rewrite /interpret_unregister big_opL_cons. Qed.

Lemma interpret_singleton l' q ls :
  q <> 0%Qz ->
  interpret [(l', q, ls)] ≡ (l' ↤{q} ls)%I.
Proof.
  intros.
  rewrite /interpret. simpl. iSplit; eauto.
  iIntros "([? ?] & _)". iFrame.
Qed.

Lemma addresses_cons triple triples :
  addresses (triple :: triples) =
  addresses triples ⊎ {[+ address triple +]}.
Proof.
  unfold addresses. simpl. multiset_solver.
Qed.

Lemma exploit_triples_dom σ π triples :
  dom π ⊆ dom σ ->
  pred σ π -∗
  interpret triples -∗
  ⌜ ∀ l', l' ∈ addresses triples → l' ∈ dom π ⌝.
Proof.
  intros.
  induction triples as [| [[l' q] ls] triples ]; simpl;
  iIntros "Hauth Htriples".
  { iPureIntro. multiset_solver. }
  iDestruct "Htriples" as "[[%Hq Htriple] Htriples]". simpl.
  iDestruct (exploit_mapsfrom_dom_pre with "Hauth Htriple") as %Hhead.
  1,2:easy.
  iDestruct (IHtriples with "Hauth Htriples") as %Htail.
  iPureIntro.
  intro. rewrite addresses_cons. multiset_solver.
Qed.

Lemma dom_fold_register dσ π (addrs : gmultiset loc) l :
  dom π ⊆ dσ ->
  (∀ l' : loc, l' ∈ addrs → l' ∈ dom π) ->
  dom (set_fold (register l) π addrs) ⊆ dσ.
Proof.
  induction addrs as [| x addrs] using gmultiset_ind;
    intros Hd Ha.
  { multiset_solver. }
  { rewrite gmultiset_disj_union_comm.
    rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton.
    multiset_solver. }
Qed.

Lemma pred_foldr_register l :
  ∀ triples σ π,
  dom π ⊆ dom σ ->
  pred σ π -∗ interpret triples ==∗
  pred σ (set_fold (register l) π (addresses triples)) ∗
  interpret (map (update l) triples).
Proof.
  induction triples as [| [[l' q] ls] triples ];
  simpl; intros; subst; simpl; [eauto|].
  iIntros "? [Hi ?]".
  iDestruct (exploit_triples_dom with "[$] [$]") as "%Hi". easy.
  iMod (IHtriples with "[$] [$]") as "[? ?]". easy.
  iDestruct "Hi" as "[%Hq ?]".
  iMod (pred_register with "[$] [$]") as "[? ?]".
  { eauto using dom_fold_register. }
  { easy. }
  rewrite addresses_cons.
  rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton.
  by iFrame.
Qed.

Lemma pred_foldr_unregister l :
  ∀ σ (xs : list loc) π,
    dom π ⊆ dom σ ->
   (forall l', gmultiset.multiplicity l' (list_to_set_disj xs) <= gmultiset.multiplicity l (predecessors π l')) ->
  pred σ π  ==∗
  ∃ π',
  pred σ π' ∗
  interpret_unregister l xs ∗
  ⌜ foldr (unregister l) π xs ≾ π' ∧ π' ≾ π ⌝.
Proof.
  induction xs as [| x xs];
    simpl; intros ? ? Hxs; subst; simpl.
  { iIntros. iModIntro. iExists _. iFrame. rewrite interpret_unregister_nil. eauto. }
  iIntros "Hauth".
  rewrite interpret_unregister_cons.
  iMod (IHxs with "Hauth")
    as (π1) "(Hauth & Htriples & %Hlo1 & %Hhi1)".
  { easy. }
  { intros l'. specialize (Hxs l').
    rewrite gmultiset.multiplicity_disj_union in Hxs.
    destruct (decide (x=l')); subst.
    { rewrite gmultiset.multiplicity_singleton in Hxs. lia. }
    { rewrite gmultiset.multiplicity_singleton_ne // in Hxs. } }
  iMod (pred_unregister with "Hauth")
    as (π2) "(Hauth & Htriple & %Hlo2 & %Hhi2)"; last iFrame.
  { destruct Hhi1 as (->&?). easy. }
  { destruct Hlo1 as (?&Hlo1). specialize (Hlo1 x l).
    assert (l∈ predecessors (foldr (unregister l) π xs) x); last multiset_solver.
    rewrite /elem_of /gmultiset_elem_of.
    rewrite predecessors_foldr_unregister.
    rewrite decide_True //.
    specialize (Hxs x).
    rewrite gmultiset.multiplicity_disj_union gmultiset.multiplicity_singleton in Hxs. lia. }
  iModIntro. iExists _. iFrame. iPureIntro.
  eauto using approx_transitive, unregister_approx.
Qed.

(* ------------------------------------------------------------------------ *)

Lemma invariant_alloc_no_pointers σ π l b :
  invariant σ π →
  l ∉ dom σ →
  b ≠ deallocated →
  pointers b = ∅ →
  invariant (<[l:= b]> σ) (<[l:=∅]> π).
Proof.
  intros ? ? ? Hb.
  assert (<[l:=∅]> π = set_fold (register l) (<[l:=∅]> π) (pointers b)) as ->.
  { by rewrite Hb. }
  eapply invariant_alloc; try easy.
  rewrite Hb. set_solver.
Qed.

(* Our store interpretation predicate is preserved by the allocation of a
   new block [b] at a fresh location [l].

   As explained earlier, the user must provide a list of triples
   [(l', q, ls)], where [l'] ranges over the locations contained
   in the block [b], and must provide the assertion [l' ↤{q} ls]
   that corresponds to each of these triples.

   After the operation, the location [l] is added as an extra predecessor
   in each of these triples: each such triple becomes [l' ↤{q} ls ⊎ {[l]}].

   In addition, the user receives [l ↦ b], as in ordinary Separation Logic,
   and [l ↤ ∅], which stores that the new block has no predecessors. *)

Lemma ph_alloc σ l b :
  σ !! l = None →
  pointers (BBlock b) = ∅ →
  ph_interp σ ==∗
  ph_interp (<[l:=BBlock b]> σ) ∗ l ↤ ∅.
Proof.
  intros Hσl Hpointers.
  rewrite /ph_interp.
  iIntros "Hph".
  iDestruct "Hph" as (π) "(Hauth & %Hinv)".
  generalize Hinv; intros (Hco & Hmirror & Hclosure).

  (* [l] is fresh, so is not in the domain of [σ]. *)
  assert (l ∉ dom σ) by eauto.
  (* By coincidence, the domain of [π] is a subset of that of [σ],
     so [l] is not the domain of [π] either. *)
  assert (Hπl: l ∉ dom π) by eauto using use_coincidence_reverse.

  (* Move from [π] to [π'], which extends [pi] with a mapping of [l]
     to an empty multiset of predececessors. At the same time, we obtain the
     assertion [l ↤ ∅]. *)
  set (π' := <[l:=∅]> π).
  iMod (pred_alloc _ π l (BBlock b) with "Hauth") as "[Hauth Hmapsfrom]".
  1-3: eauto using invariant_dom.
  (* Conclude. *)
  iModIntro. iFrame.
  iExists _. iFrame. eauto using invariant_alloc_no_pointers.
Qed.

(* ------------------------------------------------------------------------ *)

Local Lemma gen_heap_valid_big σ locs A:
  ph_interp σ ∗
  ([∗ set] l ∈ locs, mapsfrom_set l 1 A) -∗
  ⌜ locs ⊆ dom σ ⌝.
Proof.
  (* By induction on the set [locs]. *)
  pattern locs. eapply set_ind_L; clear locs.
  (* Case: ∅. *)
  { eauto. }
  { intros l locs Hl IH. rewrite big_sepS_union; last set_solver.
    rewrite big_sepS_singleton.
    iIntros "(Hh & [% (?&_)] & Hlocs)".
    iDestruct (exploit_mapsfrom_dom with "Hh [$]") as %Hone. done.
    iDestruct (IH with "[$]") as %Htwo.
    iPureIntro. set_solver. }
Qed.

(* ------------------------------------------------------------------------ *)

(* The predicate [ph_interp σ] allows deallocating a set of locations [locs],
   provided this set is closed under predecessors. *)

(* This operation consumes [mapsfrom_set l 1%Qp locs]
   for every location [l] in the set [locs]. It does not require any
   information about the successors of the block [b], and does not update
   their predecessor fields. We adopt a mechanism that allows delayed
   updates: we produce a proof that the location [l] has been deallocated.
   A separate rule allows removing a dead location from a predecessor set. *)

(* We produce a witness that the set [locs] contains no roots and is closed
   under predecessors. This fact is stored in terms of successors. *)

Lemma pred_update_store_deallocate σ π locs :
  pred σ π -∗ pred (deallocate locs σ) π.
Proof.
  iIntros "[%μ [%Hμ Hauth]]".
  iExists _. eauto using tied_store_deallocate.
Qed.

Lemma ph_free_group σ (locs:gset loc) :
  ph_interp σ ∗
  ([∗ set] l ∈ locs, mapsfrom_set l 1%Qz locs)
  ==∗
  ph_interp (deallocate locs σ) ∗
  ⌜ ∀ m m', m' ∈ successors σ m → m' ∈ locs → m ∈ locs ⌝.
Proof.
  rewrite /ph_interp.
  iIntros "(Hi&?)".
  iDestruct (gen_heap_valid_big with "[$]") as "%Hlocs".

  iDestruct "Hi" as "[%(?&%)]".

  iDestruct (pred_update_store_deallocate _ _ locs with "[$]") as "Hpred".
  (* Update [π] by removing [locs] from its domain. *)
  iMod (pred_free_group with "[$]") as "[Hauth %Hclosed]".
  { rewrite dom_deallocate. eauto using invariant_dom. }
  { intros. rewrite /freed /deallocate stdpp.gmap_lookup_mset_inside //. set_solver. }
  destruct Hclosed as (ls',(Hfreed & Hclosed)).

  iFrame.

  assert (∀ l : loc, l ∉ locs → l ∈ ls' → freed σ l).
  { intros ?? Hl. apply Hfreed in Hl.
    unfold freed, deallocate in *.
    rewrite stdpp.gmap_lookup_mset_outside // in Hl.  }

  (* The invariant is preserved. Conclude. *)
  iModIntro. iSplitL.
  + iExists _. iFrame.
    iPureIntro. eapply invariant_free;  naive_solver.
  + eauto using successors_predecessors_corollary.
Qed.


(* The memory block at address [l] may contain one or more pointers
   to itself. *)

(* The lemma is stored in terms of [mapsfrom], as opposed to
   [mapsfrom_set], because this may be more convenient. We may
   end up needing both versions anyway. *)

Lemma ph_free_singleton σ l p ls :
  dom ls ⊆ {[l]} →
  ph_interp σ             ∗  l ↤ ls ==∗
  ph_interp (<[l:=deallocated]> σ) ∗
  ⌜ ∀ m, l ∈ successors σ m → m = l ⌝.
Proof.
  iIntros (Hls) "(Hph & Hmapsfrom)".
  iDestruct (exploit_mapsfrom_dom with "[$] [$]") as %Hone. done.
  iMod (ph_free_group σ {[l]} with "[Hph Hmapsfrom]")
    as "(Hph & %Hfacts)".
  { iFrame "Hph". rewrite  big_sepS_singleton.
    iFrame. iExists ls. by iFrame "Hmapsfrom". }
  rewrite /deallocate gmap_mset_singleton; last eauto.
  iFrame. iPureIntro.
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)

(* For any location l', it is safe to assert that it is pointed-by by any
   number of freed location.
   This is sound even if l' is not yet allocated O.o *)
Lemma ph_cleanup σ l' ms :
  (∀m, m ∈ ms → freed σ m) →
  ph_interp σ  ==∗
  ph_interp σ ∗ l' ↤{0} (of_gmultiset_neg ms).
Proof.
  intros Hms.
  rewrite /ph_interp.
  iIntros "[%π [Hπ %Hinv]]".

  iMod (pred_update_freed σ π l' with "Hπ") as "[? ?]".
  { eauto using invariant_dom. }
  { done. }
  iFrame. iExists _. by iFrame.
Qed.

Lemma ph_cleanup_singleton σ l' m :
  freed σ m ->
  ph_interp σ ==∗
  ph_interp σ ∗ l' ↤{0} {[-m-]}.
Proof.
  iIntros (?) "Hh".
  iMod (ph_cleanup σ l' {[+ m +]} with "[$]").
  { intros m'. rewrite gmultiset_elem_of_singleton. intros ->. eauto. }
  rewrite of_gmultiset_neg_singleton.
  by iFrame.
Qed.

Local Lemma ph_get_empty_mapsfrom l' σ :
  ph_interp σ ==∗ ph_interp σ ∗ l' ↤{0} ∅.
Proof.
  iIntros "[% (?&%)]".
  iMod (get_empty_mapsfrom with "[$]") as "(?&?)". eauto using invariant_dom.
  iFrame. iModIntro. iExists _. by iFrame.
Qed.

Lemma ph_cleanup_singletons (i:nat) σ l' m :
  freed σ m ->
  ph_interp σ  ==∗
  ph_interp σ ∗ l' ↤{0} {[ m := -i ]}.
Proof.
  iIntros (?) "?".
  iInduction i as [|] "IH".
  { iMod (ph_get_empty_mapsfrom with "[$]") as "(?&?)". eauto.
    iFrame. assert({[m := - 0%nat]} ≡ ∅) as -> by smultiset_solver.
    by iFrame. }
  { iMod (ph_cleanup_singleton with "[$]") as "(?&?)". eauto.
    iMod ("IH" with "[$]") as "(?&?)".
    iDestruct (mapsfrom_join with "[$][$]") as "?".
    assert (({[m := - i]} ⊎ {[-m-]}) ≡ {[m := - S i]}) as-> by smultiset_solver.
    rewrite left_id. by iFrame. }
Qed.

Lemma ph_cleanup_mapsfromset σ l l' (q:Qz) S :
  freed σ l ->
  ph_interp σ ∗ mapsfrom_set l' q S  ==∗
  ph_interp σ ∗ mapsfrom_set l' q (S ∖ {[l]}).
Proof.
  iIntros (?) "(?&[%(?&%hd)])".

  iDestruct (mapsfrom_correct with "[$]") as "%".

  destruct (decide (multiplicity l ps ≤ 0))%Z.
  { iDestruct (mapsfrom_weak _ (smultiset.delete l ps) with "[$]") as "?".
    { eauto using AllNeg_delete. }
    { intros x. rewrite multiplicity_delete. case_decide; subst; lia. }
    iFrame. iModIntro. iExists _. iFrame.
    iPureIntro.
    rewrite smultiset.dom_delete. set_solver. }
  { iMod (ph_cleanup_singletons (Z.to_nat (multiplicity l ps)) with "[$]") as "(?&?)".
    done.
    iDestruct (mapsfrom_join with "[$][$]") as "?".
    rewrite left_id. iModIntro.  iFrame. iExists _. iFrame. iPureIntro.
    rewrite Z2Nat.id; last lia.
    rewrite comm. fold (smultiset.delete l ps).
    rewrite smultiset.dom_delete. set_solver. }
Qed.

Lemma pred_update_store σ π l b b':
  b ≠ deallocated →
  b' ≠ deallocated →
  pred (<[l := b]> σ) π -∗ pred (<[l := b']> σ) π.
Proof.
  iIntros (? ?) "[%μ [%Hμ ?]]".
  iExists _. eauto using tied_update_store.
Qed.

Lemma ph_update σ (l:loc) b b' new_triples :
  length b = length b' ->
  addresses new_triples = new_pointers (BBlock b) (BBlock b') →
  ph_interp (<[l := BBlock b]> σ) ∗
  interpret new_triples  ==∗
  ph_interp (<[l := BBlock b']> σ) ∗
  interpret_unregister l (elements (old_pointers (BBlock b) (BBlock b'))) ∗
  interpret (map (update l) new_triples).
Proof.
  intros Hb Hnaddr.
  rewrite /ph_interp.
  iIntros "([%(Hauth & %Hinv)] & Hntriples)".

  assert (dom π ⊆ dom (<[l:=BBlock b]> σ)) by (eauto using invariant_dom).

  iDestruct (exploit_triples_dom with "Hauth Hntriples") as %Hlive; try easy.
  rewrite Hnaddr in Hlive.

  (* Update [π] by unregistering every edge from [l] to a location [l']
     in [block_pointers b ∖ block_pointers b'] and by registering every
     edge from [l] to some [l'] in [block_pointers b' ∖ block_pointers b]. *)

  iMod (pred_foldr_unregister with "Hauth")
    as (π') "(Hauth & Hotriples & %Hlo & %Hhi)"; last iFrame.
  { easy. }
  { rewrite /old_pointers.
    intros l'. destruct Hinv as (? & Hmir & ?).
    specialize (Hmir l l').
    rewrite successors_insert in Hmir.
    rewrite list_to_set_disj_elements.
    multiset. lia. }

  iMod (pred_foldr_register l new_triples with "Hauth Hntriples")
    as "(Hauth & Hntriples)".
  { destruct Hhi as (->&_). easy. }

  (* Conclude. *)
  iModIntro. iFrame. iExists _.
  iDestruct (pred_update_store with "[$]") as "?"; last iFrame; eauto.
  iPureIntro.
  (* The invariant is preserved. *)
  rewrite Hnaddr.
  eapply (invariant_update_imprecise σ l _ _ π π' Hinv);
    eauto using gmultiset_in_set_in_elements.
Qed.

(* ------------------------------------------------------------------------ *)

(* Timelessness. *)

Global Instance timeless_mapsfrom l q ls :
  Timeless (mapsfrom l q ls).
Proof. apply _. Qed.

Global Instance timeless_mapsfrom_set l q locs :
  Timeless (mapsfrom_set l q locs).
Proof. apply _. Qed.

(* ------------------------------------------------------------------------ *)

End ReasoningRules.

(* ------------------------------------------------------------------------ *)

(* Notations for assertions. *)

Global Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Global Notation "l ↦□ v" := (mapsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Global Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Global Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

(* Predecessor set. *)

Notation "l ↤{ q } ls" :=
  (mapsfrom l q%Qz ls)
  (at level 20, format "l  ↤{ q }  ls")
: bi_scope.

Notation "l ↤ ls" :=
  (mapsfrom l 1%Qz ls)
  (at level 20, format "l  ↤  ls")
: bi_scope.

(* ------------------------------------------------------------------------ *)

(* The following definitions have to do with initializing the heap.
   They are used in the proof of adequacy. *)

Module Initialization.

  Definition phΣ : gFunctors := #[ GFunctor (predR loc) ].

  Class phPreG Σ := {
      phPreG_pred :: inG Σ (predR loc);
  }.

  Global Instance subG_phPreG {Σ} :
    subG phΣ Σ → phPreG Σ.
  Proof. solve_inG. Qed.

  Lemma ph_init `{!phPreG Σ} :
    ⊢ |==> ∃ _ : phG Σ,
    ph_interp (∅:store).
  Proof.
    iIntros. rewrite /ph_interp.

    (* Allocate the ghost cell that holds [π]. *)
    set (π := ∅ : gmap loc (gmultiset loc)).
    set (μ := ∅ : gmap loc (fracset loc)).

    iMod (own_alloc (● (fmap full_gmultiset π ⋅ μ) : predR loc)) as (γ) "Hpred".
    { rewrite auth_auth_valid. done. }

    (* Conclude. *)
    iExists (PhG Σ _ γ).
    iModIntro.
    iExists π.
    iSplitL; eauto using invariant_init.
    iExists _. eauto using tied_init.
  Qed.

End Initialization.
