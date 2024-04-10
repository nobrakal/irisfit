From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gset gmap auth csum.
From stdpp Require Import gmap fin_map_dom gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets.
From irisfit Require Import disc interp_base wp_updates.

Set Implicit Arguments.

Section pbt.

Context `{!interpGS sz Σ}.

(* ------------------------------------------------------------------------ *)
(* Defines [pbt]. *)

Local Notation "l ⟸{ q } s" :=
  (pbt l q%Qp s)
  (at level 20, format "l  ⟸{ q }  s")
: bi_scope.
Local Notation "l ⟸ ls" :=
  (l ⟸{ 1%Qp } ls)%I
  (at level 20, format "l  ⟸  ls")
    : bi_scope.

Global Instance timeless_pbt l p S :
  Timeless (pbt l p S).
Proof. apply _. Qed.

Definition pbt_dead l : iProp Σ :=
  own γctx (◯ {[l:=discarded tt]}).

Global Instance timeless_pbt_dead l :
  Timeless (pbt_dead l).
Proof. apply _. Qed.

Global Instance pers_pbt_dead l :
  Persistent (pbt_dead l).
Proof. apply _. Qed.

Lemma pbt_PBT l q S :
  l ⟸{q} S ⊣⊢ PBT S {[l:=q]}.
Proof. rewrite /PBT big_sepM_singleton //. Qed.

Lemma pbt_split l q1 q2 s1 s2 :
  l ⟸{q1+q2} (s1 ∪ s2) ⊢ l ⟸{q1} s1 ∗ l ⟸{q2} s2.
Proof. rewrite pbt_op //. Qed.

Lemma pbt_split_half_empty l p S :
  l ⟸{p} S -∗ l ⟸{p/2} S ∗ l ⟸{p/2} ∅.
Proof.
  iIntros.
  iApply pbt_split. rewrite Qp.div_2 right_id_L //.
Qed.

Lemma pbt_join l (q1 q2:Qp) s1 s2 :
  l ⟸{q1} s1 ∗ l ⟸{q2} s2 ⊢ l ⟸{q1+q2} (s1 ∪ s2).
Proof. rewrite pbt_op //. Qed.

Local Lemma frac_pbt l q1 q2 s1 s2 :
  l ⟸{q1+q2} (s1 ∪ s2) ⊣⊢ l ⟸{q1} s1 ∗ l ⟸{q2} s2.
Proof. iSplit. iApply pbt_split. iApply pbt_join. Qed.

Lemma pbt_valid r p S :
  r ⟸{p} S -∗ ⌜p ≤ 1⌝%Qp.
Proof.
  iIntros "[% (%&?)]".
  iDestruct (own_valid with "[$]") as "%Hv".
  rewrite auth_frag_valid singleton_valid live_valid pair_valid in Hv.
  destruct Hv as (Hv,?). easy.
Qed.

Lemma pbt_valid2 r p1 p2 S1 S2 :
  r ⟸{p1} S1 -∗ r ⟸{p2} S2 -∗ ⌜ p1+p2 ≤ 1⌝%Qp.
Proof.
  iIntros.
  iDestruct (pbt_join with "[$]") as "?".
  iDestruct (pbt_valid with "[$]") as "%".
  iPureIntro. rewrite comm //.
Qed.

Lemma PBT_borrow_pbt l q k S :
  k !! l = Some q ->
  PBT S k -∗ (pbt l q S ∗ (pbt l q S -∗ PBT S k)).
Proof.
  iIntros (?) "HS".
  iDestruct (big_sepM_lookup_acc with "HS") as "(?&?)". done. iFrame.
Qed.

Lemma confront_pbt_pbt l l' p p' S S' :
  ¬ (p+p' ≤ 1)%Qp ->
  l ⟸{p} S ∗ l' ⟸{p'} S' -∗ ⌜l ≠ l'⌝.
Proof.
  iIntros (Hf) "(H1 & H2)".
  iIntros (?). subst.
  iDestruct (pbt_valid2 with "H1 H2") as "%".
  iPureIntro. eauto.
Qed.

Lemma confront_pbt_PBT l S S' M :
  l ⟸ S ∗ PBT S' M -∗ ⌜l ∉ dom M⌝.
Proof.
  iIntros "(?&?)". iIntros (Hl).
  apply elem_of_dom in Hl. destruct Hl as (?&?).
  iDestruct (big_sepM_lookup with "[$]") as "?". done.
  iDestruct (confront_pbt_pbt with "[$]") as "%Hv".
  { apply Qp.not_add_le_r. }
  iPureIntro. set_solver.
Qed.

Lemma auth_ctx_leftover_disj ρ μ :
  ( forall l x, μ !! l = Some x -> x = discarded tt) ->
  ✓ (map1 ρ ⋅ μ)  ->
  dom ρ ## dom μ.
Proof.
  intros Hμ Hv.
  intros l Hl1 Hl2.
  apply elem_of_dom in Hl1. destruct Hl1 as (x1,Hx1).
  rewrite elem_of_dom in Hl2. destruct Hl2 as (?,Hx2).
  specialize (Hv l).
  rewrite lookup_op /map1 lookup_fmap Hx1 Hx2 in Hv.
  simpl in *. rewrite Some_valid in Hv.
  apply live_valid_op_inv in Hv. destruct Hv as (?,?).
  naive_solver.
Qed.

Lemma pbt_precise_exploit_core l ρ q S μ  :
  (∀ (l : loc)  x, μ !! l = Some x → x = discarded tt) ->
  own γctx (● (map1 ρ ⋅ μ)) ∗ pbt_precise l q S -∗
  ⌜dom ρ ## dom μ /\ μ !! l = None /\ ∃ x : gset thread_id, ρ !! l = Some x ∧ S ⊆ x ∧ (q = 1%Qp → x = S)⌝.
Proof.
  iIntros (Hctx) "(Ha&Hf)".
  iDestruct (own_valid_2 with "Ha Hf" ) as "%Hv".
  iPureIntro.
  apply auth_both_valid_discrete in Hv. destruct Hv as (Hv1,Hv2).
  apply auth_ctx_leftover_disj in Hv2; last by naive_solver.
  rewrite singleton_included_l in Hv1.
  destruct Hv1 as (y,(Hy1&Hy2)).
  rewrite lookup_op /map1 lookup_fmap in Hy1.
  rewrite -Hy1 in Hy2.
  destruct_decide (decide (l∈dom ρ)) as Hl.
  { assert (μ !! l = None) as Hl'.
    { rewrite -not_elem_of_dom.  intros ?. set_solver. }
    split_and !; eauto.
    rewrite Hl' right_id in Hy1.
    rewrite Hl' right_id in Hy2.
    destruct (ρ !! l) eqn:E.
    2:{ exfalso. rewrite E in Hy1. inversion Hy1. }
    rewrite E in Hy1. rewrite E in Hy2. simpl in *.
    exists g. split; eauto. split.
    { rewrite Some_included live_included in Hy2.
      destruct Hy2 as [HS|HS].
      { inversion HS. set_solver. }
      { rewrite pair_included gset_included in HS. naive_solver. } }
    { intros ?.  subst.
      apply Some_included_exclusive in Hy2. inversion Hy2. simpl in *. naive_solver.
      apply _. easy. } }
  exfalso. apply not_elem_of_dom in Hl.
  rewrite Hl left_id in Hy1.
  rewrite Hy1 Hl left_id in Hy2.
  destruct (μ !! l) as [|] eqn:E.
  2:{ inversion Hy1. subst. rewrite E in H. naive_solver. }
  rewrite E in Hy1. rewrite -Hy1 in Hy2.
  apply Hctx in E. simpl in *.
  apply Some_included in Hy2. rewrite E in Hy2.
  destruct Hy2 as [HS|HS].
  { inversion HS. }
  { destruct HS as (?,?).  destruct x; inversion H. }
Qed.

Lemma pbt_precise_exploit_aux l ρ u q S :
  auth_ctx ρ u ∗ pbt_precise l q S -∗ ⌜exists x, ρ !! l = Some x /\ S ⊆ x /\ (q=1%Qp -> x=S)⌝.
Proof.
  iIntros "([% (%Hctx&Ha)]&Hf)".
  iDestruct (pbt_precise_exploit_core with "[$]") as "%Hv".
  all:naive_solver.
Qed.

Lemma pbt_precise_exploit l ρ u q S :
  auth_ctx ρ u ∗ pbt_precise l q S -∗ ⌜exists x, ρ !! l = Some x /\ S ⊆ x⌝.
Proof.
  iIntros. iDestruct (pbt_precise_exploit_aux with "[$]") as "%Hs".
  iPureIntro. naive_solver.
Qed.

Lemma pbt_precise_exploit_full l ρ u S :
  auth_ctx ρ u ∗ pbt_precise l 1%Qp S -∗ ⌜ρ !! l = Some S⌝.
Proof.
  iIntros. iDestruct (pbt_precise_exploit_aux with "[$]") as "%Hs".
  iPureIntro. naive_solver.
Qed.

Lemma pbt_exploit l ρ u q S :
  auth_ctx ρ u ∗ pbt l q S -∗ ⌜exists x, ρ !! l = Some x⌝.
Proof.
  iIntros "(?&[%(%&?)])". iDestruct (pbt_precise_exploit with "[$]") as "%Hs".
  iPureIntro. naive_solver.
Qed.

Lemma pbt_dead_exploit l ρ u :
  auth_ctx ρ u ∗ pbt_dead l -∗ ⌜l ∉ dom ρ /\ l ∈ u⌝.
Proof.
  iIntros "([% ((%&%)&Ha)]&Hf)".
  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
  iPureIntro.
  apply auth_both_valid_discrete in Hv. destruct Hv as (Hv1,Hv2).
  rewrite singleton_included_l in Hv1. destruct Hv1 as (y&Hy1&Hy2).
  assert (y ≡ discarded tt) as E.
  { apply Some_included in Hy2. destruct Hy2 as [E|E]; first done.
    specialize (Hv2 l). rewrite Hy1 in Hv2.
    apply csum_included in E. destruct E as [E|[E|E]].
    { subst. inversion Hv2. }
    { destruct E as (?&?&?). naive_solver. }
    { destruct E as (?&?&?&?&E). subst. inversion H1. subst.
      rewrite Some_valid Cinr_valid in Hv2.
      apply to_agree_uninj in Hv2. destruct Hv2 as (?&X). rewrite -X in E.
      apply to_agree_included in E. rewrite -X -E //. } }
  rewrite E in Hy1. clear Hy2 E. split.
  { intros Hl. apply elem_of_dom in Hl. destruct Hl as (?&E).
    rewrite lookup_op /map1 lookup_fmap E in Hy1.
    destruct (μ !! l).
    { inversion Hy1. subst. destruct c; inversion H3. }
    { inversion Hy1. subst. inversion H3. } }
  { destruct ((map1 ρ ⋅ μ) !! l) eqn:Hl.
    2:{ rewrite Hl in Hy1. inversion Hy1. }
    apply stdpp.prove_in_dom in Hl. rewrite dom_op /map1 dom_fmap in Hl.
    set_solver. }
Qed.

Lemma confront_pbt_pbt_dead l q L :
  pbt_dead l -∗ l ⟸{q} L -∗ False.
Proof.
  iIntros "? [% (%&?)]".
  iDestruct (own_valid_2 with "[$][$]") as  "%Hv".
  iPureIntro. rewrite -auth_frag_op singleton_op in Hv.
  rewrite auth_frag_valid singleton_valid in Hv.
  inversion Hv.
Qed.

Lemma insert_op_l `{Countable K} {A : cmra} l (u:A) (k1 k2:gmap K A)  :
  l ∉ dom k2 ->
  <[l:=u]> (k1 ⋅ k2) = <[l:=u]> k1 ⋅ k2.
Proof.
  intros Hl2. apply not_elem_of_dom in Hl2.
  apply map_eq. intros l'. rewrite lookup_op. destruct (decide (l=l')); subst.
  { rewrite lookup_insert Hl2 lookup_insert // right_id //. }
  { rewrite !lookup_insert_ne // lookup_op //. }
Qed.

Lemma pbt_precise_approx' S' ρ u l q S g :
  ρ !! l = Some g ->
  auth_ctx ρ u ∗ pbt_precise l q S ==∗ auth_ctx (<[l:=g ∪ S']> ρ) u ∗ pbt_precise l q (S ∪S').
Proof.
  iIntros (Hl) "([% (%Hctx&Ha)]&Hf)".
  iDestruct (own_valid with "Ha" ) as "%Hva".
  rewrite auth_auth_valid in Hva.
  eapply auth_ctx_leftover_disj in Hva; last by naive_solver.
  iMod (own_update_2 with "Ha Hf") as "[? ?]".
  { apply auth_update.
    eapply singleton_local_update.
    assert (μ !! l = None) as Hl'.
    { apply not_elem_of_dom. intros ?.
      assert (l ∈ dom ρ) by eauto. set_solver. }
    rewrite lookup_op /map1 lookup_fmap Hl' Hl. reflexivity.
    apply live_local_update, prod_local_update_2.
    apply (gset_local_add _ _ S'). }
  iFrame. iExists μ. iFrame "%".
  rewrite insert_op_l; eauto.
  rewrite /map1 fmap_insert. iFrame.
  iPureIntro.
  rewrite dom_insert_L.
  destruct Hctx. split; eauto.
  assert (l ∈ dom ρ) by eauto. set_solver.
Qed.

Lemma synchro_dead_approx τ ρ x x' l :
  ρ !! l = Some x ->
  synchro_dead τ ρ ->
  synchro_dead τ (<[l:=x']> ρ).
Proof.
  intros ? Hs ? ? Hl'.
  specialize (Hs _ _ Hl'). rewrite dom_insert_lookup_L //.
Qed.

Lemma pbt_precise_approx S' l mt b k e σ q S :
  interp mt b k e σ ∗ pbt_precise l q S ==∗ interp mt b k e σ ∗ pbt_precise l q (S ∪ S').
Proof.
  iIntros "[Hi Hn]".
  destruct_interp "Hi".
  iDestruct (pbt_precise_exploit with "[$]") as "%Hs".
  destruct Hs as (?,(?&?)).
  iMod (pbt_precise_approx' with "[$]") as "(?&?)".
  eauto.
  iFrame.
  iModIntro.
  iExists ms,τ, (<[l:=x ∪ S']> ρ),η.
  iFrame. iPureIntro.
  split_and !; eauto using roots_inv_extend, synchro_dead_approx.
Qed.

Lemma pbt_approx S' S l q :
  l ⟸{q} S -∗ l ⟸{q} (S ∪ S').
Proof.
  iIntros "[% (%&?)]".
  iExists _. iFrame. iPureIntro. set_solver.
Qed.

Lemma PBT_pbt_iterated S k :
  PBT S k = ([∗ map] l ↦ q ∈ k, pbt l q S)%I.
Proof. done. Qed.

Lemma PBT_approx S' S k : PBT S k  -∗ PBT (S∪S') k.
Proof.
  iIntros. iApply (big_sepM_impl with "[$]").
  iModIntro. iIntros. iApply (pbt_approx with "[$]").
Qed.

Lemma pbt_exchange l q1 q2 S1 S2 i:
  i ∈ S1 ->
  l ⟸{q1} S1 -∗ l ⟸{q2} S2 -∗ l ⟸{q1} S1 ∗ l ⟸{q2} (S2 ∖ {[i]}).
Proof.
  iIntros. iApply pbt_split.
  replace (S1 ∪ S2 ∖ {[i]}) with (S1 ∪ S2).
  2:{ rewrite {2}(union_difference_singleton_L i S1) //. rewrite -assoc_L.
      rewrite -difference_union_distr_l_L -union_difference_singleton_L //.
      set_solver. }
  iApply pbt_join. iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* Defines [vpbt]. *)

Definition vpbt  (v:val) (p:Qp) (S:gset thread_id)  :=
  match v with
  | val_loc l => pbt l p S
  | _ => True%I end.

Global Instance timeless_vpbt v p S :
  Timeless (vpbt v p S).
Proof. destruct v; apply _. Qed.

Local Notation "v ⟸?{ q } s" :=
  (vpbt v q%Qp s)
  (at level 20, format "v  ⟸?{ q }  s")
: bi_scope.
Local Notation "v ⟸? ls" :=
  (v ⟸{ 1%Qp } ls)%I
  (at level 20, format "v  ⟸?  ls")
: bi_scope.

Lemma vpbt_split v q1 q2 s1 s2 :
  v ⟸?{q1+q2} (s1 ∪ s2) -∗ v ⟸?{q1} s1 ∗ v ⟸?{q2} s2.
Proof.
  iIntros. destruct v; eauto.
  iApply pbt_split. iFrame.
Qed.

Lemma vpbt_join v (q1 q2:Qp) s1 s2 :
 v ⟸?{q1} s1 ∗ v ⟸?{q2} s2 -∗ v ⟸?{q1+q2} (s1 ∪ s2).
Proof.
  iIntros. destruct v; eauto.
  iApply pbt_join. iFrame.
Qed.

Lemma vpbt_not_loc S p v :
  ¬ (is_loc v) ->
  vpbt v p S ≡ True%I.
Proof. by destruct v. Qed.

Lemma is_loc_inv v :
  is_loc v -> exists l, v = val_loc l.
Proof. destruct v; naive_solver. Qed.

Lemma confront_pbt_vpbt l l' p p' S S' :
  ¬ (p+p' ≤ 1)%Qp ->
  l ⟸{p} S ∗ l' ⟸?{p'} S' -∗ ⌜val_loc l ≠ l'⌝.
Proof.
  destruct l'; eauto. simpl.
  iIntros (?) "(? & ?)".
  iDestruct (confront_pbt_pbt with "[$]") as "%". rewrite comm. easy.
  iPureIntro. intros E. injection E. congruence.
Qed.

Lemma confront_vpbt_vpbt l l' p p' S S' :
  ¬ (p+p' ≤ 1)%Qp ->
  l ⟸?{p} S ∗ l' ⟸?{p'} S' -∗ ⌜locs l ∩ locs l' = ∅⌝.
Proof.
  destruct l,l'; try (iIntros; iPureIntro; set_solver).
  iIntros. iDestruct (confront_pbt_pbt with "[$]") as "%". eauto.
  iPureIntro. set_solver.
Qed.

Lemma vpbt_approx S' l q S :
  l ⟸?{q} S -∗ l ⟸?{q} (S ∪ S').
Proof.
  iIntros "?". iIntros. destruct l; try by iFrame. iApply pbt_approx. iFrame.
Qed.

End pbt.

Global Notation "l ⟸{ q } s" :=
  (pbt l q%Qp s)
  (at level 20, format "l  ⟸{ q }  s")
: bi_scope.
Global Notation "l ⟸ ls" :=
  (l ⟸{ 1%Qp } ls)%I
  (at level 20, format "l  ⟸  ls")
: bi_scope.

Global Notation "v ⟸?{ q } s" :=
  (vpbt v q%Qp s)
  (at level 20, format "v  ⟸?{ q }  s")
: bi_scope.
Global Notation "v ⟸? ls" :=
  (v ⟸?{ 1%Qp } ls)%I
  (at level 20, format "v  ⟸?  ls")
: bi_scope.

From iris.bi.lib Require Import fractional.

Global Instance pbt_fractional `{!interpGS sz Σ} l S : Fractional (λ q, pbt l q S)%I.
Proof.
  intros ? ?. iSplit.
  { iIntros. iApply pbt_split. rewrite idemp_L. iFrame. }
  { iIntros. iDestruct (pbt_join with "[$]") as "?". rewrite idemp_L. iFrame. }
Qed.
Global Instance pbt_as_fractional `{!interpGS sz Σ} l S q : AsFractional (pbt l q S) (λ q, pbt l q S)%I q.
Proof. constructor; [eauto | apply _]. Qed.

Global Instance vpbt_fractional `{!interpGS sz Σ} v S : Fractional (λ q, vpbt v q S)%I.
Proof. intros ? ?. destruct v; simpl; rewrite ?left_id //. apply pbt_fractional. Qed.

Global Instance vpbt_as_fractional `{!interpGS sz Σ} v S q : AsFractional (vpbt v q S) (λ q, vpbt v q S)%I q.
Proof. constructor; [eauto | apply _]. Qed.
