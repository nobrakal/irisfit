From Coq Require Import Program.Equality Wellfounded.
From stdpp Require Import base option relations.
From iris.proofmode Require Import proofmode.
From irisfit.lib Require Import qz.
From irisfit.language Require Import language.
From irisfit.language Require Import semantics reducible syntax_instances.
From irisfit.program_logic Require Import wp_adequacy.
From irisfit.final Require Export final_semantics temporal_logic.

Definition count_allocated σ :=
  map_fold (λ (_ : loc) (b : block) (acc : nat), match b with BDeallocated => acc | _ => S acc end) 0 σ.

Local Definition gcok (σ σ':store) :=
  (forall l, l ∈ dom σ -> σ !!! l = σ' !!! l \/ (σ !!! l ≠ BDeallocated /\ σ' !!! l = BDeallocated)).

Local Lemma ok_insert i x1 x2 m1 m2 :
  i ∉ dom m1 ->
  gcok (<[i:=x1]> m1) (<[i:=x2]> m2) ->
  gcok m1 m2.
Proof.
  intros E1 Hok l Hl.
  assert (i ≠ l) by set_solver.
  assert (l ∈ dom (<[i:=x1]> m1)) as E.
  { rewrite dom_insert_L. set_solver. }
  apply Hok in E. rewrite !lookup_total_insert_ne // in E.
Qed.

Local Lemma gc_impl r σ σ' :
  gc r σ σ' ->
  gcok σ σ'.
Proof.
  intros (_&Hgc) l Hl.
  destruct (σ !!! l) eqn:?; destruct (Hgc l Hl); try naive_solver.
  all:left; rewrite -H //.
Qed.

Lemma gc_neq_size_lt r σ σ' :
  σ ≠ σ' ->
  gc r σ σ' ->
  count_allocated σ' < count_allocated σ.
Proof.
  intros X1 X2.
  assert (dom σ = dom σ') as Hd by (by destruct X2).
  apply gc_impl in X2.
  revert X1 X2.
  cut (gcok σ σ' →  (σ ≠ σ' → count_allocated σ' < count_allocated σ) /\ (count_allocated σ' <= count_allocated σ)). naive_solver.
  eapply stdpp.map_fold_ind_2 with (P:= fun x1 x2 m1 m2 => gcok m2 m1 -> (m2 ≠ m1 → x1 < x2) /\ (x1 <= x2)).
  { intros ?? [][]; lia. }
  { intros ?? [][]; lia. }
  { intros. rewrite -!not_elem_of_dom Hd //. }
  { split. congruence. lia. }
  { intros ??????????? E Hok.
    destruct E as [E1 E2].
    { eauto using ok_insert. }
    split.
    { intros X. destruct (Hok i) as [E|E].
      { rewrite dom_insert_L //. set_solver. }
      { rewrite !lookup_total_insert in E. subst.
        assert (r1 < r2); last (destruct x1; lia). apply E1.
        { intros ->. congruence. } }
      { rewrite !lookup_total_insert in E. destruct E as (?&->).
        destruct x2; try done. lia. } }
    { destruct x1,x2; try lia. exfalso.
      destruct (Hok i) as [E|E].
      { rewrite dom_insert_L //. set_solver. }
      all:rewrite !lookup_total_insert // in E; try naive_solver. } }
Qed.

Lemma no_allocated_block_forall σ :
  count_allocated σ = 0 ->
  forall l b, σ !! l = Some b -> b = BDeallocated.
Proof.
  apply map_fold_ind with
    (P := fun m x => m = 0 -> forall l b, x !! l = Some b -> b = BDeallocated).
  { naive_solver. }
  intros l b m n Hl IH. destruct b; try lia. intros ->.
  intros l' b. rewrite lookup_insert_case.
  case_decide; eauto. naive_solver.
Qed.

Lemma gc_no_allocated_block r σ σ' :
  count_allocated σ = 0 ->
  gc r σ σ' ->
  σ = σ'.
Proof.
  intros Hc (Hd&Hgc). apply map_eq. intros l.
  destruct_decide (decide (l∈dom σ)) as Hl; last first.
  { rewrite !not_elem_of_dom_1 //. set_solver. }
  { rewrite !lookup_lookup_total_dom //; last set_solver.
    destruct (Hgc _ Hl) as [Hx | Hx].
    { rewrite Hx //. }
    { destruct Hx as (_&Hx). rewrite Hx.
      destruct (σ !!! l) eqn:E; try done. exfalso.
      rewrite lookup_total_alt in E. destruct (σ !! l) eqn:E'; last naive_solver.
      simpl in *. inversion E. subst.
      by eapply no_allocated_block_forall in E'. } }
Qed.


Lemma count_allocated_replace_block σ l b b' :
  σ !! l = Some (BBlock b') ->
  count_allocated (<[l:=BBlock b]> σ) = (count_allocated σ).
Proof.
  intros Hl. rewrite -{2}(insert_delete _ l _ Hl).
  rewrite -{1}insert_delete_insert.
  rewrite /count_allocated !map_fold_insert_L //.
  2,4:rewrite lookup_delete //.
  1,2:intros ? ? [][] ; naive_solver.
Qed.

Lemma count_allocated_insert_block σ l b :
  count_allocated (<[l:=BBlock b]> σ) = match σ !! l with Some (BBlock _) => (count_allocated σ) | _ => count_allocated σ +1 end.
Proof.
  destruct (σ !! l) as [b'| ] eqn:Hl.
  { destruct b'.
    { erewrite count_allocated_replace_block; done. }
    { rewrite -{2}(insert_delete _ l _ Hl).
      rewrite -{1}insert_delete_insert.
      rewrite /count_allocated !map_fold_insert_L //. lia.
      2,4:rewrite lookup_delete //.
      1,2:intros ? ? [][] ; naive_solver. } }
  { rewrite /count_allocated !map_fold_insert_L //. lia.
    intros ? ? [][] ; naive_solver. }
Qed.

Lemma atomic_step_not_alloc_preserves_count_allocated t g σ t' g' σ' efs :
  (forall n, ¬ IsAlloc n t) ->
  atomic_step t g σ t' g' σ' efs ->
  count_allocated σ = count_allocated σ'.
Proof.
  intros Ha Hstep. dependent induction Hstep; subst.
  { apply IHHstep. intros ??. apply (Ha n). by constructor. }
  inversion H; subst; last done.
  inversion H0; subst; eauto.
  { exfalso. apply (Ha n). constructor. }
  { erewrite count_allocated_replace_block; eauto. }
  { case_decide; eauto; subst.
    erewrite count_allocated_replace_block; eauto. }
Qed.

Lemma atomic_step_count_allocated_le t g σ t' g' σ' efs :
  atomic_step t g σ t' g' σ' efs ->
  count_allocated σ' <= count_allocated σ + 1.
Proof.
  intros Hstep. dependent induction Hstep; subst.
  { apply IHHstep. }
  inversion H; subst; last by lia.
  inversion H0; subst; try lia.
  { erewrite count_allocated_insert_block.
    rewrite H1. lia. }
  { erewrite count_allocated_replace_block; eauto. lia. }
  { case_decide; subst; try lia.
    erewrite count_allocated_replace_block; eauto; lia. }
Qed.

Section WithSize.
Context (sz:nat -> nat).

Definition NeedGC sz ms σ (t:tm) :=
  ∃ n, IsAlloc n t /\ available sz ms σ < sz (Z.to_nat n).

Lemma NotNeedWill ms σ t :
  ¬ NeedGC sz ms σ t -> AllocFits sz ms σ t.
Proof.
  intros X n E.
  destruct_decide (decide (sz (Z.to_nat n) <= available sz ms σ)). done. exfalso.
  apply X. eexists. split. done. lia.
Qed.

Lemma NeedNotWill ms σ t :
  NeedGC sz ms σ t -> ¬ AllocFits sz ms σ t.
Proof.
  intros (?&Ha&?) Hwill.
  apply Hwill in Ha. lia.
Qed.
End WithSize.

Lemma AllOut_app l1 l2 :
  AllOut (l1 ++ l2) <-> AllOut l1 /\ AllOut l2.
Proof. rewrite /AllOut Forall_fmap Forall_app -!Forall_fmap //. Qed.

Lemma AllOut_cons t g l :
  AllOut ((t,g)::l) <-> g=Out /\ AllOut l.
Proof. rewrite /AllOut list.Forall_cons //. Qed.

Lemma list_inv_r {A:Type} (l:list A) :
  l=nil \/ exists l' x, l = l' ++ [x].
Proof.
  induction l using rev_ind. eauto.
  right. eauto.
Qed.

Lemma atomic_step_inv_ctxs t g σ t' g' σ' efs :
  atomic_step t g σ t' g' σ' efs ->
  exists es t1 t2, t=fill_items es t1 /\ t' = fill_items es t2 /\ head_step_conc t1 g σ t2 g' σ' efs.
Proof.
  induction 1; subst.
  { destruct IHatomic_step as (es&t3&t4&->&->&?).
    eexists (E::es),t3,t4. done. }
  eexists nil,_,_. done.
Qed.
