From Coq Require Import ssreflect.
From stdpp Require Import base binders gmap gmultiset.

From irisfit Require Import syntax syntax_instances final_semantics common.


Definition isalloc t :=
  match find_ctxs t with
  | (_,t') =>
      match t' with
      | tm_alloc (tm_val (val_int n)) => Some n
      | _ => None end end.

Lemma IsAlloc_fill_items_inv n es t :
  to_val t = None ->
  IsAlloc n (fill_items es t) ->
  IsAlloc n t.
Proof.
  revert t.
  induction es; intros t Ht Ha; first done.
  simpl in *.
  apply IsAlloc_fill_item_inv in Ha. eauto.
  destruct es; try done. apply to_val_fill_item.
Qed.

Lemma isalloc_IsAlloc t n:
  isalloc t = Some n <-> IsAlloc n t.
Proof.
  unfold isalloc.
  destruct (find_ctxs t) eqn:Hc.
  split.
  { destruct t0; try done. destruct t0; try done. destruct v; try done. inversion 1.
    subst.
    apply find_ctxs_correct2 in Hc. destruct Hc as (?&->).
    induction l; by econstructor. }
  { intros Ha. assert (to_val t0 = None).
    { eauto using find_ctxs_no_val,IsAlloc_no_val. }
    apply find_ctxs_correct2 in Hc. destruct Hc as (?&->).
    apply IsAlloc_fill_items_inv in Ha; eauto.
    inversion Ha. done. exfalso. subst.
    rewrite find_ctx_correct1 in H0; try done.
    eauto using IsAlloc_no_val. }
Qed.

Global Instance isalloc_decision t : (Decision (∃ n, IsAlloc n t)).
Proof.
  destruct (isalloc t) eqn:E; [left|right].
  { exists z. by eapply isalloc_IsAlloc. }
  { intros (n&Hn). apply isalloc_IsAlloc in Hn. congruence. }
Qed.

Definition needgc sz a t :=
  match isalloc t with
  | None => false
  | Some n => bool_decide (a < sz n)%nat end.

Lemma needgc_correct sz ms σ t :
  NeedGC sz ms σ t <-> needgc (fun x => sz (Z.to_nat x)) (available sz ms σ) t.
Proof.
  unfold needgc.
  split; intros Ha.
  { destruct Ha as (n&Hn&?).
    apply isalloc_IsAlloc in Hn. rewrite Hn.
    apply bool_decide_spec. lia. }
  { destruct (isalloc t) eqn:E; last naive_solver.
    apply isalloc_IsAlloc in E.
    eexists. split; first done.
    rewrite bool_decide_spec in Ha. lia. }
Qed.

Global Instance needgc_decision sz ms σ t : (Decision (NeedGC sz ms σ t)).
Proof.
  destruct_decide (decide (needgc (fun x => sz (Z.to_nat x)) (available sz ms σ) t)); [left|right]; rewrite needgc_correct //.
Qed.

Global Instance willfit_decision sz ms σ t : (Decision (AllocFits sz ms σ t)).
Proof.
  destruct_decide (decide (NeedGC sz ms σ t)); [right|left]; eauto using NotNeedWill,NeedNotWill.
Qed.


Definition ispoll t :=
  match find_ctxs t with
  | (_,tm_poll) => true
  | _ => false end.

Lemma IsPoll_fill_items_inv es t :
  to_val t = None ->
  IsPoll (fill_items es t) ->
  IsPoll t.
Proof.
  revert t.
  induction es; intros t Ht Ha; try done.
  simpl in *.
  apply IsPoll_fill_item_inv in Ha. eauto.
  destruct es; try done. apply to_val_fill_item.
Qed.

Lemma ispoll_correct t:
  ispoll t <-> IsPoll t.
Proof.
  unfold ispoll.
  destruct (find_ctxs t) eqn:Hc.
  split.
  { apply find_ctxs_correct2 in Hc. destruct Hc as (?&->).
    destruct t0; try done. intros _.
    induction l; by econstructor. }
  { intros Hpoll.
    assert (to_val t0 = None).
    { eapply find_ctxs_no_val; eauto using IsPoll_no_val. }
    apply find_ctxs_correct2 in Hc. destruct Hc as (?&->).
    apply IsPoll_fill_items_inv in Hpoll; eauto using IsPoll_no_val.
    inversion Hpoll. done. exfalso. subst.
    rewrite find_ctx_correct1 in H0; try done.
    eauto using IsPoll_no_val. }
Qed.

Global Instance ispoll_decision t : (Decision (IsPoll t)).
Proof.
  destruct_decide (decide (ispoll t)); [left|right]; rewrite -ispoll_correct //.
Qed.
