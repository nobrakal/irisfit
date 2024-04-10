From Coq Require Import ssreflect.
From stdpp Require Import base binders gmap gmultiset.
From Equations Require Import Equations.

From irisfit Require Import syntax.

Fixpoint find_ctx_list (ts:list tm) : option (list val * tm * list tm) :=
  match ts with
  | [] => None
  | t::ts =>
      match to_val t with
      | Some v =>
          match find_ctx_list ts with
          | None => None
          | Some (vs,t',ts') => Some (v::vs,t',ts') end
      | None => Some ([],t,ts) end end.

Definition find_ctx (t:tm) : option (ctx * tm) :=
  match t with
  | tm_val _ | tm_var _ | tm_enter | tm_exit | tm_poll | tm_fork _ => None
  | tm_alloc t1 =>
      match to_val t1 with
      | Some v => None
      | None => Some (ctx_alloc, t1) end
  | tm_if t1 t2 t3 =>
      match to_val t1 with
      | Some v => None
      | None => Some (ctx_if t2 t3,t1) end
  | tm_load t1 t2 =>
      match to_val t1 with
      | Some v1 =>
          match to_val t2 with
          | Some v2 => None
          | None => Some (ctx_load2 v1, t2) end
      | None => Some (ctx_load1 t2,t1) end
  | tm_store t1 t2 t3 =>
      match to_val t1 with
      | Some v1 =>
          match to_val t2 with
          | Some v2 =>
              match to_val t3 with
              | Some _ => None
              | None => Some (ctx_store3 v1 v2, t3) end
          | None => Some (ctx_store2 v1 t3, t2) end
      | None => Some (ctx_store1 t2 t3,t1) end
  | tm_call_prim p t1 t2 =>
      match to_val t1 with
      | Some v1 =>
          match to_val t2 with
          | Some _ => None
          | None => Some (ctx_call_prim2 p v1, t2) end
      | None => Some (ctx_call_prim1 p t2, t1) end
  | tm_let x t1 t2 =>
      match to_val t1 with
      | Some _ => None
      | None => Some (ctx_let x t2,t1) end
  | tm_cas t1 t2 t3 t4 =>
      match to_val t1 with
      | Some v1 =>
          match to_val t2 with
          | Some v2 =>
              match to_val t3 with
              | Some v3 =>
                  match to_val t4 with
                  | Some _ => None
                  | None => Some (ctx_cas4 v1 v2 v3, t4) end
              | None => Some (ctx_cas3 v1 v2 t4, t3) end
          | None => Some (ctx_cas2 v1 t3 t4, t2) end
      | None => Some (ctx_cas1 t2 t3 t4,t1) end
  | tm_call t ts =>
      match to_val t with
      | Some v =>
          match find_ctx_list ts with
          | None => None
          | Some (vs,t,ts) =>
              Some (ctx_call2 v vs ts,t) end
      | None => Some (ctx_call1 ts,t) end
  end.

Lemma find_ctx_list_correct1 vs t ts:
  to_val t = None ->
  find_ctx_list ((tm_val <$> vs) ++ t :: ts) = Some (vs,t,ts).
Proof.
  intros Ht. induction vs; simpl; rewrite ?Ht ?IHvs //.
Qed.

Lemma find_ctx_list_correct2 l vs t ts :
  find_ctx_list l = Some (vs, t, ts) ->
  to_val t = None /\ l = (tm_val <$> vs) ++ t::ts.
Proof.
  revert vs t ts. induction l; intros vs t ts.
  { inversion 1. }
  simpl.
  destruct (to_val a) eqn:Hv.
  { destruct (find_ctx_list l) as [((?,?),?)|]; inversion 1. subst.
    specialize (IHl _ _ _ eq_refl). destruct IHl as [? ->]. split; first done.
    apply to_val_Some in Hv. subst. done. }
  { inversion 1. subst. done. }
Qed.

Lemma find_ctx_list_correct3 xs :
  find_ctx_list xs = None ->
  exists ys, xs = tm_val <$> ys.
Proof.
  induction xs; simpl; intros Hfind.
  { by exists nil. }
  { destruct (to_val a) eqn:Hv; last congruence.
    destruct (find_ctx_list xs) as [((?,?),?)|] eqn:Go; first congruence.
    destruct a; try done.
    apply IHxs in Hfind. destruct Hfind as (?&->). exists (v0::x). done. }
Qed.

Lemma find_ctx_correct1 E t :
  to_val t = None ->
  find_ctx (fill_item E t) = Some (E,t).
Proof.
  intros Ht.
  destruct E; simpl; try destruct (to_val t) eqn:Ht; rewrite ?Ht; try done.
  rewrite find_ctx_list_correct1 //.
Qed.

Ltac go :=
  match goal with
  | |- context G [to_val ?t] => destruct (to_val t) eqn:? end.

Ltac apply_to_val_some :=
  match goal with
  | H : to_val ?t = Some _ |- _ => apply to_val_Some in H; subst t end.

Ltac go_inv := go; try by inversion 1.

Lemma find_ctx_correct2 E t t' :
  find_ctx t = Some (E,t') ->
  to_val t' = None /\ t = fill_item E t'.
Proof.
  unfold find_ctx.
  destruct E; destruct t; repeat go_inv.
  all:try (destruct (find_ctx_list l) as [((?,?),?)|]; simpl in *; inversion 1; done).
  all:repeat apply_to_val_some.
  all:try(inversion 1; subst; done).
  1,2:destruct (find_ctx_list l0) as [((?,?),?)|] eqn:?; inversion 1.
  all:destruct (find_ctx_list l1) as [((?,?),?)|] eqn:?; inversion 1.
  all:subst; apply find_ctx_list_correct2 in Heqo; naive_solver.
Qed.

Definition fill_items (ks:list ctx) (t:tm) := List.fold_right fill_item t ks.

Lemma locs_fill_items ls e :
  locs (fill_items ls e) = locs ls ∪ locs e.
Proof.
  revert e. induction ls; intros e.
  { set_solver. }
  { simpl. rewrite locs_fill_item IHls. set_solver. }
Qed.

Lemma fill_items_app es1 es2 t:
  fill_items (es1++es2) t = fill_items es1 (fill_items es2 t).
Proof.
  rewrite /fill_items foldr_app //.
Qed.

Equations find_ctxs (t:tm) : (list ctx * tm) by wf (tm_size t) :=
  find_ctxs t :=
    match find_ctx t as c return (c = find_ctx t -> (list ctx * tm)) with
    | None => fun _ => ([],t)
    | Some (E,t) => fun _ =>
        let '(es,t) := find_ctxs t in (E::es,t) end eq_refl.
Next Obligation.
  symmetry in e. apply find_ctx_correct2 in e as (?&?).
  subst. apply tm_size_ctx_lt.
Qed.

Lemma find_ctxs_correct1 Es t :
  to_val t = None ->
  find_ctx t = None ->
  find_ctxs (fill_items Es t) = (Es,t).
Proof.
  intros Ht1 Ht2.
  induction Es; rewrite find_ctxs_equation_1; simpl.
  { rewrite Ht2 //. }
  { rewrite find_ctx_correct1.
    { rewrite IHEs //. }
    { destruct Es; try done. simpl. apply to_val_fill_item. } }
Qed.

Lemma find_ctxs_correct2 Es t t' :
  find_ctxs t = (Es,t') ->
  find_ctx t' = None /\ t = fill_items Es t'.
Proof.
  revert t; induction Es; intros t; rewrite find_ctxs_equation_1; simpl.
  { destruct (find_ctx t) as [(?,?)|] eqn:Ht.
    { destruct (find_ctxs t0); inversion 1. }
    { inversion 1. subst. done. } }
  { destruct (find_ctx t) as [(?,?)|] eqn:He; simpl; last inversion 1.
    destruct (find_ctxs t0) eqn:Ht0. inversion 1. subst.
    destruct (IHEs _ Ht0) as (?&?). subst. split; first done.
    apply find_ctx_correct2 in He. destruct He as (?&?). subst. done. }
Qed.

Lemma find_ctxs_no_val es t t' :
  to_val t = None ->
  find_ctxs t = (es,t') ->
  to_val t' = None.
Proof.
  revert t; induction es; intros t Ht; rewrite find_ctxs_equation_1; simpl.
  { destruct (find_ctx t) as [(?,?)|] eqn:?.
    { destruct (find_ctxs t0); inversion 1. }
    { inversion 1. subst. done. } }
  { destruct (find_ctx t) as [(?,?)|] eqn:He; simpl; last inversion 1.
    destruct (find_ctxs t0) eqn:Ht0. inversion 1. subst.
    apply find_ctx_correct2 in He. destruct He as (X&?). subst.
    eauto. }
Qed.
