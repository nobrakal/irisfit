From Coq Require Import ssreflect Wellfounded.
From stdpp Require Import base binders gmap gmultiset list.

From irisfit Require Import syntax notation.

From irisfit.final Require Import final_semantics temporal_logic.


Inductive weak_anf : tm -> Prop :=
| wa1 : forall v,
    weak_anf_val v ->
    weak_anf v
| wa2 : forall x, weak_anf (tm_var x)
| wa3 : weak_anf tm_enter
| wa4 : weak_anf tm_exit
| wa5 : weak_anf tm_poll
| wa6 : forall t1 xs,
    base_anf t1 ->
    Forall base_anf xs ->
    weak_anf (tm_call t1 xs)
| wa7 : forall b t1 t2,
    weak_anf t1 ->
    weak_anf t2 ->
    weak_anf (tm_let b t1 t2)
| wa8 : forall t1 t2,
    weak_anf t1 ->
    weak_anf t2 ->
    weak_anf (tm_load t1 t2)
| wa9 : forall p t1 t2,
    weak_anf t1 ->
    weak_anf t2 ->
    weak_anf (tm_call_prim p t1 t2)
| wa10 : forall t,
    weak_anf t ->
    weak_anf (tm_alloc t)
| wa10' : forall t,
    weak_anf t ->
    weak_anf (tm_fork t)
| wa11 : forall t1 t2 t3,
    weak_anf t1 ->
    weak_anf t2 ->
    weak_anf t3 ->
    weak_anf (tm_if t1 t2 t3)
| wa12 : forall t1 t2 t3,
    weak_anf t1 ->
    weak_anf t2 ->
    weak_anf t3 ->
    weak_anf (tm_store t1 t2 t3)
| wa13 : forall t1 t2 t3 t4,
    weak_anf t1 ->
    weak_anf t2 ->
    weak_anf t3 ->
    weak_anf t4 ->
    weak_anf (tm_cas t1 t2 t3 t4)
with weak_anf_val : val -> Prop :=
| wav1 : forall self args body,
    weak_anf body ->
    weak_anf_val (val_code self args body)
| wav2 : forall v,
    (match v with val_code _ _ _ => False | _ => True end) ->
    weak_anf_val v
with base_anf : tm -> Prop :=
| ba1 : forall x,
    base_anf (tm_var x)
| ba2 : forall v,
    weak_anf_val v ->
    base_anf (tm_val v)
.

#[local] Hint Constructors weak_anf  weak_anf_val base_anf : anf.

Definition weak_anf_block b :=
  match b with
  | BDeallocated => True
  | BBlock vs => Forall weak_anf_val vs end.

Definition store_inv (σ:store) :=
  map_Forall (fun _ => weak_anf_block) σ.

Definition weak_anf_opt t :=
  match t with
  | None => True
  | Some t => weak_anf t end.

Definition weak_anf_ctx (E:ctx) : Prop :=
  match E with
  | ctx_let b t => weak_anf t
  | ctx_call1 ts => Forall base_anf ts
  | ctx_call2 v vs ts =>
      weak_anf_val v /\ Forall weak_anf_val vs /\ Forall base_anf ts
  | ctx_call_prim1 p t => weak_anf t
  | ctx_call_prim2 p v => weak_anf_val v
  | ctx_if t1 t2 => weak_anf t1 /\ weak_anf t2
  | ctx_alloc => True
  | ctx_load1 t => weak_anf t
  | ctx_load2 v => weak_anf_val v
  | ctx_store1 t1 t2 => weak_anf t1 /\ weak_anf t2
  | ctx_store2 v1 t2 => weak_anf_val v1 /\ weak_anf t2
  | ctx_store3 v1 v2 => weak_anf_val v1 /\ weak_anf_val v2
  | ctx_cas1 t1 t2 t3 => weak_anf t1 /\ weak_anf t2 /\ weak_anf t3
  | ctx_cas2 v1 t2 t3 => weak_anf_val v1 /\ weak_anf t2 /\ weak_anf t3
  | ctx_cas3 v1 v2 t3 => weak_anf_val v1 /\ weak_anf_val v2 /\ weak_anf t3
  | ctx_cas4 v1 v2 v3 => weak_anf_val v1 /\ weak_anf_val v2 /\ weak_anf v3 end.

Lemma base_weak t :
  base_anf t ->
  weak_anf t.
Proof.
  inversion 1; subst; eauto with anf.
Qed.

Lemma weak_anf_to_val (v:val) :
  weak_anf v ->
  weak_anf_val v.
Proof.
  by inversion 1.
Qed.

Definition is_ctx_call E :=
  match E with
  | ctx_call1 _ | ctx_call2 _ _ _ => True
  | _ => False end.

Lemma weak_anf_fill_item_inv E t :
  weak_anf (fill_item E t) ->
  weak_anf_ctx E /\ weak_anf t /\ (is_ctx_call E -> base_anf t).
Proof.
  destruct E; simpl; inversion 1; subst;
    try naive_solver by eauto using weak_anf_to_val with anf.
  { split; eauto using Forall_impl,base_weak. }
  { apply Forall_app in H3. destruct H3.
    inversion H1. subst.
    split_and !; eauto using Forall_impl,base_weak,weak_anf_to_val with anf.
    apply list.Forall_forall. intros ??.
    eapply list.Forall_forall in H0; eauto using base_weak,weak_anf_to_val.
    apply elem_of_list_fmap. eauto. }
Qed.

Lemma weak_anf_fill_item E t :
  weak_anf t ->
  (is_ctx_call E -> base_anf t) ->
  weak_anf_ctx E ->
  weak_anf (fill_item E t).
Proof.
  intros Ht.
  destruct E; simpl; eauto with anf.
  { intros Hbase (X1&X2&X3). constructor; eauto with anf.
    apply Forall_app. split.
    { apply list.Forall_forall. intros ? Hx.
      apply elem_of_list_fmap in Hx. destruct Hx as (?&->&Hx).
      eapply list.Forall_forall in X2; eauto with anf. }
    { constructor; eauto. } }
  all:intros _.
  all:intros; constructor; try naive_solver.
  all:constructor; naive_solver.
Qed.

Lemma atomic_step_no_var x g1 σ1 t2 g2 σ2 efs :
  atomic_step (tm_var x) g1 σ1 t2 g2 σ2 efs -> False.
Proof.
  inversion 1; subst. by destruct E.
  inversion H0; subst. by inversion H1.
Qed.

Lemma base_anf_subst s v t :
  weak_anf_val v ->
  base_anf t ->
  base_anf (subst s v t).
Proof.
  inversion 2; subst; simpl; [case_decide; eauto with anf| done].
Qed.

Lemma weak_anf_subst x v t :
  weak_anf_val v ->
  weak_anf t ->
  weak_anf (subst' x v t).
Proof.
  destruct x; first done. simpl.
  intros X1.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)); intros X2.
  inversion X2; subst; simpl; eauto with anf.
  { case_decide; eauto with anf. }
  { constructor.
    { eauto using base_anf_subst. }
    { clear X2 H0 H. induction xs. done.
      rewrite fmap_cons. inversion H1. subst.
      constructor; eauto using base_anf_subst. } }
  { case_decide; subst; constructor; eauto; apply H; simpl; eauto; lia. }
  all:constructor; apply H; eauto; simpl; lia.
Qed.

Lemma weak_anf_substs xs t :
  Forall (fun '(_,v) => weak_anf_val v) xs ->
  weak_anf t ->
  weak_anf (substs' xs t).
Proof.
  intros Hfor Hweak. induction xs as [|(?,?)].
  { eauto. }
  { simpl. inversion Hfor. subst.
    apply weak_anf_subst; eauto. }
Qed.

Lemma store_inv_alloc σ l n :
  σ !! l = None ->
  store_inv σ ->
  store_inv (<[l:=BBlock (replicate n val_unit)]> σ).
Proof.
  intros ? Hinv.
  apply map_Forall_insert. done. split; last done.
  simpl. apply list.Forall_forall. intros ?.
  rewrite elem_of_replicate. intros (->&_). by constructor.
Qed.

Lemma store_inv_insert (n:nat) σ l bs (v:val) :
  weak_anf_val v ->
  store_inv σ ->
  σ !! l = Some (BBlock bs) ->
  store_inv (<[l:=BBlock (<[n:=v]> bs)]> σ).
Proof.
  intros X1 Hinv Hl.
  apply map_Forall_insert_2; last done.
  apply Forall_insert.
  { apply Hinv in Hl. done. }
  { inversion X1. simpl. naive_solver. destruct v; naive_solver. }
Qed.

Lemma store_inv_load σ l (bs:list val) n (v:val) :
  store_inv σ ->
  σ !! l = Some (BBlock bs) ->
  bs !! n = Some v ->
  weak_anf v.
Proof.
  intros Hstore X1 X2.
  apply map_Forall_lookup in Hstore.
  apply Hstore in X1. simpl in X1.
  eapply Forall_lookup in X1; eauto with anf.
Qed.

Lemma head_step_conc_weak_anf t1 g1 σ1 t2 g2 σ2 efs :
  weak_anf t1 ->
  store_inv σ1 ->
  head_step_conc t1 g1 σ1 t2 g2 σ2 efs ->
  weak_anf t2 /\ store_inv σ2 /\ weak_anf_opt efs.
Proof.
  intros Hweak Hstore. inversion 1; subst; simpl.
  2:{ split_and !; eauto with anf. by inversion Hweak. }
  rewrite right_id.
  inversion H0; subst; inversion Hweak; subst; eauto with anf.
  { split; last done. eauto using weak_anf_subst, weak_anf_to_val. }
  { split; last done. inversion H5. subst. inversion H4; last done. subst.
    apply weak_anf_substs; eauto.
    simpl. apply Forall_cons. done.
    clear Hweak H0 H H5 H4.
    revert args H1. induction vs; intros args Hargs.
    { destruct args. constructor. simpl in Hargs. lia. }
    { destruct args. simpl in Hargs. lia. simpl.
      inversion H6. subst. constructor; eauto using base_weak,weak_anf_to_val. } }
  { split; last done. destruct p,v1,v2; inversion H1; subst; eauto with anf. }
  { destruct b; eauto with anf. }
  { eauto using store_inv_alloc with anf. }
  { eauto using store_inv_load with anf. }
  { eauto 15 using store_inv_insert,weak_anf_to_val with anf. }
  { split; eauto with anf. case_decide; eauto 15 using store_inv_insert,weak_anf_to_val with anf. }
Qed.

Lemma atomic_step_weak_anf t1 g1 σ1 t2 g2 σ2 efs :
  weak_anf t1 ->
  store_inv σ1 ->
  atomic_step t1 g1 σ1 t2 g2 σ2 efs ->
  weak_anf t2 /\ store_inv σ2 /\ weak_anf_opt efs.
Proof.
  intros Hweak Hstore Hstep.
  induction Hstep; subst.
  { apply weak_anf_fill_item_inv in Hweak. destruct Hweak as (X1&X2&X3).
    edestruct IHHstep as (?&?&?); eauto.
    split_and !; eauto. apply weak_anf_fill_item; eauto.
    { intros HC. apply X3 in HC. inversion HC; subst.
      { exfalso. eauto using atomic_step_no_var. }
      { exfalso. by apply atomic_step_no_val in Hstep. } } }
  { eauto using head_step_conc_weak_anf. }
Qed.

Lemma atomic_step_weak_anf_rtc ρ ρ' :
  Forall weak_anf ρ.1.*1 ->
  store_inv ρ.2 ->
  rtc step_oblivious ρ ρ' ->
  Forall weak_anf ρ'.1.*1 /\ store_inv ρ'.2.
Proof.
  intros Hfor Hstore. induction 1. done.
  destruct x as (θ,σ),y as (θ',σ').
  inversion H; subst.
  rewrite fmap_app fmap_cons in Hfor.
  apply Forall_app in Hfor. destruct Hfor as (?&Hfor). inversion Hfor. subst.
  apply atomic_step_weak_anf in H7; eauto.
  destruct H7 as (?&?&?).
  apply IHrtc; eauto. rewrite fmap_app fmap_cons fmap_app.
  apply Forall_app. split; eauto. constructor; eauto.
  apply Forall_app. split; eauto. destruct efs; constructor; eauto.
Qed.

Lemma store_inv_gc r σ σ' :
  store_inv σ ->
  gc r σ σ' ->
  store_inv σ'.
Proof.
  intros Hs [Hd Hr] l b' Hl.
  assert (l ∈ dom σ) as Hl'.
  { rewrite Hd. by eapply elem_of_dom. }
  assert (is_Some (σ !! l)) as (b&Hb).
  { by eapply elem_of_dom. }
  destruct (Hr _ Hl') as [E|(_&E)].
  { rewrite !lookup_total_alt Hl Hb in E.
    eapply Hs; eauto. naive_solver. }
  { rewrite lookup_total_alt Hl in E.
    replace b' with BDeallocated by naive_solver. done. }
Qed.

Lemma atomic_step_gc_weak_anf_rtc sz ms ρ ρ' :
  Forall weak_anf ρ.1.*1 ->
  store_inv ρ.2 ->
  rtc (step_default sz ms) ρ ρ' ->
  Forall weak_anf ρ'.1.*1 /\ store_inv ρ'.2.
Proof.
  intros Hfor Hstore. induction 1. done.
  destruct x as (θ,σ),y as (θ',σ').
  destruct H as (c&Hen&Hstep).
  inversion Hstep; subst.
  { apply elem_of_middle in H5. destruct H5 as (l1&l2&->&?).
    rewrite fmap_app fmap_cons in Hfor.
    apply Forall_app in Hfor. destruct Hfor as (?&Hfor). inversion Hfor. subst.
    apply atomic_step_weak_anf in H6; eauto.
    destruct H6 as (?&?&?).
    apply IHrtc; eauto.
    rewrite insert_app_r_alt // Nat.sub_diag. simpl.
    rewrite fmap_app fmap_app fmap_cons. simpl.
    apply Forall_app. split; eauto.
    { apply Forall_app. split. eauto. constructor; eauto. }
    { destruct efs; constructor; eauto. } }
  { eauto using store_inv_gc. }
Qed.

Lemma weak_anf_always sz ms t :
  weak_anf t ->
  Always (step_default sz ms) (init t) (λ '(θ, _), Forall weak_anf θ.*1).
Proof.
  intros  ? (?,?) Hrtc.
  eapply atomic_step_gc_weak_anf_rtc in Hrtc. naive_solver.
  { by constructor. }
  { intros ??. naive_solver. }
Qed.
