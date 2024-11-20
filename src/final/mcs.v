From Coq Require Import Program.Equality Wellfounded.
From stdpp Require Import base option relations.
From iris.proofmode Require Import proofmode.
From irisfit.lib Require Import qz.
From irisfit.language Require Import language syntax_instances.
From irisfit.final Require Import common.

Fixpoint tm_size' (t : tm):= 1 +
  match t with
  | tm_var _ => 0
  | tm_val v =>
      match v with
      | (val_code _ _ code) => tm_size' code
      | _ => 0 end
  | tm_enter | tm_exit | tm_poll => 1
  | tm_call t1 xs => tm_size' t1 + list_sum (tm_size' <$> xs)
  | tm_let _ t1 t2 | tm_load t1 t2 | tm_call_prim _ t1 t2   => tm_size' t1 + tm_size' t2
  | tm_alloc t1 => tm_size' t1
  | tm_store t1 t2 t3 | tm_if t1 t2 t3 => tm_size' t1 + tm_size' t2 + tm_size' t3
  | tm_cas t1 t2 t3 t4 => tm_size' t1 + tm_size' t2 + tm_size' t3 + tm_size' t4
  | tm_fork t1  => 1 + tm_size' t1 (* Adding one so  size () + size t < size (fork t) *)
  end.

(* max code size *)
Inductive mcs (n:nat) : tm -> Prop :=
| mcs1 : forall self args body,
    tm_size body <= n ->
    mcs n body ->
    mcs n (tm_val (val_code self args body))
| mcs1' : forall v,
    match v with
    | (val_code _ _ code) => False
    | _ => True end ->
    mcs n (tm_val v)
| mcs2 : forall x, mcs n (tm_var x)
| mcs3 : mcs n tm_enter
| mcs4 : mcs n tm_exit
| mcs5 : mcs n tm_poll
| mcs6 : forall t1 xs,
    mcs n t1 ->
    Forall (mcs n) xs ->
    mcs n (tm_call t1 xs)
| mcs7 : forall b t1 t2,
    mcs n t1 ->
    mcs n t2 ->
    mcs n (tm_let b t1 t2)
| mcs8 : forall t1 t2,
    mcs n t1 ->
    mcs n t2 ->
    mcs n (tm_load t1 t2)
| mcs9 : forall p t1 t2,
    mcs n t1 ->
    mcs n t2 ->
    mcs n (tm_call_prim p t1 t2)
| mcs10 : forall t,
    mcs n t ->
    mcs n (tm_alloc t)
| mcs10' : forall t,
    mcs n t ->
    mcs n (tm_fork t)
| mcs11 : forall t1 t2 t3,
    mcs n t1 ->
    mcs n t2 ->
    mcs n t3 ->
    mcs n (tm_if t1 t2 t3)
| mcs12 : forall t1 t2 t3,
    mcs n t1 ->
    mcs n t2 ->
    mcs n t3 ->
    mcs n (tm_store t1 t2 t3)
| mcs13 : forall t1 t2 t3 t4,
    mcs n t1 ->
    mcs n t2 ->
    mcs n t3 ->
    mcs n t4 ->
    mcs n (tm_cas t1 t2 t3 t4).

#[local] Hint Constructors mcs : mcs.

Lemma mcs_fill_item_inv1 n E t :
  mcs n (fill_item E t) ->
  mcs n t.
Proof.
  destruct E; inversion 1; subst; eauto.
  eapply list.Forall_forall; eauto. set_solver.
Qed.

Lemma mcs_fill_item_inv2 n E t :
  mcs n (fill_item E t) ->
  forall t', mcs n t' -> mcs n (fill_item E t').
Proof.
  destruct E; inversion 1; subst; simpl; eauto using mcs.
  intros t' Ht'. constructor. done.
  apply Forall_app in H3.
  destruct H3 as (?&?). inversion H1. subst.
  rewrite Forall_app. split; first done. constructor; eauto.
Qed.

Lemma mcs_subst n x (v:val) t :
  mcs n v ->
  mcs n t ->
  mcs n (subst' x v t).
Proof.
  intros X1 X2. destruct x; try done.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  inversion X2; subst; simpl; eauto using mcs.
  { case_decide; eauto using mcs. }
  { constructor.
    { apply H; eauto. simpl. lia. }
    clear X2 H0. induction xs.
    { apply Forall_nil. }
    { inversion H1. subst x l. rewrite fmap_cons. apply Forall_cons.
      { apply H. simpl. lia. done. }
      { apply IHxs; last done. intros ???.
        apply H. simpl.  simpl in *.
        pose proof (tm_size_non_zero a). unfold "<$>" in *. lia.
        done. } } }
  { case_decide.
    all:constructor; eauto using mcs; apply H; simpl; eauto; lia. }
  all:(constructor; eauto using mcs; apply H; simpl; eauto; lia).
Qed.

Lemma mcs_substs' n xs vs body :
  mcs n body ->
  Forall (mcs n) (tm_val <$> vs) ->
  mcs n (substs' (zip xs vs) body).
Proof.
  revert vs body. induction xs; simpl; intros vs body Hmcs Hfor.
  eauto. destruct vs. done.
  simpl. rewrite fmap_cons in Hfor. inversion Hfor. subst x l.
  apply mcs_subst. done. eauto.
Qed.

Definition mcs_val M v :=
  match v with
  | val_code _ _ body => tm_size body ≤ M /\ mcs M body
  | _ => True end.

Definition block_inv M (b:block) :=
  match b with
  | BDeallocated => True
  | BBlock vs => Forall (mcs_val M) vs end.
Definition store_inv M (σ:store) :=
  map_Forall (fun (_:loc) => block_inv M) σ.

Lemma store_inv_alloc M σ l n :
  σ !! l = None ->
  store_inv M σ ->
  store_inv M (<[l:=BBlock (replicate n val_unit)]> σ).
Proof.
  intros ? Hinv.
  apply map_Forall_insert. done. split; last done.
  simpl. apply list.Forall_forall. intros ?.
  rewrite elem_of_replicate. intros (->&_). done.
Qed.

Lemma store_inv_insert M (n:nat) σ l bs (v:val) :
  mcs M v ->
  store_inv M σ ->
  σ !! l = Some (BBlock bs) ->
  store_inv M (<[l:=BBlock (<[n:=v]> bs)]> σ).
Proof.
  intros X1 Hinv Hl.
  apply map_Forall_insert_2; last done.
  apply Forall_insert.
  { apply Hinv in Hl. done. }
  { inversion X1. simpl. naive_solver. destruct v; naive_solver. }
Qed.

Lemma mcs_val_mcs M v :
  mcs_val M v ->
  mcs M v.
Proof.
  destruct v; eauto using mcs. simpl.
  intros ?. apply mcs1; naive_solver.
Qed.

Lemma atomic_step_mcs n t g σ t' g' σ' efs :
  store_inv n σ ->
  mcs n t ->
  atomic_step t g σ t' g' σ' efs ->
  mcs n t' /\ Forall (fun '(t,_) => mcs n t) (opt_to_list efs) /\ store_inv n σ'.
Proof.
  intros Hinv Hmcs Hstep.
  induction Hstep; subst.
  { destruct IHHstep as (?&?&?);
      eauto using mcs_fill_item_inv1,mcs_fill_item_inv2. }
  { inversion H; subst.
    2:{ split_and !; eauto using mcs. simpl.
        inversion Hmcs. subst. apply Forall_singleton. done. }
    simpl. split_and !. 2:constructor.
    { inversion H0; subst; inversion Hmcs; subst; eauto using mcs.
      { eauto using mcs_subst. }
      { apply mcs_substs'.
        { inversion H5. done. done. }
        { rewrite fmap_cons. apply Forall_cons; eauto. } }
      { destruct p,v1,v2; inversion H1; eauto using mcs. }
      { destruct b; eauto. }
      { apply Hinv in H2.  simpl in *. rewrite list.Forall_forall in H2.
        apply elem_of_list_lookup_2 in H5. apply H2 in H5.
        eauto using mcs_val_mcs. } }
    { inversion H0; subst; eauto.
      { apply store_inv_alloc; eauto. }
      { inversion Hmcs. apply store_inv_insert; eauto. }
      { case_decide; eauto. inversion Hmcs. apply store_inv_insert; eauto. } } }
Qed.

Lemma store_inv_gc M r σ σ' :
  gc r σ σ' ->
  store_inv M σ ->
  store_inv M σ'.
Proof.
  intros (Hd&X). rewrite /store_inv !map_Forall_lookup => Hinv.
  intros l x Hx.
  assert (l ∈ dom σ) as Hl.
  { rewrite Hd. by apply elem_of_dom. }
  assert (is_Some (σ !! l)) as (x'&Hx').
  { apply elem_of_dom. set_solver. }
  apply X in Hl. rewrite !lookup_total_alt Hx Hx' in Hl.
  destruct Hl as [Hl|(_&Hl)]; simpl in Hl; subst; eauto. done.
Qed.

Lemma step_gc_mcs sz ms n ρ ρ' :
  store_inv n ρ.2 ->
  step_default sz ms ρ ρ' ->
  Forall (fun '(t,_) => mcs n t) ρ.1 ->
  Forall (fun '(t,_) => mcs n t) ρ'.1 /\ store_inv n ρ'.2.
Proof.
  intros ? (c&_&Hstep) Hfor.
  inversion Hstep; subst.
  { rename H0 into Hπ.
    assert (exists l1 l2, θ = l1 ++ (t,g)::l2 /\ length l1 = π ) as (l1&l2&E&?).
    { do 2 eexists. split. symmetry. apply take_drop_middle. done.
      rewrite take_length. apply lookup_lt_Some in Hπ. lia. }
    subst. rewrite Forall_app in Hfor. destruct Hfor as (?&Ha).
    inversion Ha. subst x l. simpl.
    rewrite Forall_app.
    replace (length l1) with (length l1 + 0) by lia.
    rewrite insert_app_r. rewrite Forall_app. simpl.
    eapply atomic_step_mcs in H1; eauto. destruct H1 as (?&?&?).
    split_and !; try done. apply Forall_cons; done. }
  { split; first done. simpl. eauto using store_inv_gc. }
Qed.

Lemma mcs_weak n m t :
  mcs n t ->
  n <= m ->
  mcs m t.
Proof.
  intros Hmcs E.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size' PeanoNat.Nat.lt_wf_0)). inversion Hmcs; subst; eauto using mcs.
  { apply mcs1. lia. apply H; eauto. }
  { constructor.
    { apply H; eauto. simpl. lia. }
    { clear Hmcs H0. induction xs.
      { apply Forall_nil. }
      { inversion H1. subst x l. apply Forall_cons.
        { apply H; eauto. simpl. lia. }
        { apply IHxs; last done. intros ??.
          apply H. simpl.  simpl in *.
          pose proof (tm_size_non_zero a). unfold "<$>" in *. lia. } } } }
  all:constructor; apply H; eauto; simpl; lia.
Qed.

Lemma size_size' t :
  tm_size t <= tm_size' t.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; simpl.
  { destruct v; simpl; lia. }
  { assert (list_sum (tm_size <$> l) <= list_sum (tm_size' <$> l)).
    { induction l. simpl; lia.
      assert (list_sum (tm_size <$> l) ≤ list_sum (tm_size' <$> l)).
      { apply IHl. intros ??. apply H. simpl in *. unfold "<$>" in *. lia. }
      rewrite !fmap_cons. pose proof (H a). simpl in *. lia. }
    pose proof (H t). simpl in *. lia. }
  all:try pose proof (H t1); try pose proof (H t2); try pose proof (H t3); try pose proof (H t4); try pose proof (H t); simpl in *; lia.
  all:try lia.
Qed.

Lemma find_max t:
  exists n, mcs n t.
Proof.
  exists (tm_size' t).
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size' PeanoNat.Nat.lt_wf_0)).
  destruct t.
  { destruct v.
    1-4:by apply mcs1'.
    apply mcs1. simpl. pose proof (size_size' t). lia.
    eapply mcs_weak. apply H; simpl; lia.
    simpl. lia. }
  { constructor.
    { eapply mcs_weak. apply H; simpl; lia. simpl. lia. }
    { assert ((tm_size' (tm_call t l) <= (tm_size' (tm_call t l)))) by lia.
      remember (tm_size' (tm_call t l)) as x. rewrite {1}Heqx in H0. clear Heqx.
      induction l.
      { apply Forall_nil. }
      { apply Forall_cons.
        { eapply mcs_weak. apply H; simpl in *; try lia. simpl in *. lia. }
        { apply IHl. simpl in *.
          pose proof (tm_size_non_zero a). unfold "<$>" in *. lia. } } } }
  all:try constructor.
  all:eapply mcs_weak; [eapply H; simpl; lia| ].
  all:simpl; lia.
Qed.

Lemma rtc_step_mcs M sz ms ρ ρ' :
  store_inv M ρ.2 ->
  rtc (step_default sz ms) ρ ρ' ->
  Forall (fun '(t,_) => mcs M t) ρ.1 ->
  Forall (fun '(t,_) => mcs M t) ρ'.1 /\ store_inv M ρ'.2.
Proof.
  induction 2; eauto. intros Hstep.
  eapply step_gc_mcs in H0; eauto. destruct H0. eauto.
Qed.

Lemma rtc_step_mcs_init sz ms t :
  exists M, Always (step_default sz ms) (init t) (fun ρ => Forall (fun '(t,_) => mcs M t) ρ.1).
Proof.
  destruct (find_max t) as (M&?).
  exists M. intros ? Hsteps. eapply rtc_step_mcs in Hsteps; eauto. naive_solver.
  { apply map_Forall_empty. }
  { apply Forall_singleton. done. }
Qed.
