From Coq Require Import ssreflect Wellfounded.
From stdpp Require Import base binders gmap gmultiset ssreflect.

From irisfit Require Import syntax notation.
From irisfit.final Require Import common mcs instances addpp.

Definition isaddpp t := exists t', t = addpp t'.
Definition isaddpp_val v := exists v', v = addpp_val v'.

(* [alctx t] describes an evaluation context where all branches
   are of the form [addpp _] *)
Definition alctx (E:ctx) : Prop :=
  match E with
  | ctx_let b t => isaddpp t
  | ctx_call1 ts => Forall isaddpp ts
  | ctx_call2 v vs ts =>
      isaddpp_val v /\ Forall isaddpp_val vs /\ Forall isaddpp ts
  | ctx_call_prim1 p t => isaddpp t
  | ctx_call_prim2 p v => isaddpp_val v
  | ctx_if t1 t2 => isaddpp t1 /\ isaddpp t2
  | ctx_alloc => True
  | ctx_load1 t => isaddpp t
  | ctx_load2 v => isaddpp_val v
  | ctx_store1 t1 t2 => isaddpp t1 /\ isaddpp t2
  | ctx_store2 v1 t2 => isaddpp v1 /\ isaddpp t2
  | ctx_store3 v1 v2 => isaddpp v1 /\ isaddpp v2
  | ctx_cas1 t1 t2 t3 => isaddpp t1 /\ isaddpp t2 /\ isaddpp t3
  | ctx_cas2 v1 t2 t3 => isaddpp_val v1 /\ isaddpp t2 /\ isaddpp t3
  | ctx_cas3 v1 v2 t3 => isaddpp_val v1 /\ isaddpp_val v2 /\ isaddpp t3
  | ctx_cas4 v1 v2 v3 => isaddpp_val v1 /\ isaddpp_val v2 /\ isaddpp v3 end.

(* almost captures the fact that during evaluation, the code looks "almost"
   like an addpp.
   The nat captures the "distance" to an addpp config. *)
Inductive almost : nat -> tm -> Prop :=
| Al1 : forall t, almost 0 (addpp t)
| Al2 : forall n E t,
    alctx E ->
    to_val t = None ->
    almost n t ->
    almost (S n) (fill_item E t)
| Al41 : forall t ts,
    isaddpp t ->
    Forall isaddpp ts ->
    almost 1 (tm_let BAnon val_unit (tm_call t ts))
| Al42 : forall v vs,
    isaddpp_val v ->
    Forall isaddpp_val vs ->
    almost 1 (tm_call v (tm_val <$> vs)).

Definition almostex t := exists n, almost n t.

Lemma addpp_fill_item_inv E t t0 :
  fill_item E t = addpp t0 ->
  exists t', t = addpp t'.
Proof.
  destruct E; simpl.
  { destruct t0; inversion 1; subst; simpl in *.
    by exists tm_poll. by eexists.  }
  all:destruct t0; inversion 1; subst; eauto.
  all:try by destruct v.
  all:try by destruct v0.
  all:try by destruct v1.
  all:try by destruct v2.
Qed.

Lemma al1 (t' t:tm) :
  t = addpp t' ->
  almost 0 t.
Proof.
  intros ->. apply Al1.
Qed.

Lemma addpp_fill_item_inv2 t' E (t:tm) :
  t ≠ tm_poll ->
  isaddpp (fill_item E t) ->
  isaddpp t' ->
  isaddpp (fill_item E t').
Proof.
  intros Ht (t0&Ht0) (t1&Ht1).
  destruct E; simpl.
  { destruct t0; inversion Ht0; subst; simpl in *.
    { congruence. }
    { by eexists (let: b0 := t1 in t0_2)%T. } }
  all:destruct t0; inversion Ht0; subst; eauto.
  { by exists (tm_call_prim p0 (t1) (t0_2)). }
  { rewrite H1. by exists (tm_call_prim p0 (t0_1) (t1)). }
  { by exists (if: t1 then t0_2 else t0_3)%T. }
  { by exists ((tm_alloc (t1))). }
  { by exists ((t1).[t0_2])%T. }
  { rewrite H0. by exists ((t0_1).[t1])%T. }
  { by exists ((t1).[t0_2] <- (t0_3))%T. }
  { rewrite H0. by exists ((t0_1).[t1] <- (t0_3))%T. }
  { rewrite H0 H1. by exists ((t0_1).[t0_2] <- (t1))%T. }
  { by exists (tm_cas t1 t0_2 t0_3 (t0_4))%T. }
  { rewrite H0. by exists (tm_cas t0_1 t1 t0_3 (t0_4)). }
  { rewrite H0 H1. by exists (tm_cas t0_1 t0_2 t1 (t0_4)). }
  { rewrite H0 H1 H2. by exists (tm_cas t0_1 t0_2 t0_3 (t1)). }
Qed.

Lemma isaddpp_fill_item_inv E t :
  isaddpp (fill_item E t) ->
  isaddpp t.
Proof.
  intros (?&X).
  apply addpp_fill_item_inv in X. eauto.
Qed.

Lemma almost_fill_item_inv E t :
  to_val t = None ->
  almostex (fill_item E t) ->
  almostex t.
Proof.
  intros Ht. intros (n&Hn). inversion Hn.
  { symmetry in H1. apply addpp_fill_item_inv in H1. destruct H1 as (?&->).
    exists 0. apply Al1. }
  { apply fill_item_inj in H; eauto. subst. eexists. naive_solver. }
  { exfalso. destruct E; inversion H. subst. naive_solver. }
  { destruct E; inversion H; subst.
    { exists 0. by apply al1 with v. }
    { apply (@f_equal _ _ (fun x => x !! (length (tm_val <$> l)))) in H5.
      rewrite lookup_app_r in H5. 2:lia.
      rewrite Nat.sub_diag in H5. simpl in *.
      rewrite list_lookup_fmap in H5.
      destruct (vs !! length (tm_val <$> l)) eqn:?; last by inversion H5.
      destruct t; inversion H5. subst. eapply list.Forall_forall in H2.
      2:{ apply elem_of_list_lookup. eauto. }
      exists 0. by apply al1 with v1. } }
Qed.

Lemma atomic_step_addpp_almost_forked t g σ t' g' σ' efs :
  almostex t ->
  atomic_step t g σ t' g' σ' efs ->
  Forall (λ '(t0, _), almost 0 t0) (opt_to_list efs).
Proof.
  intros Ha.
  induction 1.
  { apply IHatomic_step. subst.
    eapply almost_fill_item_inv; eauto using atomic_step_no_val. }
  inversion H; subst.
  { apply Forall_nil. }
  { simpl. destruct Ha as (n&Ha). inversion Ha.
    { destruct t0; inversion H2.
      subst. apply Forall_singleton, Al1. }
    { exfalso. destruct E; inversion H0. } }
Qed.

Lemma addpp_let_val t0 x (v:val) t :
  addpp t0 = (let: x := v in t)%T ->
  isaddpp (subst' x v t).
Proof.
  intros Eq.
  destruct t0; inversion Eq. subst.
  apply addpp_val_inv in H1. destruct H1 as (v'&->&->).
  rewrite subst'_addpp_val //. by eexists.
Qed.

Lemma addpp_if_almost t0 (b:bool) t1 t2 :
  addpp t0 = (if: b then t1 else t2)%T ->
  isaddpp (if b then t1 else t2) .
Proof.
  destruct t0; simpl in *; inversion 1. subst. destruct b; by eexists.
Qed.

Lemma isaddpp_fill_items_no_poll (t1 t2:tm) es :
  t1 ≠ tm_poll ->
  isaddpp t2 ->
  isaddpp (fill_items es t1) ->
  isaddpp (fill_items es t2).
Proof.
  revert t1 t2.
  induction es; intros t1 t2 E (?&->).
  { intros _. by eexists. }
  { simpl. intros ?.
    eapply addpp_fill_item_inv2. 2:done.
    2:{ eapply IHes; try done. by eexists.
        apply isaddpp_fill_item_inv in H. done. }
    destruct es.
    { destruct x; naive_solver. }
    by destruct c. }
Qed.

Lemma al1' t :
  isaddpp t ->
  almost 0 t.
Proof.
  intros (?&->). apply Al1.
Qed.

Lemma isaddpp_fill_items_inv es t :
  isaddpp (fill_items es t) ->
  isaddpp t.
Proof.
  revert t. induction es; intros t. done.
  simpl. intros (x&Hx).
  apply addpp_fill_item_inv in Hx. eauto.
Qed.

Lemma isaddpp_fill_item_inv_ctx E t :
  t ≠ tm_poll ->
  isaddpp (fill_item E t) ->
  alctx E.
Proof.
  intros ? (x&Hx). destruct E; destruct x; inversion Hx; subst; simpl in *; try done.
  all:try split_and !; try by eexists.
  { destruct x1; inversion H2. by eexists. }
  { destruct x1; inversion H1. by eexists. }
  { destruct x1; inversion H1. by eexists. }
  { destruct x1; inversion H1. by eexists. }
  { destruct x2; inversion H2. by eexists. }
  { destruct x1; inversion H1. by eexists. }
  { destruct x2; inversion H2. by eexists. }
Qed.

Lemma isaddpp_inv_call es b t1 ts :
  isaddpp (fill_items es (let: b := tm_poll in tm_call t1 ts)) ->
  isaddpp t1 /\ exists xs, ts = addpp <$> xs.
Proof.
  induction es.
  { intros (x&Hx). destruct x; inversion Hx; subst.
    split; eauto. by eexists.
    destruct x2; inversion H2. }
  { intros His. simpl in *.
    eauto using isaddpp_fill_item_inv. }
Qed.

Lemma isaddpp_let_call E es :
  is_let_call E ->
  isaddpp (fill_items es (fill_item E tm_poll)) ->
  almost (S (length es)) (fill_items es (fill_item E ()%V)).
Proof.
  destruct E; try done. simpl. destruct b; try done.
  destruct t; try done. intros _.
  intros His.
  pose proof (isaddpp_inv_call _ _ _ _ His) as ((?&->)&(?&->)).
  induction es; simpl in *.
  { apply Al41. by eexists. apply list.Forall_forall.
    intros ?. rewrite elem_of_list_fmap. intros (?&->&_). by eexists. }
  { apply Al2.
    { eapply isaddpp_fill_item_inv_ctx; eauto. destruct es; try done. by destruct c. }
    { destruct es; try done. apply to_val_fill_item. }
    { apply IHes. eauto using isaddpp_fill_item_inv. } }
Qed.

Lemma go_poll_exit E :
  ¬ is_let_call E ->
  isaddpp (fill_item E tm_poll) ->
  isaddpp (fill_item E ()%V).
Proof.
  intros X1 (x&Hx).
  destruct E; inversion Hx; try done.
  all:destruct x; inversion H0; subst; simpl in *; try done.
  { by exists (tm_let b0 ()%V (x2))%T. }
  { by exists ((tm_call_prim p0 ()%V (x2)))%T. }
  { rewrite H2. by exists (tm_call_prim p0 (x1) ()%V)%T. }
  { by exists (if: ()%V then x2 else x3)%T. }
  { by exists (tm_alloc ()%V)%T. }
  { by exists (().[x2])%T. }
  { rewrite H1. by exists ((x1).[()])%T. }
  { by exists (().[x2] <- (x3))%T. }
  { rewrite H1. by exists ((x1).[()] <- (x3))%T. }
  { rewrite H1 H2. by exists ((x1).[x2] <- ())%T. }
  { by exists (tm_cas ()%V x2 x3 x4). }
  { rewrite H1. by exists (tm_cas x1 ()%V x3 x4). }
  { rewrite H1 H2. by exists (tm_cas x1 x2 ()%V x4). }
  { rewrite H1 H2 H3. by exists (tm_cas x1 x2 x3 ()%V). }
Qed.

Lemma isaddpp_no_let E es :
  ¬ is_let_call E ->
  isaddpp (fill_items es (fill_item E tm_poll)) ->
  isaddpp (fill_items es (fill_item E ()%V)).
Proof.
  intros ? His. induction es; simpl in *.
  { by eapply go_poll_exit. }
  { eapply addpp_fill_item_inv2; eauto.
    { destruct es. by destruct E. by destruct c. }
    { apply IHes. by eapply isaddpp_fill_item_inv. } }
Qed.

Lemma go_poll es :
  isaddpp (fill_items es tm_poll) ->
  almostex (fill_items es ()%V).
Proof.
  destruct (list_inv_r es) as [|(es'&E&->)]; subst; intros His.
  { exists 0. apply al1'. by exists val_unit. }
  { rewrite fill_items_app. rewrite fill_items_app in His. simpl in *.
    destruct_decide (decide (is_let_call E)).
    { eexists. eauto using isaddpp_let_call. }
    { exists 0. by eapply al1', isaddpp_no_let. } }
Qed.

Definition block_inv (b:block) :=
  match b with
  | BDeallocated => True
  | BBlock vs => Forall isaddpp_val vs end.
Definition store_inv (σ:store) :=
  map_Forall (fun (_:loc) => block_inv) σ.

Lemma store_inv_alloc σ l n :
  σ !! l = None ->
  store_inv σ ->
  store_inv (<[l:=notation.BBlock (replicate n ())]> σ).
Proof.
  intros ? Hinv.
  apply map_Forall_insert. done. split; last done.
  simpl. apply list.Forall_forall. intros ?.
  rewrite elem_of_replicate. intros (->&_). by exists val_unit.
Qed.

Lemma head_step_inv_addpp t1 g1 σ1 t2 g2 σ2 efs :
  store_inv σ1 ->
  isaddpp t1 ->
  head_step_conc t1 g1 σ1 t2 g2 σ2 efs ->
  isaddpp t2 ∧ store_inv σ2.
Proof.
  intros Hinv E Hstep.
  inversion Hstep; subst.
  2:{ split; last done. by exists val_unit. }
  inversion H; subst; try congruence.
  { destruct E. split; last done. by eapply addpp_let_val. }
  { destruct E as (x&X); destruct x; inversion X. }
  { split; last done. eexists v. apply val_ok_no_code.
    destruct p,v1,v2; naive_solver. }
  { destruct E. eauto using addpp_if_almost. }
  { split. by exists (val_loc l). eauto using store_inv_alloc. }
  { split; last done.
    apply Hinv in H1. simpl in *. rewrite list.Forall_forall in H1.
    apply elem_of_list_lookup_2 in H4. apply H1 in H4.
    destruct H4 as (?&->). exists x. done. }
  all:try by (split; last done; exists val_unit).
  { split. by exists val_unit.
    apply map_Forall_insert_2; last done.
    apply Forall_insert.
    { apply Hinv in H4. done. }
    { destruct E as (x&Hx). destruct x; inversion Hx.
      destruct x3; inversion H5. by eexists. } }
  { split.
    by exists (bool_decide (v1 = v1')).
    case_decide; try done.
    apply map_Forall_insert_2; last done.
    apply Forall_insert.
    { apply Hinv in H5. done. }
    { destruct E as (x&Hx). destruct x; inversion Hx.
      destruct x4; inversion H8. by eexists. } }
Qed.

Lemma IsPoll_fill_items es t:
  IsPoll t ->
  IsPoll (fill_items es t).
Proof.
  induction es; eauto using IsPollCtx.
Qed.

Definition option_fold {A B:Type} (x:B) (f:A -> B) (y: option A) :=
  match y with
  | Some x => f x
  | None => x end.

Lemma atomic_step_addpp_addpp t g σ t' g' σ' efs :
  ¬ IsPoll t ->
  store_inv σ ->
  isaddpp t ->
  atomic_step t g σ t' g' σ' efs ->
  isaddpp t'.
Proof.
  intros Hp ? Hadd Hstep.
  apply atomic_step_inv_ctxs in Hstep.
  destruct Hstep as (es&t1&t2&Ht&Ht'&Head). subst.
  destruct_decide (decide (t1=tm_poll)).
  { exfalso. apply Hp. apply IsPoll_fill_items. subst. by econstructor. }
  pose proof (isaddpp_fill_items_inv _ _ Hadd).
  eapply head_step_inv_addpp in Head; eauto. destruct Head as (?&?).
  eauto using isaddpp_fill_items_no_poll.
Qed.

Lemma neg_ispoll_fill_item_inv E t:
  ¬ IsPoll (fill_item E t) ->
  ¬ IsPoll t.
Proof.
  intros X ?. eauto using IsPollCtx.
Qed.

Lemma tm_size_fill_item_lt E t1 t2 n :
  tm_size t1 +n < tm_size t2 ->
  tm_size (fill_item E t1) +n < tm_size (fill_item E t2).
Proof.
  destruct E; simpl; try lia.
  rewrite !fmap_app !fmap_cons !list_sum_app. simpl. lia.
Qed.

Lemma tm_size_fill_item_lt' E t1 t2 n :
  tm_size t1 < tm_size t2 + n ->
  tm_size (fill_item E t1) < tm_size (fill_item E t2) + n.
Proof.
  destruct E; simpl; try lia.
  rewrite !fmap_app !fmap_cons !list_sum_app. simpl. lia.
Qed.

Lemma atomic_step_addpp_size_no_poll t g σ t' g' σ' efs :
  ¬ IsPoll t ->
  isaddpp t ->
  atomic_step t g σ t' g' σ' efs ->
  tm_size t'  + option_fold 0 tm_size efs < tm_size t.
Proof.
  intros Hp Hadd. induction 1; subst.
  { apply neg_ispoll_fill_item_inv in Hp.
    apply isaddpp_fill_item_inv in Hadd.
    apply IHatomic_step in Hadd; eauto.
    eauto using tm_size_fill_item_lt. }
  { inversion H; subst; simpl.
    2:lia.
    inversion H0; subst; simpl; try lia.
    { rewrite size_subst'. lia. }
    { exfalso. inversion Hadd. destruct x; inversion H2. }
    { destruct b; simpl; lia. } }
Qed.

Lemma atomic_step_addpp_almost t g σ t' g' σ' efs :
  store_inv σ ->
  isaddpp t ->
  atomic_step t g σ t' g' σ' efs ->
  almostex t'.
Proof.
  intros X Eq Hstep.
  apply atomic_step_inv_ctxs in Hstep.
  destruct Hstep as (es&t1&t2&Ht&Ht'&Head). subst.
  destruct_decide (decide (t1=tm_poll)).
  { subst. assert (t2=val_unit /\ σ=σ') as (->&->).
    { inversion Head; subst. by inversion H. }
    eauto using go_poll. }
  { pose proof (isaddpp_fill_items_inv _ _ Eq).
    eapply head_step_inv_addpp in Head; eauto. destruct Head as (?&?).
    eexists. apply al1'. eauto using isaddpp_fill_items_no_poll. }
Qed.

Lemma atomic_step_addpp_store_inv t g σ t' g' σ' efs :
  store_inv σ ->
  isaddpp t ->
  atomic_step t g σ t' g' σ' efs ->
  store_inv σ'.
Proof.
  intros X Eq Hstep.
  apply atomic_step_inv_ctxs in Hstep.
  destruct Hstep as (es&t1&t2&Ht&Ht'&Head). subst.
  destruct_decide (decide (t1=tm_poll)).
  { subst. assert (t2=val_unit /\ σ=σ') as (->&->).
    { inversion Head; subst. by inversion H. }
    eauto using go_poll. }
  { pose proof (isaddpp_fill_items_inv _ _ Eq).
    eapply head_step_inv_addpp in Head; eauto. destruct Head as (?&?).
    done. }
Qed.

Lemma head_step_conc_no_val t1 g1 σ1 t2 g2 σ2 efs  :
  head_step_conc t1 g1 σ1 t2 g2 σ2 efs ->
  to_val t1 = None.
Proof.
  inversion 1; subst. eauto using head_step_no_val. done.
Qed.

Lemma find_ctx_list_all_val vs :
  find_ctx_list (tm_val <$> vs) = None.
Proof.
  induction vs; try done. rewrite fmap_cons. simpl.
  rewrite IHvs //.
Qed.

Lemma almost_val n (v:val):
  almost n v -> isaddpp v.
Proof.
  inversion 1. by eexists.
  apply (@f_equal _ _ to_val) in H0.
  rewrite to_val_fill_item in H0. done.
Qed.

Lemma almostex_val (v:val):
  almostex v -> isaddpp v.
Proof.
  intros (?&Hv). eauto using almost_val.
Qed.

Lemma forall_isaddpp_inv l :
  Forall isaddpp l -> exists ts, l = addpp <$> ts.
Proof.
  induction l. by exists nil.
  inversion 1. subst.
  apply IHl in H3. destruct H3 as (ts&->).
  destruct H2 as (x&->).
  exists (x::ts). done.
Qed.

Lemma Forall_isaddp_val_isaddpp_val xs :
  Forall isaddpp_val (addpp_val <$> xs).
Proof.
  rewrite list.Forall_forall. intros ?. rewrite elem_of_list_fmap.
  intros (?&->&_). by eexists.
Qed.

Lemma Forall_isaddp_isaddpp xs :
  Forall isaddpp (addpp <$> xs).
Proof.
  rewrite list.Forall_forall. intros ?. rewrite elem_of_list_fmap.
  intros (?&->&_). by eexists.
Qed.

Lemma Forall_isaddp_val_inv xs :
  Forall isaddpp_val xs ->
  exists ys, xs = addpp_val <$> ys.
Proof.
  induction xs; simpl; intros Hfor. by exists nil.
  inversion Hfor; subst.
  apply IHxs in H2. destruct H2 as (?&->).
  destruct H1 as (?&->). by exists (x0::x).
Qed.

Lemma Forall_isaddp_inv xs :
  Forall isaddpp xs ->
  exists ys, xs = addpp <$> ys.
Proof.
  induction xs; simpl; intros Hfor. by exists nil.
  inversion Hfor; subst.
  apply IHxs in H2. destruct H2 as (?&->).
  destruct H1 as (?&->). by exists (x0::x).
Qed.

Lemma almost_call_vall (v:val) xs :
  almost 1 ((addpp v) (addpp <$> xs)).
Proof.
  destruct (find_ctx_list xs) as [((l1,?),l2)|] eqn:Hfind.
  { apply find_ctx_list_correct2 in Hfind. destruct Hfind as (?&->).
    rewrite fmap_app commute_ok fmap_cons.
    apply Al2 with (E:=ctx_call2 (addpp_val _) (addpp_val <$> l1) _).
    { simpl. split_and !. by eexists. apply Forall_isaddp_val_isaddpp_val. apply Forall_isaddp_isaddpp. }
    { destruct t; try done. }
    { apply Al1. } }
  { apply find_ctx_list_correct3 in Hfind. destruct Hfind as (vs&->).
    rewrite commute_ok.
    apply Al42. by eexists. apply Forall_isaddp_val_isaddpp_val. }
Qed.

Lemma al0 (t' t:tm) :
  t = addpp t' ->
  almostex t.
Proof.
  intros ->. eexists. apply Al1.
Qed.

Lemma goval1 E (v:val) :
  alctx E ->
  isaddpp_val v ->
  exists n, n <= 1 /\ almost n (fill_item E v).
Proof.
  destruct E; simpl.
  { intros (?&->) (?&->). exists 0. split; first lia.
    by apply al1 with (let: b := x0 in x)%T. }
  { intros Hfor (?&->).
    apply forall_isaddpp_inv in Hfor. destruct Hfor as (xs&->).
    exists 1. split. done. apply almost_call_vall. }
  { intros ((?&->)&E1&E2) (?&->).
    apply Forall_isaddp_val_inv in E1.
    apply Forall_isaddp_inv in E2.
    destruct E1 as (?&->), E2 as (xs&->).
    replace ((tm_val <$> (addpp_val <$> x1)) ++ tm_val (addpp_val x0) :: (addpp <$> xs)) with
      (addpp <$> ((tm_val <$> x1) ++ tm_val x0 :: xs)).
    2:{ rewrite !fmap_app commute_ok. f_equal.  }
    exists 1. split. done. apply almost_call_vall. }
  { intros (?&->) (?&->). exists 0; split; first lia. by apply al1 with (tm_call_prim p x0 x)%T. }
  { intros (?&->) (?&->). exists 0; split; first lia. by apply al1 with (tm_call_prim p x x0). }
  { intros ((?&->)&(?&->)) (?&->). exists 0; split; first lia. by apply al1 with (tm_if x1 x x0). }
  { intros _ (?&->). exists 0; split; first lia. by apply al1 with (tm_alloc x). }
  { intros (?&->) (?&->). exists 0; split; first lia. by apply al1 with ((x0).[x])%T. }
  { intros (?&->) (?&->).  exists 0; split; first lia. by apply al1 with ((x).[x0])%T. }
  { intros ((?&->)&(?&->)) (?&->). exists 0; split; first lia. by apply al1 with ((x1).[x] <- (x0))%T. }
  { intros ((?&->)&(?&->)) (?&->). exists 0; split; first lia. by apply al1 with ((x).[x1] <- (x0))%T. }
  { intros ((?&->)&(?&->)) (?&->). exists 0; split; first lia. by apply al1 with ((x).[x0] <- (x1))%T. }
  { intros ((x1&->)&(x2&->)&(x3&->)) (x4&->). exists 0; split; first lia. by apply al1 with (tm_cas x4 x1 x2 x3). }
  { intros ((x1&->)&(x2&->)&(x3&->)) (x4&->). exists 0; split; first lia. by apply al1 with (tm_cas x1 x4 x2 x3). }
  { intros ((x1&->)&(x2&->)&(x3&->)) (x4&->). exists 0; split; first lia. by apply al1 with (tm_cas x1 x2 x4 x3). }
  { intros ((x1&->)&(x2&->)&(x3&->)) (x4&->). exists 0; split; first lia. by apply al1 with (tm_cas x1 x2 x3 x4). }
Qed.

Lemma goval1' E (v:val) :
  alctx E ->
  isaddpp_val v ->
  almostex (fill_item E v).
Proof.
  intros ??. edestruct goval1 as (?&?&?); eauto. by eexists.
Qed.

Lemma isaddpp_val_inv (v:val) :
  isaddpp v -> isaddpp_val v.
Proof.
  intros (?&Eq). destruct x; inversion Eq. by eexists.
Qed.

Lemma isaddpp_val_mu_inv self args body :
  isaddpp_val (μ: self, args, body) ->
  isaddpp body.
Proof.
  intros (x&Hx). destruct x; try done.
  inversion Hx. subst. by eexists.
Qed.

Lemma atomic_step_almost_almost t g σ t' g' σ' efs :
  store_inv σ ->
  almostex t ->
  atomic_step t g σ t' g' σ' efs ->
  almostex t'.
Proof.
  intros X (n&Hal). revert t'.
  induction Hal; intros t' Hstep.
  { eapply atomic_step_addpp_almost; eauto. by eexists. }
  { apply invert_step_context in Hstep; eauto.
    destruct Hstep as (?&->&?).
    destruct (to_val x) eqn:Hx.
    { destruct x; inversion Hx. subst.
      apply IHHal in H1.
      apply almostex_val,isaddpp_val_inv in H1.
      by apply goval1'. }
    { apply IHHal in H1.
      destruct H1. eexists. apply Al2; eauto. } }
  { apply invert_step_let_val in Hstep. destruct Hstep as (->&?&?&?). subst. simpl.
    destruct H as (?&->). apply Forall_isaddp_inv in H0. destruct H0 as (?&->).
    destruct (to_val (addpp x)) eqn:?.
    { destruct x; inversion Heqo. eexists. apply almost_call_vall. }
    { eexists. apply Al2 with (E:=ctx_call1 (addpp <$> x0)).
      { simpl. apply Forall_isaddp_isaddpp. }
      { done. }
      { apply Al1. } } }
  { inversion Hstep; subst.
    { exfalso.
      destruct E; inversion H1; subst. apply atomic_step_no_val in H3; done.
      apply has_to_be_val in H5; eauto using atomic_step_no_val. }
    inversion H1; subst. inversion H2; subst.
    apply list_fmap_eq_inj in H13.
    2:{ by inversion 1. }
    subst. inversion H6. subst.
    destruct (isaddpp_val_mu_inv _ _ _ H) as (?&->).
    destruct H as (?&->).
    apply Forall_isaddp_val_inv in H0. destruct H0 as (?&->).
    rewrite -fmap_cons.
    rewrite substs'_addpp_val. eexists. apply Al1. }
Qed.

Lemma store_inv_atomic_step t g σ t' g' σ' efs :
  store_inv σ ->
  almostex t ->
  atomic_step t g σ t' g' σ' efs ->
  store_inv σ'.
Proof.
  intros ? (n&Hal). revert t'; induction Hal; intros t' Hstep.
  { apply atomic_step_addpp_store_inv in Hstep; eauto. eexists. done. }
  { apply invert_step_context in Hstep; naive_solver. }
  { apply invert_step_let_val in Hstep. naive_solver. }
  { inversion Hstep; subst.
    { exfalso.
      destruct E; inversion H2; subst. apply atomic_step_no_val in H4; done.
      apply has_to_be_val in H6; eauto using atomic_step_no_val. }
    inversion H2. subst. inversion H3. naive_solver. }
Qed.

Lemma store_inv_gc r σ σ' :
  gc r σ σ' ->
  store_inv σ ->
  store_inv σ'.
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

Lemma lookup_extract_middle {A:Type} (l:list A) n x :
  l !! n = Some x ->
  exists l1 l2, l = l1 ++ x::l2 /\ length l1 = n.
Proof.
  intros X.
  do 2 eexists. split. symmetry. apply take_drop_middle. done.
  rewrite take_length. apply lookup_lt_Some in X. lia.
Qed.

Lemma step_addpp_almost sz ms ρ ρ' :
  store_inv ρ.2 ->
  step_main sz ms ρ ρ' ->
  Forall (fun '(t,_) => almostex t) ρ.1 ->
  Forall (fun '(t,_) => almostex t) ρ'.1 /\ store_inv ρ'.2.
Proof.
  intros X (?&?&Hstep) Hfor.
  inversion Hstep; subst.
  2:{ split; eauto using store_inv_gc. }
  rename H0 into Hπ.
  destruct (lookup_extract_middle _ _ _ Hπ) as (l1&l2&E&?).
  subst. rewrite Forall_app in Hfor. destruct Hfor as (?&Ha).
  inversion Ha. subst x l. simpl.
  rewrite Forall_app.
  replace (length l1) with (length l1 + 0) by lia.
  rewrite insert_app_r. rewrite Forall_app. simpl.
  split_and !; try done. apply Forall_cons; try done.
  { apply atomic_step_almost_almost in H1; naive_solver. }
  { eapply Forall_impl. 2:eauto using atomic_step_addpp_almost_forked.
    intros (?&?). intros ?. by eexists. }
  { apply store_inv_atomic_step in H1; naive_solver. }
Qed.

Lemma rtc_step_addpp_almost sz ms ρ ρ' :
  store_inv ρ.2 ->
  rtc (step_main sz ms) ρ ρ' ->
  Forall (fun '(t,_) => almostex t) ρ.1 ->
  Forall (fun '(t,_) => almostex t) ρ'.1 /\ store_inv ρ'.2.
Proof.
  induction 2; eauto using step_addpp_almost. intros ?.
  eapply step_addpp_almost in H0; eauto. destruct H0. eauto.
Qed.

Lemma tm_size_vals vs :
  list_sum (tm_size <$> (tm_val <$> vs)) = length vs.
Proof. induction vs; simpl. done. rewrite -IHvs //. Qed.

Lemma atomic_step_almost_almostex M t n g σ t' g' σ' efs :
  ¬ IsPoll t ->
  mcs M t ->
  store_inv σ ->
  almost n t ->
  atomic_step t g σ t' g' σ' efs ->
  (* A normal step *)
  (exists n', n' <= n /\ almost n' t' /\ tm_size t' + option_fold 0 tm_size efs < tm_size t ) \/
  (* We did a call. *)
  (exists n', efs=None /\ σ'=σ /\ n' < n /\ almost n' t' /\ tm_size t' < tm_size t + M).
Proof.
  intros Hp Hmcs X Hal. revert t'.
  induction Hal; intros t' Hstep.
  (* An addpp does a step, and does not remove a poll: it is still an
     addpp, and the size decreases (as addpp cannot be calls) *)
  { left. exists 0. split_and !; try lia.
    { apply atomic_step_addpp_addpp in Hstep; eauto using al1'. by eexists. }
    apply atomic_step_addpp_size_no_poll in Hstep; eauto. by eexists. }
  { apply neg_ispoll_fill_item_inv in Hp.
    apply mcs_fill_item_inv1 in Hmcs.
    apply invert_step_context in Hstep; last done.
    destruct Hstep as (?&->&Hstep).
    apply IHHal in Hstep; eauto.
    destruct Hstep as [(n'&?&?&?)|(n'&?&?&?&?&?)]; [left|right].
    { destruct (to_val x) eqn:Hx.
      { destruct x; inversion Hx. subst.
        apply almost_val,isaddpp_val_inv in H2.
        eapply goval1 in H2; eauto. destruct H2 as (n0&?&?).
        exists n0. split_and !; try done; try lia.
        eauto using tm_size_fill_item_lt. }
      exists (S n'). split_and !; eauto using Al2,tm_size_fill_item_lt. lia. }
    { destruct (to_val x) eqn:Hx.
      { destruct x; inversion Hx. subst.
        apply almost_val,isaddpp_val_inv in H4.
        eapply goval1 in H4; eauto. destruct H4 as (n0&?&?).
        exists n0. split_and !; try done; try lia.
        eauto using tm_size_fill_item_lt'. }
      exists (S n'). split_and !; eauto using Al2,tm_size_fill_item_lt'. lia. } }
  (* We reduce a let unit, it reduces the size and left untouched the number
     of constructors *)
  { left.
    apply invert_step_let_val in Hstep. destruct Hstep as (->&?&?&?). subst. simpl.
    destruct H as (?&->). apply Forall_isaddp_inv in H0. destruct H0 as (?&->).
    exists 1. split_and !. lia. 2:lia.
    destruct (to_val (addpp x)) eqn:?.
    { destruct x; inversion Heqo.
      apply almost_call_vall. }
    { apply Al2 with (E:=ctx_call1 (addpp <$> x0)).
      { simpl. apply Forall_isaddp_isaddpp. }
      { done. }
      { apply Al1. } } }
  (* We are doing a call. It reduces the number of constructor.
     But we know that the size of the reduced term is bounded *)
  { inversion Hstep; subst.
    { exfalso.
      destruct E; inversion H1; subst. apply atomic_step_no_val in H3; done.
      apply has_to_be_val in H5; eauto using atomic_step_no_val. }
    inversion H1; subst. inversion H2; subst.
    right. exists 0. split_and !. done. done. lia.
    { apply list_fmap_eq_inj in H13.
      2:{ by inversion 1. }
      subst. inversion H6. subst.
      destruct (isaddpp_val_mu_inv _ _ _ H) as (?&->).
      destruct H as (?&->).
      apply Forall_isaddp_val_inv in H0. destruct H0 as (?&->).
      rewrite -fmap_cons.
      rewrite substs'_addpp_val. apply Al1. }
    { rewrite H6. simpl. rewrite tm_size_vals.
      rewrite size_subst' size_substs'.
      inversion Hmcs; subst. rewrite H6 in H8. inversion H8; try done.
      subst. lia. } }
Qed.

Lemma exhibit (θ:list (tm*status)) :
  Forall (λ '(t, _), almostex t) θ ->
  exists (xs:list nat), Forall2 (fun '(t, _) n => almost n t) θ xs.
Proof.
  induction θ as [|(?&?)]; intros Hfor.
  { exists nil. apply Forall2_nil. }
  { inversion Hfor. subst. apply IHθ in H2. destruct H2 as (xs&?).
    destruct H1 as (x&?). exists (x::xs). eauto using Forall2_cons. }
Qed.

Lemma exhibit_back (θ:list (tm*status)) xs :
  Forall2 (fun '(t, _) n => almost n t) θ xs ->
  Forall (λ '(t, _), almostex t) θ.
Proof.
  revert xs. induction θ as [|(?&?)]; intros xs Hfor.
  { apply Forall_nil. }
  { inversion Hfor. subst. apply IHθ in H3.
    apply Forall_cons; eauto. by eexists. }
Qed.

Definition sumsize (θ:list (tm*status)) :=
  sum_list ((fun '(t, _) => tm_size t) <$> θ).

Lemma sumsize_nil :
  sumsize [] = 0.
Proof. done. Qed.

Lemma sumsize_cons t g θ :
  sumsize ((t,g)::θ) = tm_size t + sumsize θ.
Proof. done. Qed.

Lemma sum_list_app θ1 θ2 :
  sum_list (θ1 ++ θ2) = sum_list θ1 + sum_list θ2.
Proof.
  revert θ2. induction θ1 as [|]; intros θ2.
  done. rewrite -app_comm_cons -Nat.add_assoc -IHθ1 //.
Qed.

Lemma sumsize_app θ1 θ2 :
  sumsize (θ1 ++ θ2) = sumsize θ1 + sumsize θ2.
Proof. rewrite /sumsize fmap_app sum_list_app //. Qed.

Definition sizecfg M θ xs :=
  sumsize θ + M * sum_list xs.

Definition add_forked (efs:option tm) :=
  match efs with Some _ => [0] | _ => [] end.

(* [sizecfg M θ xs] decreases at each step, except for GC steps.
   M represents the largest size increase from a call, θ the threads,
   and xs the list of possible calls per threads.
   [count_allocated σ] decreases at each GC step.
   [sizecfg M θ xs + count_allocated σ] decreases at each step,
   except for allocations. (each allocation reduces the size of 1, and
   increases of one the number of allocated block of 1).
   But we know that there is at most [sizecfg M θ xs] allocations.
   Hence [2*(sizecfg M θ xs) + count_allocated σ] indeed decreases
   at each step.
 *)
Lemma go_after_at_most sz ms M θ σ xs :
  ¬ EveryAllocFits sz ms (θ,σ) ->
  store_inv σ ->
  Always (step_main sz ms) (θ,σ) ((fun ρ => Forall (fun '(t,_) => mcs M t) ρ.1)) ->
  Forall2 (λ '(t, _) n, almost n t) θ xs ->
  AfterAtMostWeak (step_main sz ms) (EveryAllocFits sz ms)
    (S (2*(sizecfg M θ xs) + count_allocated σ)) (θ, σ).
Proof.
  intros Hneed Hinv Halmcs Hfor.
  remember (2*(sizecfg M θ xs) + count_allocated σ) as m.
  revert θ σ xs Heqm Hneed Halmcs Hfor Hinv.
  induction m using lt_wf_ind; intros θ σ xs -> Hneed Halmcs Hfor Hinv.
  apply HoldsWLater.
  intros (θ',σ') Hstep.

  assert (Forall (λ '(t, _), mcs M t) θ) as Hmcs.
  { specialize (Halmcs _ (rtc_refl _ _)). done. }
  assert (Always (step_main sz ms) (θ', σ') (λ ρ : configuration, Forall (λ '(t, _), mcs M t) ρ.1)) as Halmcs'.
  { intros ??. apply Halmcs. by eapply rtc_l. }
  clear Halmcs.

  assert (store_inv σ') as Hinv'.
  { eapply step_addpp_almost in Hstep; eauto using exhibit_back.
    naive_solver. }

  destruct Hstep as (c&Hen&Hstep).
  destruct c as [π|].
  { inversion_clear Hstep.
    destruct Hen as (t0&g0&Hn&Hwill&Hpoll).
    assert (t0=t/\g0=g) as (->&->) by naive_solver.
    assert (¬ IsPoll t).
    { naive_solver. }
    clear Hpoll H0 Hneed.
    destruct_decide (decide (EveryAllocFits sz ms (θ',σ'))).
    { by apply HoldsWNow. }

    destruct (sizecfg M θ xs + (count_allocated σ + sizecfg M θ xs)) eqn:R.
    { exfalso. unfold sizecfg in *. assert (sumsize θ=0). lia. destruct θ.
      { inversion Hn. }
      { destruct p; simpl in *. destruct t0; simpl in *; lia. } }

    generalize Hfor. intros ?.
    eapply Forall2_lookup_l in Hfor; eauto. destruct Hfor as (?&Hxs&?).

    assert (Forall (λ '(t0, _), almost 0 t0) (opt_to_list efs)).
    { eapply atomic_step_addpp_almost_forked; eauto. by eexists. }

    assert (count_allocated σ' <= count_allocated σ + 1)
      by eauto using atomic_step_count_allocated_le.

    eapply atomic_step_almost_almostex in H1; eauto; first last.
    { eapply Forall_lookup in Hmcs; eauto. apply Hmcs. }

    destruct H1 as [(n'&?&?&?)| (n'&->&->&?&?&?)].
    { assert (Forall2 (λ '(t, _) (n : nat), almost n t) θ' (<[π:=n']>xs ++ add_forked efs)).
      { subst. apply Forall2_app.
        { apply Forall2_insert; eauto. }
        { destruct efs. apply Forall2_cons. inversion H5. done. constructor.
          constructor. } }

      assert (2* (sizecfg M θ' (<[π:=n']> xs ++ add_forked efs)) + count_allocated σ' < S n).
      { rewrite -R. unfold sizecfg.
        assert (sumsize θ' + M * sum_list (<[π:=n']> xs ++ add_forked efs) < sumsize θ + M * sum_list xs).
        { subst. clear H.
          apply lookup_extract_middle in Hn. destruct Hn as (l1&l2&->&?).
          apply lookup_extract_middle in Hxs. destruct Hxs as (l1'&l2'&->&?).
          rewrite !sumsize_app !sum_list_app sumsize_cons. simpl.
          rewrite !insert_app_r_alt; try lia.
          replace (π - length l1) with 0 by lia.
          replace (π - length l1') with 0 by lia.
          rewrite !sumsize_app !sum_list_app sumsize_cons. simpl.
          destruct efs; simpl in *.
          { rewrite sumsize_cons sumsize_nil. nia. }
          { rewrite sumsize_nil. nia. } }
        lia. }
      eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto.
      lia. lia. }
    { assert (Forall2 (λ '(t, _) (n : nat), almost n t) θ' (<[π:=n']>xs)).
      { subst. simpl. rewrite right_id_L.
        apply Forall2_insert; eauto. }

      assert (2*(sizecfg M θ' (<[π:=n']> xs)) + count_allocated σ < S n).
      { rewrite -R. subst. simpl.
        apply lookup_extract_middle in Hn. destruct Hn as (l1&l2&->&?).
        apply lookup_extract_middle in Hxs. destruct Hxs as (l1'&l2'&->&?).
        unfold sizecfg.
        rewrite !insert_app_r_alt; try lia.
        replace (π - length l1) with 0 by lia.
        replace (π - length l1') with 0 by lia.
        rewrite !sumsize_app !sum_list_app !sumsize_cons sumsize_nil. simpl.
        nia. }
       eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto. lia. lia. } }
  { inversion Hstep. subst θ'. subst. clear Hneed.

    destruct (2*(sizecfg M θ xs + count_allocated σ)) eqn:R.
    { exfalso. unfold sizecfg in *. assert (count_allocated σ=0). lia.
      eauto using gc_no_allocated_block. }

    destruct_decide (decide (EveryAllocFits sz ms (θ,σ'))).
    { by apply HoldsWNow. }

    apply gc_neq_size_lt in H4; eauto.
    eapply after_at_most_weak_le. 2:eapply H; only 2:reflexivity; eauto. all:lia. }
Qed.

(* Main result of the file *)
Theorem weak_liveness_addpp sz ms t :
  Always (step_main sz ms) (init (addpp t))
    (EventuallyWeak (step_main sz ms) (EveryAllocFits sz ms)).
Proof.
  intros ? Hsteps.
  assert (Forall (fun '(t,_) => almostex t) ρ'.1 /\ store_inv ρ'.2) as (Hfor&Hinv).
  { eapply rtc_step_addpp_almost; eauto.
    { apply map_Forall_empty. }
    simpl. apply Forall_singleton. by eapply al0. }
  destruct ρ' as (θ,σ). simpl in *.

  destruct_decide (decide (EveryAllocFits sz ms (θ,σ))).
  { exists 0. by constructor. }

  apply exhibit in Hfor. destruct Hfor as (xs&Hfor).
  edestruct (rtc_step_mcs_init sz ms (addpp t)) as (M&HM).
  eexists. eapply go_after_at_most; eauto.
  { by eapply always_middle. }
Qed.
