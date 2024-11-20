From Coq Require Import ssreflect Wellfounded.
From stdpp Require Import base binders gmap gmultiset list.
From iris.proofmode Require Import proofmode.

From irisfit.final Require Import final_semantics common mcs addpp weak_anf.
From irisfit Require Import language notation strong_safety wp_adequacy reducible.

(* ------------------------------------------------------------------------ *)
(* Some relations.*)

Definition rel t t' := t = addpp t'.
Definition rel_val v v' := v = addpp_val v'.

Definition rel_ctx (E E':ctx) : Prop :=
  match E,E' with
  | ctx_let b t,ctx_let b' t' => b=b' /\ rel t t'
  | ctx_call1 ts,ctx_call1 ts' => ts = addpp <$> ts'
  | ctx_call2 v vs ts, ctx_call2 v' vs' ts' =>
      v = addpp_val v' /\ vs = addpp_val <$> vs' /\ ts = addpp <$> ts'
  | ctx_call_prim1 p t, ctx_call_prim1 p' t' => p = p' /\ rel t t'
  | ctx_call_prim2 p v, ctx_call_prim2 p' v' => p = p' /\ rel_val v v'
  | ctx_if t1 t2,ctx_if t1' t2' => rel t1 t1' /\ rel t2 t2'
  | ctx_alloc,ctx_alloc => True
  | ctx_load1 t,ctx_load1 t' => rel t t'
  | ctx_load2 v,ctx_load2 v' => rel_val v v'
  | ctx_store1 t1 t2, ctx_store1 t1' t2' => rel t1 t1' /\ rel t2 t2'
  | ctx_store2 v1 t2, ctx_store2 v1' t2' => rel_val v1 v1' /\ rel t2 t2'
  | ctx_store3 v1 v2,ctx_store3 v1' v2' => rel_val v1 v1' /\ rel_val v2 v2'
  | ctx_cas1 t1 t2 t3,ctx_cas1 t1' t2' t3' => rel t1 t1' /\ rel t2 t2' /\ rel t3 t3'
  | ctx_cas2 v1 t2 t3,ctx_cas2 v1' t2' t3' => rel_val v1 v1' /\ rel t2 t2' /\ rel t3 t3'
  | ctx_cas3 v1 v2 t3,ctx_cas3 v1' v2' t3' => rel_val v1 v1' /\ rel_val v2 v2' /\ rel t3 t3'
  | ctx_cas4 v1 v2 v3,ctx_cas4 v1' v2' v3' => rel_val v1 v1' /\ rel_val v2 v2' /\ rel_val v3 v3'
  | _,_ => False end.

Inductive almost : tm -> tm -> Prop :=
| Al1 : forall t t',
    t = addpp t' ->
    almost t t'
| Al2 : forall E E' t t',
    rel_ctx E E' ->
    to_val t = None ->
    almost t t' ->
    almost (fill_item E t) (fill_item E' t')
| Al3 : forall t t' ts ts',
    t = addpp t' ->
    ts = addpp <$> ts' ->
    almost (tm_let BAnon val_unit (tm_call t ts)) (tm_call t' ts')
| Al4 : forall v v' vs vs',
    v = addpp_val v' ->
    vs = addpp_val <$> vs' ->
    almost (tm_call v (tm_val <$> vs)) (tm_call v' (tm_val <$> vs')).

Definition strong '(t,g) '(t',g') :=
  almost t t' /\ (g:status) = g'.

Definition addpp_block b :=
  match b with
  | BDeallocated => BDeallocated
  | BBlock b => BBlock (addpp_val <$> b) end.

Definition rel_store (σ σ':gmap loc block) :=
  σ = addpp_block <$> σ'.

Definition rel_fs efs efs' :=
  match efs,efs' with
  | None,None => True
  | Some t, Some t' => rel t t'
  | _,_ => False end.

(* ------------------------------------------------------------------------ *)

Local Ltac gov H := apply addpp_val_inv in H; destruct H as (?&->&->).
Local Ltac govs H := symmetry in H; apply addpp_val_inv in H; destruct H as (?&->&->).

Lemma addpp_fill_item_inv2 t' E (t:tm) :
  t' ≠ tm_poll \/ ¬ is_let_call E ->
  addpp t = fill_item E t' ->
  exists E' t0,  t' = addpp t0 /\ t = fill_item E' t0 /\ rel_ctx E E'.
Proof.
  intros X1 X2.
  destruct E; simpl in *.
  { destruct t; inversion X2; subst; simpl in *.
    { naive_solver. }
    { exists (ctx_let b t2),t1. done. } }
  all:destruct t; inversion X2; subst; eauto.
  { eexists (ctx_call_prim1 _ _),_. done. }
  { gov H1. eexists (ctx_call_prim2 _ _),_. done. }
  { eexists (ctx_if _ _),_. done. }
  { eexists ctx_alloc,_. done. }
  { eexists (ctx_load1 _),_. done. }
  { gov H0. eexists (ctx_load2 _),_. done. }
  { eexists (ctx_store1 _ _),_. done. }
  { gov H0. eexists (ctx_store2 _ _),_. done. }
  { gov H0. gov H1. eexists (ctx_store3 _ _),_. done. }
  { eexists (ctx_cas1 _ _ _),_. done. }
  { gov H0. eexists (ctx_cas2 _ _ _),_. done. }
  { gov H0. gov H1. eexists (ctx_cas3 _ _ _),_. done. }
  { gov H0. gov H1. gov H2. eexists (ctx_cas4 _ _ _),_. done. }
Qed.

Lemma isaddpp_fill_items_inv t' es t :
  t' ≠ tm_poll ->
  addpp t = fill_items es t' ->
  exists t0 es', Forall2 rel_ctx es es' /\ t = fill_items es' t0 /\ t' = addpp t0.
Proof.
  revert t t'. induction es; intros t t' Ht.
  { eexists t,nil. split_and !; try done. }
  { simpl. intros Ha. apply addpp_fill_item_inv2 in Ha.
    2:{ left. destruct es; try done. by destruct c. }
    destruct Ha as (?&?&X&->&?).
    symmetry in X. apply IHes in X; eauto. destruct X as (?&?&?&?&?). subst.
    eexists _,(x::_). eauto. }
Qed.

Lemma addpp_inj t1 t2 :
  addpp t1 = addpp t2 ->
  t1 = t2.
Proof.
  revert t2; induction t1 using (well_founded_induction (wf_inverse_image _ nat _ tm_size' PeanoNat.Nat.lt_wf_0)); intros t2 Eq.
  destruct t1,t2; simpl in *; inversion Eq; subst.
  { destruct v,v0; inversion Eq; eauto.
    apply H in H4. naive_solver. lia. }
  { apply H in H1; last lia. rewrite H1. clear Eq. f_equal.
    revert l0 H2. induction l; intros l0 H2.
    { destruct l0; inversion H2. done. }
    { destruct l0; inversion H2. subst.
      apply H in H3; simpl; last lia. subst. f_equal.
      apply IHl; last naive_solver. intros ???. apply H. simpl in *. unfold "<$>" in *. lia. } }
  { destruct t2_1; inversion H2. destruct t2_2; inversion H3. }
  { f_equal; apply H; simpl; try done; try lia. }
  { done. }
  { destruct t1_1; inversion H2. destruct t1_2; inversion H3. }
  all:f_equal; (apply H; [lia|done]).
Qed.

Lemma addpp_val_inj v1 v2 :
  addpp_val v1 = addpp_val v2 ->
  v1 = v2.
Proof.
  intros Eq.
  apply (@f_equal _ _  tm_val) in Eq. apply (addpp_inj v1 v2) in Eq. by inversion Eq.
Qed.

Local Ltac gox H := symmetry in H; apply addpp_val_inv in H; destruct H as (?&?&?).

Lemma rel_store_insert σ σ' l n :
  rel_store σ σ' ->
  rel_store (<[l:=notation.BBlock (replicate n ())]> σ) (<[l:=notation.BBlock (replicate n ())]> σ').
Proof.
  unfold rel_store. intros ->.
  rewrite fmap_insert. f_equal. simpl. f_equal.
  induction n; try done.
  rewrite replicate_S fmap_cons. f_equal. done.
Qed.

Lemma rel_store_load σ σ' bs l :
  rel_store σ σ' ->
  σ !! l = Some (notation.BBlock bs) ->
  exists bs', σ' !! l = Some (notation.BBlock bs') /\ bs = addpp_val <$> bs'.
Proof.
  intros ->. rewrite lookup_fmap. destruct (σ' !! l) as [x|]; last naive_solver.
  destruct x; naive_solver.
Qed.

Lemma rel_store_update l n v σ σ' bs:
  rel_store σ σ' ->
  rel_store (<[l:=notation.BBlock (<[n:=addpp_val v]> (addpp_val <$> bs))]> σ)
    (<[l:=notation.BBlock (<[n:=v]> bs)]> σ').
Proof.
  intros ->. unfold rel_store. rewrite fmap_insert. f_equal. simpl. f_equal.
  rewrite list_fmap_insert //.
Qed.

Lemma rel_store_dom σ σ' :
  rel_store σ σ' ->
  dom σ = dom σ'.
Proof.
  intros ->. rewrite dom_fmap_L //.
Qed.

Lemma head_step_inv_addpp t1 g1 σ1 t2 g2 σ2 σ1' :
  rel_store σ1 σ1' ->
  head_step (addpp t1) g1 σ1 t2 g2 σ2 ->
  exists t2' σ2', head_step t1 g1 σ1' t2' g2 σ2' /\ t2 = addpp t2' /\ rel_store σ2 σ2'.
Proof.
  intros Hstore.
  inversion 1; subst.
  { destruct t1; inversion H0; subst.
    govs H3. eexists _,σ1'. split_and !.
    { by apply HeadLet. }
    { rewrite subst'_addpp_val //. }
    { done. } }
  { exfalso. destruct t1; inversion H0. }
  { eexists v,_. split_and !; last done.
    { destruct t1; inversion H0; subst.
      govs H4. govs H5.
      apply HeadCallPrim. rewrite -H1.
      destruct p0,x,x0; try naive_solver; simpl; f_equal.
      { destruct_decide (decide ((μ: b, l, t) = (μ: b0, l0, t0))).
        { rewrite !bool_decide_true //. inversion H2. subst. done. }
        { rewrite !bool_decide_false //. intros ?. apply H2.
          inversion H3. subst. apply addpp_inj in H7. naive_solver. } }
      { destruct_decide (decide ((μ: b, l, t) ≠ (μ: b0, l0, t0))).
        { rewrite !bool_decide_true //. intros ?. apply H2.
          inversion H3. subst. apply addpp_inj in H7. naive_solver. }
        { rewrite !bool_decide_false //. intros ?. apply H3. naive_solver.
          naive_solver. } } }
    { apply val_ok_no_code. destruct p,v1,v2; inversion H1; done. } }
  { destruct t1; inversion H0. gox H2. subst. destruct x; inversion H2. subst.
    eexists _,_. split_and !; last done. by apply HeadIf. destruct b0; done. }
  { destruct t1; inversion H0. destruct t1; inversion H0. destruct v; inversion H4. subst.
    eexists _,(<[l:=notation.BBlock (replicate (Z.to_nat _) ())]> σ1'). split_and !.
    { eapply HeadAlloc; try done.
      apply not_elem_of_dom. apply not_elem_of_dom in H1. by erewrite <- rel_store_dom. }
    { done. }
    { eauto using rel_store_insert. } }
  { destruct t1; inversion H0. destruct t1_1; inversion H3. destruct v0; inversion H7.
    destruct t1_2; inversion H6. destruct v0; inversion H9. subst.
    eapply rel_store_load in H2; eauto. destruct H2 as (?&?&->).
    rewrite list_lookup_fmap in H5. destruct (x !! Z.to_nat z) eqn:G; try done.
    eexists _,_. split_and !; last done.
    { eapply HeadLoad; try done. }
    { naive_solver. } }
  { destruct t1; inversion H0. destruct t1_1; inversion H2.
    destruct v0; inversion H7. destruct t1_2; inversion H3.
    destruct t1_3; inversion H6. destruct v0; inversion H9. subst.
    eapply rel_store_load in H5; eauto. destruct H5 as (?&?&->).
    eexists _,_. split_and !.
    3:{ eauto using rel_store_update. }
    { eapply HeadStore; last done; try done.
      rewrite fmap_length // in H4. }
    { done. } }
  { destruct t1; inversion H0.
    destruct t1_1; inversion H2. destruct v; inversion H2.
    destruct t1_2; inversion H3. destruct v; inversion H3.
    destruct t1_3; inversion H4. destruct t1_4; inversion H8. subst.
    eapply rel_store_load in H6; eauto. generalize H6. intros X. destruct H6 as (?&?&->).
    rewrite list_lookup_fmap in H7. destruct (x !! Z.to_nat z ) eqn:G; try done.
    case_decide as Hv.
    { assert (v=v1).
      { rewrite -Hv in H7. inversion H7. apply addpp_val_inj in H10. done. }
      eexists _,_. split_and !.
      { by eapply HeadCAS. }
      { rewrite Hv. rewrite !bool_decide_true //. }
      { rewrite decide_True //. eauto using rel_store_update. } }
    { assert (v≠v1) by naive_solver.
      eexists _,_. split_and !.
      { by eapply HeadCAS. }
      { rewrite !bool_decide_false //. }
      { rewrite decide_False //. } } }
  { destruct t1; inversion H1. eexists _,_. split_and !; last done. apply HeadEnter. done. }
  { destruct t1; inversion H1. eexists _,_. split_and !; last done. apply HeadExit. done. }
  { destruct t1; inversion H1. eexists _,_. split_and !; last done. apply HeadPoll. done. }
Qed.

Lemma head_step_conc_inv_addpp t1 g1 σ1 t2 g2 σ2 efs σ1' :
  rel_store σ1 σ1' ->
  head_step_conc (addpp t1) g1 σ1 t2 g2 σ2 efs ->
  exists t2' σ2' efs', head_step_conc t1 g1 σ1' t2' g2 σ2' efs' /\ t2 = addpp t2' /\ rel_fs efs efs' /\ rel_store σ2 σ2'.
Proof.
  intros Hstore.
  inversion 1; subst.
  { eapply head_step_inv_addpp in H0; try done. destruct H0 as (?&?&?&?&?).
    eexists _,_,None. split_and !; try done. eauto using HeadSeq. }
  { destruct t1; inversion H; subst.
    eexists _,_,(Some t1). split_and !; last done. by apply HeadFork. done. done. }
Qed.


Lemma atomic_step_fill_items es t1 g1 σ1 t2 g2 σ2 efs :
  atomic_step t1 g1 σ1 t2 g2 σ2 efs ->
  atomic_step (fill_items es t1) g1 σ1 (fill_items es t2) g2 σ2 efs.
Proof.
  revert t1 t2. induction es; intros t1 t2 Hstep. done.
  simpl. eauto using StepCtx.
Qed.

Lemma almost_call x xs :
  almost ((addpp x) (addpp <$> xs)) (x xs).
Proof.
  destruct (to_val (addpp x)) eqn:Hx.
  2:{ apply Al2 with (E:=ctx_call1 _) (E':=ctx_call1 _). done. done. by apply Al1. }
  destruct x; inversion Hx.
  destruct (find_ctx_list xs) as [((l1,?),l2)|] eqn:Hfind.
  { apply find_ctx_list_correct2 in Hfind. destruct Hfind as (?&->).
    rewrite fmap_app commute_ok fmap_cons.
    eapply Al2 with (E:=ctx_call2 (addpp_val _) (addpp_val <$> l1) _) (E':=ctx_call2 _ _ _).
    { done. }
    { by destruct t. }
    { by apply Al1. } }
  { apply find_ctx_list_correct3 in Hfind. destruct Hfind as (vs&->).
    rewrite commute_ok.
    apply Al4. done. done. }
Qed.

Lemma almost_fill_item_addpp E E' x :
  rel_ctx E E' ->
  almost (fill_item E (addpp x)) (fill_item E' x).
Proof.
  destruct E,E'; try done; simpl.
  { intros (->&->).
    by eapply Al1 with (t' := tm_let _ _ _). }
  { intros ->. apply almost_call. }
  { intros (->&->&->).
    replace ((tm_val <$> (addpp_val <$> l1)) ++ addpp x :: (addpp <$> l2)) with
      (addpp <$> ((tm_val <$> l1) ++ x :: l2)).
    2:{ rewrite !fmap_app commute_ok. f_equal. }
    replace (tm_val (addpp_val v0)) with (addpp v0) by done.
    apply almost_call. }
  { intros (->&->). by eapply Al1 with (t':=tm_call_prim _ _ _). }
  { intros (->&->). by eapply Al1 with (t':=tm_call_prim _ _ _). }
  { intros (->&->). by eapply Al1 with (t':=tm_if _ _ _). }
  { intros _. by eapply Al1 with (t':=tm_alloc x). }
  { intros ->. by eapply Al1 with (t':=tm_load _ _). }
  { intros ->. by eapply Al1 with (t':=tm_load _ _). }
  { intros (->&->). by eapply Al1 with (t':=tm_store _ _ _). }
  { intros (->&->). by eapply Al1 with (t':=tm_store _ _ _). }
  { intros (->&->). by eapply Al1 with (t':=tm_store _ _ _). }
  { intros (->&->&->). by eapply Al1 with (t':=tm_cas _ _ _ _). }
  { intros (->&->&->). by eapply Al1 with (t':=tm_cas _ _ _ _). }
  { intros (->&->&->). by eapply Al1 with (t':=tm_cas _ _ _ _). }
  { intros (->&->&->). by eapply Al1 with (t':=tm_cas _ _ _ _). }
Qed.

Lemma almost_fill_items_addpp es es' x :
  Forall2 rel_ctx es es' ->
  almost (fill_items es (addpp x)) (fill_items es' x).
Proof.
  revert x es'. induction es; intros x es' Hfor.
  { inversion Hfor. subst. by eapply Al1. }
  { inversion Hfor. subst. simpl.
    destruct es.
    { inversion H3. subst. by apply almost_fill_item_addpp. }
    { apply Al2; eauto. by destruct c. } }
Qed.

Lemma isaddpp_let_call E es t :
  is_let_call E ->
  addpp t = fill_items es (fill_item E tm_poll) ->
  almost (fill_items es (fill_item E ()%V)) t.
Proof.
  destruct E; try done. simpl. destruct b; try done.
  destruct t0; try done. intros _.
  intros His.
  revert t His. induction es; simpl in *; intros t His.
  { destruct t; inversion His; subst.
    { by eapply Al3. }
    { exfalso. destruct t2; inversion H2. } }
  apply addpp_fill_item_inv2 in His.
  2:{ left. destruct es; try done. by destruct c. }
  destruct His as (?&?&?&->&?).
  apply Al2. done.
  { destruct es; try done. apply to_val_fill_item. }
  eauto.
Qed.

Lemma go_poll_exit E t1 σ :
  ¬ is_let_call E ->
  addpp t1 = (fill_item E tm_poll) ->
  ∃ t2', atomic_step t1 Out σ t2' Out σ None /\ almost (fill_item E ()%V) t2'.
Proof.
  intros HE Hadd.
  apply addpp_fill_item_inv2 in Hadd. 2:eauto.
  destruct Hadd as (?&?&?&?&?).
  destruct x0; inversion H.
  eexists. split.
  { eapply StepCtx. done. reflexivity.
    apply StepHead,HeadSeq,HeadPoll. }
  { destruct E,x; inversion H1; unfold rel,rel_val in *; subst; try (by apply Al1); simpl.
    { assert (tm_val val_unit = addpp val_unit) as Eq by done.
      rewrite {1}Eq. apply almost_call. }
    { destruct H3 as (->&->).
      replace ((tm_val <$> (addpp_val <$> l1)) ++ tm_val ()%V :: (addpp <$> l2)) with
        (addpp <$> ((tm_val <$> l1) ++ tm_val ()%V :: l2)).
      replace (tm_val (addpp_val v0)) with (addpp v0) by done.
      apply almost_call.
      rewrite fmap_app. simpl. rewrite commute_ok //. }
    all:destruct H3 as (->&->); by apply Al1. }
Qed.

Lemma go_poll_exits es E t1 σ :
  ¬ is_let_call E ->
  addpp t1 = (fill_items es (fill_item E tm_poll)) ->
  ∃ t2', atomic_step t1 Out σ t2' Out σ None /\ almost (fill_items es (fill_item E ()%V)) t2'.
Proof.
  revert t1. induction es; simpl; intros t1 X1 X2.
  { eauto using go_poll_exit. }
  apply addpp_fill_item_inv2 in X2.
  2:{ left. destruct es. by destruct E. by destruct c. }
  destruct X2 as (?&?&?&?&?). symmetry in H. subst.
  apply IHes in H; eauto. destruct H as (?&?&?).
  eexists. split. eapply StepCtx. 1,2:reflexivity. done.
  apply Al2; try done.
  { destruct es. by destruct E. by destruct c. }
Qed.

Lemma go_poll es t1 σ :
  addpp t1 = fill_items es tm_poll ->
  almost (fill_items es ()%V) t1 \/
    (∃ t2', atomic_step t1 Out σ t2' Out σ None /\ almost (fill_items es ()%V) t2').
Proof.
  destruct (list_inv_r es) as [|(es'&E&->)]; subst; intros His.
  { simpl in *. destruct t1; inversion His. right.
    eexists _. split. apply StepHead,HeadSeq,HeadPoll. by apply Al1. }
  { rewrite fill_items_app. rewrite fill_items_app in His. simpl in *.
    destruct_decide (decide (is_let_call E)).
    { left. eauto using isaddpp_let_call. }
    { right. eauto using go_poll_exits. } }
Qed.

Lemma atomic_step_addpp_almost t1 g1 σ1 t2 g2 σ2 efs σ1':
  rel_store σ1 σ1' ->
  atomic_step (addpp t1) g1 σ1 t2 g2 σ2 efs ->
  (almost t2 t1 ∧ g2 = g1 ∧ σ2 = σ1 ∧ efs = None)
  ∨ (∃ t2' σ2' efs', atomic_step t1 g1 σ1' t2' g2 σ2' efs' ∧ almost t2 t2' /\ rel_fs efs efs' /\ rel_store σ2 σ2').
Proof.
  intros Hstore Hstep.
  apply atomic_step_inv_ctxs in Hstep.
  destruct Hstep as (es&x1&x2&Hx1&Hx2&Head). subst.
  assert (find_ctx x1 = None) as Hfind.
  { destruct (find_ctx x1) as [(?&?)|] eqn:X; last done. exfalso.
    apply find_ctx_correct2 in X. destruct X as (?&->).
    by eapply head_step_conc_no_ctx. }
  destruct_decide (decide (x1=tm_poll)) as Hne.
  { subst. assert (x2=val_unit /\ g1=Out /\ g2 =Out /\ σ1=σ2 /\ efs = None) as (->&->&->&->&->).
    { inversion Head; subst. by inversion H. }
    eapply go_poll in Hx1. destruct Hx1 as [|(?&Hx1&?)]. eauto.
    right. eexists _,_,None. split_and !; by eauto. }
  { right. destruct (isaddpp_fill_items_inv _ _ _ Hne Hx1) as (t0&es'&?&->&->).
    eapply head_step_conc_inv_addpp in Head; eauto. destruct Head as (?&?&?&?&?&?&?).
    eexists _,_,_. split_and !; try done.
    { apply atomic_step_fill_items. by apply StepHead. }
    subst. eauto using almost_fill_items_addpp. }
Qed.

Lemma locs_addpp t :
  locs (addpp t) = locs t.
Proof.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; try done; simpl.
  { destruct v; try done. }
  { auto_locs. rewrite left_id_L. f_equal.
    { apply H. simpl. lia. }
    { induction l. done. simpl. f_equal.
      { apply H; simpl; lia. }
      { apply IHl. intros ??. apply H. simpl in *. unfold "<$>" in *. lia. } } }
  all:auto_locs; repeat erewrite H; simpl; first done; lia.
Qed.

Lemma almost_fill_item E E' t t' :
  rel_ctx E E' ->
  almost t t' ->
  almost (fill_item E t) (fill_item E' t').
Proof.
  intros He Hal. inversion Hal; subst.
  { by apply almost_fill_item_addpp. }
  { apply Al2; eauto. apply to_val_fill_item. }
  { apply Al2; eauto. }
  { apply Al2; eauto. }
Qed.

Lemma atomic_step_almost_almost t1' t1 g1 σ1 t2 g2 σ2 efs σ1':
  rel_store σ1 σ1' ->
  almost t1 t1' ->
  atomic_step t1 g1 σ1 t2 g2 σ2 efs ->
  (almost t2 t1' ∧ g2 = g1 ∧ σ2 = σ1 ∧ efs = None)
  ∨ (∃ t2' σ2' efs', atomic_step t1' g1 σ1' t2' g2 σ2' efs' ∧ almost t2 t2' /\ rel_fs efs efs' /\ rel_store σ2 σ2').
Proof.
  intros Hstore Hrel. revert t2.
  induction Hrel; intros t2 Hstep.
  { subst. eauto using atomic_step_addpp_almost. }
  { apply invert_step_context in Hstep; eauto.
    destruct Hstep as (?&->&?).
    apply IHHrel in H1. destruct H1 as [(?&->&->&->)|(t2'&efs'&?&?&?&?&?)].
    { left. eauto using almost_fill_item. }
    { right. eexists _,_,_. split_and !; try done.
      { by eapply StepCtx. }
      { eauto using almost_fill_item. } } }
  { apply invert_step_let_val in Hstep. destruct Hstep as (->&?&?&?). subst. simpl.
    left. split_and !; try done. apply almost_call. }
  { right. inversion Hstep; subst.
    { exfalso.
      destruct E; inversion H1; subst. apply atomic_step_no_val in H3; done.
      apply has_to_be_val in H2; eauto using atomic_step_no_val. }
    inversion H1; subst. inversion H; subst.
    apply list_fmap_eq_inj in H11.
    2:{ by inversion 1. }
    destruct v'; inversion H4. subst.
    eexists _,_,None. split_and !; try done.
    { apply StepHead,HeadSeq,HeadCall. 2,4:reflexivity.
      { rewrite fmap_length in H3. done. }
      { rewrite -locs_addpp //. } }
    { replace (μ: self, args, addpp t) with (addpp_val (μ: self, args, t)) by done.
      rewrite -fmap_cons substs'_addpp_val. by apply Al1. } }
Qed.

Lemma rel_store_size sz σ σ' :
  rel_store σ σ' ->
  size_heap sz σ = size_heap sz σ'.
Proof.
  intros ->. unfold size_heap.
  eapply stdpp.map_fold_ind_2 with (P:= fun x1 x2 _ _ => x1 = x2).
  { intros ?????. lia. }
  { intros ?????. lia. }
  { intros ?. rewrite lookup_fmap. destruct (σ' !! i); done. }
  { done. }
  { intros ????????? X1 X2 ->. rewrite lookup_fmap in X1.
    destruct (σ' !! i); try done. destruct b,x1; inversion X1; try done.
    { simpl. rewrite H2. inversion X2. simpl.
      apply (@f_equal _ _ length) in H2. rewrite fmap_length in H2. naive_solver. }
    { inversion X2. subst. simpl. lia. } }
Qed.

Lemma rel_store_avail sz ms σ σ' :
  rel_store σ σ' ->
  available sz ms σ = available sz ms σ'.
Proof.
  intros ?. unfold available. by erewrite rel_store_size.
Qed.

Definition is_call E :=
  match E with ctx_call1 _ | ctx_call2 _ _ _ => true | _ => false end.

Lemma addpp_fill_item_eq E t :
  ¬ is_call E ->
  exists E', addpp (fill_item E t) = fill_item E' (addpp t).
Proof.
  destruct E; try done; intros _.
  by eexists (ctx_let _ _).
  by eexists (ctx_call_prim1 _ _).
  by eexists (ctx_call_prim2 _ _).
  by eexists (ctx_if _ _).
  by eexists ctx_alloc.
  by eexists (ctx_load1 _).
  by eexists (ctx_load2 _).
  by eexists (ctx_store1 _ _).
  by eexists (ctx_store2 _ _).
  by eexists (ctx_store3 _ _).
  by eexists (ctx_cas1 _ _ _).
  by eexists (ctx_cas2 _ _ _).
  by eexists (ctx_cas3 _ _ _).
  by eexists (ctx_cas4 _ _ _).
Qed.

Lemma almost_to_val t t' :
  almost t t' ->
  to_val t = None ->
  to_val t' = None.
Proof.
  inversion 1; subst; eauto.
  { destruct t'; done. }
  { intros ?. apply to_val_fill_item. }
Qed.

Lemma reducible_add_poll t σ:
  reducible (tm_poll ;; t)%T Out σ.
Proof.
  eexists _,_,_,_.
  eapply StepCtx with (E:=ctx_let _ _); try done.
  apply StepHead, HeadSeq, HeadPoll.
Qed.

Inductive IsCall : tm -> Prop :=
| IC1 : forall (t:tm) ts,
    IsCall (t ts)%T
| IC2 : forall E t,
    IsCall t ->
    IsCall (fill_item E t)
.

Lemma reducible_addpp t t' σ σ' g:
  (IsCall t' -> g = Out) ->
  t = addpp t' ->
  rel_store σ σ' ->
  reducible t' g σ' ->
  reducible t g σ.
Proof.
  intros Hcall Ht -> (t1&σ1&g1&efs&Hstep).
  revert t Ht. induction Hstep; subst; intros t ->.
  { destruct_decide (decide (is_call E)) as Hc.
    { assert (g1=Out) as ->.
      { apply Hcall. destruct E; subst; try done; eapply IC1. }
      destruct E; try done; simpl; apply reducible_add_poll. }
    apply (addpp_fill_item_eq _ t1) in Hc. destruct Hc as (?&->).
    apply reducible_context. apply IHHstep; eauto. intros Ht. eauto using IC2. }
  { inversion H; subst.
    2:{ simpl. apply reducible_fork. }
    inversion H0; subst; simpl.
    { apply reducible_let_val. }
    { apply reducible_add_poll. }
    { apply reducible_prim.
      destruct p,v1,v2; inversion H1; done. }
    { apply reducible_if. }
    { eauto using reducible_alloc. }
    { eapply reducible_load. rewrite lookup_fmap H2 //.
      rewrite fmap_length. apply lookup_lt_Some in H5. lia. }
    { eapply reducible_store. rewrite lookup_fmap H5 //.
      rewrite fmap_length; eauto using lookup_lt_Some. }
    { eapply reducible_cas.
      { rewrite lookup_fmap H6 //. }
      { rewrite list_lookup_fmap H7 //. }
      { lia. } }
    { apply reducible_enter. }
    { apply reducible_exit. }
    { apply reducible_poll. } }
Qed.

Lemma red_rel t g t' σ σ' :
  (IsCall t' -> g = Out) ->
  almost t t' ->
  rel_store σ σ' ->
  reducible t' g σ' ->
  reducible t g σ.
Proof.
  intros Hcall Hal Hred Hstep.
  induction Hal; subst.
  { eauto using reducible_addpp. }
  { apply reducible_context. apply IHHal.
    { eauto using IC2. }
    destruct Hstep as (t1&σ1&g1&efs&Hstep).
    apply invert_step_context in Hstep; eauto using almost_to_val.
    destruct Hstep as (?&->&?). by repeat eexists. }
  { apply reducible_let_val. }
  { destruct Hstep as (t1&σ1&g1&efs&Hstep).
    inversion Hstep; subst.
    { exfalso. destruct E; inversion H. subst.
      2:{  eapply has_to_be_val; try done. eauto using atomic_step_no_val. }
      by apply atomic_step_no_val in H1. }
    inversion H; try done. subst. inversion H0. subst.
    inversion H4; subst. rewrite -commute_ok H11 commute_ok. simpl.
    apply reducible_call. rewrite fmap_length //. rewrite locs_addpp //. }
Qed.

Lemma not_stuck_rel t g t' g' σ σ' :
  (IsCall t' -> g = Out) ->
  strong (t,g) (t',g') ->
  rel_store σ σ' ->
  not_stuck t' g' σ' ->
  not_stuck t g σ.
Proof.
  intros ? (?&->) Hstore [(Hs&?)|Hred].
  { left. split; last done.
    destruct (to_val t) eqn:X. done. eapply almost_to_val in X; eauto.
    rewrite X in Hs. by inversion Hs. }
  { right. eauto using red_rel. }
Qed.

Lemma all_not_stuck_rel θ σ θ' σ' :
  Forall (fun '(t,g) => IsCall t -> g = Out) θ' ->
  Forall2 strong θ θ' ->
  rel_store σ σ' ->
  all_not_stuck θ' σ' ->
  all_not_stuck θ σ.
Proof.
  intros X Hf Hrel Hall. intros t g Htg.
  apply elem_of_list_split in Htg. destruct Htg as (l1&l2&->).
  apply Forall2_app_inv_l in Hf. destruct Hf as (l1'&l2'&_&Hf&->).
  apply Forall2_cons_inv_l in Hf. destruct Hf as ((t',g')&l2''&(?&->)&?&->).
  apply Forall_app in X. destruct X as (_&X). inversion X. subst.
  eapply not_stuck_rel; eauto. done. apply Hall. set_solver.
Qed.

Lemma strongs_cangc θ θ':
  Forall2 strong θ θ' ->
  AllOut θ <-> AllOut θ'.
Proof.
  revert θ'. induction θ as [|(?,?)]; intros θ' Hfor.
  { apply Forall2_nil_inv_l in Hfor. subst. done. }
  { apply Forall2_cons_inv_l in Hfor. destruct Hfor as ((?,?)&?&(_&->)&?&->).
    rewrite !AllOut_cons. rewrite IHθ //. }
Qed.

Lemma locs_cons `{Location A} x (xs:list A) :
  locs (x::xs) = locs x ∪ locs xs.
Proof. by auto_locs. Qed.

Lemma locs_addpp_vals (ls:list val) :
  locs (addpp_val <$> ls) = locs ls.
Proof.
  induction ls. done.
  rewrite fmap_cons !locs_cons IHls. f_equal. by destruct a.
Qed.

Lemma locs_addpp_val v :
  locs (addpp_val v) = locs v.
Proof. by destruct v. Qed.

Lemma locs_addpps (ts:list tm) :
  locs (addpp <$> ts) = locs ts.
Proof.
  induction ts. done. rewrite !fmap_cons !locs_cons. rewrite IHts. f_equal.
  apply locs_addpp.
Qed.

Local Ltac sla := first [apply locs_addpp | apply locs_addpp_val | apply locs_addpps | apply locs_addpp_vals].

Lemma rel_ctx_locs E E' :
  rel_ctx E E' ->
  locs E = locs E'.
Proof.
  destruct E,E'; simpl; try done.
  { intros (->&->). auto_locs. sla. }
  { intros ->. sla. }
  { intros (->&->&->). auto_locs. f_equal. f_equal.
    all:sla. }
  { intros (->&->). auto_locs. sla. }
  { intros (->&->). auto_locs. sla. }
  { intros (->&->). auto_locs. f_equal; sla. }
  1-2:intros ->; sla.
  1-3:intros (->&->); auto_locs; f_equal; sla.
  1-4:intros (->&->&->); auto_locs; f_equal; [|sla]; f_equal; sla.
Qed.

Lemma almost_locs t t' :
  almost t t' ->
  locs t = locs t'.
Proof.
  induction 1; subst.
  { rewrite locs_addpp //. }
  { rewrite !locs_fill_item IHalmost. f_equal. eauto using rel_ctx_locs. }
  { auto_locs. rewrite left_id_L. f_equal; sla. }
  { auto_locs. f_equal; sla. }
Qed.

Lemma strongs_locs θ θ' :
  Forall2 strong θ θ' ->
  locs θ.*1 = locs θ'.*1.
Proof.
  revert θ'. induction θ as [|(?,?)]; intros θ' Hfor.
  { apply Forall2_nil_inv_l in Hfor. subst. done. }
  { apply Forall2_cons_inv_l in Hfor. destruct Hfor as ((?,?)&?&(Hal&_)&?&->).
    rewrite !fmap_cons. simpl. rewrite /locs /location_list /locs_list.
    rewrite !fmap_cons. simpl. f_equal.
    by erewrite almost_locs.
    by apply IHθ. }
Qed.

Lemma rel_store_preserves_successor σ σ' l l' :
  rel_store σ σ' ->
  successor σ l l' <-> successor σ' l l'.
Proof.
  intros ->. rewrite /successor /hypotheses.successors.
  rewrite lookup_fmap. destruct (σ' !! l) as [b|].
  2:set_solver. simpl.
  destruct b; last set_solver. simpl.
  rewrite !block_pointer_set_block_elem.
  rewrite locs_addpp_vals //.
Qed.

Lemma rel_store_preserves_reachable r σ σ' l :
  rel_store σ σ' ->
  reachable r σ l <-> reachable r σ' l.
Proof.
  intros ->. split.
  { intros (x&Hx&Hrtc). exists x. split. done.
    eapply rtc_subrel. 2:apply Hrtc. intros l' ? Hs.
    rewrite -rel_store_preserves_successor //. }
  { intros (x&Hx&Hrtc). exists x. split. done.
    eapply rtc_subrel. 2:apply Hrtc. intros l' ? Hs.
    rewrite rel_store_preserves_successor //. }
Qed.

Lemma rel_store_collect r σ σ' :
  rel_store σ σ' ->
  rel_store (collect r σ) (collect r σ').
Proof.
  intros ->. unfold rel_store. apply map_eq.
  intros l.
  rewrite /collect map_lookup_imap !lookup_fmap map_lookup_imap.
  destruct (σ' !! l) eqn:Hl; last done. simpl.
  unfold collect_block.
  destruct_decide (decide (reachable r σ' l)).
  { rewrite decide_True //. by eapply rel_store_preserves_reachable. }
  { rewrite decide_False //. intros X. apply H. rewrite -rel_store_preserves_reachable //. }
Qed.

Lemma addpp_is_alloc n t :
  IsAlloc n (addpp t) →
  IsAlloc n t.
Proof.
  remember (addpp t) as t'. intros His.
  revert t Heqt'.
  induction His; intros t' Heq.
  { destruct t'; inversion Heq.  destruct t'; inversion Heq. destruct v; inversion H1. subst. by econstructor. }
  { symmetry in Heq. apply addpp_fill_item_inv2 in Heq.
    2:{ left. inversion His. eauto. subst. by destruct E0. }
    destruct Heq as (?&?&->&->&_). eauto using IsAllocCtx. }
Qed.

Lemma almost_is_alloc n t t' :
  almost t t' ->
  IsAlloc n t ->
  IsAlloc n t'.
Proof.
  induction 1; subst.
  { eauto using addpp_is_alloc. }
  { intros His. apply IsAlloc_fill_item_inv in His; eauto using IsAllocCtx. }
  { inversion 1. exfalso. destruct E; inversion H0. subst.
    by apply IsAlloc_no_val in H2. }
  { inversion 1. exfalso.
    destruct E; inversion H0; subst.
    { by apply IsAlloc_no_val in H2. }
    { symmetry in H5. eapply has_to_be_val; last done. eauto using IsAlloc_no_val. } }
Qed.

Lemma almost_will_fit sz ms σ σ' t t' :
  rel_store σ σ' ->
  almost t t' ->
  AllocFits sz ms σ' t' ->
  AllocFits sz ms σ t.
Proof.
  intros ????. erewrite rel_store_avail; eauto using almost_is_alloc.
Qed.

Lemma strongs_allwillfit sz ms σ σ' θ θ' :
  rel_store σ σ' ->
  Forall2 strong θ θ' ->
  EveryAllocFits sz ms (θ',σ') ->
  EveryAllocFits sz ms (θ,σ).
Proof.
  intros ? Hstrong Hwill. apply list.Forall_forall.
  intros x Hx. apply elem_of_list_fmap in Hx. destruct Hx as ((t,g)&->&Htg).
  apply elem_of_list_lookup in Htg. destruct Htg as (i&Htg).
  eapply Forall2_lookup_l in Hstrong; eauto. destruct Hstrong as ((t',g')&Htg'&(Hal&->)).
  eapply list.Forall_forall in Hwill.
  2:{ apply elem_of_list_fmap. exists (t',g'). split. reflexivity. eapply elem_of_list_lookup. eauto. }
  { simpl in *. eauto using almost_will_fit. }
Qed.

Lemma IsCall_inv t :
  IsCall t ->
  exists es t' ts, t = fill_items es (tm_call t' ts).
Proof.
  induction 1.
  { eexists nil,_,_. reflexivity. }
  { destruct IHIsCall as (es&?&?&->). eexists (E::es),_,_. reflexivity. }
Qed.

Lemma atomic_step_weak_anf_call es (t:tm) ts g σ t0 g0 σ0 efs :
  weak_anf (fill_items es (t ts)%T) ->
  atomic_step (fill_items es (t ts)) g σ t0 g0 σ0 efs ->
  g = Out.
Proof.
  revert t0; induction es; intros t0. simpl. inversion 1; subst.
  { inversion 1; subst.
    { exfalso. destruct E; inversion H1; subst.
      { inversion H2; subst; eauto using atomic_step_no_var.
        by eapply atomic_step_no_val in H5. }
      { apply Forall_app in H3. destruct H3 as (?&H3).
        inversion H3. subst. inversion H8; subst;
          eauto using atomic_step_no_var.
        by eapply atomic_step_no_val in H5. } }
    {  inversion H1; subst. by inversion H4. } }
  { simpl. intros Hweak Hstep.
    apply weak_anf_fill_item_inv in Hweak.
    apply invert_step_context in Hstep.
    2:{ destruct es; try done. apply to_val_fill_item. }
    naive_solver. }
Qed.

Lemma calls_are_outside θ σ :
  Forall weak_anf θ.*1 ->
  all_not_stuck θ σ ->
  Forall (λ '(t, g), IsCall t → g = Out) θ.
Proof.
  intros Hfor Hnot. apply list.Forall_forall.
  intros (t,g) Htg Hcall.
  apply IsCall_inv in Hcall. destruct Hcall as (es&t'&ts'&->).
  specialize (Hnot _ _ Htg). destruct Hnot as [(?&?)|(t0&σ0&g0&efs&?)].
  { done. }
  { apply elem_of_list_lookup in Htg.
    destruct Htg as (i&Hi).
    eapply Forall_lookup with (i:=i) in Hfor.
    2:{ rewrite list_lookup_fmap Hi //. }
    eauto using atomic_step_weak_anf_call. }
Qed.

Lemma is_alloc_not_weak_base n t :
  IsAlloc n t ->
  ¬ base_anf t.
Proof.
  inversion 1; subst.
  { inversion 1. }
  { destruct E; inversion 1. }
Qed.

Lemma addpp_is_alloc' n t :
  weak_anf t ->
  IsAlloc n t →
  IsAlloc n (addpp t).
Proof.
  intros Hweak His.
  induction His.
  { constructor. }
  { apply weak_anf_fill_item_inv in Hweak. destruct Hweak as (?&?&?).
    assert (¬ base_anf t) by eauto using is_alloc_not_weak_base.
    destruct_decide (decide (is_call E)) as HE.
    { exfalso. destruct E; naive_solver. }
    apply (addpp_fill_item_eq _ t) in HE. destruct HE as (?&->).
    constructor. eauto. }
Qed.

Lemma weak_anf_is_alloc_no_call n (t:tm) ts :
  weak_anf (t ts)%T ->
  IsAlloc n (t ts)%T ->
  False.
Proof.
  intros Hweak. inversion 1. subst.
  inversion Hweak. subst. destruct E; inversion H0; subst.
  { by eapply is_alloc_not_weak_base. }
  { simpl in H0. eapply is_alloc_not_weak_base; try done.
    eapply list.Forall_forall in H5. done. set_solver. }
Qed.

Lemma is_poll_not_weak_base t :
  IsPoll t ->
  ¬ base_anf t.
Proof.
  inversion 1; subst.
  { inversion 1. }
  { destruct E; inversion 1. }
Qed.

Lemma weak_anf_is_poll_no_call (t:tm) ts :
  weak_anf (t ts)%T ->
  IsPoll (t ts)%T ->
  False.
Proof.
  intros Hweak. inversion 1. subst.
  inversion Hweak. subst. destruct E; inversion H0; subst.
  { by eapply is_poll_not_weak_base. }
  { simpl in H0. eapply is_poll_not_weak_base; try done.
    eapply list.Forall_forall in H5. done. set_solver. }
Qed.

Lemma almost_is_alloc' n t t' :
  weak_anf t' ->
  almost t t' ->
  IsAlloc n t' ->
  IsAlloc n t.
Proof.
  induction 2; subst.
  { eauto using addpp_is_alloc'. }
  { intros His. apply IsAlloc_fill_item_inv in His; eauto using almost_to_val.
    apply weak_anf_fill_item_inv in H. destruct H as (?&?&?). constructor; eauto. }
  all:intros ?; exfalso; by eapply weak_anf_is_alloc_no_call.
Qed.

Lemma almost_will_fit' sz ms σ σ' t t' :
  rel_store σ σ' ->
  weak_anf t' ->
  almost t t' ->
  AllocFits sz ms σ t ->
  AllocFits sz ms σ' t'.
Proof.
  intros ?????. erewrite <- rel_store_avail; eauto using almost_is_alloc'.
Qed.

Lemma addpp_is_poll' t :
  weak_anf t ->
  IsPoll t →
  IsPoll (addpp t).
Proof.
  intros Hweak His.
  induction His.
  { constructor. }
  { apply weak_anf_fill_item_inv in Hweak. destruct Hweak as (?&?&?).
    assert (¬ base_anf t) by eauto using is_poll_not_weak_base.
    destruct_decide (decide (is_call E)) as HE.
    { exfalso. destruct E; naive_solver. }
    apply (addpp_fill_item_eq _ t) in HE. destruct HE as (?&->).
    constructor; eauto. }
Qed.

Lemma almost_is_poll' t t' :
  weak_anf t' ->
  almost t t' ->
  IsPoll t' ->
  IsPoll t.
Proof.
  induction 2; subst.
  { eauto using addpp_is_poll'. }
  { intros His. apply IsPoll_fill_item_inv in His; eauto using almost_to_val.
    apply weak_anf_fill_item_inv in H. destruct H as (?&?&?). constructor; eauto. }
  all:intros ?; exfalso; by eapply weak_anf_is_poll_no_call.
Qed.

Lemma forall_almost_will_fit sz ms σ σ' θ θ' :
  rel_store σ σ' ->
  Forall2 almost θ.*1 θ'.*1 ->
  Forall weak_anf θ'.*1 ->
  EveryAllocFits sz ms (θ,σ) ->
  EveryAllocFits sz ms (θ',σ').
Proof.
  intros ? Hfor2 Hfor Hall.
  apply list.Forall_forall. intros t' Ht'.
  apply elem_of_list_lookup in Ht'. destruct Ht' as (i&Ht').
  eapply Forall2_lookup_r in Hfor2; last done. destruct Hfor2 as (t&Ht&Hal).
  eapply almost_will_fit'; eauto.
  { eapply list.Forall_forall. done. eapply elem_of_list_lookup. eauto. }
  { eapply list.Forall_forall. done. eapply elem_of_list_lookup. eauto. }
Qed.

Lemma forall_strong_forall_almost θ θ' :
  Forall2 strong θ θ' ->
  Forall2 almost θ.*1 θ'.*1.
Proof.
  revert θ'. induction θ; intros θ'; inversion 1.
  { by constructor. }
  { subst. rewrite !fmap_cons. constructor; eauto. destruct a,y; naive_solver. }
Qed.

Definition mimic (σ1 σ2 : store) : store :=
  map_imap (fun l b => Some (match b with | BDeallocated => BDeallocated | _ => σ1 !!! l end)) σ2.

Lemma dom_mimic σ1 σ2 :
  dom (mimic σ1 σ2) = dom σ2.
Proof.
  unfold mimic.
  apply leibniz_equiv. intros l. rewrite !elem_of_dom.
  split.
  { intros (x&Hx). rewrite map_lookup_imap in Hx.
    by destruct (σ2 !! l). }
  { intros (x&Hx). rewrite map_lookup_imap Hx //. }
Qed.

Lemma gc_rel_store r σ1 σ1' σ2 :
  σ1 ≠ σ2 ->
  rel_store σ1 σ1' ->
  gc r σ1 σ2 ->
  exists σ2', gc r σ1' σ2' /\ σ1' ≠ σ2' /\ rel_store σ2 σ2'.
Proof.
  intros Eq -> [Hdom Hgc].
  rewrite dom_fmap_L in Hdom.
  rewrite dom_fmap_L in Hgc.
  exists (mimic σ1' σ2).
  assert (σ2 = addpp_block <$> (mimic σ1' σ2)) as Ho.
  { apply map_eq. intros l.
    rewrite lookup_fmap /mimic map_lookup_imap.
    destruct (σ2 !! l) eqn:E2. 2:done. destruct b; last done.
    simpl. rewrite lookup_total_alt.
    assert (l ∈ dom σ1') as Hl.
    { rewrite Hdom. by apply elem_of_dom. }
    assert (is_Some ( (σ1' !! l))) as (b1&E1).
    { by apply elem_of_dom. }
    specialize (Hgc l Hl). destruct Hgc as [Hgc|(?&Hgc)].
    { rewrite !lookup_total_alt lookup_fmap E1 E2 in Hgc.
      simpl in *. rewrite E1 Hgc //. }
    { exfalso. rewrite lookup_total_alt E2 // in Hgc. } }
  split_and !; eauto.
  { split.
    { rewrite Hdom dom_mimic //. }
    { intros l Hl.
      specialize (Hgc l Hl).
      destruct Hgc as [Hgc|(?&Hgc)].
      { left. rewrite !lookup_total_alt in Hgc.
        rewrite lookup_fmap in Hgc. rewrite !lookup_total_alt.
        rewrite /mimic map_lookup_imap.
        destruct (σ2 !! l) as [b2|] eqn:E2.
        2:{ exfalso. apply not_elem_of_dom in E2. set_solver. }
        apply elem_of_dom in Hl. destruct Hl as (b1&E1). simpl in *.
        rewrite lookup_total_alt E1. simpl. destruct b2; try done.
        rewrite E1 in Hgc. destruct b1; inversion Hgc. done. }
      { right. split.
        { rewrite <- rel_store_preserves_reachable. done. done. }
        { destruct (σ2 !! l) as [b2|] eqn:E2.
          2:{ exfalso. apply not_elem_of_dom in E2. set_solver. }
          apply elem_of_dom in Hl. destruct Hl as (b1&E1). simpl in *.
          rewrite lookup_total_alt E2 in Hgc. simpl in Hgc.
          rewrite /mimic lookup_total_alt map_lookup_imap E2 Hgc //. } } } }
  { intros F. apply Eq. rewrite Ho {1}F //. }
Qed.

Lemma forall_strong_all_outside θ θ' :
  Forall2 strong θ θ' ->
  AllOut θ ->
  AllOut θ'.
Proof.
  revert θ'. induction θ; intros θ'; inversion 1.
  { by constructor. }
  { subst. inversion 1. subst. constructor; eauto.
    { destruct a,y; naive_solver. }
    by apply IHθ. }
Qed.

Lemma step_gc_rel sz ms θ1 σ1 θ2 σ2 θ1' σ1' :
  step_default sz ms (θ1,σ1) (θ2,σ2) ->
  Forall weak_anf θ1'.*1 ->
  rel_store σ1 σ1' ->
  Forall2 strong θ1 θ1' ->
  exists θ2' σ2', rtc (step_default sz ms) (θ1',σ1') (θ2',σ2') /\ Forall2 strong θ2 θ2' /\ rel_store σ2 σ2'.
Proof.
  intros (a&Hen&Hstep) Hweap Hstore Hfor.
  inversion Hstep; subst.
  { assert (Forall2 almost θ1.*1 θ1'.*1) as Halmost by eauto using forall_strong_forall_almost.
    apply elem_of_middle in H4.  destruct H4 as (l1&l2&->&?).
    apply Forall2_app_inv_l in Hfor.
    destruct Hfor as (l1'&l2'&?&Hfor&?). subst.
    apply Forall2_cons_inv_l in Hfor. destruct Hfor as ((?&l3')&?&Hs&?&->).
    destruct Hs as (?&->). generalize H1. intros Hsim.
    eapply atomic_step_almost_almost in H1; eauto.
    destruct H1 as [(?&->&->&->)| (?&?&?&?&?&?&?) ].
    { eexists _,_. split_and !. apply rtc_refl.
      { simpl. rewrite right_id insert_app_r_alt; last lia. rewrite Nat.sub_diag.
        apply Forall2_app. done. apply Forall2_cons. done. done. }
      { done. } }
    { assert (length l1 = length l1') as Hl by eauto using Forall2_length.
      destruct Hen as (?&?&Eq&?&?).
      rewrite lookup_app_r in Eq; last lia. rewrite Hl Nat.sub_diag in Eq. simpl in Eq. inversion Eq.
      subst x3 x4.
      eexists _,_.
      rewrite !insert_app_r_alt; last lia. rewrite Nat.sub_diag.
      split_and !.
      { apply rtc_once.
        exists (Thread (length l1)).
        split.
        { simpl.
          assert (weak_anf t0).
          { eapply list.Forall_forall. done. rewrite fmap_app fmap_cons. set_solver. }
          eexists _,_. split_and !.
          { rewrite lookup_app_r; last lia. rewrite Hl Nat.sub_diag. reflexivity. }
          { eauto using almost_will_fit'. }
          { intros ?.
            eapply forall_almost_will_fit; eauto using almost_is_poll'. } }
        { econstructor; eauto.
          rewrite lookup_app_r; last lia. rewrite Hl Nat.sub_diag. reflexivity. } }
      { apply Forall2_app.
        { rewrite !insert_app_r_alt; last lia. rewrite Hl Nat.sub_diag.
          apply Forall2_app. done. simpl.
          { by constructor. } }
        { destruct efs,x2; try done.
          { simpl. constructor; last done. split; try done. by apply Al1. } } }
      { done. } } }
  { eapply gc_rel_store in H3; eauto. destruct H3 as (σ2'&Hgc&Hneq&?).
    eexists _,σ2'. split_and !; eauto.
    { apply rtc_once. eexists GC. split.
      { done. }
      { econstructor. rewrite -(strongs_locs θ2) //. done. } } }
Qed.

Lemma rtc_step_rel sz ms θ1 σ1 θ2 σ2 θ1' σ1' :
  rtc (step_default sz ms) (θ1,σ1) (θ2,σ2) ->
  rel_store σ1 σ1' ->
  Forall2 strong θ1 θ1' ->
  Always (step_default sz ms) (θ1',σ1') (fun '(θ,_) => Forall weak_anf θ.*1)  ->
  exists θ2' σ2', rtc (step_default sz ms) (θ1',σ1') (θ2',σ2') /\ Forall2 strong θ2 θ2' /\ rel_store σ2 σ2'.
Proof.
  remember (θ1,σ1) as ρ1. remember (θ2,σ2) as ρ2.
  replace θ1 with (fst ρ1) by naive_solver.
  replace σ1 with (snd ρ1) by naive_solver.
  replace θ2 with (fst ρ2) by naive_solver.
  replace σ2 with (snd ρ2) by naive_solver.
  clear dependent θ1 σ1 θ2 σ2.
  intros Hrtc. revert θ1' σ1'. induction Hrtc; intros θ1' σ1' Hstore Hfor Hal.
  { eexists _,_. split_and !; eauto. apply rtc_refl. }
  destruct x as (θ,σ), y as (θ',σ'), z as (θ0&σ0). simpl in *.

  assert (Forall weak_anf θ1'.*1).
  { specialize (Hal _ (rtc_refl _ _)). done. }
  eapply step_gc_rel in H; eauto. destruct H as (?&?&?&Hstrong'&Hfor').
  eapply IHHrtc in Hstrong'; eauto.
  2:{ intros ? Hsteps. apply Hal. by etrans. }
  destruct Hstrong' as (θlast&σlast&?&?&?).
  exists θlast, σlast. split_and!; try done. by etrans.
Qed.


Lemma addpp_is_poll_is_callt t t' :
  IsPoll t ->
  ¬ IsPoll t' ->
  t = addpp t' ->
  IsCall t'.
Proof.
  intros E. revert t'. induction E; intros t' X Eq.
  { destruct t'; inversion Eq. exfalso. apply X. constructor. }
  { destruct_decide (decide (is_let_call E)) as Hc.
    { destruct E; try done. simpl in Eq. destruct t'; inversion Eq.
      apply IC1. subst. eapply IC2 with (E:=ctx_let _ _). apply IHE; last done.
      intros ?. apply X. by eapply IsPollCtx with (E:=ctx_let _ _). }
    symmetry in Eq. apply addpp_fill_item_inv2 in Eq; last eauto.
    destruct Eq as (?&?&->&->&_). apply IC2. apply IHE; eauto using IsPollCtx. }
Qed.

Lemma almost_is_poll_is_call t t' :
  IsPoll t ->
  ¬ IsPoll t' ->
  almost t t' ->
  IsCall t'.
Proof.
  intros X1 X2. induction 1.
  { subst. eauto using addpp_is_poll_is_callt.  }
  { apply IC2. apply IHalmost. apply IsPoll_fill_item_inv in X1; eauto.
    intros ?. apply X2. econstructor; eauto. }
  all:apply IC1.
Qed.

Lemma IsCall_no_val t :
  IsCall t ->
  to_val t = None.
Proof.
  inversion 1. done. apply to_val_fill_item.
Qed.

Lemma call_not_alloc n t :
  weak_anf t ->
  IsCall t ->
  IsAlloc n t ->
  False.
Proof.
  induction 2.
  { eauto using weak_anf_is_alloc_no_call. }
  { intros X. apply IsAlloc_fill_item_inv in X; eauto using IsCall_no_val.
    apply weak_anf_fill_item_inv in H. naive_solver. }
Qed.

Lemma call_not_poll t :
  weak_anf t ->
  IsCall t ->
  IsPoll t ->
  False.
Proof.
  induction 2.
  { eauto using weak_anf_is_poll_no_call. }
  { intros X. apply IsPoll_fill_item_inv in X; eauto using IsCall_no_val.
    apply weak_anf_fill_item_inv in H. naive_solver. }
Qed.

Lemma call_is_enabled sz ms θ σ π t g :
  θ !! π = Some (t,g) ->
  weak_anf t ->
  IsCall t ->
  Enabled sz ms (Thread π) (θ, σ).
Proof.
  intros X1 X2. eexists _,_. split_and !; try done.
  { intros ??. exfalso. eauto using call_not_alloc. }
  { intros ?. exfalso. eauto using call_not_poll. }
Qed.

Lemma IsCall_not_stuck_true sz θ t i g ms σ :
  weak_anf t ->
  IsCall t ->
  θ !! i = Some (t, g) ->
  strong_safety.NotStuck sz ms (Thread i) (θ, σ) ->
  g=Out.
Proof.
  intros Hweak HC Hi Hnot.
  apply IsCall_inv in HC. destruct HC as (es&t'&ts'&->).
  destruct Hnot as [(?&?)|X].
  { naive_solver. }
  { destruct X as (?&X). destruct X as (?&X). inversion X. subst.
    rewrite Hi in H3. inversion H3. subst.
    apply atomic_step_weak_anf_call in H4;
    eauto using atomic_step_weak_anf_call. }
Qed.

Lemma strongs_aapao sz ms θ θ' σ σ' :
  Forall weak_anf θ'.*1 ->
  Forall2 strong θ θ' ->
  rel_store σ σ' ->
  ( ∀ π, Enabled sz ms (Thread π) (θ', σ') → strong_safety.NotStuck sz ms (Thread π) (θ', σ')) ->
  paao (θ', σ') ->
  paao (θ, σ).
Proof.
  intros Hweaks Hstrongs Hrel Hgo Haaa.
  intros ?? X E.
  apply elem_of_list_lookup in X. destruct X as (i&Hi).
  eapply Forall2_lookup_l in Hstrongs; last done.
  destruct Hstrongs as ((t'&g')&?&(?&<-)).

  destruct E as [E|(?&E)].
  { destruct_decide (decide (IsPoll t')).
    { eapply (Haaa t' g); eauto. eapply elem_of_list_lookup. eauto. }
    { apply almost_is_poll_is_call in H0; eauto.
      assert (weak_anf t').
      { eapply list.Forall_forall. done. apply elem_of_list_fmap. eexists _. split.
        2:{ apply elem_of_list_lookup. eauto. } done. }
      eauto using call_is_enabled, IsCall_not_stuck_true. } }
  { eapply (Haaa t' g); eauto. eapply elem_of_list_lookup. eauto.
    right. eexists _. eauto using almost_is_alloc. }
Qed.

Lemma gc_rel_store' r σ1 σ1' σ2' :
  rel_store σ1 σ1' ->
  gc r σ1' σ2' ->
  exists σ2, gc r σ1 σ2 /\ rel_store σ2 σ2'.
Proof.
  intros -> [Hdom Hgc].
  exists (addpp_block <$> σ2').
  split; last done.
  split.
  { rewrite !dom_fmap_L //. }
  rewrite dom_fmap_L.
  intros l Hl.
  assert (is_Some (σ1' !! l)) as (b1&E1).
  { apply elem_of_dom. set_solver. }
  assert (is_Some (σ2' !! l)) as (b2&E2).
  { apply elem_of_dom. set_solver. }
  destruct (Hgc _ Hl) as [X|(X1&X2)]; [left | right].
  { rewrite !lookup_total_alt E1 E2 in X. simpl in X. subst.
    rewrite !lookup_total_alt !lookup_fmap E1 E2 //. }
  { rewrite lookup_total_alt E2 in X2. simpl in X2. subst. split.
    { rewrite rel_store_preserves_reachable. 2:done. done. }
    { rewrite lookup_total_alt lookup_fmap E2 //. } }
Qed.

Lemma strongs_gns sz ms θ θ' σ σ' :
  Forall2 strong θ θ' ->
  rel_store σ σ' ->
  gccmeaf sz ms (θ', σ') ->
  gccmeaf sz ms (θ, σ).
Proof.
  intros Hstrongs Hrel Hgns Hout Hall.
  eapply forall_strong_all_outside in Hout; eauto.
  eapply Hgns in Hout.
  assert (¬ EveryAllocFits sz ms (θ',σ')) as Hne.
  { intros X. apply Hall. eauto using strongs_allwillfit. }
  apply Hout in Hne.
  destruct Hne as (σ0&Hgc&?).
  eapply gc_rel_store' in Hgc; last done.
  destruct Hgc as (σ2&Hgc&Hrel2).
  exists σ2. split.
  { erewrite strongs_locs. done. done. }
  { eauto using strongs_allwillfit. }
Qed.

Lemma Forall_weak_anf_lookup θ i t (g:status) :
  θ !! i = Some (t,g) ->
  Forall weak_anf θ.*1 ->
  weak_anf t.
Proof.
  intros ??.
  eapply list.Forall_forall. done. apply elem_of_list_fmap. eexists _. split.
  2:{ apply elem_of_list_lookup. eauto. } done.
Qed.

Lemma strongs_allwillfit' sz ms σ σ' θ θ' :
  rel_store σ σ' ->
  Forall weak_anf θ'.*1 ->
  Forall2 strong θ θ' ->
  EveryAllocFits sz ms (θ,σ) ->
  EveryAllocFits sz ms (θ',σ').
Proof.
  intros ? Hweak Hstrong Hwill. apply list.Forall_forall.
  intros x Hx. apply elem_of_list_fmap in Hx. destruct Hx as ((t',g')&->&Htg').
  apply elem_of_list_lookup in Htg'. destruct Htg' as (i&Htg').
  eapply Forall2_lookup_r in Hstrong; eauto. destruct Hstrong as ((t,g)&Htg&(Hal&->)).
  simpl. eapply almost_will_fit'; eauto using Forall_weak_anf_lookup.
  eapply list.Forall_forall in Hwill.
  2:{ apply elem_of_list_fmap. exists (t,g'). split. reflexivity. eapply elem_of_list_lookup. eauto. }
  done.
Qed.

Lemma strongs_enabled sz ms π θ σ θ' σ' :
  Forall weak_anf θ'.*1 ->
  Forall2 strong θ θ' ->
  rel_store σ σ' ->
  Enabled sz ms (Thread π) (θ, σ) ->
  Enabled sz ms (Thread π) (θ', σ') .
Proof.
  intros Hfor Hstrongs Hrel (t&g&Htg&?&?).
  destruct (Forall2_lookup_l _ _ _ _ _ Hstrongs Htg) as ((t'&g')&?&(?&<-)).
  assert (weak_anf t') by eauto using Forall_weak_anf_lookup.
  eexists _,_. split_and !; try done.
  { eauto using almost_will_fit'. }
  { intros Hpoll.
    eapply almost_is_poll' in Hpoll; eauto.
    eapply strongs_allwillfit'; eauto. }
Qed.

Lemma almost_is_val t v :
  almost t (tm_val v) ->
  exists v', t = tm_val v'.
Proof.
  inversion 1; subst.
  { eexists . done. }
  { by destruct E'. }
Qed.

Lemma strongs_exited π θ σ θ' σ' :
  Forall2 strong θ θ' ->
  Ended (Thread π) (θ',σ') ->
  Ended (Thread π) (θ,σ).
Proof.
  intros Hstrongs (t'&g'&Htg'&Hv&?).
  destruct (Forall2_lookup_r _ _ _ _ _ Hstrongs Htg') as ((t&g)&?&(?&<-)).
  eexists _,_. split_and !; eauto.
  destruct Hv as (v&Hv). destruct t'; inversion Hv. subst v0.
  apply almost_is_val in H1. destruct H1 as (?&->). done.
Qed.


Lemma fred_rel sz ms π θ θ' σ σ' :
  Forall weak_anf θ'.*1 ->
  Forall2 strong θ θ' ->
  rel_store σ σ' ->
  Enabled sz ms (Thread π) (θ, σ) ->
  strong_safety.Reducible sz ms (Thread π) (θ', σ') ->
  strong_safety.Reducible sz ms (Thread π) (θ, σ).
Proof.
  intros Hweak Hstrongs Hrel ? X. generalize X. intros ((θ1'&σ1')&(_&Hstep)).
  inversion Hstep. subst.
  assert (reducible t g σ') as Hred by by repeat eexists.
  destruct (Forall2_lookup_r _ _ _ _ _ Hstrongs H5) as ((t1&g1)&?&(?&<-)).
  eapply red_rel in Hred; try done.
  2:{ intros ?. eapply IsCall_not_stuck_true; try done.
      2:by right. eauto using Forall_weak_anf_lookup. }
  destruct Hred as (?&?&?&?&?).
  eexists _. split. done. by econstructor.
Qed.

(* Main result of the file. *)
Theorem addpp_preserves_safety sz ms' ms t :
  weak_anf t ->
  Always (step_default sz ms') (init t) (StronglySafe sz ms) ->
  Always (step_default sz ms') (init (addpp t)) (StronglySafe sz ms).
Proof.
  intros Hweak Halways (θ,σ) Hsteps.
  pose proof (weak_anf_always sz ms' _ Hweak) as Hweak'.
  eapply (rtc_step_rel _ _ _ _ _ _ [(t,Out)] ∅) in Hsteps; first last; eauto.
  { apply Forall2_cons. split; try done. by apply Al1. constructor. }
  { rewrite /rel_store fmap_empty //. }
  destruct Hsteps as (θ'&σ'&Hsteps&Hfor&?).
  assert (Forall weak_anf θ'.*1) as Hweak''.
  { by apply Hweak' in Hsteps. }
  apply Halways in Hsteps. destruct Hsteps as (X1&X2&X3).
  split_and !.
  { eauto using strongs_aapao. }
  { eauto using strongs_gns. }
  { intros π Hπ.
    assert (Enabled sz ms (Thread π) (θ', σ')) as Hen by eauto using strongs_enabled.
    apply X3 in Hen.
    destruct Hen as [|Hen].
    { left. by eapply strongs_exited. }
    { right. eauto using fred_rel. } }
Qed.
