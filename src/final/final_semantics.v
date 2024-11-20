From Coq Require Import Program.Equality ssreflect.
From stdpp Require Import gmap relations list ssreflect.

From irisfit.spacelang Require Import hypotheses.
From irisfit Require Export head_semantics pointers store semantics substitution more_maps_and_sets.
From irisfit.final Require Export gc.
From irisfit.program_logic Require Import linked wp_adequacy.

Set Implicit Arguments.

(* ------------------------------------------------------------------------ *)
(* [Auxiliary predicates] *)

Inductive IsAlloc : Z -> tm -> Prop :=
| IsAllocHead : forall n, IsAlloc n (tm_alloc n)
| IsAllocCtx : forall n E t, IsAlloc n t -> IsAlloc n (fill_item E t).

Lemma IsAlloc_no_val n t :
  IsAlloc n t ->
  to_val t = None.
Proof. inversion 1; try done. by destruct E. Qed.

Lemma IsAlloc_fill_item_inv n E t :
  to_val t = None ->
  IsAlloc n (fill_item E t) ->
  IsAlloc n t.
Proof.
  inversion 2.
  { destruct E; naive_solver. }
  apply fill_item_inj in H1; eauto using IsAlloc_no_val.
  naive_solver.
Qed.

Inductive IsPoll : tm -> Prop :=
| IsPollHead : IsPoll tm_poll
| IsPollCtx : forall E t, IsPoll t -> IsPoll (fill_item E t).

Lemma IsPoll_no_val t :
  IsPoll t ->
  to_val t = None.
Proof.
  induction 1. done. apply to_val_fill_item.
Qed.

Lemma IsPoll_fill_item_inv E t :
  to_val t = None ->
  IsPoll (fill_item E t) ->
  IsPoll t.
Proof.
  inversion 2.
  { destruct E; naive_solver. }
  apply fill_item_inj in H1; eauto using IsPoll_no_val.
  naive_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* [Semantics] *)

Section WithSize.
Context (sz:nat -> nat).

Definition configuration : Type := (list (tm*status) * store).

Inductive action :=
| Thread of nat
| GC.

Definition WellFormed (a:action) (ρ:configuration) : Prop :=
  let '(θ,σ) := ρ in
  match a with
  | Thread π => π < length θ
  | GC => live_heap_size sz (locs θ.*1) σ ≠ size_heap sz σ end.

Definition AllocFits (ms:nat) (σ:store) (t:tm) :=
  forall n, IsAlloc n t -> sz (Z.to_nat n) <= available sz ms σ.
Definition EveryAllocFits (ms:nat) : configuration -> Prop :=
  fun '(θ,σ) => Forall (AllocFits ms σ) θ.*1.

Inductive step_action : action -> configuration -> configuration -> Prop :=
| ActionThread : forall θ σ θ' σ' t g t' g' π efs,
    θ !! π = Some (t,g) ->
    atomic_step t g σ t' g' σ' efs ->
    θ' = <[π:=(t',g')]> θ ++ opt_to_list efs →
    step_action (Thread π) (θ,σ) (θ',σ')
| ActionGC : forall θ σ σ',
    gc (locs θ.*1) σ σ' ->
    σ ≠ σ' ->
    step_action GC (θ,σ) (θ,σ')
.

Definition Enabled (ms:nat) (a:action) (c:configuration) : Prop :=
  let '(θ,σ) := c in
  match a with
  | Thread π =>
      exists t g, θ !! π = Some (t,g)
             /\ (AllocFits ms σ t)
             /\ (IsPoll t -> EveryAllocFits ms c)
  | GC => AllOut θ end.

Definition step_enabled (ms:nat) a (ρ ρ':configuration) : Prop :=
  Enabled ms a ρ /\ step_action a ρ ρ'.

Definition step_default (ms:nat) (ρ ρ':configuration) : Prop :=
  ∃ a, step_enabled ms a ρ ρ'.

Definition is_val (t:tm) := match t with tm_val _ => true | _ => false end.

Lemma forall_is_val_inv xs :
  Forall is_val xs ->
  exists vs, xs = tm_val <$> vs.
Proof.
  induction xs. by exists nil.
  inversion 1; subst.
  apply IHxs in H3. destruct H3 as (vs&->).
  destruct a; try done. exists (v::vs). done.
Qed.

Definition init (t:tm) : list (tm*status) * store := ([(t,Out)],∅).

(* ------------------------------------------------------------------------ *)
(* Towards [steps_gc_steps] *)

Lemma zip_cons {A B} (x:A) (y:B) xs ys :
  zip (x::xs) (y::ys) = (x,y)::zip xs ys.
Proof. easy. Qed.

Local Lemma gc_read_root l bs r σ σ' :
  l ∈ r ->
  gc r σ σ' ->
  σ' !! l = Some (BBlock bs) ->
  σ !! l = Some (BBlock bs).
Proof.
  intros Hl [Hr1 Hr2] Hb.
  assert (l ∈ dom σ) as Hlr.
  { rewrite Hr1. apply elem_of_dom.  rewrite Hb. easy. }
  apply Hr2 in Hlr.

  assert (reachable r σ l) as Hlr'.
  { eauto using roots_are_reachable. }

  destruct Hlr as [Hlr|]; try easy.
  rewrite !lookup_total_alt in Hlr.
  rewrite Hb in Hlr. simpl in Hlr.
  destruct (σ !! l); naive_solver.
Qed.

Lemma gc_alloc l σ σ' r n :
  l ∉ dom σ' ->
  gc r σ σ' ->
  gc ({[l]} ∪ r) (<[l:=BBlock (replicate n val_unit)]> σ)
    (<[l:=BBlock (replicate n val_unit)]> σ').
Proof.
  intros ? []. constructor.
  { rewrite !dom_insert_L //. set_solver. }
  intros l'. rewrite dom_insert_L elem_of_union elem_of_singleton.
  destruct_decide (decide (l=l')); subst.
  { intros _. left. rewrite !lookup_total_insert //. }
  intros [|]; first congruence.
  destruct (H1 _ H3) as [|(?&?)]; [left|right].
  { rewrite !lookup_total_insert_ne //. }
  { rewrite lookup_total_insert_ne //. split; last done.

    intros X. apply reachable_union in X. destruct X as [X|X].
    { destruct X as (?&?&Hrtc). assert (x=l) by set_solver. subst.
      inversion Hrtc; try done. subst.
      rewrite /successor /successors lookup_insert in H7.
      erewrite pointers.block_no_pointers in H7. 2:done. 2:done. set_solver. }

    { apply analyze_reachable_after_alloc in X; try done.
      { apply not_elem_of_dom. set_solver. }
      { intros ? Hp. erewrite pointers.block_no_pointers in Hp.
        2:done. 2:done. set_solver. } } }
Qed.

Lemma gc_load l n r σ σ' bs v :
  gc ({[l]} ∪ r) σ σ' ->
  σ' !! l = Some (BBlock bs) ->
  bs !! n = Some v ->
  gc (locs v ∪ r) σ σ'.
Proof.
  intros [] ??. constructor; first done.
  intros l0 Hl0. destruct (H0 _ Hl0) as [|(?&?)];[left|right]; first done.
  split; last done. intros Hr. apply H3.
  destruct Hr as (x&Hx&?). rewrite elem_of_union in Hx. destruct Hx.
  { exists l. split. set_solver. eapply rtc_l; last done.
    eapply successor_to_rstore.
    { eapply gc_read_root; try done. set_solver. }
    apply pointers.pointers_locs. apply locs_elem_subseteq in H2. set_solver. }
  { exists x. split; first set_solver. done. }
Qed.

Lemma gc_store l n v σ σ' r' r bs :
  {[l]} ∪ locs v ⊆ r' ->
  gc (r' ∪ r) σ σ' ->
  σ' !! l = Some (BBlock bs) ->
  gc r (<[l:=BBlock (<[n:=v]> bs)]> σ)
    (<[l:=BBlock (<[n:=v]> bs)]> σ').
Proof.
  intros Hl [] ?. constructor.
  { rewrite !dom_insert_L //. set_solver. }
  intros l' H'. rewrite dom_insert_L elem_of_union elem_of_singleton in H'.
  destruct_decide (decide (l=l')).
  { clear H'. subst l'. left. rewrite !lookup_total_insert //. }
  destruct H' as [|]; first congruence.
  destruct (H0 _ H3) as [|(?&?)]; subst.
  { left. rewrite !lookup_total_insert_ne //. }
  right. rewrite lookup_total_insert_ne //. split; last done.

  intros (x&Hx&Hr).
  apply analyze_path_after_heap_update with (b:=BBlock bs) in Hr.
  2:{ eapply gc_read_root. 2:done. 2:done. set_solver. }
  eapply H4. apply reachable_union.
  destruct Hr as [|(l0&?&?&?)].
  { right. exists x. eauto. }
  { left. apply block_pointer_set_insert in H6. destruct H6; last naive_solver.
    destruct v. 2-5:set_solver. assert (l0=l1) by set_solver. subst.
    exists l1. split. set_solver. done. }
Qed.

Lemma head_step_gc_insensitive t1 g1 σ1 t2 g2 σ2 σ1' r :
  gc (locs t1 ∪ r) σ1' σ1 ->
  head_step t1 g1 σ1 t2 g2 σ2 ->
  ∃ σ2' : store, head_step t1 g1 σ1' t2 g2 σ2' ∧ gc (locs t2 ∪ r) σ2' σ2.
Proof.
  intros Hgc. inversion 1; subst.
  { eexists; split; first eauto using head_step. eapply gc_weak; first done.
    destruct x; first set_solver. apply union_mono_r. etrans. apply locs_subst. set_solver. }
  { eexists. split. apply HeadCall; try done.
    eapply gc_weak; try done.
    pose proof (locs_substs' (zip (self :: args) (val_code self args body :: vs)) body) as Hlocs.
    rewrite zip_cons fmap_cons snd_zip in Hlocs; last lia.
    auto_locs. set_solver. }
  { eexists; split; first eauto using head_step. eapply gc_weak; first done.
    assert (locs v = ∅).
    { destruct p,v1,v2; inversion H0; set_solver. }
    set_solver. }
  { eexists; split; first eauto using head_step. eapply gc_weak; first done.
    destruct b; set_solver. }
  { eexists. split.
    { eapply HeadAlloc; try done.
      apply not_elem_of_dom. erewrite gc_dom; last done. eauto using not_elem_of_dom. }
    { auto_locs. apply gc_alloc. eauto using not_elem_of_dom.
      eapply gc_weak; try done. set_solver. } }
  { eexists; split.
    { eapply HeadLoad; try done. eapply gc_read_root; try done. set_solver. }
    { eapply gc_load; try done. eapply gc_weak; try done. set_solver. } }
  { eexists; split.
    { eapply HeadStore; try done. eapply gc_read_root; try done. set_solver. }
    { replace (locs_tm val_unit ∪ r) with r by set_solver.
      eapply gc_store; try done. eapply gc_weak; first done. set_solver.  } }
  { eexists. split.
    { eapply HeadCAS; try done. eapply gc_read_root; try done. set_solver. }
    case_decide.
    { subst. rewrite bool_decide_true //.
      replace (locs_tm true ∪ r) with r by set_solver.
      eapply gc_store; try done. eapply gc_weak; first done. set_solver. }
    { rewrite bool_decide_false //. eapply gc_weak. done. set_solver. } }
  all:eexists; split; first eauto using head_step.
  all:eapply gc_weak; first done; set_solver.
Qed.

Lemma atomic_step_gc_insensitive1 r σ1' e1 g1 σ1 e2 g2 σ2 efs :
  atomic_step e1 g1 σ1 e2 g2 σ2 efs ->
  gc (locs e1 ∪ r) σ1' σ1 ->
  ∃ σ2', atomic_step e1 g1 σ1' e2 g2 σ2' efs /\ gc (locs e2 ∪ r ∪ locs efs) σ2' σ2.
Proof.
  intros Hstep. revert r. induction Hstep; intros r Hgc; subst.
  { rewrite locs_fill_item in Hgc.
    replace (locs E ∪ locs t1 ∪ r) with (locs t1 ∪ (locs E ∪ r)) in Hgc by set_solver.
    apply IHHstep in Hgc. destruct Hgc as (?&?&?).
    eexists. split. eapply StepCtx; eauto. rewrite locs_fill_item.
    replace (locs E ∪ locs t2 ∪ r) with (locs t2 ∪ (locs E ∪ r)) by set_solver. done. }

  assert (∃ σ2', head_step_conc t1 g1 σ1' t2 g2 σ2' efs ∧ gc (locs t2 ∪ r ∪ locs efs) σ2' σ2) as (?&?&?);
    last eauto using StepHead.
  inversion H; subst; last first.
  { eexists. split; first eauto using HeadFork. eapply gc_weak. done. set_solver. }

  eapply head_step_gc_insensitive in H0; last done.
  destruct H0 as (?&?&?). replace (locs None) with (∅ :gset loc) by set_solver.
  rewrite right_id_L.
  eauto using HeadSeq, head_step_gc_insensitive.
Qed.

Lemma elem_of_middle {A:Type} (ls:list A) n x :
  ls !! n = Some x ->
  exists l1 l2, ls = l1 ++ x::l2 /\ length l1 = n.
Proof.
  intros E.
  assert (n < length ls).
  { by eapply lookup_lt_is_Some_1. }
  apply take_drop_middle in E.
  eexists _,_. split. done. rewrite take_length. lia.
Qed.

Lemma main_to_oblivious_pre ms ρ1 σ1 σ1' ρ2 σ2 :
  rtc (step_default ms) (ρ1,σ1) (ρ2,σ2) ->
  gc (locs ρ1.*1) σ1' σ1 ->
  ∃ σ2', rtc step_oblivious (ρ1,σ1') (ρ2,σ2') /\ gc (locs ρ2.*1) σ2' σ2.
Proof.
  intros Hstep. revert σ1'.
  dependent induction Hstep; intros ? Hgc.
  { eauto using rtc_refl. }
  destruct y.
  destruct H as (c&Henabled&Hc).
  destruct c; last first.
  { inversion Hc. subst. eapply IHHstep. done. done. eauto using gc_trans. }
  { destruct Henabled as (t'&g'&Htg&E1&E2). inversion Hc. subst.
    apply elem_of_middle in H4. destruct H4 as (l1&l2&->&Hlength).
    assert (locs (l1 ++ (t, g0) :: l2).*1 = locs t ∪ (locs l1.*1 ∪ locs l2.*1)) as X.
    { auto_locs. rewrite !fmap_app !fmap_cons union_list_app_L union_list_cons.
      set_solver. }
    rewrite X in Hgc.
    eapply atomic_step_gc_insensitive1 in H5; last done.
    destruct H5 as (?&?&?).
    edestruct IHHstep as (σ2'&?&?); try done.
    { eapply gc_weak; first done.
      replace n with (n+0) by lia. rewrite -Hlength.
      rewrite insert_app_r. simpl. auto_locs.
      rewrite !fmap_app !fmap_cons !union_list_app_L !union_list_cons.
      destruct efs; simpl; set_solver. }
    { eexists. split; last done. eapply rtc_l; try done.
      eapply semantics.StepAtomic; try done.
      replace n with (n+0) by lia. rewrite -Hlength.
      rewrite insert_app_r -assoc_L. f_equal. } }
Qed.

Lemma main_to_oblivious ms ρ1 σ1 ρ2 σ2 :
  rtc (step_default ms) (ρ1,σ1) (ρ2,σ2) ->
  ∃ σ2', rtc step_oblivious (ρ1,σ1) (ρ2,σ2') /\ gc (locs ρ2.*1) σ2' σ2.
Proof. eauto using main_to_oblivious_pre,gc_id. Qed.

(* ------------------------------------------------------------------------ *)

Lemma step_oblivious_alt c1 c2 :
  step_oblivious c1 c2 <-> (exists π, step_action (Thread π) c1 c2).
Proof.
  split.
  { inversion 1. subst.
    exists (length ts1). econstructor; try done.
    { rewrite lookup_app_r // Nat.sub_diag //. }
    { rewrite insert_app_r_alt // Nat.sub_diag. simpl.
      rewrite -app_assoc. f_equal. } }
  { intros (π&Hπ). inversion Hπ. subst.
    apply elem_of_middle in H0. destruct H0 as (l1&l2&->&?). subst.
    econstructor; eauto.
    rewrite insert_app_r_alt // Nat.sub_diag. simpl.
    rewrite -app_assoc. f_equal. }
Qed.

End WithSize.
