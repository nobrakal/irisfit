From irisfit.language Require Import notation.
From irisfit.program_logic Require Import interp triple more_space_lang.
From irisfit.program_logic Require Import wpc.
From irisfit.lib Require Import qz smultiset.
From irisfit.program_logic Require Import utils.
From irisfit.examples Require Import instantiation.

From diaframe Require Import pure_solver.
From diaframe Require Export proofmode_base.

Global Opaque mapsto.mapsto.
Global Opaque mapsfrom.
Global Opaque smultiset_equiv.
Global Opaque smultiset_disj_union.
Global Opaque interp.
Global Opaque pbt PBT.

(* ------------------------------------------------------------------------ *)
(* We extend the pure solver to call set_solver on goals requiring to prove
   the equality of sets. *)

(******************************************************************************)
(* Rewriting sets *)

(* Using rewrite to solve typeclasses instances. Maybe defining a set of lemmas
   already proving the right instances is more efficient *)
Ltac rew_map_set_step tt :=
  first [ rewrite left_id_L | rewrite right_id_L
        | rewrite difference_empty_L].

Ltac rew_set_core tt :=
  repeat (rew_map_set_step tt).

Tactic Notation "rew_set" := rew_set_core tt.

(* this auto_locs focus only on the goal. *)
Ltac auto_locs_goal :=
  unfold locs, location_list, location_ctx, location_tm, location_val, locs_list;
  simpl;
  rewrite ?locs_fill_item ?locs_fmap_vals;
  repeat auto_locs_val;
  rew_set_core tt.

Ltac simpl_locs :=
  autorewrite with rewrite_llocs_tm;
  auto_locs_goal.

Ltac solve_locs :=
  match goal with
  | |- @eq (gset _) _ _ => simpl_locs; set_solver
  | |- @subseteq (gset _) _ _ => simpl_locs; set_solver end.

Global Hint Extern 4 (SolveSepSideCondition ?φ) => unfold SolveSepSideCondition; trySolvePure; solve_locs : typeclass_instances.

Section Diaframe.

Context `{hi:!interpGS0 Σ}.

(* ------------------------------------------------------------------------ *)
(* Wpc -> Wp *)

Definition is_val t : bool :=
  match t with
  | tm_val _ => true
  | _ => false end.

Definition to_val_force t : val :=
  match t with
  | tm_val v => v
  | _ => val_unit end.

Lemma fmap_to_val_force ts :
  forallb is_val ts →
  tm_val <$> (to_val_force <$> ts) = ts.
Proof.
  intros.
  induction ts as [|t ts]; try easy.
  do 2 rewrite fmap_cons.
  destruct t; simpl in *; try easy.
  f_equal. eauto.
Qed.

Lemma wpc_call_tac `{!Enc A} E i X t self args body ts (Q:A -> iProp Σ) :
  t = (val_code self args body) ->
  forallb is_val ts →
  length args = length ts →
  locs body = ∅ →
   ▷ (£1 -∗ wpc E i X (substs' (zip (self :: args) (t :: (to_val_force <$> ts))) body) Q) -∗
  wpc E i X (tm_call t ts) Q.
Proof.
  iIntros. subst.
  iApply (wpc_call with "[$]"); eauto.
  { rewrite fmap_length //. }
  { rewrite fmap_to_val_force //. }
Qed.

Global Instance wp_call_instance `{!Enc A} E i X self args body ts (Φ:A -> iProp Σ) :
  SolveSepSideCondition (locs body = ∅) ->
  SolveSepSideCondition (forallb is_val ts = true) ->
  SolveSepSideCondition (length args = length ts) ->
  HINT1 empty_hyp_first ✱ [wpc E i X (substs' (zip (self :: args) ((val_code self args body) :: (to_val_force <$> ts))) body) Φ] ⊫ [id]; wpc E i X (tm_call (val_code self args body) ts) Φ.
Proof.
  intros.
  iSteps.
  iApply wpc_call_tac; eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Post *)

Global Instance val_instance (A:Type) (EA:Enc A) E i X (v:val) (Φ:A -> iProp Σ):
  HINT1 empty_hyp_first ✱ [post Φ v] ⊫ [id]; wpc E i X v Φ.
Proof.
  iSteps.
  iApply wpc_val.
  iFrame.
Qed.

Global Instance post_val_instance (v:val) (Φ:val -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ v] ⊫ [id]; post Φ v.
Proof. rewrite post_val. iSteps. Qed.
Global Instance post_nat_instance (v:Z) (Φ:Z -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ v] ⊫ [id]; post Φ v.
Proof. rewrite post_nat. iSteps. Qed.
Global Instance post_loc_instance (v:loc) (Φ:loc -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ v] ⊫ [id]; post Φ v.
Proof. rewrite post_loc. iSteps. Qed.
Global Instance post_unit_instance (Φ:unit -> iProp Σ):
  HINT1 empty_hyp_first ✱ [Φ tt] ⊫ [id]; post Φ val_unit.
Proof. rewrite post_unit. iSteps. Qed.

Definition go_int t :=
  match t with
  | tm_val (val_int _) => true
  | _ => false end.

Ltac derive_val_instance :=
  intros;
  iSteps;
  iApply (wpc_mono_val with "[$]");
  eauto.

Global Instance go_nat_instance_val E i X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_int t) ->
  HINT1 empty_hyp_first ✱ [wpc E i X t (fun (n:Z) => Φ (enc n))] ⊫ [id]; wpc E i X t Φ.
Proof. derive_val_instance. Qed.

Definition go_loc t :=
  match t with
  | tm_alloc _ | tm_val (val_loc _) => true
  | _ => false end.
Global Instance go_loc_instance_val E i X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_loc t) ->
  HINT1 empty_hyp_first ✱ [wpc E i X t (fun (l:loc) => Φ (enc l))] ⊫ [id]; wpc E i X t Φ.
Proof. derive_val_instance. Qed.


Definition go_unit t :=
  match t with
  | tm_store _ _ _ | tm_val val_unit => true
  | _ => false end.
Global Instance go_unit_instance_val E i X t (Φ:val -> iProp Σ):
  SolveSepSideCondition (go_unit t) ->
  HINT1 empty_hyp_first ✱ [wpc E i X t (fun (_:unit) => Φ (enc tt))] ⊫ [id]; wpc E i X t Φ.
Proof. derive_val_instance. Qed.

(* ------------------------------------------------------------------------ *)
(* Rules *)

Global Instance store_instance1 E i X (l:loc) (n:Z) (v:val) (Φ:unit -> iProp Σ):
  SolveSepSideCondition (is_loc v = false) ->
  HINT1 empty_hyp_first ✱
    [∃vs, l ↦ vs ∗ ⌜0 <= n < Z.to_nat (length vs)⌝%Z ∗
         (∀ ret, (l ↦ (<[Z.to_nat n:=v]> vs)
            ∗ (vs !!! Z.to_nat n)↤?{0}({[-l-]})) -∗ Φ ret) ] ⊫ [id]; wpc E i X (tm_store l n v) Φ | 50.
Proof.
  intros.
  iSteps as (???) "H1 H2".
  iApply (wpc_mono with "[H1]").
  { iApply (@wpc_store _ _ _ _ _ _ _ _ _ 1%Qp ∅); last iFrame.
    { destruct v; naive_solver. }
    { lia. }
    { rewrite vmapsfrom_no_loc //. by apply Is_true_false_2. } }
  iSteps.
Qed.

Global Instance store_instance2 E i X (l:loc) (n:Z) (v:val) (Φ:unit -> iProp Σ):
  HINT1 empty_hyp_last ✱
    [∃vs qv lsv, l ↦ vs ∗ ⌜0 <= n < Z.to_nat (length vs)⌝%Z ∗ v ↤?{qv} lsv ∗ ⌜is_loc v -> qv ≠ 0%Qz⌝ ∗
         (∀ ret, (l ↦ (<[Z.to_nat n:=v]> vs)
            ∗ v↤?{qv}(lsv ⊎ {[+ l +]})
            ∗ (vs !!! Z.to_nat n)↤?{0}({[-l-]})) -∗ Φ ret) ] ⊫ [id]; wpc E i X (tm_store l n v) Φ | 80.
Proof.
  iSteps as (??????) "H1 H2 H3".
  iApply (wpc_mono with "[H1 H2]").
  iApply wpc_store; last iFrame; eauto.
  iSteps.
Qed.

Lemma wpc_alloc_split E i (n:Z) (m:Qz) X :
  (0 < n)%Z ->
  Qz_le (nat_to_Qz (Z.to_nat n)) m ->
  ♢ m -∗
  wpc E i X (tm_alloc n)
  (fun (l:loc) =>
     ♢ (m - Z.to_nat n) ∗
     l ↦ (replicate (Z.to_nat n) val_unit) ∗
     l ↤ ∅ ∗
     l ⟸ {[i]}).
Proof.
  iIntros (??) "?".
  setoid_rewrite <- (Qz_sub_add m (Z.to_nat n)) at 1; try easy.
  iDestruct (diamonds_split with "[$]") as "[H1 H2]".
  iApply (wpc_mono with "[H2]"). iApply (wpc_alloc with "[H2]"). lia.
  conclude_diamonds. iSmash.
Qed.

Global Instance alloc_instance E i X (n:Z) (Φ:loc -> iProp Σ):
  HINT1 empty_hyp_first ✱ [⌜0<n⌝%Z ∗ ∃m, ♢m ∗⌜Qz_le (nat_to_Qz (Z.to_nat n)) m⌝ ∗ (∀ l, (♢ (m - Z.to_nat n) ∗
           l ↦ (replicate (Z.to_nat n) val_unit) ∗
           l ↤ ∅ ∗
           l ⟸ {[i]}) -∗ Φ l) ] ⊫ [id]; wpc E i X (alloc n) Φ.
Proof.
  iSteps as (???) "H1 H2".
  iApply (wpc_mono with "[H1]").
  iApply wpc_alloc_split; last iFrame. easy. easy.
  iSteps.
Qed.

(*
Global Instance mergable_consume_mapsto_own  l (q1 q2:Qz) (ls1 ls2:smultiset loc) :
  MergableConsume (l ↤{q1} ls1)%I (λ p Pin Pout,
      TCAnd (TCEq Pin (l ↤{q2} ls2)) $
(*        TCAnd (proofmode_classes.IsOp (A := gfracR) q q1 q2) $
        TCAnd (proofmode_classes.IsOp (A := smultisetR) ls ls1 ls2) $ *)
        (TCEq Pout (l ↤{q1 + q2} (ls1 ⊎ ls2))))%I | 30.
Proof.
  rewrite /MergableConsume => p Pin Pout [-> ->]. (* [+ [Hls +] ] ]. *)
  rewrite bi.intuitionistically_if_elim.
  iStartProof.
  iIntros "(H1 & ?)".
  iApply (mapsfrom_join with "[H1]"); iFrame.
Qed.
*)
End Diaframe.
