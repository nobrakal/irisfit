From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap gset.

From irisfit.language Require Import language.
From irisfit.program_logic Require Export wp_clean wp_closure wp_spec.
From irisfit.program_logic Require Export wpc wpc_more more_space_lang triple.

From irisfit.examples Require Export utils instantiation.
From irisfit.lib Require Export qz smultiset.

From irisfit Require Import diaframe.
From diaframe Require Export proofmode_base.

Ltac wpc_call :=
  iApply @wpc_call_tac; first reflexivity; only 1,2:compute_done;
  [ auto_locs_goal; set_solver | iModIntro; iIntros "_"; simpl ].

Lemma wpc_call_spec_tac `{interpGS0 Σ} (k:gmap loc Qp) (A:Type) (EA:Enc A) E i r n (env:list (val*Qz)) l ts P (Ψ:A -> iProp Σ) :
  length ts = n ->
  forallb is_val ts →
  locs env.*1 ∖ set_of_option r ⊆ dom k ->
  Spec n env P l -∗
  PBT {[i]} k -∗
  ▷ (∀ t, £1 -∗ PBT {[i]} k -∗ P l (to_val_force <$> ts) t -∗ wpc E i r t Ψ) -∗
  wpc E i r (call_clo l ts) Ψ.
Proof.
  iIntros.
  rewrite -(fmap_to_val_force ts) //.
  iApply (wpc_call_spec with "[$][$]"); eauto.
  rewrite fmap_length //.
  rewrite fmap_to_val_force //.
Qed.

Lemma wpc_call_spec_souv_tac `{interpGS0 Σ} (A:Type) (EA:Enc A) E i r n (env:list (val*Qz)) l ts P (Ψ:A -> iProp Σ) :
  length ts = n ->
  forallb is_val ts →
  locs env.*1 ⊆ r ->
  Spec n env P l -∗
  ▷ (∀ t, £1 -∗ P l (to_val_force <$> ts) t -∗ wpc E i (Some r) t Ψ) -∗
  wpc E i (Some r) (call_clo l ts) Ψ.
Proof.
  iIntros.
  rewrite -(fmap_to_val_force ts) //.
  iApply (wpc_call_spec_souv with "[$]"); eauto.
  rewrite fmap_length //.
  rewrite fmap_to_val_force //.
Qed.

Class Convertible (A B:Type) `{Enc A} `{Enc B} := {conv:A -> B; conv_enc : forall x, enc (conv x) = enc x }.

Global Instance Conv_refl (A:Type) (EA:Enc A) : Convertible A A := {conv:=id; conv_enc:=fun _ => eq_refl}.
Global Instance Conv_unit_val : Convertible unit val := {conv:=fun _ => val_unit; conv_enc:=fun _ => eq_refl}.
Global Instance Conv_unit_val' : Convertible () val := {conv:=fun _ => val_unit; conv_enc:=fun _ => eq_refl}.
Global Instance Conv_nat_val : Convertible Z val := {conv:=val_int; conv_enc:=fun _ => eq_refl}.
Global Instance Conv_loc_val : Convertible loc val := {conv:=val_loc; conv_enc:=fun _ => eq_refl}.
Global Instance Conv_bool_val : Convertible bool val := {conv:=val_bool; conv_enc:=fun _ => eq_refl}.
Lemma post_convertible `{interpGS0 Σ} `{Convertible B A} (Q:A -> iProp Σ) v :
  post (fun b:B => Q (conv b)) v -∗
  post Q v.
Proof.
  iIntros "[% (% & ?)]". subst.
  iExists (conv a).
  rewrite !conv_enc //. iFrame. eauto.
Qed.


Lemma wpc_convertible `{interpGS0 Σ} (B:Type) `{Convertible B A} E i r t (Q:A -> iProp Σ) :
  wpc E i r t (fun (b:B) => Q (conv b)) -∗
  wpc E i r t Q.
Proof.
  iIntros "Hwp".
  rewrite !wpc_eq.
  iIntros. iSpecialize ("Hwp" with "[$]").
  destruct r.
  { iIntros. iSpecialize ("Hwp" with "[%//][$]").
    iApply (wp_mono with "[$]"). iIntros (?) "(?&?&?)". iFrame.
    iApply (@post_convertible with "[$]"). }
  { iApply (wp_mono with "[$]"). iIntros (?) "(?&?)". iFrame.
    iApply (@post_convertible with "[$]"). }
Qed.

Definition opt_incl (r r':option (gset loc)) :=
  match r,r' with Some r,Some r' => r' ⊆ r | _,None => True | _,_ => False end.

Lemma wpc_apply `{interpGS0 Σ} (A B:Type) (Q:A -> iProp Σ) (Q':B -> iProp Σ) `(Convertible B A) E i r r' t P :
  opt_incl r r' ->
  (P -∗ wpc E i r' t Q') -∗
  P ∗ (∀ v, Q' v -∗ Q (conv v))%I -∗
  wpc E i r t Q.
Proof.
  iIntros (?) "Hwp (? & Hc)".
  iSpecialize ("Hwp" with "[$]").
  destruct r,r'; try done.
  { iApply @wpc_weak; eauto.
    iApply (@wpc_convertible _ _ B).
    iApply (@wpc_mono with "[$]").
    iFrame. }
  { iApply wpc_noclean.
    iApply (@wpc_convertible _ _ B).
    iApply (@wpc_mono with "[$]").
    iFrame. }
  { iApply (@wpc_convertible _ _ B).
    iApply (@wpc_mono with "[$]").
    iFrame. }
Qed.

Lemma opt_incl_refl r :
  opt_incl r r.
Proof. destruct r; set_solver. Qed.

Ltac solve_side_apply tt :=
  match goal with
  | |- Convertible _ _ => apply _
  | |- opt_incl _ _ => try apply opt_incl_refl
  | _ => idtac end.

Ltac wpc_apply_tac H :=
  unshelve (iApply wpc_apply);
  only 8:iApply H;
  solve_side_apply tt;
  last iFrame.

Tactic Notation "wpc_apply" uconstr(H) := wpc_apply_tac H.

Lemma wpc_call_prim_tac `{!interpGS0 Σ} (A:Type) (EA:Enc A) E i X p v1 v2  (w:A) (Q:A -> iProp Σ) :
  eval_call_prim p v1 v2 = Some (enc w) ->
  Q w -∗
  wpc E i X (tm_call_prim p v1 v2) Q.
Proof.
  iIntros (Hw) "?".
  iApply wpc_mono.
  iApply wpc_call_prim. eauto.
  iSteps.
Qed.

Ltac wpc_call_prim :=
  iApply wpc_call_prim_tac; [ reflexivity |].

Ltac wpc_conv H :=
  unshelve (iApply wpc_convertible);
  only 4: iApply H;
  only 1: apply _.

(******************************************************************************)
Ltac solve_atomic := first [left; constructor | right; easy].

(******************************************************************************)
(* mine some diamonds. *)

From iris.proofmode Require Import coq_tactics proofmode reduction spec_patterns intro_patterns.

Ltac fetch_diamonds Δ k :=
  lazymatch Δ with
  | context[Esnoc _ ?Hdiams (♢ ?c)%I] => k Hdiams c
  | _ =>
      fail "mine: could not find any space credits in hypothesis" end.

Ltac mine_aux n Hdst Hdiams c :=
  let xs := intro_pat.parse Hdst in
  replace (c:Qz) with ((c-n)%Qz + n%Qz)%Qz;
  [ iDestruct (diamonds_split with "[$]") as [IList [ IIdent Hdiams::xs ] ]; rew_qz; simpl |
    rew_qz; simpl; try easy; try lia ].

Ltac mine n Hdst :=
  lazymatch goal with
  | |- envs_entails ?Δ _ =>
      let mine' := mine_aux n Hdst in
      fetch_diamonds Δ mine' end.

Tactic Notation "mine" constr(n) "as" constr(ipat) :=
  mine n ipat.
Tactic Notation "mine" constr(n) :=
  mine n as "?".

(******************************************************************************)
(* wp_alloc. *)
Ltac wpc_alloc :=
  lazymatch goal with
  | |- envs_entails _ (wpc _ _ _ (tm_alloc (tm_val (val_int ?n))) _) =>
      mine (Z.to_nat n);
      wpc_apply wpc_alloc; [try lia| iFrame]
      end.

(******************************************************************************)


Lemma locs_subst_precise x v t:
  locs_tm (subst x v t) = locs t ∪ (if (decide (x ∈ free_variables t)) then locs v else ∅).
Proof. apply locs_subst_precise. Qed.

Ltac compute_decide_in_fv :=
  match goal with
  | |- context E [decide (?x ∈ free_variables ?t)] =>
      let i := fresh "efv" in
      set (i:=(decide (x ∈ free_variables t)));
      vm_compute in i; subst i
  end.

Ltac simpl_locs_clo :=
  repeat (compute_decide_in_fv); simpl.


(******************************************************************************)
(* not_dead

   Here, we want to rule out impossible cases, were the impossibility can come
   from multiple part. *)

(* First, a lemma for the "simple" case, without a wpc goal. *)
Lemma confront_pure_dag `{interpGS0 Σ} l :
  †l -∗
  (∃ x1 x2, pbt l x1 x2) -∗
  False.
Proof.
  iIntros "? [% [% ?]]".
  iApply (confront_pbt_dag with "[$]").
Qed.

(* A tactic to apply this lemma automatically *)
Ltac not_dead_pure l :=
  iExFalso;
  iApply (confront_pure_dag l with "[$]");
  iExists _,_; by iFrame.

(* A lemma for the "complex" case, which needs access to interp. *)
Lemma confront_dag_wpc l `{interpGS0 Σ} (A:Type) (EA:Enc A) E i r t (Q:A -> iProp Σ) :
  (l ∈ set_of_option r ∪ locs t) ->
  †l -∗
  wpc E i r t Q .
Proof.
  iIntros (Hl) "Hl".
  apply elem_of_union in Hl.
  destruct Hl.
  { destruct r; last set_solver. by iApply wpc_exfalso_dag_souvenir. }
  { iApply wpc_exfalso. by iApply no_dangling_pointer. iIntros. iFrame. }
Qed.

Ltac not_dead_impure l :=
  lazymatch goal with
  | |- envs_entails _ (wpc _ _ _ _ _) =>
      iApply (confront_dag_wpc l with "[$]"); set_solver end.

Ltac not_dead l :=
  first [not_dead_pure l | not_dead_impure l].

(******************************************************************************)
(* pclean: clean pbt *)

Lemma pclean `{interpGS0 Σ} v p S (A:Type)(EA:Enc A) E i r t (Q:A -> iProp Σ) :
  locs v ∩ (locs t ∖ r) = ∅ ->
  v ⟸?{p} S -∗
  (v ⟸?{p} (S ∖ {[i]}) -∗ wpc E i (Some r) t Q) -∗
  wpc E i (Some r) t Q.
Proof.
  iIntros.
  iApply wpc_conseq.
  { iApply (supd_vclean v). easy. }
  iFrame.
Qed.

Ltac pclean_with_core v H1 H2 tac :=
  iApply (pclean v with H1); [ tac tt | iIntros H2; rewrite ?difference_diag_L].
Ltac pclean_with v H tac := pclean_with_core v H H tac.
Ltac pclean_core v tac :=  pclean_with_core v "[$]" "?" tac.

Ltac set_solver_tt tt := set_solver.

Tactic Notation "pclean" constr(l) "with" constr(H) "by" tactic(tac) :=
  pclean_with l H tac.
Tactic Notation "pclean" constr(l) "with" constr(H) :=
  pclean l with H by set_solver_tt.

Tactic Notation "pclean" constr(l) "by" tactic(tac) :=
  pclean_core l tac.
Tactic Notation "pclean" constr(l) :=
  pclean l by set_solver_tt.

(******************************************************************************)
(* papprox: approx the pbt *)

Ltac papprox_with_core v H1 H2 :=
  match goal with
  | |- envs_entails _ (wpc _ ?π _ _ _) =>
      iDestruct (vpbt_approx {[π]} v with H1) as H2; rewrite ?left_id_L end.
Ltac papprox_with v H  := papprox_with_core v H H.
Ltac papprox_core v :=  papprox_with_core v "[$]" "?".

Tactic Notation "papprox" constr(v) "with" constr(H) :=
  papprox_with v H.
Tactic Notation "papprox" constr(v):=
  papprox_core v.

(******************************************************************************)
(* wpc_let_* *)

Ltac wpc_let_noclean :=
  iApply @wpc_let_noclean.

Ltac wpc_let_empty :=
  iApply wpc_let_empty;
  [ auto_locs_goal; reflexivity | |];
  [ set_solver | ].

(******************************************************************************)
(* "easy" proofmode *)

Lemma wpc_if_nolater `{interpGS0 Σ} (A:Type) (EA:Enc A) E (c:bool) i r t1 t2 (Q:A -> iProp Σ) :
  (if c then wpc E i r t1 Q else wpc E i r t2 Q)
  ⊢ wpc E i r (tm_if c t1 t2) Q.
Proof. iIntros. iApply @wpc_if. iSmash. Qed.

Ltac wpc_if := iApply @wpc_if_nolater.

Lemma wpc_val_tac `{interpGS0 Σ} (A:Type) (EA:Enc A) E i r (v:val) (v':A) (Q:A -> iProp Σ) :
  v = enc v' ->
  Q v' -∗
  wpc E i r (tm_val v) Q.
Proof. intros ->. iApply wpc_val. Qed.

Ltac wpc_val := unshelve iApply @wpc_val_tac; only 2:reflexivity.

(******************************************************************************)
(* wpc_load *)

Lemma wpc_load_no_loc_tac (A:Type) (EA:Enc A) `{interpGS0 Σ} E i X (l:loc) (n:Z) q vs (a:A) (Q:A -> iProp Σ) :
  (0 ≤ n < Z.to_nat (length vs))%Z ->
  (vs !!! Z.to_nat n) = enc a ->
  ¬ is_loc (enc a) ->
  l ↦{q}  vs ∗ (l ↦{q} vs -∗ Q a) ⊢
  wpc E i X (tm_load l n) Q.
Proof.
  iIntros (???) "(?&HP)".
  iApply (wpc_mono with "[-HP]").
  { iApply wpc_load_no_loc; eauto. }
  iSmash.
Qed.

Ltac wpc_load_no_loc_tac tac :=
  iApply @wpc_load_no_loc_tac; last tac tt;
  [ simpl; try first [lia; compute_done] | try reflexivity | try easy | ].

Tactic Notation "wpc_load_no_loc" constr(H) :=
  wpc_load_no_loc_tac ltac:(fun _ => iFrame H).

Tactic Notation "wpc_load_no_loc" :=
  wpc_load_no_loc_tac ltac:(fun _ => iFrame).

Lemma wpc_load_tac (A:Type) (EA:Enc A) `{interpGS0 Σ} E i X (l:loc) (n:Z) q p S vs (a:A) (Q:A -> iProp Σ) :
  (0 ≤ n < Z.to_nat (length vs))%Z ->
  (vs !!! Z.to_nat n) = enc a ->
  l ↦{q} vs ∗ (vs !!! Z.to_nat n) ⟸?{p} S ∗ (l ↦{q} vs ∗ (vs!!! Z.to_nat n)  ⟸?{p} (S ∪ {[i]}) -∗ Q a) ⊢
  wpc E i X (tm_load l n) Q.
Proof.
  iIntros (??) "(?&?&HP)".
  iApply (wpc_mono with "[-HP]").
  { iApply wpc_load; eauto. iFrame. }
  iSmash.
Qed.

Ltac wpc_load_tac tac1 tac2 :=
  iApply @wpc_load_tac; last tac1 tt; last tac2 tt;
  [ simpl; first [lia; compute_done] | try reflexivity
  | rewrite ?left_id_L ?right_id_L ?bi.True_sep ?bi.sep_True ].

Tactic Notation "wpc_load" constr(H1) constr(H2) :=
  wpc_load_tac ltac:(fun _ => iFrame H1) ltac:(fun _ => iFrame H2).

Tactic Notation "wpc_load" :=
  wpc_load_tac ltac:(fun _ => iFrame) ltac:(fun _ => simpl;iFrame).

Ltac wpc_store :=
  wpc_apply wpc_store; only 1,2:(eauto;try compute_done); last iIntros ([]).

Lemma wpc_bind_if_noclean `{interpGS0 Σ} (A:Type) (EA:Enc A) E i r (t1 t2 t3:tm) (Q : A -> iProp Σ) :
  wpc E i None t1 (fun c:bool => if c then wpc E i r t2 Q else wpc E i r t3 Q) -∗
  wpc E i r (tm_if t1 t2  t3) Q.
Proof.
  iIntros.
  iApply (wpc_bind_noclean (ctx_if t2 t3)).
  iApply (@wpc_convertible _ _ bool).
  iApply (wpc_mono with "[$]").
  iIntros. Unshelve. 2:apply _. simpl. wpc_if.
  iFrame.
Qed.

(******************************************************************************)

Lemma wp_apply `{interpGS0 Σ} (Q Q':val -> iProp Σ) E i b t P :
  (P -∗ wp E i b t Q') -∗
  P ∗ (∀ v, Q' v -∗ Q v)%I -∗
  wp E i b  t Q.
Proof.
  iIntros "Hwp (?&?)".
  iSpecialize ("Hwp" with "[$]").
  iApply (wp_mono with "[$]").
  iFrame.
Qed.

Ltac wp_apply H :=
  iApply wp_apply; only 1:iApply H; last iFrame "#∗".
