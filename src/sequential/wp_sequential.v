From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gset gmap auth excl.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import disc qz qz_cmra smultiset.
From irisfit.language Require Import language.

From irisfit.program_logic Require Import more_space_lang more_cmras more_maps_and_sets.
From irisfit.program_logic Require Import interp more_interp pbt.

From irisfit.program_logic Require Import wp_alloc wp_load wp_store wp_call wp_call_prim wp_clean wp_free utils.

(* This file defines a new WP in terms of the base WP, in which in which we recover the
   reasoning rules of the POPL'23 paper.
   This is done in a [session], which parameterize all the definitions.

   This new WP may be useful, but the interface with the base WP is a bit painful.
 *)

(* The cmras we need for the sequential mode *)
Class seqG Σ := SeqG {
  iseq1 : inG Σ (authUR (gmapUR loc fracR));
  iseq2 : inG Σ (authUR (gsetUR loc));
}.

Local Existing Instance iseq1.
Local Existing Instance iseq2.

(* The ghost state associated to the session. *)
Record session := Session {
  γl : gname;
  γd : gname;
  tid : thread_id;
  mask : coPset;
}.

Local Instance session_inhabited : Inhabited session.
Proof. constructor. constructor; exact inhabitant. Qed.

From iris.bi Require Import monpred.

Canonical Structure session_bi_index :=
  {| bi_index_type := session; bi_index_rel := eq |}.

Definition vProp Σ := monPred session_bi_index (uPredI (iResUR Σ)).
Definition vPropO Σ := monPredO session_bi_index (uPredI (iResUR Σ)).
Definition vPropI Σ := monPredI session_bi_index (uPredI (iResUR Σ)).

Section Sequential.
Context `{!interpGS sz Σ, !seqG Σ}.

Definition spbt l p : vProp Σ :=
  MonPred (fun s => l ⟸{p} {[s.(tid)]})%I _.

Lemma pbt_concl l q1 q2 S1 S2 :
  q1=q2 -> S1=S2 -> pbt l q1 S1 -∗ pbt l q2 S2.
Proof. intros. subst. eauto. Qed.

Lemma spbt_split l p q :
  spbt l (p+q)%Qp ⊣⊢ spbt l p ∗ spbt l q.
Proof.
  constructor. intros []. rewrite /spbt monPred_at_sep. simpl.
  iSplit.
  { iIntros. iApply pbt_split.
    iApply (pbt_concl with "[$]"); set_solver. }
  { iIntros "(?&?)". iDestruct (pbt_join _ p with "[$]") as "?".
    iApply (pbt_concl with "[$]"); set_solver. }
Qed.

Lemma spbt_valid l p :
  spbt l p ⊢ ⌜✓p⌝.
Proof.
  constructor. intros []. rewrite monPred_at_pure.
  iIntros. iDestruct (pbt_valid with "[$]") as "%Hv".
  iPureIntro. done.
Qed.

(* For each location manipulated by the program,
   either it is pbt or dead. Or we are not anymore in the seq mode. *)
Definition seq_loc l p : vProp Σ :=
  (embed (†l) ∨ spbt l p)%I.

Definition seq_locs (τ:gmap loc Qp) : vProp Σ :=
  ([∗ map] l↦v ∈ τ, seq_loc l v)%I.

Definition map_auth (τ:gmap loc Qp) :=
  MonPred (fun s => own s.(γl) (●τ)) _.

Definition set_auth (x:gset loc) :=
  MonPred (fun s => own s.(γd) (●x)) _.

Definition nocrit :=
  MonPred (fun s => outside s.(tid)) _.

Definition seq_inv_inner (b:bool): vProp Σ :=
  (nocrit ∗ ∃ (τ:gmap loc Qp) (μ:gset loc), ⌜dom τ ## μ /\ (b -> μ = ∅)⌝ ∗ map_auth τ ∗ set_auth (dom τ ∪ μ) ∗ seq_locs τ)%I.

Definition seq_mode : vProp Σ := seq_inv_inner true.
Definition no_seq_mode : vProp Σ := seq_inv_inner false.

Definition registered l : vProp Σ :=
  MonPred (fun s => own s.(γd) (◯{[l]}))%I _.

Global Instance persistent_registered l : Persistent (registered l).
Proof.
  constructor. simpl. intros []. simpl. iIntros.
  rewrite monPred_at_persistently. iModIntro. done.
Qed.

Definition vregistered v : vProp Σ :=
  match v with
  | val_loc l => registered l
  | _ => True%I end.

Global Instance persistent_vregistered v : Persistent (vregistered v).
Proof. destruct v; apply _. Qed.

Inductive bracketed : Set :=
| Balanced : bracketed
| Unbalanced : bracketed
.

(* The new wp, where [seq_mode] plays the role of a kind of [state_interp].
   The wp is also parameterized by a bracketed argument, which allows to leave the
   session earlier (useful for CPS). *)
Definition wp_pre (o:bracketed) (b:bool) (t:tm) (Q:val -> vProp Σ) : vProp Σ :=
  MonPred (fun s => wp s.(mask) b s.(tid) t (fun v => Q v s))%I _.

Definition wp o b t Q : vProp Σ :=
  (seq_mode -∗ wp_pre o b t (fun v => (if o then seq_mode else True) ∗ Q v))%I.

Lemma wp_strong_mono o b t Q Q' :
  wp o b t Q -∗ (∀ v, Q v ==∗ Q' v) -∗ wp o b t Q'.
Proof.
  iIntros "Hwp HP". iIntros "Ha". iDestruct ("Hwp" with "Ha") as "?".
  iStopProof. constructor. intros [].
  rewrite monPred_at_sep monPred_at_forall /wp_pre. simpl.
  iIntros "(Hwp&HP)".
  iApply (wp_strong_mono with "[$]"). eauto. iIntros (?).
  iSpecialize ("Hwp" $! v). rewrite monPred_at_wand !monPred_at_sep. simpl.
  iIntros "(?&?)". iFrame.
  iSpecialize ("Hwp" with "[%//][$]").
  by rewrite monPred_at_bupd.
Qed.

Lemma wp_mono o b t Q Q' :
  wp o b t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wp o b t Q'.
Proof.
  iIntros "Hwp HP". iApply (wp_strong_mono with "[$]").
  iIntros. by iApply "HP".
Qed.

Lemma monPred_at_wp o b t Q s :
  wp o b t Q s ⊣⊢ (seq_mode s -∗ wp.wp s.(mask) b s.(tid) t (fun v => (if o then seq_mode s else True) ∗ Q v s)).
Proof.
  rewrite /wp monPred_at_wand. iSplit.
  { iIntros "Hwp ?". iSpecialize ("Hwp" with "[%//][$]").
    iApply (wp.wp_mono with "[$]"). iIntros. rewrite monPred_at_sep.
    destruct o; try done. rewrite monPred_at_pure //. }
  { iIntros "Hwp". iIntros (j Hj). inversion Hj. subst.
    iIntros. iSpecialize ("Hwp" with "[$]").
    iApply (wp.wp_mono with "[$]"). iIntros.
    rewrite monPred_at_sep. destruct o; try done. rewrite monPred_at_pure //. }
Qed.

Lemma bupd_wp o b t Q :
  (|==> wp o b t Q)%I ⊢ wp o b t Q.
Proof.
  constructor. intros. rewrite monPred_at_bupd monPred_at_wp.
  iIntros "Hwp ?". iApply bupd_wp. iApply "Hwp". iFrame.
Qed.

Lemma wp_postpone o b t Q :
  wp Balanced b t (fun v => wp o b v Q) ⊢ wp o b t Q.
Proof.
  constructor. intros. rewrite !monPred_at_wp. iIntros "Hwp ?".
  iApply wp_postpone. iSpecialize ("Hwp" with "[$]"). iApply (wp.wp_mono with "[$]").
  iIntros (?) "(?&Hwp)". rewrite monPred_at_wp.
  iApply "Hwp"; eauto.
Qed.

(* We need to redefine mapsfrom, and overwrite notations. *)
Definition mapsfrom l q S : vProp Σ :=
  (embed (l ↤{q} S) ∗ registered l)%I.
Definition vmapsfrom v q S : vProp Σ :=
  (embed (v ↤?{q} S) ∗ vregistered v)%I.

Global Instance proper_mapsfrom x q : Proper (equiv ==> equiv) (mapsfrom x q).
Proof. rewrite /mapsfrom. now iIntros (? ? ->). Qed.
Global Instance proper_vmapsfrom x q : Proper (equiv ==> equiv) (vmapsfrom x q).
Proof. rewrite /vmapsfrom. now iIntros (? ? ->). Qed.

Notation "l ↤{ q } ls" :=
  (mapsfrom l q%Qz ls)
  (at level 20, format "l  ↤{ q }  ls")
: bi_scope.

Notation "l ↤ ls" :=
  (mapsfrom l 1%Qz ls)
  (at level 20, format "l  ↤ ls")
: bi_scope.

Notation "v ↤?{ q } ls" :=
  (vmapsfrom v q%Qz ls)
  (at level 20, format "v  ↤?{ q }  ls")
: bi_scope.

Notation "v ↤? ls" :=
  (vmapsfrom v 1%Qz ls)
  (at level 20, format "v  ↤? ls")
: bi_scope.

(* We even need to redefine points-to, for load *)
Definition mapsto l p bs : vProp Σ :=
  (embed (l ↦{p} bs) ∗ ([∗ list] v ∈ bs, vregistered v))%I.

Local Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Local Notation "l ↦□ v" := (mapsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Local Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Definition seq l p : vProp Σ :=
  MonPred (fun s => own s.(γl) (◯{[l := p]})) _.

Lemma seq_split l p q :
  seq l (p+q)%Qp ⊣⊢ seq l p ∗ seq l q.
Proof.
  constructor. intros []. rewrite /seq monPred_at_sep. simpl.
  iSplit. iIntros "(?&?)". iFrame.
  iIntros "(?&?)". rewrite /seq -frac_op -singleton_op auth_frag_op own_op. iFrame.
Qed.

(* A bit of redundancy here:
   [registered l] can be derived from [seq_inv * seq  l p].
   But it requires access to the invariant. So we can store the assertion here. *)
Definition Stackable l p : vProp Σ :=
  (spbt l (p/2)%Qp ∗ registered l ∗ seq l (p/2)%Qp)%I.
Definition Stackables M : vProp Σ :=
  ([∗ map] l ↦ p ∈ M, Stackable l p)%I.

Lemma Stackable_split l p q :
  Stackable l (p+q) ⊣⊢ Stackable l p ∗ Stackable l q.
Proof.
  iSplit.
  { iIntros "(H1&#?&H2)".
    rewrite Qp.div_add_distr seq_split. iDestruct ("H2") as "(?&?)". iFrame "∗ #".
    by iApply spbt_split. }
  { iIntros "((?&#?&?)&(?&_&?))". iFrame "#".
    iDestruct (seq_split _ (p/2) with "[$]") as "?".
    iDestruct (spbt_split _ (p/2) with "[$]") as "?".
    rewrite -!Qp.div_add_distr. iFrame. }
Qed.

Lemma Stackables_split M1 M2 :
  Stackables (M1 ⋅ M2) ⊣⊢ Stackables M1 ∗ Stackables M2.
Proof.
  revert M2. pattern M1. apply map_ind.
  { intros. rewrite left_id_L /Stackables big_sepM_empty left_id. easy. }
  iIntros (l ? ? Hml IH M2).
  rewrite {2}/Stackables big_sepM_insert //.
  destruct (M2 !! l) as [q|] eqn:Hl.
  { rewrite -(insert_id M2 l q) // -(insert_delete_insert M2 l q).
    rewrite -insert_op /Stackables.
    rewrite !big_sepM_insert //.
    2:{ rewrite lookup_op Hml lookup_delete //. }
    2:{ rewrite lookup_delete //. }
    rewrite Stackable_split.
    unfold Stackables in *. rewrite (IH (delete l M2)).
    iSplit; iIntros "((?&?)&?&?)"; iFrame. }
  { rewrite -insert_op_l.
    2:now apply not_elem_of_dom.
    rewrite /Stackables big_sepM_insert.
    2:{ rewrite lookup_op Hml Hl //. }
    unfold Stackables in *. rewrite IH.
    iSplit; iIntros "(?&HL)"; by iFrame. }
Qed.

(* Being balanced is stronger. *)
Lemma wp_balance o b t Q :
  wp Balanced b t Q ⊢ wp o b t Q.
Proof.
  destruct o; eauto.
  iIntros "Hwp ?".
  iDestruct ("Hwp" with "[$]") as "?". iStopProof. constructor. intros [].
  simpl. iIntros. iApply (wp.wp_mono with "[$]"). iIntros (?).
  rewrite !monPred_at_sep monPred_at_pure. iIntros "(?&?)".
  by iFrame.
Qed.

(* We can abort at any time *)
Lemma abort_seq_mode :
  seq_mode ⊢ no_seq_mode.
Proof.
  iIntros "(?&[%[% ((%&%)&?&?&?)]])". iFrame. iExists _,_. by iFrame.
Qed.

Definition wit E0 tid0 : vProp Σ :=
  MonPred (fun s => ⌜s.(mask) = E0 /\ s.(tid) = tid0⌝)%I _.

Lemma wp_abort_seq b t (Q:val -> vProp Σ) :
  (∀ E tid s, embed (wit E tid s ∗ no_seq_mode s -∗ wp.wp E b tid t (fun v => Q v s))) -∗
  wp Unbalanced b t Q.
Proof.
  iIntros "Hwp". iIntros "Ha".
  iDestruct (abort_seq_mode with "Ha") as "?".
  iStopProof. constructor. intros s.
  rewrite monPred_at_sep. iIntros "(X&Y)".
  do 3 (rewrite monPred_at_forall; iSpecialize ("X" $! _)).
  rewrite monPred_at_embed. simpl.
  iApply (wp.wp_mono with "[-]").
  { iApply "X". by iFrame. }
  iIntros. rewrite monPred_at_sep monPred_at_pure. by iFrame.
Qed.

Lemma wp_val o b v Q :
  Q v ⊢ wp o b (tm_val v) Q.
Proof.
  rewrite -wp_balance. constructor. intros.
  iIntros. rewrite monPred_at_wp. iIntros.
  iApply wp_val. by iFrame.
Qed.

Lemma wp_if o b (c:bool) t1 t2 Q :
  (if c then wp o b t1 Q else wp o b t2 Q)
  ⊢ wp o b (tm_if c t1 t2) Q.
Proof.
  constructor. intros. iIntros "Hwp". rewrite monPred_at_wp. iIntros.
  iApply wp_if. iModIntro. iIntros. destruct c; rewrite monPred_at_wp.
  all:iApply ("Hwp" with "[$]").
Qed.

Lemma wp_nofree o b t Q :
  wp o false t Q ⊢ wp o b t Q.
Proof.
  constructor. intros. rewrite !monPred_at_wp. iIntros "Hwp ?".
  iApply wp_noclean. iApply ("Hwp" with "[$]").
Qed.

Lemma big_sepM_stackables M S k :
  ([∗ map] l↦p ∈ M, l ⟸{p / k} S )%I ==∗ PBT S ((fun x => x/k)%Qp <$> M) ∗ (PBT S ((fun x => x/k)%Qp <$> M) -∗ ([∗ map] l↦p ∈ M, l ⟸{p / k} S )%I).
Proof.
  iIntros "Hg".
  iInduction M as [|] "IH" using map_ind.
  { iFrame.
    iSplitL; last eauto.
    rewrite /PBT fmap_empty. by iApply big_sepM_empty. }
  { rewrite big_sepM_insert //.
    iDestruct "Hg" as "(?&?)".
    iMod ("IH" with "[$]") as "(?&Hb)". rewrite pbt_PBT.
    iDestruct (PBT_insert2 with "[$]") as "?".
    { rewrite dom_fmap. apply not_elem_of_dom. eauto. }
    rewrite fmap_insert. iFrame.
    iModIntro. iIntros. iDestruct (PBT_insert1 with "[$]") as "(?&?)".
    { rewrite dom_fmap. apply not_elem_of_dom. eauto. }
    iFrame. iApply "Hb". iFrame. }
Qed.

Lemma Stackables_PBT s M :
  Stackables M s ==∗ ∃ M', ⌜dom M = dom M'⌝∗ PBT {[s.(tid)]} M' ∗ (PBT {[s.(tid)]} M' -∗ Stackables M s).
Proof.
  iIntros "HS".
  iAssert (([∗ map] l↦p ∈ M, spbt l (p/2)%Qp s) ∗ [∗ map] l↦p ∈ M, registered l s ∗ seq l (p/2)%Qp s)%I with "[HS]" as "(HS&?)".
  { iApply big_sepM_sep. rewrite /Stackables /Stackable monPred_at_big_sepM.
    iApply (big_sepM_mono with "[$]"). intros. rewrite !monPred_at_sep //. }
  iExists ((fun x => x/2)%Qp <$> M).
  iMod (big_sepM_stackables with "[$]") as "(?&Hb)". iFrame.
  iModIntro.
  iSplitR.
  { iPureIntro. rewrite dom_fmap_L //. }
  iIntros. rewrite /Stackables /Stackable monPred_at_big_sepM.
  iSpecialize ("Hb" with "[$]"). iDestruct (big_sepM_sep with "[$]") as "?".
  iApply (big_sepM_mono with "[$]"). intros. rewrite !monPred_at_sep //.
Qed.

Lemma wp_bind o b K L t Q :
  locs K = dom L ->
  wp Balanced b t (fun v => Stackables L -∗ wp o b (fill_item K v) Q) ∗
  Stackables L ⊢
  wp o b (fill_item K t) Q.
Proof.
  intros. constructor. intros s. rewrite monPred_at_wp.
  rewrite monPred_at_sep.
  iIntros "(Hwp&?)". iIntros.
  rewrite monPred_at_wp. iIntros.
  iSpecialize ("Hwp" with "[$]").
  iApply wp.bupd_wp.
  iMod (Stackables_PBT with "[$]") as "[% (%&?&Hb)]".
  iApply (wp_bind with "[Hwp Hb] [$]"); eauto.
  { transitivity (dom L); eauto. }
  iApply (wp.wp_mono with "[$]").
  iIntros (?) "(?&Hwp) ?".
  iSpecialize ("Hb" with "[$]"). rewrite monPred_at_wand.
  iSpecialize ("Hwp" with "[%//][$]").
  iApply wp.bupd_wp. rewrite monPred_at_wp.
  iApply "Hwp"; by iFrame.
Qed.

Lemma wp_bind_nofree o b K t Q :
  wp Balanced false t (fun v => wp o b (fill_item K v) Q) ⊢
  wp o b (fill_item K t) Q.
Proof.
  constructor. intros. rewrite !monPred_at_wp.
  iIntros "Hwp Ha".
  iDestruct ("Hwp" with "[$]") as "?".
  iApply wp_bind_noclean.
  iApply (wp.wp_mono with "[$]").
  iIntros (?) "(?&Hwp)".
  iApply wp.bupd_wp. rewrite !monPred_at_wp.
  iApply ("Hwp" with "[$]").
Qed.

Lemma wp_let_val o b x (v:val) t Q :
  wp o b (subst' x v t) Q ⊢
  wp o b (tm_let x v t) Q.
Proof.
  constructor. intros. rewrite !monPred_at_wp.
  iIntros "Hwp Ha".
  iDestruct ("Hwp" with "[$]") as "?".
  iApply wp.wp_let_val.
  iFrame. iModIntro. eauto.
Qed.

Lemma wp_let_nofree o x t1 t2 b Q :
  wp Balanced false t1 (fun v => wp o b (subst' x v t2) Q) -∗
  wp o b (tm_let x t1 t2) Q.
Proof.
  intros. iIntros "H".
  iApply (wp_bind_nofree _ b (ctx_let x t2) with "[H]").
  iApply (wp_mono with "[$]").
  iIntros (?) "Hwp ". simpl.
  iApply wp_let_val. now iApply "Hwp".
Qed.

Lemma vregistered_alloc s n :
  ⊢ |==> [∗ list] v ∈ replicate n val_unit, vregistered v s.
Proof.
  iStartProof.
  iInduction n as [] "IH".
  { by iModIntro. }
  iMod "IH". simpl. rewrite monPred_at_pure left_id. by iFrame.
Qed.

Lemma seq_locs_insert1 l p τ :
  l ∉ dom τ ->
  spbt l p ∗ seq_locs τ -∗ seq_locs (<[l:=p%Qp]> τ).
Proof.
  iIntros (?) "(?&?)".
  iApply big_sepM_insert.
  { now apply not_elem_of_dom. }
  iFrame.
Qed.

Lemma confront_pbt_dag l p :
  spbt l p ∗ embed († l) ⊢ False.
Proof.
  constructor. intros []. rewrite monPred_at_sep monPred_at_embed monPred_at_pure.
  apply confront_pbt_dag.
Qed.

Lemma seq_locs_insert2 l p q τ :
  τ !! l = Some q ->
  spbt l p ∗ seq_locs τ -∗ ⌜✓(p⋅q)⌝ ∗ seq_locs (<[l:=(p+q)%Qp]> τ).
Proof.
  iIntros (?) "(?&Hτ)".
  rewrite /seq_locs.
  rewrite -(insert_id τ l q) //. rewrite insert_insert.
  rewrite !big_sepM_insert_delete.
  iDestruct "Hτ" as "(Hi&?)". iFrame.
  rewrite /seq_loc. iDestruct "Hi" as "[?|?]".
  { iExFalso. iApply confront_pbt_dag. iFrame. }
  { iDestruct (spbt_split with "[$]") as "?".
    rewrite comm_L.
    iDestruct (spbt_valid with "[$]") as "%Hv".
    by iFrame. }
Qed.

Lemma insert_witness l S :
  set_auth S ⊢ |==> set_auth ({[l]} ∪ S) ∗ registered l.
Proof.
  intros. constructor. intros [].
  rewrite monPred_at_bupd monPred_at_sep. simpl.
  rewrite -own_op. iIntros.
  iMod (own_update with "[$]") as "(?&?)".
  apply auth_update_alloc with (a' := ({[l]} ∪ S)). apply gset_local_update . set_solver.
  rewrite !own_op. iFrame. iApply (gset_conclude with "[$]"). set_solver.
Qed.

Lemma add_local_upd (τ : gmap loc Qp) l p q :
  τ !! l = Some q ->
  ✓(p ⋅ q) ->
  (τ, ε) ~l~> (<[l:=p ⋅ q]> τ, {[l := p]}).
Proof.
  intros Hl ?. apply local_update_discrete .
  intros z ? Hz.
  split.
  { apply insert_valid; eauto. }
  intros l'.
  rewrite !lookup_insert_case !lookup_opM !lookup_insert_case lookup_empty.
  specialize (Hz l').
  rewrite lookup_opM lookup_empty left_id in Hz.
  case_decide; subst.
  { rewrite -Hz Hl Some_op //. }
  { rewrite left_id //. }
Qed.

Lemma add_tau2 l (p:Qp) q τ :
  τ !! l = Some q ->
  ✓(p⋅q) ->
  map_auth τ ⊢ |==>
  map_auth (<[l:=(p+q)%Qp]> τ) ∗ seq l p.
Proof.
  intros. constructor. intros [].
  rewrite monPred_at_bupd monPred_at_sep. simpl.
  iIntros.
  rewrite /seq -own_op.
  iApply (own_update with "[$]").
  apply auth_update_alloc.
  rewrite -frac_op.
  apply add_local_upd; eauto.
Qed.

Lemma add_tau1 l (p:Qp) τ :
  l ∉ dom τ ->
  ✓p ->
  map_auth τ ⊢ |==>
  map_auth (<[l:=(p/2)%Qp]> τ) ∗ seq l (p/2)%Qp.
Proof.
  intros. constructor. intros [].
  rewrite monPred_at_bupd monPred_at_sep. simpl.
  iIntros.
  rewrite /seq -own_op.
  iApply (own_update with "[$]").
  apply auth_update_alloc.
  apply alloc_singleton_local_update.
  now apply not_elem_of_dom.
  apply Some_valid. rewrite frac_valid.
  trans (1/2)%Qp. 2:by vm_compute. apply Qp.div_le_mono_r.
  easy.
Qed.

Lemma add_to_seq_inv l p :
  seq_mode ∗ spbt l p  ⊢ |==>
  registered l ∗ seq l (p/2)%Qp ∗ seq_mode ∗ spbt l (p/2)%Qp .
Proof.
  iIntros "((?&[% [% ((%&%)&?&?&?)]])&Hpl)".

  iMod (insert_witness l with "[$]") as "(?&?)".

  destruct_decide (decide (l ∈ μ)).
  { exfalso. set_solver. }

  iDestruct (spbt_valid with "[$]") as "%Hv".
  rewrite -{1}(Qp.div_2 p). rewrite spbt_split. iDestruct "Hpl" as "(?&?)".

  destruct_decide (decide (l ∈ dom τ)) as Hl.
  { generalize Hl. intros Hl'. rewrite elem_of_dom in Hl. destruct Hl as (x,?).
    iDestruct (seq_locs_insert2 with "[$]") as "(%&?)". eauto.
    iMod (add_tau2 with "[$]") as "(?&?)". 1-2:eauto.
    iFrame. iModIntro. iExists _,_. iFrame.
    rewrite dom_insert_L assoc_L. iFrame.
    iPureIntro. split_and !; eauto. set_solver. }

  iMod (add_tau1 with "[$]") as "(?&?)". eauto.
  { apply Hv. }
  iDestruct (seq_locs_insert1 with "[$]") as "?". eauto.
  iFrame. iModIntro. iFrame. iExists _,_. iFrame.
  rewrite dom_insert_L assoc_L. iFrame.
  iPureIntro. split_and !; eauto. set_solver.
Qed.


Lemma add_to_seq_inv' s l p :
  seq_mode s ∗ spbt l p s  ⊢ |==>
  registered l s ∗ seq l (p/2)%Qp s ∗ seq_mode s ∗ spbt l (p/2)%Qp s.
Proof. rewrite -!monPred_at_sep -monPred_at_bupd. apply add_to_seq_inv. Qed.

Definition diamond n : vProp Σ := embed (diamond n).
Local Notation "♢ n" := (diamond n)%I%Qz (at level 20) : bi_scope.

Lemma extract_crit s :
  seq_mode s -∗
  outside s.(tid) ∗ (outside s.(tid) -∗ seq_mode s).
Proof.
  rewrite /seq_mode /seq_inv_inner !monPred_at_sep.
  iIntros "(?&?)". iFrame. iIntros "?". iFrame.
Qed.

Lemma wp_alloc' o b (n:nat) :
  n ≠ 0 ->
  ♢ (sz n) ⊢
  wp o b (tm_alloc n)
    (fun v => ∃ l, ⌜v = val_loc l⌝ ∗
           l ↦ (replicate n val_unit) ∗
           l ↤ ∅ ∗
           Stackable l 1%Qp ∗embed (meta_token l (⊤ ∖ ↑irisfit_nm))).
Proof.
  rewrite -wp_balance.
  constructor. intros s. rewrite /diamond monPred_at_embed monPred_at_wp.
  iIntros "Hn Ha".
  iDestruct (extract_crit with "Ha") as "(?&Ha)".
  iApply wp.wp_postpone.
  iApply (wp.wp_mono with "[-Ha]").

  iApply (wp_alloc' with "[-]"). lia. iFrame. conclude_diamonds. f_equal. lia.
  iIntros (?) "[% (?&?&?&(?&?)&?&?&?)]".

  iApply wp.bupd_wp.
  iSpecialize ("Ha" with "[$]").
  iMod (add_to_seq_inv' with "[$]") as "(#?&?&?&?)".

  iMod (vregistered_alloc s n).
  iModIntro.

  iApply wp.wp_val. iFrame.
  rewrite monPred_at_exist. iExists _. rewrite !monPred_at_sep monPred_at_pure !monPred_at_embed.
  iFrame "∗#". rewrite Nat2Z.id. iFrame. by iApply monPred_at_big_sepL.
Qed.

Lemma wp_alloc o b (n:nat) :
  n ≠ 0 ->
  ♢ (sz n) -∗
  wp o b (tm_alloc n)
    (fun v => ∃ l, ⌜v = val_loc l⌝ ∗
           l ↦ (replicate n val_unit) ∗
           l ↤ ∅ ∗
           Stackable l 1%Qp).
Proof.
  iIntros.
  iApply (wp_mono with "[-]").
  iApply (wp_alloc' with "[$]"). done.
  iIntros (?) "[%l (?&?&?&?&_)]".
  iExists l. iFrame.
Qed.

Lemma seq_locs_lookup s τ l :
  set_auth (dom τ) s ∗ registered l s ∗ seq_locs τ  s -∗ set_auth (dom τ) s ∗  ∃ v, seq_loc l v s ∗ (seq_loc l v s -∗ seq_locs τ s).
Proof.
  destruct s. rewrite /seq_locs. simpl.
  rewrite {1}monPred_at_big_sepM.
  iIntros "(Ha&Hf&?)".
  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
  apply auth_both_valid_discrete in Hv.
  destruct Hv as (Hv,?). apply gset_included in Hv.
  assert (l ∈ (dom τ)) as Hl by set_solver.
  apply elem_of_dom in Hl. destruct Hl as (x,?).

  iDestruct (big_sepM_insert_acc with "[$]") as "(?&Hb)". eauto.
  iFrame. iExists _. iFrame. iIntros.
  iSpecialize ("Hb" with "[$]"). rewrite insert_id //.
  rewrite monPred_at_big_sepM //.
Qed.

Lemma vpb_or_dead_reachable s vs n v l q V b  :
  vs !! n = Some v ->
  l ∈ V ->
  seq_mode s ∗ vregistered v s ∗ mapsto.mapsto l q vs =[b|tid s|V]=∗
  ∃ p, ( v ⟸?{p} {[tid s]} -∗ seq_mode s) ∗ v ⟸?{p} {[tid s]} ∗ mapsto.mapsto l q vs.
Proof.
  iIntros (? ?) "(Hi&?&Hvd)". iIntros.
  destruct_decide (decide (is_loc v)) as Eq.
  { apply is_loc_inv in Eq. destruct Eq as (?,?). subst.
    rewrite /seq_mode /seq_inv_inner {1}monPred_at_sep. iDestruct "Hi" as "(?&Hi)".
    rewrite {1}monPred_at_exist. iDestruct "Hi" as "[% Hi]".
    rewrite {1}monPred_at_exist. iDestruct "Hi" as "[% Hi]".
    rewrite !monPred_at_sep monPred_at_pure.
    iDestruct "Hi" as "((%&%Hμ)&?&?)".
    rewrite Hμ // right_id_L.
    iDestruct (seq_locs_lookup with "[$]") as "(?&[%op (Hpl & Hback)])". eauto.
    rewrite {1}/seq_loc monPred_at_or monPred_at_embed.
    iDestruct "Hpl" as "[? | ?]".
    { iMod (no_dangling_pointer1 with "[$] [%//] [$]") as "(?&?)"; eauto. }
    { iFrame. iModIntro. iExists _. iFrame. iIntros.
      rewrite monPred_at_sep. iFrame.
      rewrite monPred_at_exist. iExists _.
      rewrite monPred_at_exist. iExists _.
      rewrite !monPred_at_sep monPred_at_pure.
      iFrame. iSplitR. { eauto. }
      rewrite Hμ // right_id_L. iFrame.
      iApply "Hback". iFrame. } }
  { iFrame. iExists 1%Qp. rewrite vpbt_not_loc //. }
Qed.

Lemma wp_load o b (l:loc) (n:nat) q vs :
  n < length vs ->
  l ↦{q} vs ⊢
    wp o b (tm_load l n)
    (fun v => l ↦{q} vs ∗ ⌜v = vs !!! n⌝).
Proof.
  rewrite -wp_balance.
  intros Hlength. constructor. intros s. rewrite monPred_at_wp.
  rewrite /mapsto monPred_at_sep monPred_at_big_sepL.
  iIntros "(?&?)". rewrite monPred_at_embed.

  destruct (lookup_lt_is_Some_2 _ _ Hlength) as (v,Hv).

  iDestruct (big_sepL_lookup_acc with "[$]") as "(#HN2&Hbv)"; eauto.

  iIntros "Hseq".
  iApply wp_conseq.
  iApply (vpb_or_dead_reachable _ _ _ _ l). eauto. 2:iFrame "∗ #". set_solver.
  iIntros "[%p (Hin&Hl&?)]".

  assert (v = vs !!! n).
  { rewrite list_lookup_total_alt Hv //. }

  iAssert (v ⟸?{p/2} {[tid s]} ∗ v ⟸?{p/2} ∅)%I with "[Hl]" as "(Hl&?)".
  { iApply vpbt_split. destruct v; try easy. iApply (pbt_concl with "[$]"). rewrite Qp.div_2 //. set_solver. }

  iApply (wp.wp_mono with "[-Hin Hl Hbv]").
  iApply (wp_load with "[$]"); eauto. rewrite Nat2Z.id. done. lia.

  iIntros (?) "(%&?&?&?)". subst.
  iDestruct (vpbt_join with "[$]") as "Hp".
  iAssert ((vs !!! n) ⟸?{p} {[tid s]})%I with "[Hp]" as "?".
  { destruct (vs!!!n); try easy. iApply (pbt_concl with "[$]"). rewrite Qp.div_2 //. set_solver. }

  iSpecialize ("Hin" with "[$]").
  iSpecialize ("Hbv" with "[$]").
  iFrame. rewrite !monPred_at_sep monPred_at_big_sepL monPred_at_embed monPred_at_pure.
  by iFrame.
Qed.

Lemma wp_store (l:loc) (n:nat) v qv lsv vs o b :
  (is_loc v -> qv <> 0%Qz) ->
  n < length vs ->
  l ↦ vs ∗ v ↤?{qv} lsv ⊢
    wp o b (tm_store l n v)
    (fun r => ⌜r = val_unit⌝ ∗ l ↦ (<[n:=v]> vs)
         ∗ v↤?{qv}(lsv ⊎ {[+ l +]})
         ∗ (vs !!! n)↤?{0}({[-l-]})).
Proof.
  rewrite -wp_balance.
  intros ? Hlength. constructor. intros s.
  rewrite /mapsto monPred_at_wp !monPred_at_sep !monPred_at_embed monPred_at_big_sepL.
  iIntros "((?&Hinvs)&(?&#?))".
  iIntros "Ha".

  iApply (wp.wp_mono with "[- Hinvs Ha]").

  iApply (wp_store _ _ _ l v lsv vs with "[$]"); eauto. lia.
  iIntros (?) "(%&?&?&?&?)". subst.
  iFrame.

  rewrite !monPred_at_sep !monPred_at_pure !monPred_at_embed.
  iSplitR; first easy.
  iFrame "∗ #".

  destruct (lookup_lt_is_Some_2 _ _ Hlength) as (?,Hv).
  iDestruct (big_sepL_insert_acc with "[$]") as "(#?&Hbv)"; eauto.
  rewrite Nat2Z.id.
  rewrite list_lookup_total_alt Hv. simpl. iFrame "#".
  rewrite monPred_at_big_sepL. iFrame.
  iApply "Hbv". by iFrame.
Qed.

Lemma wp_call_later self args body ts vs o b Q :
  length args = length vs →
  locs body = ∅ ->
  ts = tm_val <$> vs ->
  (▷ wp o b (substs' (zip (self::args) (val_code self args body::vs)) body) Q)
    ⊢ wp o b (tm_call (val_code self args body) ts) Q.
Proof.
  intros. constructor. intros s. rewrite monPred_at_wp.
  iIntros "Hwp Ha".
  iDestruct (extract_crit with "Ha") as "(?&Ha)".
  rewrite monPred_at_later monPred_at_wp.
  iApply wp_call; eauto. iFrame. iIntros "!> ? ?".
  iApply wp.bupd_wp. iSpecialize ("Ha" with "[$]").
  iApply ("Hwp" with "[$]").
Qed.

Lemma wp_call_prim o b (p:prim) (v1 v2:val) w :
  eval_call_prim p v1 v2 = Some w ->
  ⊢ wp o b (tm_call_prim p v1 v2) (fun v => ⌜v = w⌝).
Proof.
  intros. rewrite -wp_balance. constructor. intros.
  rewrite monPred_at_wp. iIntros "_ Ha".
  iApply wp.wp_mono. iApply wp_call_prim; eauto. iIntros (?) "(->&?)".
  rewrite monPred_at_pure.
  by iFrame.
Qed.

Definition supd b V (P Q:vProp Σ) : vProp Σ :=
  MonPred (fun s => seq_mode s ∗ P s =[b| tid s | V]=∗ seq_mode s ∗ Q s)%I _.

Lemma wp_conseq o b P Q t Q' :
  supd b (locs t) P Q -∗
  P ∗ (Q -∗ wp o b t Q') -∗
  wp o b t Q'.
Proof.
  apply bi.entails_wand.
  constructor. intros s. simpl. iIntros "Hs". rewrite monPred_at_wand.
  iIntros (x Eq). inversion Eq. subst x.
  rewrite monPred_at_sep monPred_at_wand monPred_at_wp.
  iIntros "(?&Hwp) ?".
  iApply (wp_conseq _ _ _ (seq_mode s ∗ P s)%I (seq_mode s ∗ Q s)%I with "[Hs]").
  { iApply "Hs". }
  iFrame. iIntros "(?&?)".
  iSpecialize ("Hwp" with "[%//][$]"). rewrite monPred_at_wp.
  iApply ("Hwp" with "[$]").
Qed.

Definition tupd P Q : vProp Σ :=
  (∀ b V, supd b V P Q)%I.

Lemma wp_tconseq o b P Q t Q' :
  tupd P Q -∗
  P ∗ (Q -∗ wp o b t Q') -∗
  wp o b t Q'.
Proof.
  iIntros "Ht ?".
  iApply (wp_conseq with "[Ht][$]"). done.
Qed.

Local Notation "P =[ b | V ]=∗ Q" := (⊢ supd b V P%I Q%I)
(at level 99, Q at level 200, only parsing) : stdpp_scope.
Local Notation "P =[ b | V ]=∗ Q" := (supd b V P Q)%I
(at level 99, Q at level 200) : bi_scope.

Local Notation "P =[#]=∗ Q" := (⊢ tupd P%I Q%I)
(at level 99, Q at level 200, only parsing) : stdpp_scope.
Local Notation "P =[#]=∗ Q" := (tupd P Q)%I
(at level 99, Q at level 200) : bi_scope.

Lemma seq_acc s (τ:gmap loc Qp) (l:loc) p :
  map_auth τ s ∗ seq l p s -∗ ⌜∃ (q:Qp), τ !! l = Some q ∧ (Some p ≼ Some q)⌝.
Proof.
  iIntros "(Ha&Hf)". rewrite /seq.
  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
  apply auth_both_valid_discrete in Hv. destruct Hv as (Hv,?).
  apply singleton_included_l in Hv. iPureIntro.
  destruct Hv as (y,(Hy&Hpy)). exists y. split_and !; eauto. apply leibniz_equiv. auto.
Qed.

Lemma a_little_lemma p q :
  Some p ≼ Some q ->
  (p ≤ q)%Qp.
Proof.
  intros Hpq.
  rewrite Some_included in Hpq. destruct Hpq as [Hpq|Hpq].
  { inversion Hpq. subst. naive_solver. }
  { rewrite frac_included in Hpq.
    eauto using Qp.lt_le_incl. }
Qed.

Lemma wp_free l vs V bs :
  l ∉ V ->
  dom bs ⊆ {[l]} ->
  l ↦ vs ∗ l ↤ bs ∗ Stackable l 1 =[true|V]=∗ ♢(sz (length vs)) ∗ embed († l).
Proof.
  intros. constructor. intros s. simpl.
  iIntros "_ (Hi&Hpre)". iIntros.
  rewrite !monPred_at_sep !monPred_at_embed.
  iDestruct "Hpre" as "((?&_)&(?&_)&(?&_&?))".

  rewrite /seq_mode /seq_inv_inner. iDestruct "Hi" as "(?&Hi)".
  rewrite {1}monPred_at_exist. iDestruct "Hi" as "[% Hi]".
  rewrite {1}monPred_at_exist. iDestruct "Hi" as "[% Hi]".
  rewrite !monPred_at_sep monPred_at_pure.
  iDestruct "Hi" as "((%&%)&?&?&Hτ)".

  iDestruct (seq_acc with "[$]") as "%Hq".
  destruct Hq as (q,(Hlq&Hpq)).
  rewrite /seq_locs monPred_at_big_sepM.
  iDestruct (big_sepM_lookup_acc with "[$]") as "(Hpl&Hback)". eauto.

  rewrite /seq_loc monPred_at_or monPred_at_embed.
  (* We cannot be in no_seq_mode *)
  iDestruct "Hpl" as "[?|?]".
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(?&?)". compute_done. simpl. easy. }

  iDestruct (pbt_join with "[$]") as "Hl".
  iDestruct (pbt_valid with "[$]") as "%Hv".
  assert (q = (1/2)%Qp) as Hq.
  { eapply partial_order_anti_symm. Unshelve. 4:apply Qp.le_po.
    { rewrite (Qp.add_le_mono_r _ _ (1/2)%Qp) Qp.div_2 //. }
    { apply a_little_lemma. eauto.  } }

  iAssert (l ⟸ {[tid s]})%I with "[Hl]" as "?".
  { iApply (pbt_concl with "[$]"). rewrite Hq. compute_done. set_solver. }

  iMod (supd_clean with "[$][%//][$]") as "(?&?)". eauto.
  replace ({[tid s]} ∖ {[tid s]}) with (∅:gset thread_id) by set_solver.
  iMod (interp_free with "[$][$]") as "(?&?&_&#?)"; eauto.
  iSpecialize ("Hback" with "[$]").
  iFrame.
  iModIntro. iSplitL.
  { rewrite monPred_at_exist. iExists _.
    rewrite monPred_at_exist. iExists _.
    rewrite !monPred_at_sep monPred_at_pure monPred_at_big_sepM.
    iFrame. eauto. }
  { by iFrame. }
Qed.

Lemma mapsfrom_cleanup l l' q ls:
  l ↤{q} ls ∗ embed (†l') =[#]=∗
  l ↤{q} (ls ⊎ {[-l'-]}).
Proof.
  iIntros (??). iStopProof. constructor.
  intros s. iIntros "_". simpl. iIntros "(?&Hpre)".
  rewrite /mapsfrom !monPred_at_sep !monPred_at_embed.
  iDestruct "Hpre" as "((?&?)&?)". iIntros.
  iMod (mapsfrom_cleanup with "[$][$]") as "(?&?)".
  iFrame. rewrite /mapsfrom monPred_at_sep monPred_at_embed.
  by iFrame.
Qed.

Lemma vmapsfrom_cleanup l l' q ls:
  l ↤?{q} ls ∗ embed (†l') =[#]=∗
  l ↤?{q} (ls ⊎ {[-l'-]}).
Proof.
  destruct_decide (decide (is_loc l)) as Eq.
  { apply is_loc_inv in Eq.  destruct Eq as (?,?). subst. apply mapsfrom_cleanup.  }
  { iIntros (??). iStopProof. constructor.
    intros s. iIntros "_ (?&Hpre)". rewrite monPred_at_sep /vmapsfrom monPred_at_sep monPred_at_embed. iDestruct "Hpre" as "((?&?)&?)". iIntros.
    iFrame. rewrite monPred_at_sep !monPred_at_embed. iFrame.
    destruct l; naive_solver. }
Qed.

End Sequential.

Lemma enter_seq_mode `{interpGS sz Σ, seqG Σ} o E (b:bool) tid t P Q :
  (embed P ∗ wit E tid ⊢ wp o b t (fun v => (if o then no_seq_mode -∗ embed (Q v) else embed (Q v)))) ->
  outside tid ∗ P ⊢ wp.wp E b tid t Q.
Proof.
  intros [Hwp].
  iIntros "(Hc&HP)".
  iApply wp.bupd_wp.

  iMod (own_alloc (● (∅ : gmap loc Qp))) as "[%γl Hl]".
  { apply auth_auth_valid. easy. }

  iMod (own_alloc (● (∅ : gset loc))) as "[%γd Hd]".
  { apply auth_auth_valid. easy. }

  iDestruct (Hwp (Session γl γd tid E)) as "Hwp".
  rewrite monPred_at_wp monPred_at_sep monPred_at_embed. simpl.
  iSpecialize ("Hwp" with "[HP][-]").
  { by iFrame. }
  { rewrite /seq_mode /seq_inv_inner monPred_at_sep. iFrame.
    do 2 (rewrite monPred_at_exist; iExists _).
    rewrite !monPred_at_sep monPred_at_pure. simpl. iFrame.
    rewrite dom_empty_L left_id_L. iFrame.
    iSplitR; first done. rewrite /seq_locs monPred_at_big_sepM. done. }

  iApply (wp.wp_mono with "[$]").
  iModIntro. iIntros (?) "(?&Hpost)".
  destruct o.
  2:{ rewrite monPred_at_embed //. }
  { rewrite monPred_at_wand. iSpecialize ("Hpost" with "[%//]").
    rewrite monPred_at_embed. iApply "Hpost".
    iStopProof. apply abort_seq_mode. }
Qed.

Global Opaque wp.

Global Notation "l ↤{ q } ls" :=
  (mapsfrom l q%Qz ls)
  (at level 20, format "l  ↤{ q }  ls")
: bi_scope.

Global Notation "l ↤ ls" :=
  (mapsfrom l 1%Qz ls)
  (at level 20, format "l  ↤ ls")
: bi_scope.

Global Notation "v ↤?{ q } ls" :=
  (vmapsfrom v q%Qz ls)
  (at level 20, format "v  ↤?{ q }  ls")
: bi_scope.

Global Notation "v ↤? ls" :=
  (vmapsfrom v 1%Qz ls)
  (at level 20, format "v  ↤? ls")
: bi_scope.

Global Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Global Notation "l ↦□ v" := (mapsto l DfracDiscarded v)
  (at level 20, format "l  ↦□  v") : bi_scope.
Global Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Global Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Global Notation "P =[ b | V ]=∗ Q" := (⊢ supd b V P%I Q%I)
(at level 99, Q at level 200, only parsing) : stdpp_scope.
Global Notation "P =[ b | V ]=∗ Q" := (supd b V P Q)%I
(at level 99, Q at level 200) : bi_scope.
Global Notation "P =[#]=∗ Q" := (⊢ tupd P%I Q%I)
(at level 99, Q at level 200, only parsing) : stdpp_scope.
Global Notation "P =[#]=∗ Q" := (tupd P Q)%I
(at level 99, Q at level 200) : bi_scope.
