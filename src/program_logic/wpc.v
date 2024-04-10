From iris.proofmode Require Import base proofmode classes.
From iris Require Import gen_heap.
From iris.algebra Require Import gset gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language notation.
From irisfit.program_logic Require Import more_space_lang more_maps_and_sets interp.

From irisfit.program_logic Require Import wp_alloc wp_call wp_load wp_call_prim wp_store wp_fork wp_cas.
From irisfit.program_logic Require Export more_interp pbt wp_free wp_enc wp_protected.

Section Wpc.
Context `{!interpGS sz Σ}.

(* ------------------------------------------------------------------------ *)
(* A wp_let approx *)
Lemma wp_let_approx E b π M x t1 t2 Q :
  locs t2 ⊆ dom M ->
  wp E b π t1 (fun v => £1 -∗ PBT {[π]} M -∗ wp E b π (subst' x v t2) Q) -∗
     PBT {[π]} M  -∗ wp E b π (tm_let x t1 t2) Q.
Proof.
  iIntros (Hincl) "? ?".
  rewrite (split_map M (locs t2)) //.
  iDestruct (PBT_split with "[$]") as "[Hl ?]".
  iApply (wp_let with "[-Hl]").
  3:{ iFrame. }
  { rewrite dom_restrict. set_solver. }
  iApply (wp_mono with "[$]"). iIntros (?) "Hkont ? ?".
  iDestruct (PBT_op with "[$]") as "?".
  iApply ("Hkont" with "[$][$]").
Qed.

(* ------------------------------------------------------------------------ *)
(* wpc *)

(* A wp with context: it is a kind of frame of a context, with memory. *)
Definition wpc `{Enc A} E π (r:option (gset loc)) (t:tm) (Q:A -> iProp Σ) : iProp Σ :=
  outside π -∗
  match r with
  | None => wp E false π t (fun a => (outside π ∗ post Q a))%I
  | Some r =>
     (∀ (k:gmap loc Qp), ⌜dom k = r⌝ -∗
         PBT {[π]} k -∗ wp E true π t (fun a => (outside π ∗ PBT {[π]} k ∗ post Q a)))%I end.
Lemma wpc_eq `{Enc A} E π (r:option (gset loc)) (t:tm) (Q:A -> iProp Σ) :
  wpc E π r t Q = (outside π -∗
  match r with
  | None => wp E false π t (fun a => (outside π ∗ post Q a))%I
  | Some r =>
     (∀ (k:gmap loc Qp), ⌜dom k = r⌝ -∗
         PBT {[π]} k -∗ wp E true π t (fun a => (outside π ∗ PBT {[π]} k ∗ post Q a)))%I end)%I.
Proof. reflexivity. Qed.

Global Instance wpc_ne `{!interpGS sz Σ} A (HA:Enc A) E i r t n :
  Proper (pointwise_relation A (dist n) ==> dist n) (wpc E i r t).
Proof.
  revert t. induction (lt_wf n) as [n _ IH]=> t Φ Ψ HΦ.
  unfold wpc,post,wpc.
  repeat (f_contractive || f_equiv).
Qed.

(* We inherit strong mono. *)
Lemma wpc_strong_mono (A:Type) (EA:Enc A) E1 E2 π r t (Q Q':A -> iProp Σ) :
  E1 ⊆ E2 ->
  wpc E2 π r t Q -∗ (∀ v, Q v ={E1}=∗ Q' v) -∗ wpc E2 π r t Q'.
Proof.
  iIntros (?) "Hwpc HQQ'".
  iIntros "?". destruct r.
  { iIntros (k) "??".
    iSpecialize ("Hwpc" with "[$][$][$]").
    iApply (wp_strong_mono with "[$]"). eauto.
    iIntros (?) "(?&?&?)".
    iFrame. iApply (post_strong_mono with "[$]"); eauto. }
  { iSpecialize ("Hwpc" with "[$]").
    iApply (wp_strong_mono with "[$]"). eauto.
    iIntros (?) "(?&?)". iFrame.
    iApply (post_strong_mono with "[$]"); eauto. }
Qed.

Lemma wpc_strong_mono' (A:Type) (EA:Enc A) E π r t (Q Q':A -> iProp Σ) :
  wpc E π r t Q -∗ (∀ v, Q v ={E}=∗ Q' v) -∗ wpc E π r t Q'.
Proof.
  iIntros.
  iApply (@wpc_strong_mono _ _ E with "[$]"). set_solver.
  eauto.
Qed.

Lemma wpc_mono (A:Type) (EA:Enc A) E π r t (Q Q':A -> iProp Σ) :
  wpc E π r t Q -∗ (∀ v, Q v -∗ Q' v) -∗ wpc E π r t Q'.
Proof.
  iIntros "? H".
  iApply (wpc_strong_mono' with "[$]").
  iIntros. by iApply "H".
Qed.

Ltac enter_deriv r str :=
  iIntros str;
  iIntros "Hπ"; destruct r; first iIntros (k Hk) "Hctx".

Lemma wpc_mono_val (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) (Q':val -> iProp Σ) :
  wpc E π r t Q -∗ (∀ v, Q v -∗ Q' (enc v)) -∗ wpc E π r t Q'.
Proof.
  enter_deriv r "Hwp Hq".
  { iSpecialize ("Hwp" with "[$][%//][$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&?&?)". iFrame.
    iApply (post_mono_val with "[$][$]"). }
  { iSpecialize ("Hwp" with "[$]"). iApply (wp_mono with "[$]").
    iIntros (?) "(?&?)". iFrame. iApply (post_mono_val with "[$][$]"). }
Qed.

Lemma wpc_frame_wand (A:Type) (EA:Enc A) E π r t Q (Q':A -> iProp Σ) :
  Q -∗ wpc E π r t (fun v => Q -∗ Q' v) -∗
  wpc E π r t Q'.
Proof.
  iIntros.
  iApply (wpc_mono with "[$]").
  iIntros (?) "HQ". iApply "HQ". iFrame.
Qed.

Lemma fupd_wpc (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  (|={E}=> wpc E π r t Q) ⊢ wpc E π r t Q.
Proof.
  enter_deriv r "Hwpc"; iApply fupd_wp.
  by iApply ("Hwpc" with "[$][%//][$]").
  by iApply ("Hwpc" with "[$]").
Qed.

Lemma bupd_wpc (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  (|==> wpc E π r t Q) ⊢ wpc E π r t Q.
Proof.
  iIntros "E". iApply fupd_wpc. iMod "E". by iFrame.
Qed.

Lemma wpc_fupd (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ)  :
  wpc E π r t (fun v => |={E}=> Q v) ⊢ wpc E π r t Q.
Proof. iIntros "H". iApply (wpc_strong_mono with "H"); auto. Qed.

Definition is_some {A:Type} (x:option A) :=
  match x with
  | Some _ => true
  | None => false end.

(* We can prove wpc from any wp, thanks to frame. *)
Lemma wp_wpc (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  (outside π -∗ wp E (is_some r) π t (λ v:val, outside π ∗ post Q v)) ⊢
  wpc E π r t Q.
Proof.
  enter_deriv r "X".
  all:iSpecialize ("X" with "[$]"); iApply (wp_mono with "[$]"); iIntros; by iFrame.
Qed.

(* To prove a wp, we can prove a wpc with an empty context. *)
Lemma wpc_wp_empty (A:Type) (EA:Enc A) E (b:bool) π t (Q:A -> iProp Σ) :
  outside π -∗ wpc E π (if b then Some ∅ else None) t Q -∗
  wp E b π t (λ a : val, outside π ∗ post Q a).
Proof.
  iIntros "? Hwpc".
  destruct b.
  { iSpecialize ("Hwpc" with "[$][%][]").
    2:{ iApply PBT_empty. }
    { by rewrite dom_empty_L. }
    iApply (wp_strong_mono with "[$]"); try iFrame. done.
    iIntros (?) "(?&?&?)".
    by iFrame. }
  { by iApply "Hwpc". }
Qed.

(* We can "frame" a context, and remember it. *)
Lemma wpc_extend (A:Type) (EA:Enc A) E π r2 r1 k t (Q:A -> iProp Σ) :
  r2 = dom k ->
  PBT {[π]} k ∗ wpc E π (Some (r2 ∪ r1)) t Q ⊢
  wpc E π (Some r1) t (fun v => PBT {[π]} k ∗ Q v).
Proof.
  iIntros (?) "[? Hwpc] ?".
  iIntros (k1 Hk1) "?".
  iDestruct (PBT_union with "[$]") as "?".
  iSpecialize ("Hwpc" with "[$][%][$]").
  { rewrite dom_op. set_solver. }
  iApply (wp_strong_mono with "[$]"). done.
  iIntros (?).
  rewrite PBT_op.
  iIntros "(?&(?&?)&?)".
  by iFrame.
Qed.

Lemma wpc_context (A:Type) (EA:Enc A) E π r' r t Q :
  PBT {[π]} r' ∗ wpc E π (Some (dom r' ∪ r)) t (fun v:A => PBT {[π]} r' -∗ Q v) -∗
  wpc E π (Some r) t Q.
Proof.
  iIntros.
  iDestruct (wpc_extend with "[$]") as "?"; try easy.
  iApply (wpc_mono with "[$]").
  iIntros (?) "[? Hp]".
  iApply "Hp". eauto.
Qed.

Lemma wpc_context_singleton l q r t E π (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  pbt l q {[π]} -∗ wpc E π (Some ({[l]} ∪ r)) t (fun v:A => pbt l q {[π]} -∗ Q v) -∗
  wpc E π (Some r) t Q.
Proof.
  iIntros "Hlq ?".
  rewrite {1}pbt_PBT. iApply wpc_context. iFrame "Hlq".
  rewrite dom_singleton_L. iApply (wpc_mono with "[$]"). iIntros (?) "X ?".
  rewrite pbt_PBT. by iApply "X".
Qed.

Lemma wpc_context_vsingleton v q r t E π (A:Type) (EA:Enc A) (Q:A -> iProp Σ) :
  vpbt v q {[π]} -∗ wpc E π (Some (locs v ∪ r)) t (fun w:A => vpbt v q {[π]} -∗ Q w) -∗
  wpc E π (Some r) t Q.
Proof.
  iIntros.
  destruct_decide (decide (is_loc v)) as Eq.
  { apply is_loc_inv in Eq. destruct Eq as (?,->).
    iApply (wpc_context_singleton with "[$]"). auto_locs. iFrame. }
  { rewrite locs_no_loc // left_id_L.
    iApply (wpc_mono with "[$]"). iIntros (?) "HQ".
    by iApply "HQ". }
Qed.

Lemma wpc_weak r1 (A:Type) (EA:Enc A) E π r2 t (Q:A -> iProp Σ) :
  r1 ⊆ r2 ->
  wpc E π (Some r1) t Q -∗ wpc E π (Some r2) t Q.
Proof.
  intros ?. iIntros "Hwp ?". iIntros (k Hk) "Hctx".
  rewrite (split_map k r1); last set_solver. rewrite {1}PBT_op.
  iSpecialize ("Hwp" with "[$]").
  iDestruct "Hctx" as "(?&?)".
  iDestruct ("Hwp" $! (restrict k r1) with "[%][$]") as "?".
  { rewrite dom_restrict. set_solver. }
  iApply (wp_mono with "[$]"). iIntros (?) "(?&?&?)". iFrame.
  iApply PBT_op. iFrame.
Qed.

Lemma wpc_bind `{EA:Enc A} {E π r} K t k (Q:A -> iProp Σ) :
  (locs K) ⊆ r ∪ (dom k) ->
  PBT {[π]} k -∗
  wpc E π (Some (r ∪ dom k)) t (fun (v:val) => PBT {[π]} k-∗ wpc E π (Some r) (fill_item K v) Q) -∗
  wpc E π (Some r) (fill_item K t) Q.
Proof.
  iIntros (?) "Hk Hwpc ?".
  iIntros (k' Hrk') "Hk'".

  iDestruct (PBT_kdiv with "Hk") as "[Hk1 Hk2]".
  iDestruct (PBT_kdiv with "Hk'") as "[Hk'1 Hk'2]".
  iDestruct (PBT_op with "[Hk'1 Hk1]") as "H1"; try iFrame.
  iDestruct (PBT_op with "[Hk'2 Hk2]") as "H2"; try iFrame.

  iSpecialize ("Hwpc" with "[$][%][$]"); try iFrame.
  { rewrite dom_op !dom_kdiv. set_solver. }

  assert (locs K ⊆ dom ((kdiv k) ⋅ (kdiv k'))).
  { rewrite dom_op !dom_kdiv. set_solver. }

  rewrite (split_map ((kdiv k) ⋅ (kdiv k')) (locs K)); last easy.
  iDestruct (PBT_op with "H1") as "[? Hl]".

  iApply (wp_bind with "[Hwpc Hl]"); try iFrame.
  { rewrite dom_restrict dom_op !dom_kdiv.
    set_solver. }
  iApply (wp_strong_mono with "[$]"). done.
  iIntros (v) "(?&Hkk1&Hwpc)".
  iModIntro. iIntros "Hkk2". simpl.

  iDestruct (PBT_op with "[Hl Hkk2]") as "Hkk2". iFrame "Hkk2 Hl".
  rewrite -split_map //.

  iDestruct (PBT_op with "Hkk1") as "[? ?]".
  iDestruct (PBT_op with "Hkk2") as "[? ?]".
  iDestruct (PBT_kdiv with "[$]") as "?".
  iDestruct (PBT_kdiv with "[$]") as "?".
  rewrite post_val.
  iApply ("Hwpc" with "[$][$][% //][$]").
Qed.

Lemma wpc_bind_noclean `{Enc A} {E π r} K t (Q:A -> iProp Σ) :
  wpc E π None t (fun (v:val) => wpc E π r (fill_item K v) Q) -∗
  wpc E π r (fill_item K t) Q.
Proof.
  enter_deriv r "Hwp"; iApply wp_bind_noclean; iSpecialize ("Hwp" with "[$]");
    iApply (wp_mono with "[$]"); iIntros (?) "(?&Hwp)"; rewrite post_val.
  { iApply ("Hwp" with "[$][%//][$]"). }
  { iApply ("Hwp" with "[$]"). }
Qed.

Lemma wpc_noclean (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  wpc E π None t Q ⊢
  wpc E π r t Q.
Proof.
  destruct r; last done.
  iIntros "Hwp ?". iIntros (? ?) "?".
  iApply wp_noclean.
  iSpecialize ("Hwp" with "[$]"). iApply (wp_mono with "[$]").
  iIntros (?) "(?&?)". iFrame.
Qed.

Lemma wpc_let_val (A:Type) (EA:Enc A) E π r x (v:val) t (Q:A -> iProp Σ) :
  ▷(£1 -∗ wpc E π r (subst' x v t) Q) -∗
  wpc E π r (tm_let x v t) Q.
Proof.
  enter_deriv r "Hwp"; iApply wp_let_val; iModIntro; iIntros.
  { iApply ("Hwp" with "[$][$][%//][$]"). }
  { iApply ("Hwp" with "[$][$]"). }
Qed.

Lemma wpc_let_lc (A:Type) (EA:Enc A) E π r x t1 t2 k (Q:A -> iProp Σ) :
  (locs t2) ⊆ r ∪ (dom k) ->
  PBT {[π]} k  -∗
  wpc E π (Some (r ∪ dom k)) t1 (fun v => £1 -∗ PBT {[π]} k -∗ wpc E π (Some r) (subst' x v t2) Q) -∗
  wpc E π (Some r) (tm_let x t1 t2) Q.
Proof.
  iIntros.
  iApply (wpc_bind (ctx_let x t2) with "[$]"); auto_locs; eauto.
  iApply (@wpc_mono with "[$]").
  iIntros (?) "Hwp ?". simpl.
  iApply wpc_let_val. iModIntro. iIntros.
  iApply ("Hwp" with "[$][$]").
Qed.

Lemma wpc_let (A:Type) (EA:Enc A) E π r x t1 t2 k (Q:A -> iProp Σ) :
  (locs t2) ⊆ r ∪ (dom k) ->
  PBT {[π]} k  -∗
  wpc E π (Some (r ∪ dom k)) t1 (fun (v:val) => PBT {[π]} k -∗ wpc E π (Some r) (subst' x v t2) Q) -∗
  wpc E π (Some r) (tm_let x t1 t2) Q.
Proof.
  iIntros. iApply (wpc_let_lc with "[$]"); eauto.
  iApply (wpc_mono_val with "[$]"). iIntros (?) "HP ? ?". by iApply "HP".
Qed.

Lemma wpc_let_noclean_lc (A:Type) (EA:Enc A) E π r x t1 t2 (Q:A -> iProp Σ) :
  wpc E π None t1 (fun v => £1 -∗ wpc E π r (subst' x v t2) Q) -∗
  wpc E π r (tm_let x t1 t2) Q.
Proof.
  enter_deriv r "Hwp"; iApply wp_let_noclean;
    iSpecialize ("Hwp" with "[$]"); iApply (wp_mono with "[$]");
    iIntros (?) "(?&Hwp) ?"; rewrite post_val.
  { iApply ("Hwp" with "[$][$][%//][$]"). }
  { iApply ("Hwp" with "[$]"); eauto. }
Qed.

Lemma wpc_let_noclean `{interpGS sz Σ} (A:Type) (EA:Enc A) E π r x t1 t2 (Q:A -> iProp Σ) :
  wpc E π None t1 (fun v => wpc E π r (subst' x v t2) Q) -∗
  wpc E π r (tm_let x t1 t2) Q.
Proof. iIntros. iApply wpc_let_noclean_lc; eauto. iApply (wpc_mono with "[$]"). iIntros. iFrame. Qed.

Lemma wpc_if_lc (A:Type) (EA:Enc A) E (c:bool) π r t1 t2 (Q:A -> iProp Σ) :
  ▷(£1 -∗ if c then wpc E π r t1 Q else wpc E π r t2 Q)
  ⊢ wpc E π r (tm_if c t1 t2) Q.
Proof.
  enter_deriv r "Hwpc".
  all:iApply wp_if; iModIntro; iIntros.
  { destruct c; iApply ("Hwpc" with "[$][$][%//][$]"); eauto. }
  { destruct c; iApply ("Hwpc" with "[$][$]"). }
Qed.

Lemma wpc_if (A:Type) (EA:Enc A) E (c:bool) π r t1 t2 (Q:A -> iProp Σ) :
  (if c then wpc E π r t1 Q else wpc E π r t2 Q)
  ⊢ wpc E π r (tm_if c t1 t2) Q.
Proof. iIntros. iApply wpc_if_lc. iModIntro. iIntros. iFrame. Qed.

Lemma wpc_call (A:Type) (EA:Enc A) E π r self args body vs ts (Q:A -> iProp Σ) :
  length args = length vs →
  locs body = ∅ →
  ts = tm_val <$> vs →
  ▷ (£1 -∗ wpc E π r (substs' (zip (self :: args) (val_code self args body :: vs)) body) Q) -∗
     wpc E π r (tm_call (val_code self args body) ts) Q.
Proof.
  intros.
  enter_deriv r "Hwpc".
  all:iApply (wp_strong_mono with "[-]"); try reflexivity.
  1,3: iApply wp_call; eauto; iFrame.
  1,2:iModIntro; iIntros.
  { iSpecialize ("Hwpc" with "[$][$][%//][$]"). iFrame. }
  { iSpecialize ("Hwpc" with "[$][$]"). iFrame. }
  eauto. eauto.
Qed.

Lemma wpc_call_prim_lc (A:Type) (EA:Enc A) E π r (p:prim) (v1 v2:val) (w:A) :
  eval_call_prim p v1 v2 = Some (enc w) ->
  ⊢ wpc E π r (tm_call_prim p v1 v2) (fun (v:A) => ⌜v = w⌝ ∗ £1).
Proof.
  intros. iApply wpc_noclean.
  rewrite wpc_eq. iIntros.
  iApply (wp_mono with "[]").
  iApply wp_call_prim. eauto.
  iIntros (?) "(->&?)". iFrame. iExists _. by iFrame.
Qed.

Ltac derive_no_lc H := iIntros; iApply (wpc_mono with "[-]"); first (iApply H; eauto).

Lemma wpc_call_prim (A:Type) (EA:Enc A) E π r (p:prim) (v1 v2:val) (w:A) :
  eval_call_prim p v1 v2 = Some (enc w) ->
 ⊢ wpc E π r (tm_call_prim p v1 v2) (fun (v:A) => ⌜v = w⌝).
Proof. derive_no_lc wpc_call_prim_lc. iIntros (?) "(?&?)". iFrame. Qed.

Lemma wpc_val (A:Type) (EA:Enc A) E π r (v:A) (Q:A -> iProp Σ) :
  Q v -∗
  wpc E π r (enc v) Q.
Proof.
  iIntros "?". iApply wpc_noclean. iIntros "?".  iApply wp_val.
  iFrame. iExists _. iFrame. eauto.
Qed.

Lemma wpc_postpone (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  wpc E π r t (fun (a:A) => wpc E π r (enc a) Q) -∗
  wpc E π r t Q.
Proof.
  enter_deriv r "Hwpc".
  all:iApply wp_postpone.
  { iSpecialize ("Hwpc" with "[$] [% //][$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&?&Hwpc)". iDestruct "Hwpc" as "[% (->&Hwpc)]".
    iSpecialize ("Hwpc" with "[$][% //][$]").
    eauto. }
  { iSpecialize ("Hwpc" with "[$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&Hwpc)". iDestruct "Hwpc" as "[% (->&Hwpc)]".
    iSpecialize ("Hwpc" with "[$]").
    eauto. }
Qed.

Lemma wpc_postpone_val (A:Type) (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  wpc E π r t (fun (v:val) => wpc E π r v Q) -∗
  wpc E π r t Q.
Proof.
  enter_deriv r "Hwpc".
  all:iApply wp_postpone.
  { iSpecialize ("Hwpc" with "[$] [% //][$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&?&Hwpc)". iDestruct "Hwpc" as "[% (->&Hwpc)]".
    iSpecialize ("Hwpc" with "[$][% //][$]").
    eauto. }
  { iSpecialize ("Hwpc" with "[$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&Hwpc)". iDestruct "Hwpc" as "[% (->&Hwpc)]".
    iSpecialize ("Hwpc" with "[$]").
    eauto. }
Qed.

Lemma wpc_load_lc `{Enc A} {E π X} (l:loc) (n:Z) q p S vs (a:A) :
  (0 <= n < Z.to_nat (length vs))%Z ->
  (vs !!! Z.to_nat n) = enc a ->
  l ↦{q} vs ∗ (vs !!! Z.to_nat n) ⟸?{p} S ⊢
  wpc E π X (tm_load l n) (fun (w:A) => ⌜w=a⌝ ∗ l ↦{q} vs ∗ (vs!!! Z.to_nat n)  ⟸?{p} (S ∪ {[π]}) ∗ £1).
Proof.
  iIntros (? He) "H1".
  iApply wpc_postpone_val. iApply wpc_noclean.
  iApply wp_wpc. iIntros.
  iApply (wp_mono with "[H1]").
  iApply wp_load'. 1:easy. 2:iFrame.
  lia.
  iIntros (?) "(% & ?&?)". subst.
  rewrite post_val He. iFrame. iApply wpc_val.
  iFrame. eauto.
Qed.

(* XXX remove this? Derived automatically ? *)
Lemma wpc_load_no_loc `{Enc A} {E π X} (l:loc) (n:Z) q vs (a:A) :
 (0 <= n < Z.to_nat (length vs))%Z ->
  (vs !!! Z.to_nat n) = enc a ->
  ¬ is_loc (enc a) ->
  l ↦{q} vs ⊢
  wpc E π X (tm_load l n) (fun (w:A) => ⌜w=a⌝ ∗ l ↦{q} vs).
Proof.
  iIntros (? He Hl) "H1".
  iApply (wpc_mono with "[-]").
  { iApply (wpc_load_lc _ _ _ 1%Qp ∅); eauto.  iFrame. iApply vpbt_not_loc; eauto. rewrite He //. }
  iIntros (?) "(->&?&_)". by iFrame.
Qed.

Lemma wpc_load `{Enc A} {E π X} (l:loc) (n:Z) q p S vs (a:A) :
  (0 <= n < Z.to_nat (length vs))%Z ->
  (vs !!! Z.to_nat n) = enc a ->
  l ↦{q} vs ∗ (vs !!! Z.to_nat n) ⟸?{p} S ⊢
  wpc E π X (tm_load l n) (fun (w:A) => ⌜w=a⌝ ∗ l ↦{q} vs ∗ (vs!!!Z.to_nat n)  ⟸?{p} (S ∪ {[π]})).
Proof. derive_no_lc @wpc_load_lc. iIntros (?) "(->&?&?&?)". by iFrame. Qed.

Lemma wpc_store_lc {E π X} (l:loc) (n:Z) v qv lsv vs :
  (is_loc v -> qv ≠ 0%Qz) ->
  (0 <= n < Z.to_nat (length vs))%Z ->
  l ↦ vs ∗ v ↤?{qv} lsv ⊢
    wpc E π X (tm_store l n v)
    (fun (_:unit) => l ↦ (<[Z.to_nat n:=v]> vs)
             ∗ v↤?{qv}(lsv ⊎ {[+ l +]})
             ∗ (vs !!! Z.to_nat n)↤?{0}({[-l-]}) ∗ £1).
Proof.
  iIntros. iApply wpc_noclean. iApply wp_wpc. iIntros "X".
  iApply (wp_mono with "[-X]").
  iApply wp_store; eauto. lia.
  iIntros (?) "(% & ? & ? & ?&?)".
  subst. rewrite post_unit. iFrame.
Qed.

Lemma wpc_store {E π X} (l:loc) (n:Z) v qv lsv vs :
  (is_loc v -> qv ≠ 0%Qz) ->
  (0 <= n < Z.to_nat (length vs))%Z ->
  l ↦ vs ∗ v ↤?{qv} lsv ⊢
    wpc E π X (tm_store l n v)
    (fun (_:unit) => l ↦ (<[Z.to_nat n:=v]> vs)
             ∗ v↤?{qv}(lsv ⊎ {[+ l +]})
             ∗ (vs !!! Z.to_nat n)↤?{0}({[-l-]})).
Proof. derive_no_lc @wpc_store_lc. iIntros (?) "(?&?&?&?)". by iFrame. Qed.

Lemma wpc_alloc_lc {E π X} (n:Z) :
  (0 < n)%Z ->
  ♢ (sz (Z.to_nat n)) -∗
  wpc E π X (tm_alloc n)
    (fun l => l ↦ (replicate (Z.to_nat n) val_unit) ∗
          l ↤ ∅ ∗
          l ⟸ {[π]} ∗ meta_token l (⊤ ∖ ↑irisfit_nm) ∗ £1).
Proof.
  iIntros. iApply wpc_noclean. iIntros "?".
  iApply (wp_mono with "[-]").
  iApply wp_alloc'. lia. iFrame.
  iIntros (?) "(%&%&?&?&?&?&?&?)".
  subst. rewrite post_loc. iFrame.
Qed.

Lemma wpc_alloc {E π X} (n:Z) :
  (0 < n)%Z ->
  ♢ (sz (Z.to_nat n)) -∗
  wpc E π X (tm_alloc n)
    (fun l => l ↦ (replicate (Z.to_nat n) val_unit) ∗
          l ↤ ∅ ∗
          l ⟸ {[π]} ∗
          meta_token l (⊤ ∖ ↑irisfit_nm)).
Proof. derive_no_lc @wpc_alloc_lc. iIntros (?) "(?&?&?&?&?)". by iFrame. Qed.

Lemma wpc_fork {E π r} L t :
  dom L = locs t ->
  PBT {[π]} L -∗
  (∀ j, £1 -∗ PBT {[j]} L -∗ wpc ⊤ j (Some ∅) t (fun _ => True)) -∗
  wpc E π (Some r) (tm_fork t) (fun v => ⌜v=val_unit⌝).
Proof.
  iIntros (?) "? Hwp Hout %% Hk".
  iApply (wp_mono with "[-Hk]").
  { iApply (wp_fork with "[$][$]"); eauto.
    iIntros. iSpecialize ("Hwp" with "[$][$]").
    iDestruct (wpc_wp_empty _ _ _ true with "[$][$]") as "?".
    iApply (wp_mono with "[$]"). iIntros (?) "(?&?)". iFrame. }
  { iIntros (?) "(->&?)". rewrite post_val. by iFrame. }
Qed.

Lemma wpc_cas_fail_lc {E π X} (l:loc) (q:dfrac) (i:Z) (v1 v1' v2:val) (bs:list val) :
  bs !! (Z.to_nat i) = Some v1' ->
  (0 <= i)%Z ->
  ¬ (v1=v1') ->
  l ↦{q} bs ⊢ wpc E π X (tm_cas l i v1 v2)
    (fun r => ⌜r=false⌝ ∗ l ↦{q} bs ∗ £1).
Proof.
  iIntros. iApply wpc_noclean. iApply wp_wpc. iIntros "X".
  iApply (wp_mono with "[-X]").
  { iApply wp_cas_fail; eauto. }
  iIntros (?) "[% (?&?)]". subst. rewrite post_bool. iFrame. eauto.
Qed.

Lemma wpc_cas_fail {E π X} (l:loc) (q:dfrac) (i:Z) (v1 v1' v2:val) (bs:list val) :
  bs !! (Z.to_nat i) = Some v1' ->
  (0 <= i)%Z ->
  ¬ (v1=v1') ->
  l ↦{q} bs ⊢ wpc E π X (tm_cas l i v1 v2)
    (fun r => ⌜r=false⌝ ∗ l ↦{q} bs).
Proof. derive_no_lc @wpc_cas_fail_lc. iIntros (?) "(?&?&?)". by iFrame. Qed.

Lemma wpc_cas_suc_lc {E π X} (l:loc) (i:Z) (v1 v2:val) qv (bs:list val) :
  bs !! (Z.to_nat i) = Some v1 ->
  (0 <= i)%Z ->
  (is_loc v2 -> qv≠0%Qz) ->
  l ↦ bs ∗ v2 ↤?{qv} ∅ ⊢ wpc E π X (tm_cas l i v1 v2)
    (fun r => ⌜r=true⌝ ∗ l ↦ (<[Z.to_nat i:=v2]> bs) ∗ v1 ↤?{0} {[-l-]} ∗ v2 ↤?{qv} {[+ l +]} ∗ £1).
Proof.
  iIntros. iApply wpc_noclean. iApply wp_wpc. iIntros "X".
  iApply (wp_mono with "[-X]").
  { iApply wp_cas_suc; eauto. }
  iIntros (?) "[%Eq (?&?)]". subst. rewrite post_bool. iFrame. eauto.
Qed.

Lemma wpc_cas_suc {E π X} (l:loc) (i:Z) (v1 v2:val) qv (bs:list val) :
   bs !! (Z.to_nat i) = Some v1 ->
  (0 <= i)%Z ->
  (is_loc v2 -> qv≠0%Qz) ->
  l ↦ bs ∗ v2 ↤?{qv} ∅ ⊢ wpc E π X (tm_cas l i v1 v2)
    (fun r => ⌜r=true⌝ ∗ l ↦ (<[Z.to_nat i:=v2]> bs) ∗ v1 ↤?{0} {[-l-]} ∗ v2 ↤?{qv} {[+ l +]}).
Proof. derive_no_lc @wpc_cas_suc_lc. iIntros (?) "(?&?&?&?&?)". by iFrame. Qed.

Lemma wpc_split_ctx (A:Type) (EA:Enc A) E (π:thread_id) r t (Q:A -> iProp Σ) :
  (∀ M, ⌜r = dom M⌝ -∗ PBT ∅ M -∗  wpc E π (Some r) t (fun v => PBT ∅ M ∗ Q v)) -∗
  wpc E π (Some r) t Q.
Proof.
  iIntros "Hwp ? %k %Hk Hk".
  replace ({[π]}) with ({[π]} ∪ ∅ : gset thread_id) by set_solver.
  rewrite (kdiv_both k).
  rewrite {1}PBT_op_split //.
  iDestruct "Hk" as "(?&?)".
  iSpecialize ("Hwp" with "[%][$]").
  { rewrite dom_kdiv //. }
  rewrite wpc_eq.
  iSpecialize ("Hwp" with "[$][%][$]").
  { rewrite dom_kdiv //. }
  iApply (wp_mono with "[$]"). iIntros (?) "(?&?&[% (->&?&HQ)])".
  iFrame. iSplitR "HQ".
  { iApply PBT_op_split. easy. iFrame. }
  { iExists _. by iFrame. }
Qed.

Lemma wpc_load_ctx (A:Type) (EA:Enc A) E π X (l:loc) (n:Z) q vs (a:A) :
  (0 <= n < Z.to_nat (length vs))%Z ->
  (vs !!! Z.to_nat n) = enc a ->
  locs (vs !!! Z.to_nat n) ⊆ X ->
  l ↦{q} vs ⊢
  wpc E π (Some X) (tm_load l n) (fun (w:A) => ⌜w=a⌝ ∗ l ↦{q} vs).
Proof.
  iIntros (He Ha Hvsn) "H1".
  destruct_decide (decide (is_loc (vs !!! Z.to_nat n))) as  Eq.
  { iIntros "? %% X".
    apply is_loc_inv in Eq. destruct Eq as (l',Eq).
    assert (exists p, k !! l' = Some p) as (p,Hp).
    { apply elem_of_dom. rewrite Eq in Hvsn. set_solver. }
    iDestruct (big_sepM_lookup_acc with "[$]") as "(E & Hb)".
    { eauto. }
    iApply (wp_mono with "[H1 E]").
    { iApply (@wp_load' _ _ _ _ _ _ l _ _ _ _ _ l'); eauto.
      simpl. iFrame. }
    iIntros (?) "(->&?&?&?)".
    simpl. rewrite union_idemp_L. iSpecialize ("Hb" with "[$]").
    iFrame. iExists a. iPureIntro. rewrite Ha in Eq. inversion Eq. naive_solver. }
  { iApply wpc_load_no_loc; eauto. rewrite Ha // in Eq. }
Qed.

Lemma wpc_enter `{Enc A} {E π r} t (Q: A -> iProp Σ):
  (∀ k, ⌜dom k=r⌝ -∗ PBT {[π]} k -∗ inside π ∅ -∗ wp E true π t (fun v => PBT {[π]} k ∗ outside π ∗ post Q v)) -∗
  wpc E π (Some r) (tm_enter ;; t)%T Q.
Proof.
  iIntros "Hwp Hc". iIntros (?) "? ?".
  iApply wp_let_noclean.
  iApply (wp_mono with "[Hc]").
  { by iApply wp_enter. }
  iIntros (?) "(->&?) _".
  iSpecialize ("Hwp" with "[$][$][$]").
  iApply (wp_mono with "[$]"). iIntros (?) "(?&?&?)". iFrame.
Qed.

Lemma wpc_exit `{Enc A} {E π } S k t (Q: A -> iProp Σ):
  S ∩ locs t = ∅ ->
  PBT {[π]} k ∗ inside π S ∗ wpc E π (Some (dom k)) t Q -∗
  wp E true π (tm_exit ;; t) (fun v => PBT {[π]} k ∗ outside π ∗ post Q v).
Proof.
  iIntros (?) "(X&?&Hwp)".

  iApply wp_conseq.
  { iApply inside_clean. }
  iFrame. iIntros.
  replace (S ∩ locs ( tm_exit ;; t)%T) with (∅:gset loc) by set_solver.
  iApply wp_let_noclean.
  iApply (wp_mono with "[-Hwp X]").
  { iApply (wp_exit with "[$]"). }
  iIntros (?) "(->&?) _".
  iSpecialize ("Hwp" with "[$][%//][$]").
  iApply (wp_mono with "[$]"). iIntros (?) "(?&?&?)". iFrame.
Qed.

(* XXX too many conseq... And what to do with the crit? *)
Lemma wpc_fconseq_with_souvenir_Some (A:Type) (EA:Enc A) E π P Q r t (φ:A -> iProp Σ):
  (∀ k, ⌜dom k = r⌝ -∗ PBT {[π]} k -∗ P =[ E | true | π | locs t ]=∗ PBT {[π]} k ∗ Q ) -∗
  (outside π -∗ P ∗ ( Q -∗ outside π ∗ wpc E π (Some r) t φ)) -∗
  wpc E π (Some r) t φ.
Proof.
  iIntros "HS E ? % % X".
  iDestruct ("E" with "[$]") as "(HP&HQ)".
  iSpecialize ("HS" with "[%//][$]").
  iApply (wp_fconseq with "[$][HQ][$]").
  iIntros "(?&?)". iDestruct ("HQ" with "[$]") as "(?&HQ)".
  iApply ("HQ" with "[$][%//][$]").
Qed.

Lemma wpc_fconseq_with_souvenir_None (A:Type) (EA:Enc A) E π P Q t (φ:A -> iProp Σ):
  (P =[ E | false | π | locs t ]=∗ Q ) -∗
  (outside π -∗ P ∗ ( Q -∗ outside π ∗ wpc E π None t φ)) -∗
  wpc E π None t φ.
Proof.
  iIntros "HS E ?".
  iDestruct ("E" with "[$]") as "(HP&HQ)".
  iApply (wp_fconseq with "[$][HQ][$]").
  iIntros "?". iDestruct ("HQ" with "[$]") as "(?&HQ)".
  iApply ("HQ" with "[$]").
Qed.

Lemma wpc_fconseq_with_souvenir (A:Type) (EA:Enc A) E π P Q r t (φ:A -> iProp Σ):
  ( P =[ E | true | π | locs t ∖ r ]=∗ Q ) -∗
  P ∗ (Q -∗ wpc E π (Some r) t φ) -∗
  wpc E π (Some r) t φ.
Proof.
  iIntros "HU HP".
  iApply (wpc_fconseq_with_souvenir_Some with "[HU] [HP]").
  { iIntros (k Hk) "HPBT HP". iIntros.
    rewrite (split_map k r) //.
    iDestruct (PBT_split with "[$]") as "(Hr&Hr')".
    rewrite -PBT_union. iFrame "Hr'".
    iApply (sfupd_weak_visibles with "[HU] [Hr HP] [%//] [$]").
    { rewrite dom_restrict. replace (dom k ∩ r) with r by set_solver. iFrame. }
    iFrame. iExact "HP". set_solver. }
  iIntros. iDestruct "HP" as "(?&?)". iFrame.
Qed.

Lemma wpc_fconseq (A:Type) (EA:Enc A) E π P Q r t (φ:A -> iProp Σ):
  (P =[ E | is_some r | π | locs t ∖ set_of_option r ]=∗ Q) -∗
  P ∗ (Q -∗ wpc E π r t φ) -∗
  wpc E π r t φ.
Proof.
  iIntros "HS (X&HP)". destruct r.
  { iApply (wpc_fconseq_with_souvenir with "HS").
    iFrame. }
  { iApply (wpc_fconseq_with_souvenir_None _ _ _ _ P Q with "[HS] [-]").
    { simpl. rewrite difference_empty_L //. }
    { iIntros "?". iFrame. } }
Qed.

Lemma wpc_conseq (A:Type) (EA:Enc A) E π P Q r t (φ:A -> iProp Σ):
  (P =[ is_some r | π | locs t ∖ set_of_option r  ]=∗ Q) -∗
  P ∗ (Q -∗ wpc E π r t φ) -∗
  wpc E π r t φ.
Proof.
  iIntros "HP ?".
  iApply (wpc_fconseq with "[HP][$]").
  iApply supd_sfupd. iFrame.
Qed.

Lemma wpc_exfalso (A:Type) (EA:Enc A) E π P r t (φ:A -> iProp Σ):
  (P =[ is_some r | π | locs t ]=∗ False) -∗
  (outside π -∗ P) -∗
  wpc E π r t φ.
Proof.
  iIntros "H1 HP".
  destruct r.
  { iApply (wpc_fconseq_with_souvenir_Some _ _ _ _ P False%I with "[H1]").
    { iIntros. iIntros "?". iIntros. iMod ("H1" with "[$][%//][$]") as "(?&?)". by iFrame. }
    iIntros. iSpecialize ("HP" with "[$]"). iFrame. iIntros. easy. }
  { iApply (wpc_fconseq_with_souvenir_None _ _ _ _ P False%I with "[H1]").
    { iIntros. iIntros "?". iIntros. iMod ("H1" with "[$][%//][$]") as "(?&?)". by iFrame. }
    iIntros. iSpecialize ("HP" with "[$]"). iFrame. iIntros. easy. }
Qed.

Lemma wpc_exfalso_dag_souvenir l (A:Type) (EA:Enc A) E π r t (φ:A -> iProp Σ):
  l ∈ r ->
  †l -∗
  wpc E π (Some r) t φ.
Proof.
  iIntros (?) "Hl ? %% ?".
  assert (l ∈ dom k) as Hl.
  { set_solver. }
  apply elem_of_dom in Hl. destruct Hl as (?,?).
  iDestruct (PBT_borrow_pbt l with "[$]") as "(?&?)".
  eauto.
  iDestruct (confront_pbt_dag with "[$]") as "?". easy.
Qed.

Lemma wpc_tconseq (A:Type) (EA:Enc A) E π P Q r t (φ:A -> iProp Σ):
  (P =[#]=∗ Q) -∗
  P ∗ (Q -∗ wpc E π r t φ) -∗
  wpc E π r t φ.
Proof.
  iIntros "HP ?".
  iApply (wpc_conseq with "[HP][$]").
  iApply tupd_supd. iFrame.
Qed.

Lemma wpc_atomic (A:Type) (EA:Enc A) E1 E2 π r t (Q:A -> iProp Σ) :
  Atomic t ∨ is_Some (to_val t) ->
  (|={E1,E2}=> wpc E2 π r t (fun (v:A) => |={E2,E1}=> Q v )) ⊢ wpc E1 π r t Q.
Proof.
  iIntros (?) "Hwp ?".
  destruct r; first iIntros (??) "?".
  all: iApply (wp_atomic E1 E2); eauto; iMod "Hwp"; iModIntro.
  { iSpecialize ("Hwp" with "[$][%//][$]").
    iApply (wp_mono with "[$]"). iIntros (?) "(?&?&[% (->&>?)])".
    iFrame. iModIntro. iExists _. by iFrame. }
  { iSpecialize ("Hwp" with "[$]").
    iApply (wp_mono with "[$]"). iIntros (?) "(?&[% (->&>?)])".
    iFrame. iModIntro. iExists _. by iFrame. }
Qed.

Lemma wpc_frame_step (A:Type) (EA:Enc A) P E π r t (Q:A -> iProp Σ) :
  (to_val t = None) ->
  ▷ P -∗ wpc E π r t (fun v => P -∗ Q v) -∗ wpc E π r t Q.
Proof.
  iIntros (?) "? Hwpc ?".
  destruct r; first iIntros (??) "?".
  all:iApply (wp_frame_step with "[$]"); try easy.
  { iSpecialize ("Hwpc" with "[$][%//][$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&?&[%(->&Hf)]) Hp". iFrame.
    iExists _. iSplitR; first done. by iApply "Hf". }
  { iSpecialize ("Hwpc" with "[$]").
    iApply (wp_mono with "[$]").
    iIntros (?) "(?&[%(->&Hf)]) Hp". iFrame.
    iExists _. iSplitR; first done. by iApply "Hf". }
Qed.

End Wpc.

Global Opaque wpc.

Global Instance is_except_0_wp `{!interpGS sz Σ}  A (EA:Enc A) E π r t (Q:A -> iProp Σ) :
  IsExcept0 (wpc E π r t Q).
Proof. by rewrite /IsExcept0 -{2}fupd_wpc -except_0_fupd -fupd_intro. Qed.

Global Instance elim_modal_bupd_wpc `{!interpGS sz Σ} (A:Type) (EA:Enc A) E π r t p P (Q:A -> iProp Σ) :
  ElimModal True p false (|==> P) P (wpc E π r t Q) (wpc E π r t Q).
Proof.
  by rewrite /ElimModal bi.intuitionistically_if_elim
       (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wpc.
Qed.

Global Instance elim_modal_fupd_wpc `{!interpGS sz Σ} (A:Type) (EA:Enc A) E π r t p P (Q:A -> iProp Σ) :
  ElimModal True p false
    (|={E}=> P) P
    (wpc E π r t Q) (wpc E π r t Q)%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  rewrite fupd_frame_r bi.wand_elim_r fupd_wpc //.
Qed.

Global Instance elim_modal_fupd_wpc_atomic `{!interpGS sz Σ} (A:Type) (EA:Enc A) E1 E2 π r t p P (Q:A -> iProp Σ) :
  ElimModal (Atomic t ∨ is_Some (to_val t)) p false
    (|={E1,E2}=> P) P
    (wpc E1 π r t Q) (wpc E2 π r t (fun v => |={E2,E1}=> Q v ))%I | 100.
Proof.
  intros ?.
  by rewrite bi.intuitionistically_if_elim
       fupd_frame_r bi.wand_elim_r wpc_atomic.
Qed.

Global Instance add_modal_fupd_wpc `{!interpGS sz Σ} (A:Type) (EA:Enc A) E π r t P (Q:A -> iProp Σ) :
  AddModal (|={E}=> P) P (wpc E π r t Q).
Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wpc. Qed.

Global Instance elim_acc_wpc_atomic `{!interpGS sz Σ} {X} (A:Type) (EA:Enc A) E1 E2 π r α β γ t (Q:A -> iProp Σ) :
  ElimAcc (X:=X) (Atomic t ∨ is_Some (to_val t))
    (fupd E1 E2) (fupd E2 E1)
    α β γ (wpc E1 π r t Q)
    (λ x, wpc E2 π r t (fun v => |={E2}=> β x ∗ (γ x -∗? Q v)))%I | 100.
Proof.
  iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iSpecialize ("Hinner" with "[$]").
  iApply (wpc_mono with "[$]").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.

Global Instance elim_acc_wpc_nonatomic `{!interpGS sz Σ} {X} (A:Type) (EA:Enc A) E π r α β γ t (Q:A -> iProp Σ) :
  ElimAcc (X:=X) True (fupd E E) (fupd E E)
    α β γ (wpc E π r t Q)
    (λ x, wpc E π r t (fun v => |={E}=> β x ∗ (γ x -∗? Q v)))%I .
Proof.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iApply wpc_fupd.
  iSpecialize ("Hinner" with "[$]").
  iApply (wpc_mono with "[$]").
  iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
Qed.
