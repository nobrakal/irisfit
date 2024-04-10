From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language closure notation.
From irisfit Require Import more_space_lang more_maps_and_sets.
From irisfit Require Export interp.

From irisfit Require Import interp  wp_call wp_load wp_store.

(******************************************************************************)

Class Enc (A:Type) := enc : A -> val.
Global Instance Enc_unit : Enc unit := fun _ => val_unit.
Global Instance Enc_int : Enc Z := val_int.
Global Instance Enc_loc : Enc loc := val_loc.
Global Instance Enc_bool : Enc bool := val_bool.
Global Instance Enc_val : Enc val := id.

Lemma enc_unit (x:unit) :
  enc x = val_unit.
Proof. easy. Qed.
Global Instance inj_enc_unit : @Inj unit val (=) (=) enc.
Proof. intros [] [] ?. easy. Qed.

Lemma enc_int (x:Z) :
  enc x = val_int x.
Proof. easy. Qed.
Global Instance inj_enc_nat : @Inj Z val (=) (=) enc.
Proof. intros ? ? E. injection E. easy. Qed.

Lemma enc_loc (x:loc) :
  enc x = val_loc x.
Proof. easy. Qed.
Global Instance inj_enc_loc : @Inj loc val (=) (=) enc.
Proof. intros ? ? E. injection E. easy. Qed.

Lemma enc_bool (x:bool) :
  enc x = val_bool x.
Proof. easy. Qed.
Global Instance inj_enc_bool : @Inj bool val (=) (=) enc.
Proof. intros ? ? E. injection E. easy. Qed.

Lemma enc_val (x:val) :
  enc x = x.
Proof. easy. Qed.
Global Instance inj_enc_val : @Inj val val (=) (=) enc.
Proof. intros ? ? ?. easy. Qed.

Ltac rew_enc_step tt :=
  first [ rewrite enc_unit
        | rewrite enc_int
        | rewrite enc_loc
        | rewrite enc_val ].

Ltac rew_enc_core tt :=
  repeat (rew_enc_step tt).

Tactic Notation "rew_enc" :=
  rew_enc_core tt.

(******************************************************************************)

Definition post `{Enc A} {Σ : gFunctors} (Q:A -> iProp Σ) : val -> iProp Σ :=
  fun v => (∃ a, ⌜v = enc a⌝ ∗ Q a)%I.

Lemma post_inj `{Enc A} `{Inj A val (=) (=) enc} {Σ : gFunctors} (Q:A -> iProp Σ) :
  forall v, post Q (enc v) ≡ Q v.
Proof.
  intros v.
  iSplit.
  { iIntros "[% [%E ?]]". rewrite inj_iff in E. subst. easy. }
  { iIntros. iExists _.  eauto. }
Qed.

Lemma post_val {Σ : gFunctors} (Q:val -> iProp Σ) :
  forall v, post Q v ≡ Q v.
Proof. intros v. rewrite -(enc_val v) post_inj //. Qed.

Lemma post_unit {Σ : gFunctors} (Q:unit -> iProp Σ) :
  post Q val_unit ≡ Q tt.
Proof. rewrite -(enc_unit tt) post_inj //. Qed.

Lemma post_nat {Σ : gFunctors} (Q:Z -> iProp Σ) :
  forall n, post Q (val_int n) ≡ Q n.
Proof. intros n. rewrite -(enc_int n) post_inj //. Qed.

Lemma post_bool {Σ : gFunctors} (Q:bool -> iProp Σ) :
  forall b, post Q (val_bool b) ≡ Q b.
Proof. intros n. rewrite -(enc_bool _) post_inj //. Qed.

Lemma post_loc {Σ : gFunctors} (Q:loc -> iProp Σ) :
  forall l, post Q (val_loc l) ≡ Q l.
Proof. intros l. rewrite -(enc_loc l) post_inj //. Qed.

#[export] Hint Rewrite @post_val @post_unit @post_nat @post_loc : rew_post.

(******************************************************************************)

Lemma post_strong_mono `{invGS Σ} (A:Type) (EA:Enc A) E1 E2 (Q Q':A -> iProp Σ) (v:val) :
  E1 ⊆ E2 ->
  (∀ a, Q a ={E1}=∗ Q' a) -∗
  post Q v ={E2}=∗ post Q' v.
Proof.
  iIntros (?) "Hq [%a [%E Ha]]". subst.
  iExists _. iSplitR; first easy.
  iMod (fupd_mask_subseteq E1). eauto.
  iMod ("Hq" with "[$]").
  by iFrame.
Qed.

Lemma post_strong_mono' {Σ : gFunctors} (A:Type) (EA:Enc A) (Q Q':A -> iProp Σ) (v:val) :
  (∀ a, Q a ==∗ Q' a) -∗
  post Q v ==∗ post Q' v.
Proof.
  iIntros "Hq [%a [%E Ha]]". subst.
  iExists _. iSplitR; first easy.
  iApply "Hq". by iFrame.
Qed.

Lemma post_mono {Σ : gFunctors} (A:Type) (EA:Enc A) (Q Q':A -> iProp Σ) (v:val) :
  (∀ a, Q a -∗ Q' a) -∗
  post Q v -∗ post Q' v.
Proof.
  iIntros "Hq [%a [%E ?]]". subst.
  iExists _. iSplitR; try easy.
  iApply "Hq". easy.
Qed.

Lemma post_mono_val {Σ : gFunctors} (A:Type) (EA:Enc A) (Q:A -> iProp Σ) (Q':val -> iProp Σ) (v:val) :
  (∀ a, Q a -∗ Q' (enc a)) -∗
  post Q v -∗ post Q' v.
Proof.
  iIntros "Hq [%a [%E ?]]". subst.
  iExists _. iSplitR; try easy.
  iApply "Hq". easy.
Qed.
