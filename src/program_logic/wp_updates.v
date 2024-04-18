From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gset gmap auth csum.
From stdpp Require Import gmap fin_map_dom gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit Require Import more_maps_and_sets.
From irisfit Require Import disc interp_base.

Section Updates.
Context `{interpGS sz Σ}.

(* A fancy update, giving access to [interp]. *)
Definition vsfupd E1 E2 b i V P Q : iProp Σ :=
  P -∗ ∀ mt k e σ lk,
  ⌜k !! i = Some (lk,V)⌝ -∗
  interp mt b k e σ ={E1, E2}=∗ interp mt b k e σ ∗ Q.

Definition sfupd E b i V P Q : iProp Σ := vsfupd E E b i V P Q.

Local Notation "P =[ E | b | i | V ]=∗ Q" := (sfupd E b i V P Q)%I
 (at level 99, Q at level 200).

Lemma wp_fconseq E b i P Q t φ :
  (P =[ E | b | i | locs t ]=∗ Q) -∗
  (Q -∗ wp E b i t φ) -∗
  (P -∗ wp E b i t φ).
Proof.
  iIntros "Hs Hwp ?".
  rewrite wp_unfold.
  iIntros (??????) "(%&%) ?".
  iMod ("Hs" with "[$] [% //] [$]") as "[? ?]".
  iApply ("Hwp" with "[$] [%//] [$]").
Qed.

(* As stated in the paper  *)
Local Lemma wp_consequence E b π t Φ Φ' Ψ Ψ' :
  (Φ =[E | b | π | locs t ]=∗ Φ') -∗
  (∀ v, Ψ' v =[E | b | π | locs v ]=∗ Ψ v) -∗
  (Φ' -∗ wp E b π t Ψ') -∗
  (Φ -∗ wp E b π t Ψ).
Proof.
  iIntros "H1 H2 H3 H4".
  iApply wp_postpone. iApply (wp_fconseq with "H1 [-H4] H4").
  iIntros "H5". iSpecialize ("H3" with "H5").
  iApply (wp_mono with "H3"). iIntros (v) "H6".
  iSpecialize ("H2" $! v).
  iApply (wp_fconseq with "[H2]"). done. 2:done.
  iApply wp_val.
Qed.

Lemma sfupd_weak_mask E1 E2 b i V P Q :
  (E1 ⊆ E2) ->
  (P =[ E1 | b | i | V ]=∗ Q) -∗
  P =[ E2 | b | i | V ]=∗ Q.
Proof.
  iIntros (?) "HPQ P". iIntros.
  iMod (fupd_mask_subseteq E1) as "Hclose". eauto.
  iMod ("HPQ" with "[$][%//][$]").
  iMod "Hclose". by iFrame.
Qed.

Lemma vsfupd_weak_visibles E1 E2 b i V M P Q :
  (vsfupd E1 E2 b i (V ∖ dom M) P Q) -∗
  vsfupd E1 E2 b i V (PBT {[i]} M ∗ P) (PBT {[i]} M ∗ Q).
Proof.
  iIntros "HPQ".
  iIntros "(?&?)". iIntros.
  rewrite {2}(split_map M (dom M ∩ V)). 2:set_solver.
  iDestruct (PBT_split with "[$]") as "(?&?)".
  assert ((V ∖ (dom M ∩ V) ∪ dom M ∩ V) = V) as HV.
  { rewrite difference_union_L. set_solver. }
  iMod (@interp_shift _ _ _ _ _ _ _ _ _ _ (V ∖ (dom M ∩ V)) (dom M ∩ V) (restrict M (dom M ∩ V)) with "[$]") as "(?&Hb)".
  { rewrite HV. eauto. }
  { rewrite dom_restrict assoc_L idemp_L //. }
  iMod ("HPQ" with "[$][%][$]") as "(?&?)".
  { rewrite lookup_insert. f_equal. f_equal. set_solver. }
  iMod ("Hb" with "[%][%][$]") as "(?&?)".
  2:{ rewrite lookup_insert. f_equal. }
  { split_and !; eauto. apply upd_refl. }
  rewrite insert_insert HV insert_id //.
  iFrame. iDestruct (PBT_union with "[$]") as "?".
  rewrite -split_map. 2:set_solver. by iFrame.
Qed.


Lemma sfupd_weak_visibles E b i V M P Q :
  (P =[ E | b | i | (V ∖ dom M) ]=∗ Q) -∗
  (PBT {[i]} M ∗ P) =[ E | b | i | V ]=∗ (PBT {[i]} M ∗ Q).
Proof. iIntros. rewrite /sfupd. by iApply vsfupd_weak_visibles. Qed.

(* ------------------------------------------------------------------------ *)
(* supd allows a basic update of P to Q under access to interp. *)

(* LATER: derive from vsfupd? *)
Definition supd b i V P Q : iProp Σ :=
  P -∗ ∀ mt k e σ lk,
    ⌜k !! i = Some (lk,V)⌝ -∗
    interp mt b k e σ ==∗ interp mt b k e σ ∗ Q.

Local Notation "P =[ b | i | V ]=∗ Q" := (supd b i V P Q)%I (at level 99, Q at level 200).

Lemma supd_weak_visibles b i V M P Q :
  (P =[ b | i | (V ∖ dom M) ]=∗ Q) -∗
  (PBT {[i]} M ∗ P) =[ b | i | V ]=∗ (PBT {[i]} M ∗ Q).
Proof.
  iIntros "HPQ".
  iIntros "(?&?)". iIntros.
  rewrite {2}(split_map M (dom M ∩ V)). 2:set_solver.
  iDestruct (PBT_split with "[$]") as "(?&?)".
  assert ((V ∖ (dom M ∩ V) ∪ dom M ∩ V) = V) as HV.
  { rewrite difference_union_L. set_solver. }
  iMod (@interp_shift _ _ _ _ _ _ _ _ _ _ (V ∖ (dom M ∩ V)) (dom M ∩ V) (restrict M (dom M ∩ V)) with "[$]") as "(?&Hb)".
  { rewrite HV. eauto. }
  { rewrite dom_restrict assoc_L idemp_L //. }
  iMod ("HPQ" with "[$][%][$]") as "(?&?)".
  { rewrite lookup_insert. f_equal. f_equal. set_solver. }
  iMod ("Hb" with "[%][%][$]") as "(?&?)".
  2:{ rewrite lookup_insert. f_equal. }
  { split_and !; eauto. apply upd_refl. }
  rewrite insert_insert HV insert_id //.
  iFrame. iDestruct (PBT_union with "[$]") as "?".
  rewrite -split_map. 2:set_solver. by iFrame.
Qed.

Lemma supd_sfupd E b i P Q V:
  (P =[ b | i | V ]=∗ Q) -∗ (P =[ E | b | i | V ]=∗ Q).
Proof.
  iIntros "HPQ ?". iIntros.
  iMod ("HPQ" with "[$] [%//] [$]").
  by iFrame.
Qed.

Lemma wp_conseq E b i P Q t φ :
  (P =[b | i | locs t ]=∗ Q) -∗
  P ∗ (Q -∗ wp E b i t φ) -∗
  wp E b i t φ.
Proof.
  iIntros "HPQ (? & ?)".
  iApply (@wp_fconseq E b i P Q with "[HPQ][$][$]"). eauto.
  iApply supd_sfupd. iFrame.
Qed.

(* ------------------------------------------------------------------------ *)
(* tupd allows a fancy update of P to Q under access to interp, with
   less information *)

Definition tupd P Q : iProp Σ :=
  P -∗ ∀ mt b k e σ,
  interp mt b k e σ ==∗ interp mt b k e σ ∗ Q.

Local Notation "P =[#]=∗ Q" := (tupd P Q)%I (at level 99, Q at level 200).

Lemma tupd_supd b i P Q V:
  (P =[#]=∗ Q) -∗ (P =[ b | i | V ]=∗ Q).
Proof.
  iIntros "HP". iIntros "?". iIntros.
  iApply ("HP" with "[$][$]").
Qed.

Lemma wp_tconseq E b i P Q t φ :
  (P =[#]=∗ Q) -∗
  P ∗ (Q -∗ wp E b i t φ) -∗
  wp E b i t φ.
Proof.
  iIntros "HPQ ?".
  iApply (wp_conseq with "[HPQ] [$]").
  iApply tupd_supd. iFrame.
Qed.
End Updates.

Global Notation "P =[ E | b | i | V ]=∗ Q" := (⊢ sfupd E b i V P%I Q%I)
 (at level 99, Q at level 200, only parsing) : stdpp_scope.
Global Notation "P =[ E | b | i | V ]=∗ Q" := (sfupd E b i V P Q)%I
 (at level 99, Q at level 200) : bi_scope.

Global Notation "P =[ b | i | V ]=∗ Q" := (⊢ supd b i V P%I Q%I)
 (at level 99, Q at level 200, only parsing) : stdpp_scope.
Global Notation "P =[ b | i | V ]=∗ Q" := (supd b i V P Q)%I
 (at level 99, Q at level 200) : bi_scope.

Global Notation "P =[#]=∗ Q" := (⊢ tupd P%I Q%I)
 (at level 99, Q at level 200, only parsing) : stdpp_scope.
Global Notation "P =[#]=∗ Q" := (tupd P Q)%I
 (at level 99, Q at level 200) : bi_scope.
