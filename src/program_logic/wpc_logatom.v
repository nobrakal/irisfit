From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From iris.base_logic.lib Require Import invariants.
From stdpp Require Import gmap gmultiset.

From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic.

From irisfit.lib Require Import qz smultiset.
From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language.

From irisfit.program_logic Require Import more_space_lang more_maps_and_sets.
From irisfit.program_logic Require Import interp pbt wpc triple.

Definition atomic_wpc `{interpGS sz Σ} {TA TB: tele} {A:Type} {EA:Enc A}
  (tid:thread_id) (r:option (gset loc)) (t:tm)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (post : A -> TA -> TB -> iProp Σ) (* private post. *)
  (β: TA → TB -> iProp Σ) (* atomic post-condition *)
  : iProp Σ :=
  ∀ (Φ : A → iProp Σ),
    atomic_update (⊤∖E) ∅ α β (λ.. x y, ∀ z, post z x y -∗ Φ z) -∗
    wpc ⊤ tid r t Φ.

Notation "'ACODE' t 'TID' tid 'WITH' E 'SOUV' r '<<<' P '|' ∀∀ x1 .. xn , α '>>>' '<<<' ∃∃ y1 .. yn , β '|' Q '>>>'" :=
   (P -∗ atomic_wpc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    tid (Some r) t E
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (fun v => tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, (Q v)%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
  )
    (at level 20, α, β at level 200, x1 binder, xn binder, y1 binder, yn binder)
    : triple_scope.

Notation "'ACODE' t 'TID' tid 'WITH' E 'SOUV' r '<<<' P '|' ∀∀ x1 .. xn , α '>>>' '<<<' β '|' Q '>>>'" :=
  (P -∗ atomic_wpc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
   (TB:=TeleO)
   tid (Some r) t E
   (tele_app $ λ x1, .. (λ xn, α%I) ..)
   (fun v => tele_app $ λ x1, .. (λ xn, tele_app (Q v)%I) .. )
   (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
  )
    (at level 20, α, β at level 200, x1 binder, xn binder)
    : triple_scope.

Notation "'ACODE' t 'TID' tid 'WITH' E 'SOUV' r '<<<' P '|' α '>>>' '<<<' β '|' Q '>>>'" :=
  (P -∗ atomic_wpc (TA:=TeleO) (TB:=TeleO)
   true tid r t E
   (tele_app α%I)
   (tele_app $ tele_app Q%I)
   (tele_app $ tele_app β%I))
    (at level 20, α, β at level 200)
    : triple_scope.

Section Wpc_logatom.
Context `{interpGS sz Σ}.

(* Atomic triples imply sequential triples. *)
Local Lemma atomic_wpc_seq {TA TB : tele} (A:Type) (EA:Enc A) tid r t E post (α: TA → iProp Σ) (β: TA → TB → iProp Σ)
  `{forall Lα, Laterable (α Lα)} (* This hypothesis drops in iris 4.0 *)
  :
  atomic_wpc tid r t E α post β -∗
  ∀ (Φ : A -> iProp Σ), ∀.. x, α x -∗ (∀.. y, ∀ z, post z x y -∗ β x y -∗ Φ z) -∗ wpc ⊤ tid r t Φ.
Proof.
  iIntros "Hwp" (Φ x) "Hα Hβ".
  iApply (wpc_frame_wand with "Hβ").
  iApply "Hwp".
  iAuIntro.
  iAaccIntro with "Hα". eauto.
  iIntros (y) "Hβ !>".
  rewrite ->!tele_app_bind. iIntros (?) "Hp HΦ".
  iApply ("HΦ" with "[$]"). done.
Qed.

(* We can open invariants around atomic triples. *)
Local Lemma atomic_wpc_inv {TA TB : tele} (A:Type) (EA:Enc A) tid r t E post (α: TA → iProp Σ) (β: TA → TB → iProp Σ) N I :
  ↑N ⊆ E →
  atomic_wpc tid r t (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) post (λ.. x y, ▷ I ∗ β x y) -∗
  inv N I -∗ atomic_wpc tid r t E α post β.
Proof.
  intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
  iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
  iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
  - (* abort *)
    iIntros "[HI $]". by eauto with iFrame.
  - (* commit *)
    iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
    iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
Qed.

End Wpc_logatom.
