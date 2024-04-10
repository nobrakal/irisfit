From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl.

From irisfit.examples Require Import proofmode.
From irisfit.examples.toolbox Require Import spawn_join.

Definition new_lock : val :=
  λ: [[]],
    let: "r" := alloc ^1 in
    "r".[0] <- ^0;;
    "r".

Definition try_acquire : val :=
  λ: [["r"]],
    tm_cas "r" 0 0 1.

Definition acquire : val :=
  μ: "self", [["r"]],
      let: "b" := try_acquire [["r"]] in
      if: "b"
      then val_unit
      else "self" [["r"]].

Definition release : val :=
  λ: [["r"]], "r".[0] <- 0.

Class lockG Σ := LockG { lock_tokG : inG Σ (exclR unitO) }.
Local Existing Instance lock_tokG.

Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section Spin_lock.
Context `{!interpGS0 Σ, !lockG Σ}.
Context (N : namespace).

Definition lock_inv (γ:gname) (l:loc) (R:iProp Σ) : iProp Σ :=
  ∃ b:Z, l ↦ [val_int b] ∗ (if (decide (b≠0)) then True else (own γ (Excl ()) ∗ R)).

Definition is_lock (γ : gname) (l:loc) (R : iProp Σ) : iProp Σ :=
  inv N (lock_inv γ l R).

Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
Proof. solve_proper. Qed.
Global Instance is_lock_contractive γ l : Contractive (is_lock γ l).
Proof. solve_contractive. Qed.

Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
Proof. apply _. Qed.
Global Instance locked_timeless γ : Timeless (locked γ).
Proof. apply _. Qed.

Lemma new_lock_spec i (R:iProp Σ) :
  CODE (new_lock [[]])
  TID i
  PRE (♢1 ∗ R)
  POST (fun l => ∃ γ, is_lock γ l R ∗ l ↤ ∅ ∗ l ⟸ {[i]}).
Proof.
  iIntros "(? & HR)".

  wpc_call.
  wpc_let_noclean.

  wpc_alloc. iIntros.
  wpc_let_noclean.

  iStep 6 as ([]) "H1 H2 H3 H4".

  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (inv_alloc N _ (lock_inv γ _ R) with "[HR H4 Hγ]") as "?".
  { iSteps. }

  iSmash.
Qed.

Lemma try_acquire_spec i γ l R :
  CODE (try_acquire [[l]])
  TID i
  PRE (is_lock γ l R)
  POST (fun (b:bool) => if b then locked γ ∗ R  else True).
Proof.
  iIntros "#Hi".

  wpc_call.

  iInv "Hi" as (?) "(>E & R)". solve_atomic.

  iApply (wpc_frame_step with "[$]"). easy.

  destruct (decide (b=0)); subst.
  { wpc_apply wpc_cas_suc. 1-3:naive_solver.
    iIntros (?) "(-> & ?) ?".
    iSmash. }
  { wpc_apply wpc_cas_fail. 1-3:naive_solver.
    iSmash. }
  Unshelve. exact 0.
Qed.

Lemma acquire_spec i γ l R :
  CODE (acquire [[l]])
  TID i SOUV {[l]}
  PRE (is_lock γ l R)
  POST (fun _:unit => locked γ ∗ R).
Proof.
  iIntros "#I".

  iLöb as "IH".
  wpc_call.
  wpc_let_empty.

  iApply (wpc_frame_step with "IH"). easy.
  iClear "IH".

  wpc_apply try_acquire_spec. set_solver. iFrame "#".

  iIntros (b) "? IH". simpl; rew_enc.

  wpc_if.
  destruct b. iSmash. iFrame.
Qed.

Lemma release_spec i γ l R :
  CODE (release [[l]])
  TID i
  PRE (is_lock γ l R ∗ locked γ ∗ R)
  POST (fun _:unit => True).
Proof.
  iIntros "(#I & ? & ?)".
  wpc_call.

  iInv "I" as (b) "(>I1 & I2)". solve_atomic.

  case_decide; iSmash.
Qed.

Lemma free_lock γ b l R i V :
  is_lock γ l R ∗ l ↤ ∅ ∗ l ⟸ ∅ =[⊤|b|i|V]=∗ ♢1.
Proof.
  iIntros "(#I & ? & ?)".
  iIntros.
  iInv "I" as (b') "(>E & ?)".
  iMod (interp_free' with "[$][$]") as "(?&?&?& #?)".
  iSmash.
Qed.

End Spin_lock.
