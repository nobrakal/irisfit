From iris.base_logic.lib Require Export invariants.
From iris.algebra.lib Require Import frac_auth.
From iris.bi.lib Require Export atomic.
From iris Require Import gen_heap.

From irisfit.examples Require Import proofmode faa.
From irisfit.examples Require Export ref counter_code ignore.

(* ------------------------------------------------------------------------ *)
(* The camera we need
   From Library iris.heap_lang.lib.counter *)

Class ccounterG Σ :=
  CCounterG { ccounter_inG : inG Σ (frac_authR natR) }.
Local Existing Instance ccounter_inG.

Definition ccounterΣ : gFunctors :=
  #[GFunctor (frac_authR natR)].

Global Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Section Counter.
Context `{interpGS0 Σ, ccounterG Σ}.
Context (N:namespace).

(* ------------------------------------------------------------------------ *)
(* Invariants *)

Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
  ∃ n, own γ (●F n) ∗ (isRef n l).
Definition ccounter_ctx (γ : gname) (l : loc) : iProp Σ :=
  inv N (ccounter_inv γ l).

Definition ccounter (γ : gname) (q : frac) (n : nat) : iProp Σ :=
  own γ (◯F{q} n).
Lemma ccounter_op γ q1 q2 n1 n2 :
    ccounter γ (q1 + q2) (n1 + n2) ⊣⊢ ccounter γ q1 n1 ∗ ccounter γ q2 n2.
Proof. rewrite /ccounter frac_auth_frag_op -own_op //. Qed.


Definition get_clo_spec γ (l _:loc)  (_:list val) (t:tm) : iProp Σ :=
  ∀ i q (n:nat), ccounter_ctx γ l ∗ ccounter γ q n -∗
    wpc ⊤ i (Some {[l]}) t (fun (m:Z) => ⌜if decide (q=1%Qp) then n=Z.to_nat m else n <= Z.to_nat m⌝ ∗ ccounter γ q n).

Definition incr_clo_spec γ (l _:loc) (_:list val) (t:tm): iProp Σ :=
  ∀ i q (n:nat), ccounter_ctx γ l ∗ ccounter γ q n -∗
     wpc ⊤ i (Some {[l]}) t (fun (_:unit) => ccounter γ q (S n)).

Lemma prove_incr_clo_spec l γ r qp vs :
  Spec 0 [(#r,qp)%V] (incr_clo_spec γ r) l -∗
  incr_clo_spec γ r l  vs
    (ignore [faa [[r,0,1]]])%T.
Proof.
  iIntros. iIntros (???) "(#?&Hf)".

  iApply ignore_spec.
  iApply wpc_convertible.
  iApply faa_spec_weak. 1,2:done.
  iAuIntro.
  iInv N as (c') ">(Ha&Hl)".
  unshelve iAaccIntro with "[Hl]"; first (by exists [val_int c'],c').
  { by iFrame. }
  { iSmash. }
  Unshelve. 2:apply _.

  simpl.
  iIntros "(?&Hr&_)".
  iMod (own_update_2 with "Ha Hf") as "(Ha&Hf)".
  { apply frac_auth_update. apply (nat_local_update _ _ (c' + 1) (S n)). lia. }

  rewrite Nat.add_1_r.
  replace (1%nat + c' : Z)%Z with (S c' : Z)%Z by lia. iSmash.
Qed.


Definition counter_nm := nroot.@"counter".

(* The actual counter representation predicate. *)
Definition IsCounter (p:Qp) (n:nat) (fi fg : loc) : iProp Σ :=
  ∃ γ l,
    (* The counter invariant *)
    ccounter_ctx γ l ∗
    (* The counter share we currently hold *)
    ccounter γ p n ∗
    l ⟸{p} ∅ ∗
    (* A meta on l allowing to abstract γ *)
    meta fi counter_nm (γ,l) ∗
    (* The Spec of the fi closure *)
    Spec 0 [(#l,(1/2)%Qz)]%V (incr_clo_spec γ l) fi ∗
    (* The Spec of the fg closure *)
    Spec 0 [(#l,(1/2)%Qz)]%V (get_clo_spec γ l) fg.

Lemma mk_counter_spec π :
  CODE (mk_counter [])
  TID π
  PRE (♢ 7)
  POST (fun l:loc =>
    (* We return a tuple *)
    ∃ (fi fg:loc), l ↦ [val_loc fi;val_loc fg] ∗ l ⟸ {[π]} ∗ l ↤ ∅ ∗
    (* fi & fg are abstract locations. *)
    fi ⟸ ∅ ∗ fi ↤ {[+l+]} ∗
    fg ⟸ ∅ ∗ fg ↤ {[+l+]} ∗
    (* fi & fg form a counter, with fraction 1, initialized to 0 *)
    IsCounter 1 0 fi fg).
Proof.
  iIntros.
  wpc_call.  wpc_let_empty.
  mine 1.
  wpc_apply ref_spec_no_loc. 1-2:naive_solver.

  iIntros (l) "(Hl & ? & ?&?)". rew_enc. simpl.
  iApply wpc_postpone.
  iApply (wpc_context_vsingleton (val_loc l) with "[$]").

  iAssert (|={⊤}=> ∃ γ, ccounter_ctx γ l ∗ ccounter γ 1 0)%I with "[Hl]" as ">[%γ (? & ?)]".
  { iMod (own_alloc (●F O ⋅ ◯F 0)) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid_discrete.
    iMod (inv_alloc N _ (ccounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0. by iFrame. }
    iSmash. }

  wpc_let_empty.
  mine 2.
  iDestruct (mapsfrom_split_half_empty with "[$]") as "(?&?)".

  wpc_apply (wpc_mk_spec π (incr_clo_spec γ l) [("r", val_loc l)] [1/2]%Qz). set_solver.
  1-4:compute_done.
  { simpl. iModIntro. iIntros.
    iApply (prove_incr_clo_spec with "[$]"). }
  simpl. rewrite /group_pointedbys. rew_qz. iFrame. rewrite left_id.
  iIntros (fi) "(?&Efi&Hfi&?)".
  rewrite (subst_not_in "incr"); last by vm_compute.

  rewrite pbt_PBT.
  iApply (wpc_let with "Hfi").
  { auto_locs. set_solver. }
  mine 2.
  wpc_apply (wpc_mk_spec π (get_clo_spec γ l) [("r", val_loc l)] [1/2]%Qz). set_solver.
  1-4:compute_done.
  { simpl. iModIntro.
    iIntros. iIntros (???) "(?&?)".
    destruct (decide (q=1)%Qp); subst.
    { iInv N as (c) "E". solve_atomic.
      iApply fupd_wpc. iMod "E" as "(? & Hr)". iModIntro.
      iDestruct (own_valid_2 with "[$] [$]") as "%Hv".
      apply frac_auth_agree_L in Hv. subst.
      wpc_load_no_loc; eauto. iSmash. }
    { iInv N as (c) "E". solve_atomic.
      iApply fupd_wpc. iMod "E" as "(? & Hr)". iModIntro.
      iDestruct (own_valid_2 with "[$] [$]") as "%Hv".
      apply frac_auth_included_total in Hv. apply nat_included in Hv.
      wpc_load_no_loc; eauto. iSmash. } }
  simpl. rewrite left_id.
  rew_qz. iFrame. simpl.

  iMod (meta_set _ fi (γ,l) counter_nm with "[$]").
  { solve_ndisj. }

  iIntros (fg) "(?&Efg&?&_) ?".

  wpc_let_noclean.
  wpc_alloc.
  iIntros (b) "(?&?&?&_)". simpl.

  wpc_let_noclean. wpc_store. iIntros "(?&?&?)".
  wpc_let_noclean. wpc_store. iIntros "(?&?&?)".
  simpl. rewrite left_id right_id_L.

  iApply wpc_val. iIntros. rewrite -pbt_PBT.

  iDestruct (confront_pbt_pbt b l with "[$]") as "%".
  by vm_compute.
  iDestruct (confront_pbt_vpbt b fi with "[$]") as "%".
  by vm_compute.
  iDestruct (confront_pbt_vpbt b fg with "[$]") as "%".
  by vm_compute.

  pclean l. pclean fi. pclean fg.

  iSmash.
Qed.

Lemma get_spec π p n fi fg :
  CODE (call_clo fg [[]])
  TID π
  PRE (IsCounter p n fi fg)
  POST (fun m => ⌜if decide (p = 1%Qp) then n = Z.to_nat m else n ≤ Z.to_nat m⌝ ∗ IsCounter p n fi fg).
Proof.
  iIntros "[% [% (#?&?&Hl&#?&#?&#Hfg)]]".
  papprox l with "Hl". simpl. rewrite pbt_PBT.
  iApply (wpc_call_spec_tac with "Hfg [$]").
  1-2:compute_done. set_solver.
  iModIntro. iIntros (?) "_ ? Hs". simpl.
  rewrite -pbt_PBT.
  iApply wpc_postpone. iApply (wpc_context_singleton l with "[$]"). rewrite right_id_L.
  iSpecialize ("Hs" with "[$]").
  iApply (wpc_mono with "[$]").
  iIntros (?) "(?&?) ?". pclean l. wpc_val. iFrame. iSmash.
Qed.

Lemma incr_spec π p n fi fg :
  CODE (call_clo fi [[]])
  TID π
  PRE (IsCounter p n fi fg)
  POST (fun (_:unit) => IsCounter p (S n) fi fg).
Proof.
  iIntros "[% [% (#?&?&?&#?&#Hfi&#?)]]".
  papprox l. simpl. rewrite pbt_PBT.
  iApply (wpc_call_spec_tac with "Hfi [$]").
  1-2:compute_done. set_solver.
  iModIntro. iIntros (?) "_ ? Hs". simpl.
  rewrite -pbt_PBT.
  iApply wpc_postpone. iApply (wpc_context_singleton l with "[$]"). rewrite right_id_L.
  iSpecialize ("Hs" with "[$]").
  iApply (wpc_mono with "[$]").
  iIntros (?) "? ?". pclean l. wpc_val. iSmash.
Qed.

Lemma IsCounter_split p1 p2 n1 n2 fi fg :
  IsCounter (p1+p2) (n1+n2) fi fg -∗
  IsCounter p1 n1 fi fg ∗ IsCounter p2 n2 fi fg.
Proof.
  iIntros "[% [% (#?&Hc&(?&?)&#?&?&?)]]".
  rewrite ccounter_op. iDestruct "Hc" as "(?&?)".
  iSteps.
Qed.

Lemma IsCounter_join p1 p2 n1 n2 fi fg :
  IsCounter p1 n1 fi fg ∗ IsCounter p2 n2 fi fg -∗
  IsCounter (p1+p2) (n1+n2) fi fg.
Proof.
  iIntros "([% [% (#?&?&?&#H1&Hi1&?)]]&[% [% (#?&?&?&#H2&Hi2&?)]])".
  iDestruct (meta_agree with "H1 H2") as "%Eq". inversion Eq. subst γ0 l0.
  iDestruct (ccounter_op with "[$]") as "?".
  iDestruct (pbt_join with "[$]") as "?". rewrite left_id_L.
  rewrite (comm_L _ p2) (comm_L _ n2).
  iSteps.
Qed.

Lemma counter_free n fi fg b π V :
  IsCounter 1 n fi fg ∗
  fi ⟸ ∅ ∗ fi ↤ ∅ ∗
  fg ⟸ ∅ ∗ fg ↤ ∅
  =[ ⊤ | b | π | V ]=∗
  ♢5.
Proof.
  iIntros "([% [% (?&?&?&?&?&?)]]&?&?&?&?)".
  iIntros.

  iMod (spec_free with "[$][%//][$]") as "(?&?&(?&_)&_)".
  iMod (spec_free with "[$][%//][$]") as "(?&?&(?&_)&_)".

  iDestruct (mapsfrom_join with "[$] [$]") as "?".
  rewrite Qz_div_2 left_id.

  iInv N as (c) ">(?&Hr)".

  iMod (interp_free' with "[$][$]") as "(?&?&?&#?)".

  do 2 (iDestruct (diamonds_join with "[$]") as "?"). rew_qz.
  iSmash.
Qed.

End Counter.
