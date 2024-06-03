From irisfit.examples Require Import proofmode treiber.
From irisfit.examples.sequential Require Import list.

(* This file introduces possibly bounded stacks and their specifications. *)

Definition size_lt n (c:option positive) :=
  match c with
  | Some c => n < Pos.to_nat c
  | None => True end.

(* Coq has trouble inferring things if I use an separated interp, and a separated
   "extended ghost state". So I bundle the two. *)
Class interpGSMore (Σ:gFunctors) : Set :=
  { mi1 : interpGS0 Σ;
    mi2 : stackG Σ
  }.

Global Existing Instances mi1 mi2.

Module Type StackOf.
  Parameter capacity : option positive.

  Parameter stack_empty : val.
  Parameter stack_push  : val.
  Parameter stack_pop   : val.
  Parameter stack_is_empty : val.
  Parameter stack_is_full  : val.

  Axiom locs_stack_empty : locs stack_empty = ∅.
  Axiom locs_stack_push  : locs stack_push  = ∅.
  Axiom locs_stack_pop   : locs stack_pop   = ∅.
  Axiom locs_stack_is_empty : locs stack_is_empty = ∅.
  Axiom locs_stack_is_full : locs stack_is_full = ∅.

  Parameter StackOf : forall `{interpGSMore Σ} {A} (R:A -> val -> iProp Σ),
      list (A * (Qp * Qz)) -> loc -> iProp Σ.

  Parameter empty_cost : Qz.
  Parameter cell_cost : Qz.

  Axiom stack_empty_spec : forall `{interpGSMore Σ} π A (R:A -> val -> iProp Σ),
      CODE (stack_empty [[]])
      TID π
      PRE  (♢ empty_cost)
      POST (fun s => StackOf R [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).

  Axiom stack_push_spec : forall `{interpGSMore Σ} π A (R:A -> val -> iProp Σ),
    forall s qp qz v x xs,
      size_lt (length xs) capacity ->
      qz ≠ 0%Qz ->
      CODE (stack_push [[s, v]])
      TID π
      SOUV {[s]}
      PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅)
      POST (fun (_:unit) => StackOf R ((x,(qp,qz))::xs) s).

  Axiom stack_pop_spec : forall `{interpGSMore Σ} π A (R:A -> val -> iProp Σ),
    forall s qp qz x xs,
      CODE (stack_pop [[s]])
      TID π
      SOUV {[s]}
      PRE  (StackOf R ((x,(qp,qz))::xs) s)
      POST (fun v => R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).

  Axiom stack_is_empty_spec : forall `{interpGSMore Σ} π A (R:A -> val -> iProp Σ),
    forall xs s,
      CODE (stack_is_empty [[s]])
      TID π
      SOUV {[s]}
      PRE  (StackOf R xs s)
      POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ StackOf R xs s).

  Axiom stack_is_full_spec : forall `{interpGSMore Σ} π A (R:A -> val -> iProp Σ),
    forall xs s,
      CODE (stack_is_full [[s]])
      TID π
      SOUV {[s]}
      PRE (StackOf R xs s)
      POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).

  Axiom stack_free : forall `{interpGSMore Σ} A (R:A -> val -> iProp Σ),
    forall s xs,
      s ⟸ ∅ ∗ s ↤ ∅ ∗ StackOf R xs s =[#]=∗
      ♢(empty_cost + cell_cost*length xs) ∗ † s ∗
      (∃ vs, soup R ∅ xs vs).
End StackOf.

Module Type Capacity.
  Parameter capacity : positive.
End Capacity.

Module MoreStackOf(St:StackOf).
Export St.

Lemma stack_pop_spec' `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) xs s:
  xs ≠ nil ->
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun v => ∃ x xs' qz qp, ⌜xs=(x,(qp,qz))::xs'⌝ ∗ R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅ ∗ StackOf R xs' s ∗ ♢ cell_cost).
Proof.
  iIntros. destruct xs as [|(x,(qp,qz)) xs']; try easy.
  iApply (wpc_mono with "[-]").
  { iApply stack_pop_spec. done. }
  iIntros (?) "(?&?&?&?&?)".
  iExists _,_,_,_. iFrame. eauto.
Qed.

(* A stack free for empty stacks *)
Lemma empty_stack_free `{interpGSMore Σ} A (R:A -> val -> iProp Σ) s :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ StackOf R nil s =[#]=∗ ♢ empty_cost.
Proof.
  iIntros "(?&?)". iIntros.
  iMod (@stack_free with "[$] [$]") as "(?&?&?)".
  iFrame.
  simpl. rewrite right_absorb right_id.
  by iFrame.
Qed.

(* LATER stack_free which frees the content of its children. *)
End MoreStackOf.

Module StackDominant(St:StackOf).
Export St.

Definition StackDominantOf `{interpGSMore Σ} {A} (R:A -> val -> iProp Σ)
  qp (xs:list A) (s:loc) : iProp Σ :=
  StackOf R (fmap (fun v => (v,(qp,1%Qz))) xs) s.

Lemma stack_is_empty_spec_dominant `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) qp xs s :
  CODE (stack_is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackDominantOf R qp xs s)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ StackDominantOf R qp xs s).
Proof.
  iIntros.
  wpc_apply @stack_is_empty_spec. eauto.
  iIntros (?) "(%E & ?)".
  iFrame. iPureIntro. rewrite E.
  now destruct xs.
Qed.

Lemma stack_is_full_spec_dominant `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) qp xs s :
  CODE (stack_is_full [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackDominantOf R qp xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackDominantOf R qp xs s).
Proof.
  iIntros.
  wpc_apply @stack_is_full_spec. eauto.
  iIntros (?) "(? & ?)".
  rewrite fmap_length. eauto.
Qed.

Lemma stack_empty_dominant_spec `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) qp :
  CODE (stack_empty [[]])
  TID π
  PRE (♢ empty_cost)
  POST (fun s => StackDominantOf R qp [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros.
  wpc_apply @stack_empty_spec.
  iIntros. iFrame.
Qed.

Lemma stack_push_dominant_spec `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) qp x v xs s :
  size_lt (length xs) capacity ->
  CODE (stack_push [[s, v]])
  TID π
  SOUV {[s]}
  PRE (♢ cell_cost ∗ StackDominantOf R qp xs s ∗ v ↤? ∅ ∗ v ⟸?{qp} {[π]} ∗ R x v)
  POST (fun (_:unit) => StackDominantOf R qp (x::xs) s).
Proof.
  iIntros (?) "(? & ? & ? & ? & ?)".
  wpc_apply @stack_push_spec.
  { rewrite fmap_length //. }
  { easy. }
  iFrame. iIntros. iFrame.
Qed.

Lemma stack_pop_dominant_spec `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) qp x xs s :
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE (StackDominantOf R qp (x::xs) s)
  POST (fun v => R x v ∗ v ↤? ∅ ∗ v  ⟸?{qp} {[π]} ∗ StackDominantOf R qp xs s ∗ ♢ cell_cost).
Proof.
  iIntros.
  wpc_apply @stack_pop_spec. eauto. iIntros (?) "(? & ? & ? & ?)".
  iFrame.
Qed.

Lemma stack_pop_dominant_spec' `{interpGSMore Σ} π A (R:A -> val -> iProp Σ) qp xs s :
  xs ≠ nil ->
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE (StackDominantOf R qp xs s)
  POST (fun v => ∃ y ys, ⌜xs=y::ys⌝ ∗ R y v ∗ v ↤? ∅ ∗ v ⟸?{qp} {[π]} ∗ StackDominantOf R qp ys s ∗ ♢ cell_cost).
Proof.
  iIntros (?) "?".
  destruct xs as [|v tl]; try done.
  wpc_apply @stack_pop_dominant_spec; eauto.
Qed.

Lemma stack_dominant_free `{interpGSMore Σ} A (R:A -> val -> iProp Σ) qp (xs:list A) s :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ StackDominantOf R qp xs s =[#]=∗
  ♢(empty_cost+cell_cost*length xs) ∗ †s ∗
  (∃ vs, [∗ list] x;v ∈ xs; vs,
     v ↤? ∅ ∗ v ⟸?{qp} ∅ ∗ R x v).
Proof.
  iIntros "(Hk & Hs1 & Hs2)". iIntros.
  iMod (stack_free _ R s (((λ v, (v, (qp,1%Qz))) <$> xs)) with "[$] [$]") as "(? & ? & ? & [%vs Hvs])".
  iModIntro. iFrame. rewrite fmap_length. iFrame.
  iExists vs.

  iInduction xs as [] "IH" forall (vs); simpl.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%E". subst. simpl. easy. }
  { iDestruct( big_sepL2_cons_inv_l with "[$]") as "[%v' [%vs' [%E ((? & ? & ?) & Hvs)]]]".
    subst. simpl. iFrame. iApply "IH". iFrame. }
Qed.
End StackDominant.

(* In the paper, we show a restricted interface.
   We show here that StackOf refines to it. *)
Module PaperStack(S:StackOf).
Import S.

Definition dupf : val * Qp -> val * (Qp * Qz) := fun '(v,q) => (v,(q,q:Qz)).

Lemma soup_mixer `{interpGS0 Σ} (xs:list (val*Qp)) vs :
  soup (λ x y : val, ⌜x = y⌝) ∅ (dupf <$> xs) vs -∗
  [∗ list] x ∈ xs, (x.1 ↤?{x.2:Qp} ∅ ∗ x.1 ⟸?{x.2} ∅).
Proof.
  iRevert (vs).
  iInduction xs as [|(?,?) xs] "IH"; iIntros (vs).
  eauto.
  destruct vs; eauto.
  simpl. unfold soup. simpl. iIntros "((% & ? & ?) & ?)". subst.
  iFrame. iApply "IH". iFrame.
Qed.

Definition Stack `{interpGSMore Σ} (L:list (val * Qp)) (l:loc) : iProp Σ :=
  @StackOf _ _ val (fun (x y:val) => ⌜x = y⌝)%I (dupf <$> L) l.

Lemma stack_empty_spec `{interpGSMore Σ} π :
  CODE (stack_empty [[]])
  TID π
  PRE  (♢ empty_cost)
  POST (fun s => Stack [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof. eauto using stack_empty_spec. Qed.

Lemma stack_push_spec `{interpGSMore Σ} π s qp x xs :
  size_lt (length xs) capacity ->
  CODE (stack_push [[s,x]])
  TID π
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ Stack xs s ∗ x ⟸?{qp} {[π]} ∗ x ↤?{qp} ∅)
  POST (fun (_:unit) => Stack ((x,qp)::xs) s).
Proof.
  iIntros (?) "(? & ? & ? & ?)".
  wpc_apply @stack_push_spec; eauto.
  { rewrite fmap_length //. }
  { apply Qp_to_Qz_ne_zero. }
Qed.

Lemma stack_pop_spec `{interpGSMore Σ} π s qp x xs :
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE  (Stack ((x,qp)::xs) s)
  POST (fun v => x ⟸?{qp} {[π]} ∗ v ↤?{qp} ∅ ∗ Stack xs s ∗ ♢ cell_cost).
Proof.
  iIntros.
  wpc_apply stack_pop_spec; eauto. iIntros (?) "(% & ? & ? & ?)".
  subst. iFrame.
Qed.

Lemma stack_is_empty_spec `{interpGSMore Σ} π xs s :
  CODE (stack_is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (Stack xs s)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ Stack xs s).
Proof.
  iIntros.
  wpc_apply stack_is_empty_spec; eauto. iIntros (?) "(% & ?)".
  iFrame.
  iPureIntro. destruct xs; simpl in *; naive_solver.
Qed.

Lemma stack_is_full_spec `{interpGSMore Σ} π xs s :
  CODE (stack_is_full [[s]])
  TID π
  SOUV {[s]}
  PRE (Stack xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ Stack xs s).
Proof.
  iIntros.
  wpc_apply stack_is_full_spec. eauto. iIntros (?) "(%E & ?)".
  iFrame. iPureIntro. rewrite fmap_length in E.
  eauto.
Qed.

Lemma stack_free `{interpGSMore Σ} (xs:list (val*Qp)) s :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ Stack xs s =[#]=∗
    ♢(empty_cost + cell_cost*length xs) ∗ † s ∗
    ([∗ list] x ∈ xs, (x.1 ↤?{x.2:Qp} ∅ ∗ x.1 ⟸?{x.2} ∅)).
Proof.
  iIntros "?". iIntros.
  iMod (stack_free with "[$] [$]") as "(? & (? & ? & [%vs ?]))". eauto.
  rewrite fmap_length. iFrame. iModIntro.
  iApply soup_mixer. iFrame.
Qed.
End PaperStack.
