From iris.base_logic.lib Require Export ghost_map gen_heap.
From iris.algebra Require Import numbers auth list gset gmultiset.

From irisfit.program_logic Require Import wpc_logatom.
From irisfit.program_logic Require Import wp_alloc wp_store wp_call wp_store wp_protected wp_cas wp_load wp_clean wp_free wp_call_prim.
From irisfit.examples Require Import proofmode.

(******************************************************************************)
Definition create : val :=
  λ: [[]], alloc 1.

Definition push : val :=
  μ: "self", [["s", "v"]],
    let: "h'" := alloc 2 in
    "h'".[0] <- "v";;
    tm_enter ;;
    let: "h" := "s".[0] in
    "h'".[1] <- "h";;
    let: "b" := tm_cas "s" 0 "h" "h'" in
    if: "b" then tm_exit;; val_unit else
      tm_exit;; "self" [["s","v"]].

Definition pop : val :=
  μ: "self", [["s"]],
    tm_enter;;
    let: "h" := "s".[0] in
    let: "b" := "h" '== val_unit in
    if: "b" then tm_exit ;; "self" [["s"]] else
      let: "h'" := "h".[1] in
      let: "b" := tm_cas "s" 0 "h" "h'" in
      if: "b" then let: "v" := "h".[0] in tm_exit ;; "v" else tm_exit ;; "self" [["s"]].

Definition is_empty : val :=
  λ: [["s"]],
    let: "l" := "s".[0] in
    "l" '== val_unit.

(******************************************************************************)
(* The cmras we need. *)

Canonical Structure valO := leibnizO val.
Canonical Structure locO := leibnizO loc.
Canonical Structure QzO := leibnizO Qz.
Notation modelO := (listO (prodO valO (prodO fracO QzO))).
Notation elem := (val * (Qp * Qz))%type.

Class stackG Σ :=
  StackG {
      stack_cellsG : inG Σ (authUR (gsetUR locO));
      stack_protectG : inG Σ (authUR (gmultiset  (loc*loc)));
    }.

Local Existing Instances stack_cellsG stack_protectG.

Record gstack := mk_gs { gb : gname; gp : gname }.
Global Instance gstack_eq_dec : EqDecision gstack.
Proof. solve_decision. Qed.
Global Instance gstack_countable : Countable gstack.
Proof.
  apply inj_countable with
    (f:= fun x => (x.(gb), x.(gp)))
    (g:= fun '(x1,x2) => Some (mk_gs x1 x2)).
  intros []; eauto.
Qed.

Section Treiber_proof.
Context `{interpGS0 Σ, stackG Σ}.

(* The main difficulty in this proof is that
  [push] may create a link to an internal cell from
  a "private" block that is not yet inside the stack,
  apparently preventing its collection.

  The main idea is to allow a form of ghost helping:
  if someone needs to deallocate a cell, they will be able to
  deallocate (thanks to GC-less sections) all the private cells
  pointing to it, and then deallocate the cell.

  To allow for private cells, we use a mechanism of "cells".
  Each cell is either deallocated or pointed
  by some locations.
  These locations appears in the codomain of a ghost protection map.
 *)

Definition iscell  (γ:gname) (l:loc) : iProp Σ :=
  own γ (◯ {[l]}).

Definition volatile (γ:gname) (l:loc) Φ : iProp Σ :=
  ((sizeof l 2 ∗ l ↤ ∅ ∗ l ⟸ ∅) ∨ (Φ ∗ †l ∗ ♢2)).

(* c is an inner cell, l a private loc *)
Definition protect (γ:gname) (c:loc) (l:loc) : iProp Σ :=
  volatile γ l (†c)%I.

Definition outsiders (γ:gname) (M:gmultiset (loc*loc)) : iProp Σ :=
  [∗ mset] x ∈ M, protect γ x.1 x.2.

Definition stamped (v:loc) (L:gmultiset loc) (M:gmultiset (loc*loc)) :=
  forall l', multiplicity l' L <= multiplicity (v,l') M.

Definition cell M l : iProp Σ :=
  †l ∨
  (∃ L, l ↤{1/2} (smultiset.of_gmultiset L) ∗ ⌜stamped l L M⌝).

Definition cells (γ:gname) (M:gmultiset (loc*loc)) : iProp Σ :=
  ∃ (A:gset loc),
    own γ (● A) ∗ [∗ set] l ∈ A, cell M l.

Definition reg (γ:gname) (v:val) : iProp Σ :=
  ⌜v=val_unit⌝ ∨ (∃ l, ⌜v=val_loc l⌝ ∗ iscell γ l).

Fixpoint innerList (γ:gname) (xs:list (val*(Qp*Qz))) (v:val) : iProp Σ :=
  match xs with
  | nil => ⌜v=val_unit⌝
  | (x,(p,q))::xs =>
      ∃ l v', ⌜v=val_loc l⌝ ∗
      l ↦□ [x; v'] ∗ v' ⟸? ∅ ∗ reg γ v' ∗
      (* One half of pointedby here, the other half in cells. *)
      v' ↤?{1/2} {[+l+]} ∗ x ⟸?{p} ∅ ∗ x ↤?{q} {[+l+]} ∗
      innerList γ xs v' end.

Local Instance innerList_timeless γ xs v : Timeless (innerList γ xs v).
Proof. revert v; induction xs as [|(?&?&?)]; apply _. Qed.

Definition inner γ (s:loc) (xs:list elem) : iProp Σ :=
  ∃ v, s ↦ [v] ∗ v ⟸? ∅ ∗ v ↤?{1/2} {[+s+]} ∗ reg γ v ∗ innerList γ xs v.

Definition nm := nroot.@"treiber".

Definition stack (s:loc) (xs:list elem) : iProp Σ :=
  ∃ (g:gstack) (M:gmultiset (loc*loc)),
    meta s nm g ∗
    inner g.(gb) s xs ∗
    own g.(gp) (● M) ∗
    outsiders g.(gb) M ∗
    cells g.(gb) M.

Lemma open_stack_inv_meta s g xs :
  meta s nm g -∗
  stack s xs -∗
  ∃ (M:gmultiset (loc*loc)),
    inner g.(gb) s xs ∗
    own g.(gp) (● M) ∗
    outsiders g.(gb) M ∗
    cells g.(gb) M.
Proof.
  iIntros "Hmeta (%&%&Hmeta'&?)".
  iDestruct (meta_agree with "Hmeta Hmeta'") as "->".
  iExists _. by iFrame.
Qed.

Lemma is_empty_spec π xs s :
  CODE (is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (stack s xs)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ stack s xs).
Proof.
  iIntros "Hs".
  wpc_call. wpc_let_empty.
  iDestruct "Hs" as "[%g [%M (#Hmeta&I1&I2&I3&I4)]]".

  iApply wpc_split_ctx. iIntros (X HX) "HPBT".
  assert (is_Some (X !! s)) as (p&Hp).
  { apply elem_of_dom. set_solver. }
  iDestruct (PBT_borrow_pbt with "[$]") as "(Hp&Hback)". done.
  iDestruct "I1" as "[%h (S1&S2&S3&S4&S5)]".
  iSpecialize ("Hback" with "[$]").
  destruct xs as [|(?&?&?)]; simpl.
  { iDestruct "S5" as "->". wpc_load. iSteps. wpc_call_prim. iSteps. }
  { iDestruct "S5" as "(%&%&->&?)".
    wpc_load. iIntros "(?&?)". iApply wpc_postpone.
    wpc_call_prim. pclean l. wpc_val. iSplitR; first done. iExists g,M. iFrame "#∗".
    iExists _. iFrame. simpl. iSteps. }
  Unshelve. all:exact inhabitant.
Qed.

Lemma create_spec π :
  CODE (create [[]])
  TID π
  SOUV ∅
  PRE (♢1)
  POST (fun (s:loc) => stack s [] ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros.
  wpc_call.

  iApply wpc_postpone.
  wpc_alloc.
  iIntros (s) "(?&X1&X2&?)".

  iMod (own_alloc (● (∅:gset loc))) as "[%γ2 H2]".
  { by apply auth_auth_valid. }

  iMod (own_alloc (● (∅:gmultiset (loc*loc)))) as "[%γ3 H3]".
  { by apply auth_auth_valid. }

  pose (g := mk_gs γ2 γ3).
  iMod (meta_set _ s g nm with "[$]") as "#?". solve_ndisj.

  iAssert (stack s nil) with "[-X1 X2]" as "Hs".
  { iExists _,∅. subst g. simpl. iFrame "#∗". simpl.
    iSplitR "H2".
    { iSmash. }
    iSplitR "H2".
    { by iApply big_sepMS_empty. }
    { iExists _. iFrame. by iApply big_sepS_empty. } }

  wpc_val. iFrame.
Qed.

Definition gelem γ l l' : iProp Σ := own γ (◯ ({[+ (l,l') +]})).

Definition isreg γ (v:val) (l':loc) : iProp Σ :=
  (⌜v=val_unit⌝ ∗ l' ↤ ∅ ∗ l' ⟸ ∅)
  ∨ (∃ l, ⌜v=val_loc l⌝ ∗ gelem γ l l').

Lemma register_aux (v:loc) l γ γ' M :
  (v, l) ∉ M ->
  iscell γ' v -∗
  own γ (● M) -∗
  outsiders γ' M -∗
  sizeof l 2 ∗ l ↤ ∅ ∗ l ⟸ ∅ ==∗
  own γ (● (({[+ (v, l) +]} ⊎ M))) ∗ outsiders γ' ({[+ (v, l) +]} ⊎ M) ∗ gelem γ v l.
Proof.
  iIntros (?) "H1 H2 H3 (?&?&?)".
  iMod (own_update with "H2") as "(?&?)".
  { apply auth_update_alloc.
    apply gmultiset_local_update with (Y':={[+(v,l)+]}).
    rewrite right_id_L //. }
  rewrite comm_L.
  iFrame. iApply big_sepMS_singleton.
  iFrame. iLeft. by iFrame.
Qed.

Lemma update_set_cell M M' A :
  (forall (l:loc) L, l ∈ A -> stamped l L M -> stamped l L M') ->
  ([∗ set] y ∈ A, cell M y)%I -∗
  [∗ set] y ∈ A, cell M' y.
Proof.
  iIntros. iApply (big_sepS_impl with "[$]").
  iModIntro. iIntros (??) "[?|[%(?&%)]]".
  by iLeft.
  iRight. iExists _. iFrame. iPureIntro. eauto.
Qed.

Lemma cells_update γ M M':
  (forall (l:loc) L, stamped l L M -> stamped l L M') ->
  cells γ M -∗ cells γ M'.
Proof.
  iIntros (?) "[% (?&?)]". iExists _. iFrame.
  iApply (update_set_cell with "[$]"); eauto.
Qed.

Lemma stamped_insert_fresh (v v':loc) l' L M :
  v ≠ v' ->
  stamped v L M ->
  stamped v L ({[+ (v',l') +]} ⊎ M).
Proof.
  intros ? E l0. specialize (E l0). rewrite multiplicity_disj_union. lia.
Qed.

Lemma confront_protect_pbt γ l v A :
  l ⟸ A ∗ protect γ v l -∗ False.
Proof.
  iIntros "(?&[(_&?&?)|(?&?&?)])".
  { iDestruct (pbt_valid2 with "[$][$]") as "%Hv". exfalso. by vm_compute. }
  { iApply (confront_pbt_dag with "[$]"). }
Qed.

Definition vdead v : iProp Σ :=
  ∃ l, ⌜v=val_loc l⌝ ∗ †l.

Lemma register l' γ γ' v M :
  reg γ' v -∗
  sizeof l' 2 ∗ l' ↤ ∅ ∗ l' ⟸ ∅ -∗
  cells γ' M -∗
  own γ (● M) -∗
  outsiders γ' M ==∗
  ∃ M', own γ (● M') ∗ outsiders γ' M' ∗ isreg γ v l' ∗
  ((vdead v ∗ cells γ' M')
  ∨  (v ↤?{(1/4)%Qz} ∅ ∗ ((v ↤?{1/4} {[+l'+]}) -∗ cells γ' M'))).
Proof.
  iIntros "#Hb (E1&E2&E3) Hcells H1 H2".

  iDestruct "Hb" as "[ -> | [%l (->&?)]]".
  { iSmash. }

  iAssert (⌜(l, l') ∉ M⌝ )%I as "%X".
  { iIntros (HM).
    iDestruct (big_sepMS_elem_of with "[$]") as "?". apply HM. simpl.
    iDestruct (confront_protect_pbt with "[$]") as "?". done. }

  iMod (register_aux with "[$][$][$][$]") as "(?&?&Hr)". set_solver.
  iModIntro. iExists ({[+ (l, l') +]} ⊎ M). iFrame.

  iDestruct "Hcells" as "[%A (Hba&Hs)]".
  iDestruct (more_cmras.elem_of_gset with "Hba [$]") as "%".
  replace A with ({[l]} ∪ A ∖ {[l]}).
  2:{ rewrite union_comm_L difference_union_L. set_solver. }
  rewrite big_sepS_insert. 2:set_solver.

  iSplitL "Hr". iSmash.
  iDestruct "Hs" as "(Hb&Hs)".

  iDestruct "Hb" as "[#?|[% (Hl&%E2)]]".
  { iLeft. simpl. iSplitR. iExists _. by iFrame "#".
    iExists _. iFrame. rewrite big_sepS_insert. 2:set_solver.
    iFrame. iFrame "#".
    iApply (update_set_cell with "[$]").
    intros. eapply stamped_insert_fresh; eauto. set_solver. }

  iRight.
  replace (1 / 2)%Qz with (1/4 + 1/4)%Qz by compute_done.
  rewrite -(left_id _ _ (of_gmultiset L)).
  iDestruct (mapsfrom_split with "[$]") as "(Hx&?)". 3:done.
  1,2:intros E; exfalso; by vm_compute.
  { done. }
  iFrame. iIntros.
  iExists _. iFrame "Hba". rewrite big_sepS_insert. 2:set_solver.
  iSplitR "Hs".
  { iRight. iExists ({[+ l' +]} ⊎ L). iFrame. iSplitL; last eauto.
    replace (1 / 2)%Qz with (1/4 + 1/4)%Qz by compute_done.
    rewrite of_gmultiset_disj_union of_gmultiset_singleton.
    iApply (mapsfrom_join with "[$][$]").
    iPureIntro.
    { intros l0.
      rewrite !multiplicity_disj_union. specialize (E2 l0). multiset_solver. } }
  { iApply (update_set_cell with "[$]"). intros.
    eapply stamped_insert_fresh; eauto. set_solver. }
Qed.

Definition sentenced l n : iProp Σ :=
  (l ⟸ ∅ ∗ l ↤ ∅) ∨ (†l ∗ ♢n).

Lemma stamped_delete (l:loc) M v (l':loc) L :
  v ≠ l ->
  (v,l') ∈ M ->
  stamped l L M →
  stamped l L (M ∖ {[+ (v, l') +]}).
Proof.
  intros ? ? E l0. rewrite multiplicity_difference.
  specialize (E l0). multiset_solver.
Qed.

Definition schrodinger γ M v l : iProp Σ :=
  ((vdead v ∗ cells γ M ∗ sentenced l 2) ∨
    l ↤ ∅ ∗ l ⟸ ∅ ∗ v ↤?{1/4}{[+l+]} ∗ (v ↤?{1/4} ∅ -∗ cells γ M )).

Lemma unreg l' γ γ' v M :
  own γ (● M) ∗
  outsiders γ' M ∗
  cells γ' M ∗
  reg γ' v ∗
  isreg γ v l' =[#]=∗
  ∃ M', own γ (● M') ∗ outsiders γ' M' ∗ schrodinger γ' M' v l'.
Proof.
  iIntros "(Ha&Hp&Hb&Hi&Hf)". iIntros.
  iDestruct "Hf" as "[ [-> (?&?)] | [%l (->&Hf)]]".
  { iSmash. }
  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".

  apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
  apply gmultiset_included in Hv.
  assert ((l, l') ∈ M) by multiset_solver.

  iMod (own_update_2 with "Ha Hf") as "Ha".
  { apply auth_update_dealloc.
    apply gmultiset_local_update with (X' := (M ∖ {[+ (l,l') +]})).
    multiset_solver.  }

  rewrite /outsiders big_sepMS_delete //.
  iDestruct "Hp" as "(X&?)". simpl.

  iDestruct "Hi" as "[%|[%l0 (%Eq&Hf)]]". congruence.
  inversion Eq. subst l0.
  iDestruct "Hb" as "[% (Hz&Hx)]".
  iDestruct (more_cmras.elem_of_gset with "Hz Hf") as "%Hv'".
  replace A with ({[l]} ∪ A ∖ {[l]}).
  2:{ rewrite union_comm_L difference_union_L. set_solver. }
  rewrite big_sepS_insert. 2:set_solver. iDestruct "Hx" as "(U&Hx)".
  iDestruct "U" as "[#?|[%(Z&%E2)]]".
  { iModIntro. iFrame "#∗". iExists _. iFrame.
    iLeft. iSplitR. iSmash. iSplitR "X".
    { iExists _. iFrame "Hz". rewrite big_sepS_insert. 2:set_solver.
      iSplitR. by iLeft. iApply (update_set_cell with "[$]").
      { intros. eapply stamped_delete; eauto. set_solver. } }
    { iDestruct "X" as "[(?&?&?) | (?&?)]"; [iLeft | iRight]; iFrame "#∗". } }

  iDestruct "X" as "[(?&X&?) | (?&_)]"; last first.
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(?&?)". compute_done.
    done. }
  iFrame. iModIntro. iExists _. iFrame.
  iRight. iFrame.

  iAssert (l ↤{1/4} {[+l'+]} ∗ l ↤{1/4} of_gmultiset (L∖{[+l'+]}))%I with "[Z]" as "(?&?)".
  { iApply mapsfrom_split. 3,4:done. 1,2:by vm_compute.
    replace (1 / 2)%Qz with (1/4 + 1/4)%Qz by compute_done.
    destruct_decide (decide (l' ∈ L)).
    { rewrite {1}(gmultiset_disj_union_difference' l' L) //.
      rewrite of_gmultiset_disj_union of_gmultiset_singleton //. }
    { assert (L = L ∖ {[+l'+]}) as Eq'. multiset_solver.
      rewrite {1}Eq'. iApply (mapsfrom_weak with "[$]"). by vm_compute.
      intros. generalize ((L ∖ {[+ l' +]})). intros ?.
      rewrite smultiset.multiplicity_disj_union. smultiset_solver. } }

  iFrame. iIntros.
  iDestruct (mapsfrom_join with "[$][$]") as "?".
  replace  (1/4 + 1/4)%Qz with (1 / 2)%Qz  by compute_done.
  rewrite left_id. iExists _. iFrame "Hz".
  rewrite big_sepS_insert. 2:set_solver.
  iSplitR "Hx".
  { iRight. iExists _. iFrame. iPureIntro.
    { intros l0.
      rewrite !multiplicity_difference.
      specialize (E2 l0). multiset_solver. } }
  { iApply (update_set_cell with "[$]").
    { intros. eapply stamped_delete; eauto. set_solver. } }
Qed.

Lemma add_cell h γ M L :
  cells γ M ∗
  h ↤ L =[#]=∗
  cells γ M ∗ h ↤{1/2} L ∗ iscell γ h.
Proof.
  iIntros "([%A (Ha&Hs)]&Hh)". iIntros.
  destruct_decide (decide (h ∈ A)).
  { iDestruct (big_sepS_elem_of with "[$]") as "X". done.
    iDestruct "X" as "[? | [% (?&_)]]".
    { iMod (confront_mapsfrom_dag with "[$][$]") as "(?&?)". done. done. }
    { iDestruct (mapsfrom_confront with "[$][$]") as "%". by vm_compute.
      congruence. } }

  iMod (own_update with "Ha") as "(?&?)".
  { apply auth_update_alloc. apply gset_local_add. }
  rewrite left_id. iFrame. rewrite comm_L. iModIntro.

  iAssert ( h ↤{1/2} L ∗ h ↤{1/2} ∅)%I with "[Hh]" as "(?&?)".
  { iApply (mapsfrom_split with "[$]"). 1,2: naive_solver. compute_done. rewrite right_id //. }
  iFrame.
  iExists _. iFrame. iApply big_sepS_insert. done. iFrame.
  iRight. iExists ∅. rewrite of_gmultiset_empty. iFrame.
  iPureIntro.
  { intros l. rewrite multiplicity_empty. lia. }
Qed.

Lemma schrodinger_kill γ M v l' π  S:
  sizeof l' 2 ∗
  inside π S ∗ schrodinger γ M v l' =[#]=∗
  inside π (S ∪ locs v ∪ {[l']}) ∗ †l' ∗ ♢2 ∗ cells γ M.
Proof.
  iIntros "(?&?&Hcase)". iIntros.
  iMod (dig_debt (S∪locs v∪{[l']}) with "[$][$]") as "(?&?)". set_solver.
  iDestruct "Hcase" as "[(?&?&Hs) | (?&?&?&Hback)]".
  { iDestruct "Hs" as "[(?&?) | (?&?)]". 2:by iFrame.
    iMod (interp_free'' with "[$][$]") as "(?&?&?)". by iFrame. }
  { iMod (interp_free'' with "[$][$]") as "(?&?&#?)".
    iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".
    assert (({[+ l' +]} ⊎ {[-l'-]}) ≡ ∅) as -> by smultiset_solver.
    iSpecialize ("Hback" with "[$]"). by iFrame "#∗". }
Qed.

Ltac clean_debt π :=
  iApply wp_conseq; only 1:iApply inside_clean; iFrame; iIntros "D";
  replace (inside _ _) with (inside π ∅); last (f_equal; set_solver).

Open Scope triple_scope.

Lemma push_spec (s:loc) (x:val) p q π :
  (is_loc x -> q ≠ 0%Qz) ->
  ACODE (push [[s,x]])%T
  TID π
  WITH ⊤
  SOUV {[s]}
  <<< (♢2 ∗ x ⟸?{p} {[π]} ∗ x ↤?{q} ∅) | ∀∀ xs, stack s xs >>>
  <<< stack s ((x,(p,q))::xs) | (fun (_:unit) => True)  >>>.
Proof.
  iIntros (?) "(HC&H2&H3)". iIntros (Q) "AU".
  iLöb as "IH".

  wpc_call.
  wpc_let_noclean. wpc_alloc.
  iIntros (h') "(H5&H6&H7&_)". simpl.
  iClear "HC".

  wpc_let_noclean. wpc_store.
  iIntros "(H5&H3&_)".
  simpl. rewrite left_id.

  iApply @wpc_enter. iIntros (k) "%Ek HS D".
  apply dom_singleton_inv_L in Ek. destruct Ek as (p'&->).

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
  iDestruct "I" as "[%g [%M (#Hmeta&I1&I2&I3&I4)]]".
  rewrite -{1}pbt_PBT.
  iDestruct "I1" as "[%h (S1&S2&S3&#?&S4)]".

  iApply wp_tconseq. iApply (tupd_clean_debt h'). iFrame. iIntros "(H7&D)".
  rewrite left_id_L difference_diag_L.

  iDestruct (mapsto_extract_size h' with "[$]") as "#?". simpl.

  wp_apply wp_load_inside. compute_done.
  iIntros (?) "(->&_&?&D)".
  iAssert (stack s xs0) with "[-H2 AU H3 D H5 H6 H7 HS]" as "GO".
  { iSmash. }
  iMod ("AU" with "GO") as "AU". iModIntro.
  clear dependent xs0 M.

  iIntros "_". simpl.

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
  iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (I1&I2&I3&I4)]".
  rewrite difference_diag_L.
  iMod (register h' with "[$][$][$][$][$]") as
    "[%M' (?&?&Hreg&Hcase)]".

  iDestruct "Hcase" as "[ (dag&?) | (Hmf&Hback)]".
  (* h was reclaimed by a concurrent [pop] *)
  { iDestruct "dag" as "[%l (->&#?)]".

    iApply wp_tconseq. iApply (unreg _ _ _ _ M'). iFrame "∗#".
    iIntros "[%M'' (R1&R2&Hcase)]".
    iApply wp_tconseq. iApply schrodinger_kill. iFrame "∗#".
    iIntros "(D&#?&R3&?)".

    wp_apply wp_store_dead. compute_done.
    iIntros (?) "(->&_&_)".
    iMod ("AU" with "[-H2 H3 D HS R3]") as "AU".
    { iSmash. }
    iIntros "!> _".
    clear dependent xs0 M M' M''.

    iApply wp_let_noclean.
    iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
    iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (I1&I2&I3&I4)]".
    iDestruct "I1" as "[%h (S1&S2&S3&S4&S5)]".
    destruct_decide (decide (h=l)).
    { subst. iApply wp_tconseq. simpl.
      iApply (confront_mapsfrom_dag _ l). 2:iFrame. compute_done.
      iSteps. }

    wp_apply wp_cas_fail. 1-3:done.
    iIntros (?) "(->&_&?)".
    iMod ("AU" with "[-H2 H3 D HS R3]") as "AU".
    { iSmash. }

    iIntros "!> _". simpl. iApply wp_if. iIntros "!> _".
    iApply wp_tconseq. iApply (vmapsfrom_cleanup x h'). iFrame "#∗". iIntros.
    assert ({[+ h' +]} ⊎ {[-h'-]} ≡ ∅) as -> by smultiset_solver.

    iApply wp_tconseq. iApply (debt_vtransfer x). iFrame. iIntros "(?&?)".
    iApply wp_tconseq. iApply (debt_vtransfer s). iFrame. iIntros "(?&?)".
    rewrite union_idemp_L.

    clean_debt π.
    iApply @wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L.
    rewrite -pbt_PBT. iFrame.
    iApply ("IH" with "[$][$][$][$]"). }

  (* h is still allocated, we proceed. *)
  wp_apply wp_store. intros. 1,2:compute_done.

  iIntros (?) "(->&_&H5&X&_)".
  rewrite left_id.
  iSpecialize ("Hback" with "[$]").
  iMod ("AU" with "[-H2 H3 H5 Hreg D HS]") as "AU".
  { iSmash. }

  clear dependent xs0 M M'.
  iIntros "!> _". simpl.

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&AU)". solve_atomic.
  iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (I1&I2&I3&I4)]".
  iDestruct "I1" as "[%h0 (S1&S2&S3&S4&S5)]".

  iApply wp_tconseq. iApply (unreg _ _ _ _ M). iFrame "#∗".
  iIntros "[%M' (R1&R2&Hcase)]".

  destruct_decide (decide (h=h0)); try subst h0.
  (* CAS will succeed. *)
  { iDestruct "Hcase" as "[ ([% (->&?)]&_) | (X1&X2&X3&Hback)]".
    { iApply wp_tconseq. iApply confront_mapsfrom_dag.
      2:iFrame. compute_done. iSteps. }

    iApply wp_tconseq. iApply (tupd_vclean_debt x). iFrame. iIntros "(?&D)".
    rewrite difference_diag_L.

    iApply wp.wp_postpone.
    wp_apply wp_cas_suc. 1-3:naive_solver.
    iIntros (?) "(->&_&?&?&I6)". simpl.

    iMod (mapsto_persist with "H5") as "H5".
    iDestruct (vmapsfrom_join h with "[$]") as "?".
    iDestruct (vmapsfrom_join h with "[$]") as "?".
    rewrite left_id.
    assert ((smultiset.singletonNS s ⊎ {[+ h' +]} ⊎ {[+ s +]} ≡ ∅ ⊎ {[+h'+]})) as ->.
    { smultiset.smultiset_solver. }
    iDestruct (vmapsfrom_split with "[$]") as "(?&?)". 1,2:by vm_compute.
    iSpecialize ("Hback" with "[$]").

    iApply wp_tconseq. iApply add_cell. iFrame "#∗". iIntros "(?&Hh&#?)".
    iApply wp_val.

    iDestruct "AU" as "[_ AU]".
    iMod ("AU" with "[-D HS]") as "HPOST".
    { iSmash. }

    iIntros "!> _". iApply wp_if. iModIntro. iIntros "_".
    clean_debt π.
    iApply @wpc_exit; last iFrame. set_solver. rewrite pbt_PBT. iFrame.
    do 2 iStep. iApply "HPOST". by iFrame. }
  (* Reboot *)
  { iApply wp_tconseq. iApply schrodinger_kill. iFrame "#∗".
    iIntros "(D&#?&cred&?)".
    iApply wp_tconseq. iApply (vmapsfrom_cleanup x h'). iFrame "#∗".
    assert (({[+ h' +]} ⊎ {[-h'-]}) ≡ ∅) as ->. smultiset_solver.
    iIntros "R3".

    wp_apply wp_cas_fail. 1-3:naive_solver.
    iIntros (?) "(->&_&S1)".

    iDestruct "AU" as "[AU _]".
    iMod ("AU" with "[-R3 H2 D cred HS]") as "AU".
    { iSmash. }
    iIntros "!> _". simpl. iApply wp_if. iModIntro. iIntros "_".

    iApply wp_tconseq. iApply (debt_vtransfer x). iFrame. iIntros "(?&?)".
    iApply wp_tconseq. iApply (debt_vtransfer s). iFrame. iIntros "(?&?)".
    rewrite union_idemp_L.
    clean_debt π.
    iApply @wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L -pbt_PBT.
    iFrame. iApply ("IH" with "[$][$][$][$]"). }
  Unshelve. exact inhabitant.
Qed.

Lemma free_protected (l:loc) γ L M :
  stamped l L M ->
  outsiders γ M ∗
  l ↤ of_gmultiset L =[#]=∗
  (l ↤ ∅ ∗ (†l -∗ outsiders γ M)).
Proof.
  iIntros (E) "(Hp&?)". iIntros.
  iInduction L as [|l' L] "IH" using gmultiset_ind forall (M E).
  { rewrite of_gmultiset_empty.
    iFrame. iModIntro. eauto. }

  rewrite of_gmultiset_disj_union of_gmultiset_singleton.
  assert ((l, l') ∈ M) as Hi.
  { specialize (E l'). rewrite multiplicity_disj_union in E.
    multiset_solver. }

  rewrite {3}/outsiders. rewrite big_sepMS_delete //. simpl.
  iDestruct "Hp" as "(X&Hp)".
  iDestruct "X" as "[(?&?&?)|(?&_)]"; last first.
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(_&?)"; last done.
    by vm_compute. }

  iMod (interp_free'' with "[$][$]") as "(?&?&#?)".
  iMod (mapsfrom_cleanup with "[$][$]") as "(?&?)".
  assert (({[+ l' +]} ⊎ of_gmultiset L ⊎ {[-l'-]}) ≡ of_gmultiset L) as -> by smultiset_solver.

  iMod ("IH" $! (M ∖ {[+ (l, l') +]}) with "[%][$][$][$]") as "(?&?&Hb)".
  { intros l0. specialize (E l0). rewrite multiplicity_disj_union in E.
    rewrite multiplicity_difference.
    multiset_solver. }

  iFrame. iModIntro. iIntros.
  iSpecialize ("Hb" with "[$]"). iApply big_sepMS_delete. done.
  iFrame. simpl. iFrame "#∗".
Qed.

Lemma free_cell γ l M :
  sizeof l 2 ∗
  iscell γ l ∗
  l ⟸ ∅ ∗ l ↤{1/2} ∅ ∗
  outsiders γ M ∗
  cells γ M =[#]=∗
  †l ∗ ♢2 ∗ outsiders γ M ∗ cells γ M.
Proof.
  iIntros "(?&?&?&Hp&Hl&[% (Ha&X)])". iIntros.
  iDestruct (more_cmras.elem_of_gset with "Ha [$]") as "%Hv".
  replace (A) with ({[l]} ∪ A ∖ {[l]}).
  2:{ rewrite union_comm_L difference_union_L. set_solver. }
  rewrite big_sepS_insert. 2:set_solver.

  iDestruct "X" as "([?|[% (?&%E)]]&?)".
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(_&?)"; last done. by vm_compute. }
  iDestruct (mapsfrom_join with "[$][$]") as "?". rewrite Qz_div_2 right_id.

  iMod (free_protected _ _ _ M with "[$][$]") as "(?&?&Hb)".
  { done. }
  iMod (interp_free'' with "[$][$]") as "(?&?&#?)".
  iSpecialize ("Hb" with "[$]"). iFrame "#∗". iModIntro. iExists _. iFrame "Ha".
  iApply big_sepS_insert. set_solver. iFrame. by iLeft.
Qed.

Lemma pop_spec (s:loc) π :
  ACODE (pop [[s]])%T
  TID π
  WITH ⊤
  SOUV {[s]}
  <<< True | ∀∀ xs, stack s xs >>>
  <<< ∃∃ x p q xs', ⌜xs=(x,(p,q))::xs'⌝ ∗ stack s xs' ∗ ♢2 | (fun v => ⌜v=x⌝ ∗ x ⟸?{p} {[π]} ∗ x ↤?{q} ∅) >>>.
Proof.
  iIntros "_". iIntros (Q) "AU".
  iLöb as "IH".

  wpc_call.

  iApply @wpc_enter. iIntros (k) "%Ek HS D".
  apply dom_singleton_inv_L in Ek. destruct Ek as (p'&->).

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
  iDestruct "I" as "[%g [%M (#Hmeta&I1&I2&I3&I4)]]".
  rewrite -{1}pbt_PBT.
  iDestruct "I1" as "[%h (S1&S2&S3&#?&S5)]".

  wp_apply wp_load_inside. compute_done.
  iIntros (?) "(->&_&?&D)".

  iAssert (⌜h=val_unit⌝ ∨ ∃ l x h', ⌜h=val_loc l⌝ ∗ l ↦□ [x;h'] ∗ reg _ h')%I as "#Hcase".
  { destruct xs0 as [|(?&?&?)].
    { iDestruct "S5" as "->". eauto. }
    { iDestruct "S5" as "[%[% (->&?&?&?&?&?&?)]]". iRight. iExists _,_,_.
      by iFrame. } }

  iMod ("AU" with "[-D HS]") as "AU".
  { iSmash. }
  iIntros "!> _". simpl.
  clear dependent xs0 M.

  iApply wp_let_noclean.
  iApply wp_mono. iApply wp_call_prim. done.
  iIntros (?) "(->&_) _". simpl.
  iApply wp_if. iIntros "!> _".

  iDestruct "Hcase" as "[ -> | [%[% [% (->&?&?) ]]]]".
  { iApply wp_tconseq. iApply (debt_vtransfer s). iFrame.
    iIntros "(?&?)". clean_debt π. rewrite union_idemp_L.
    iApply wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L -pbt_PBT. iFrame.
    iApply ("IH" with "[$]"). }

  rewrite bool_decide_false //.
  iApply wp_let_noclean.

  wp_apply wp_load_inside. compute_done.
  iIntros (?) "(->&_&_&D) _". simpl.

  iApply wp_let_noclean.

  iMod "AU" as (xs0) "(I&AU)". solve_atomic.
  iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (I1&I2&I3&I4)]".
  iDestruct "I1" as "[%h0 (S1&S2&S3&S4&S5)]".

  destruct_decide (decide (h0=l)).
  { subst.

    iDestruct "AU" as "[_ AU]". rename xs0 into xs.

    destruct xs as [|(v,(p,q)) xs].
    { iDestruct "S5" as "%". congruence. }
    iDestruct "S5" as "[%[% (%Eq&?&?&Hv&R1&R2&R3&?)]]". inversion Eq. subst l0. clear Eq.
    iDestruct (mapsto_agree with "[$][$]") as "%Eq". inversion Eq. subst v v'. simpl. clear Eq.

    assert ((1/2)%Qz = (1/4 + 1/4)%Qz)%Qz as Eq by compute_done.
    rewrite {2}Eq -(left_id _ _ {[+l+]}).
    iDestruct (vmapsfrom_split h' with "[$]") as "(L1&?)".
    1,2:by vm_compute.

    iApply wp_postpone.
    wp_apply wp_cas_suc. 1-3:naive_solver.

    iIntros (?) "(->&_&?&?&?)".
    iDestruct (mapsfrom_join l with "[$][$]") as "?".
    assert (({[-s-]} ⊎ {[+ s +]}) ≡ ∅) as -> by smultiset_solver.
    rewrite Qz_add_0_l.

    iDestruct (mapsto_extract_size l with "[$]") as "?". simpl.
    iDestruct "S4" as "[%|[%l0 (%Eq'&?)]]". congruence. inversion Eq'. subst l0.
    iApply wp_tconseq. iApply (free_cell _ _ M). iFrame.
    iIntros "(#?&cred&?)".

    iDestruct (vmapsfrom_join with "[$]") as "?". rewrite -Eq.
    iApply wp_tconseq. iApply (vmapsfrom_cleanup h' l). iFrame "#∗".
    assert ( ({[+ s; l +]} ⊎ {[-l-]}) ≡ {[+s+]}) as -> by smultiset_solver.
    iIntros "?".
    iApply wp_tconseq. iApply (vmapsfrom_cleanup x l). iFrame "#∗".
    assert ( (∅ ⊎ {[+ l +]} ⊎ {[-l-]}) ≡ ∅) as -> by smultiset_solver. iIntros "R3".
    iApply wp_val.

    iMod ("AU" with "[-R2 R3 D HS]") as "HPOST".
    { iSmash. }

    iIntros "!> _". iApply wp_if. iIntros "!> _". iApply wp_let_noclean.
    wp_apply wp_load_inside. compute_done.
     iIntros (?) "(->&_&_&?) _". simpl.
    iApply wp_tconseq. iApply (debt_vtransfer x). iFrame.
    iIntros "(?&?)". clean_debt π.
    iApply wpc_exit; last iFrame. set_solver. rewrite pbt_PBT. iFrame.
    do 2 iStep.
    rewrite left_id_L. iApply "HPOST". by iFrame. }
  { wp_apply wp_cas_fail. 1-3:naive_solver.
    iIntros (?) "(->&_&?)".

    iDestruct "AU" as "[AU _]".
    iMod ("AU" with "[-D HS]").
    { iSmash. }
    clear dependent M xs0.

    iIntros "!> _".
    iApply wp_if. iIntros "!> _".
    iApply wp_tconseq. iApply (debt_vtransfer s). iFrame.
    rewrite union_idemp_L.
    iIntros "(?&?)". clean_debt π.
    iApply wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L -pbt_PBT. iFrame.
    iApply ("IH" with "[$]"). }
Qed.

Lemma free_innerList γ l xs M :
  innerList γ xs l ∗
  l ⟸? ∅ ∗ reg γ l ∗ l ↤?{1/2} ∅ ∗
  outsiders γ M ∗
  cells γ M =[#]=∗
  ♢(2*length xs) ∗ outsiders γ M ∗ cells γ M ∗
  handles xs.
Proof.
  iIntros "(Hs&?&His&?&?)". iIntros.

  iInduction xs as [|(x,(p,q)) xs] "IH" forall (l).
  { simpl. rewrite right_absorb.
    iMod diamonds_zero. rewrite handles_nil. iSmash. }
  iDestruct "Hs" as "[%[% (->&?&?&?&?&?&?&?)]]".
  iDestruct (mapsto_extract_size with "[$]") as "?".
  iDestruct "His" as "[% | [%l' (%Eq'&?)]]". congruence. inversion Eq'. subst l'.
  iMod (free_cell _ _ M with "[$][$]") as "(?&#?&?&?&?)".
  iMod (vmapsfrom_cleanup x with "[$][$]") as "(?&?)".
  iMod (vmapsfrom_cleanup v' with "[$][$]") as "(?&?)".
  assert (({[+ l0 +]} ⊎ {[-l0-]}) ≡ ∅) as -> by smultiset_solver.
  iMod ("IH" with "[$][$][$][$][$][$]") as "(?&?&?&?&?)".
  iFrame. iModIntro. simpl.
  conclude_diamonds.
Qed.

Lemma treiber_free s xs :
  stack s xs ∗ s ↤ ∅ ∗ s ⟸ ∅ =[#]=∗
  †s ∗ ♢(1 + 2*length xs) ∗ handles xs.
Proof.
  iIntros "(I&?&?)". iIntros.
  iDestruct "I" as "[%g [%M (_&I1&I2&I3&I4)]]".
  iDestruct "I1" as "[%h0 (S1&S2&S3&S4&S5)]".
  iMod (interp_free' s with "[$][$]") as "(?&C1&?&#?)".
  iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".

  assert (({[+ s +]} ⊎ {[-s-]}) ≡ ∅) as -> by smultiset_solver.
  iMod (free_innerList _ _ _ M with "[$][$]") as "(?&C2&?&?&?)". iFrame "#∗".
  conclude_diamonds.
Qed.

End Treiber_proof.
