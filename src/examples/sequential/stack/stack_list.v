From irisfit.examples Require Import proofmode list stack ref.

Import ListsOf.

(* We encode stacks as pointers to a linked list. *)

Module StackList : StackOf with
Definition capacity := @None positive.
Definition capacity := @None positive.

Definition stack_empty : val :=
  λ: [[]],
    let: "l" := list_nil [[]] in
    ref [["l"]].

Definition stack_push : val :=
  λ: [["v", "s"]],
    let: "l" := get [["s"]] in
    let: "l2" := list_cons [["v","l"]] in (* here l is still pointed by s. *)
    set [["s", "l2"]].

Definition stack_pop : val :=
  λ: [["s"]],
    let: "l" := get [["s"]] in
    let: "x" := list_head [["l"]] in
    let: "l2" := list_tail [["l"]] in
    set [["s","l2"]];;
    "x".

Definition stack_is_empty : val :=
  λ: [["s"]],
    let: "l" := get [["s"]] in
    list_is_nil [["l"]].

Definition stack_is_full : val :=
  λ: [["_"]], false.

Lemma locs_stack_empty : locs stack_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_push : locs stack_push = ∅.
Proof. easy. Qed.
Lemma locs_stack_pop : locs stack_pop = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_empty : locs stack_is_empty = ∅.
Proof. easy. Qed.
Lemma locs_stack_is_full : locs stack_is_full = ∅.
Proof. easy. Qed.

(* Constant factors *)
Definition empty_cost : Qz := 1.
Definition cell_cost  : Qz := 2.

(* Stack has the full ownership of the pointer _and_ of the list.
   It even possesses a part of its Stackable, as the user will not deallocate the
   stack without giving "Stack" *)
Definition StackOf `{!interpGS0 Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qz * Qp))) (s:loc) : iProp Σ :=
  ∃ l:val,
    (* s is a reference to l *)
    isRef l s ∗
    (* The reference is invisible from the outside *)
    l ⟸? ∅ ∗ l ↤? {[+ s +]} ∗
    (* l denotes a list with content xs *)
    ListOf R xs l.

Ltac destruct_stack Hs :=
  iDestruct Hs as "[%l (Hs & ? & ? & Hl)]".

Lemma stack_is_empty_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  wpc_call.
  wpc_let_noclean.
  wpc_apply get_spec. iFrame. iIntros (r) "(->&?&?)".
  iApply wpc_postpone.
  wpc_apply @list_is_nil_spec. set_solver.
  iIntros (?) "(?&?)". pclean r.
  wpc_val. iFrame. iExists _. iFrame.
Qed.

Lemma stack_is_full_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  TID π
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof. iSteps. Qed.

Lemma stack_empty_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  TID π
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros.
  wpc_call.
  wpc_let_empty. unfold empty_cost.
  wpc_apply @list_nil_spec. rewrite left_id. iIntros (l) "(?&?&Hfl)". simpl.
  iApply wpc_postpone.
  iApply wpc_noclean.
  wpc_apply ref_spec. compute_done. iIntros (?) "(?&?&?&?&_)".
  rewrite left_id. iFrame. simpl.
  iDestruct (confront_pbt_vpbt with "[$]") as "%". by vm_compute. simpl.
  pclean l by ltac:(fun _ => destruct l; set_solver).
  wpc_val. iFrame. iExists _. iFrame.
Qed.

Lemma stack_push_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) s qp qz v x xs :
  size_lt (length xs) capacity ->
  qz ≠ 0%Qz ->
  CODE (stack_push [[v, s]])
  TID π
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅)
  POST (fun (_:unit) => StackOf R ((x,(qz,qp))::xs) s).
Proof.
  iIntros (_ ?) "(?&Hs&?&?&?)".
  destruct_stack "Hs".
  wpc_call.
  wpc_let_noclean.
  wpc_apply @get_spec. iIntros (?) "(->&?&?)". simpl.
  wpc_let_empty.
  wpc_apply @list_cons_spec_debt. set_solver. eauto. iFrame.
  iIntros (l') "(Hcl' & Hfl' & Hl')". simpl.
  iDestruct (confront_vpbt_vpbt with "[$]") as "%".
  { apply Qp.not_add_le_l. }
  pclean v.
  iSpecialize ("Hl'" with "[$]").
  rewrite opposite_singleton.
  iApply wpc_postpone.
  iApply wpc_noclean.
  wpc_apply set_spec. compute_done. iIntros ([]) "(?&?&?)".
  pclean l'. wpc_val.
  iExists _. rewrite left_id. iFrame.
  iApply "Hl'". iFrame.
Qed.

Lemma stack_pop_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) s qp qz x xs :
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R ((x,(qz,qp))::xs) s)
  POST (fun v => R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  wpc_call.
  wpc_let_noclean.
  wpc_apply @get_spec. iIntros (r) "(->&?&?)". simpl.
  iApply (wpc_let_vsingleton with "[$]"). set_solver.

  wpc_apply @list_head_spec. set_solver. iIntros (?) "(?&?&Hl)". iIntros.

  iApply (wpc_context_vsingleton v with "[$]").
  simpl. wpc_let_empty.

  wpc_apply @list_tail_spec. set_solver. iIntros (?) "[% (->&?&Hftl&?&?&?)]".
  simpl. wpc_let_noclean.

  wpc_apply set_spec. compute_done.  iIntros ([]) "(?&?&?)". simpl.

  iDestruct (mapsfrom_join l0 with "[$] [$]") as "?".
  assert ( ({[-s-]} ⊎ {[+ s +]}) ≡ ∅) as -> by smultiset_solver.
  rewrite left_id_L.

  pclean l0.
  iApply wpc_tconseq.
  { iApply (interp_free' l0). }
  iFrame. iIntros "(?&_&#?)".
  pclean v0.

  (* Now we clean. *)
  iApply wpc_tconseq.
  iApply (vmapsfrom_cleanup v).
  iFrame "#∗". iIntros "?".
  iApply wpc_tconseq.
  iApply (vmapsfrom_cleanup v0).
  iFrame "#∗". iIntros.

  (* Some rewriting *)
  assert (({[+ l0 +]} ⊎ {[-l0-]}) ≡ ∅) as -> by smultiset_solver.
  assert (({[+ l0; s +]} ⊎ {[-l0-]}) ≡ {[+s+]}) as -> by smultiset_solver.

  wpc_val. iIntros. iFrame. iExists _. iFrame.
Qed.

Lemma stack_free `{!interpGS0 Σ} A (R:A -> val -> iProp Σ) s xs :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ StackOf R xs s =[#]=∗
  ♢(empty_cost + cell_cost*length xs) ∗ † s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(Hs1 & Hs2 & Hs)". iIntros.
  destruct_stack "Hs".

  iMod (free_ref s l with "[$] [$]") as "(Hi & ? & #Hds)".
  iMod (vmapsfrom_cleanup with "[$] [Hi]") as "(? & ?)"; first iFrame.
  rewrite disj_union_singleton_opposite.

  iMod (list_free _ R l with "[$] [$]") as "(?&?&?)".
  iDestruct (diamonds_join with "[$]") as "?".
  iFrame. iModIntro. iFrame "Hds".
  conclude_diamonds.
  rewrite /empty_cost /cell_cost. rew_qz. lia.
Qed.
End StackList.
