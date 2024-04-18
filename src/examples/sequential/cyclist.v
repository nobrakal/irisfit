From irisfit.examples Require Import proofmode.

(* A cyclic list is either a reference to unit, or a reference to a
   proper list cycle.
   List cells are of the form [value,next]

   TODO: app
 *)

Definition singleton : val :=
  λ: [["x"]],
    let: "r" := alloc 2 in
    "r".[0] <- "x";;
    "r".[1] <- "r";;
    "r".

Definition copy2 : val :=
  λ: [["x"]],
    let: "x0" := "x".[0] in
    let: "x1" := "x".[1] in
    let: "r" := alloc 2 in
    "r".[0] <- "x0";;
    "r".[1] <- "x1";;
    "r".

Definition nil : val :=
  λ: [[]], alloc 1.

Definition cons : val :=
  λ: [["x", "l"]],
    let: "c" := "l".[0] in
    if: "c" '== val_unit
    then
      let: "c'" := singleton [["x"]] in
      "l".[0] <- "c'"
    else
      let: "r" := copy2 [["c"]] in
      "c".[0] <- "x";;
      "c".[1] <- "r".

Definition uncons : val :=
  λ: [["l"]],
    let: "c" := "l".[0] in
    let: "v" := "c".[0] in
    let: "n" := "c".[1] in
    if: "c" '== "n" then
      "l".[0] <- val_unit;; "v"
    else
      let: "nv" := "n".[0] in
      let: "nx" := "n".[1] in
      "c".[0] <- "nv";;
      "c".[1] <- "nx";;
      "v".

Definition next : val :=
  λ: [["l"]],
    let: "c" := "l".[0] in
    if: "c" '== val_unit then val_unit
    else
      let: "n" := "c".[1] in
      "l".[0] <- "n".

Section cyclist.
Context `{interpGS0 Σ}.

(* Segments of cyclic lists are never empty. *)
Fixpoint Seg (xs:list (val*(Qp *Qz))) (l1 l2:loc) : iProp Σ :=
  match xs with
  | [] => False
  | (x,(qp,qz))::xs => ∃ (l':loc),
  l1 ↦ [x; val_loc l'] ∗
  x ⟸?{qp} ∅ ∗ x ↤?{qz} {[+l1+]} ∗
  l' ↤{1/2} {[+l1+]} ∗ l' ⟸{1/2} ∅ ∗
  match xs with
  | [] => ⌜l' = l2⌝
  | _ => l' ⟸{1/2} ∅ ∗ l' ↤{1/2} ∅ ∗  Seg xs l' l2 end end.

Definition CycList (xs:list (val*(Qp *Qz))) (l:loc) : iProp Σ :=
  (if decide (xs = [])
  then l ↦ [val_unit]
  else ∃ l', l ↦ [val_loc l'] ∗ l' ⟸{1/2} ∅ ∗ l' ↤{1/2} {[+l+]} ∗ Seg xs l' l')%I.

Lemma nil_spec π :
  CODE (nil [[]])
  TID π
  PRE (♢1)
  POST (fun (l:loc) => CycList [] l ∗ l ⟸ {[π]} ∗ l ↤ ∅).
Proof. iSteps. Qed.

Lemma cyclist_cons_spec π x p q l xs :
  (is_loc x → q ≠ 0%Qz) ->
  CODE (cons [[x,l]])
  TID π
  SOUV {[l]}
  PRE (♢2 ∗ CycList xs l ∗ x ⟸?{p} {[π]} ∗ x ↤?{q} ∅)
  POST (fun (_:unit) => CycList ((x,(p,q))::xs) l).
Proof.
  iIntros (?) "(?&HL&?&?)".
  wpc_call.
  wpc_let_noclean.
  destruct xs as [|(v,(?,?)) ?].
  { wpc_load. iIntros "Hl".

    (* LATER a better bind... *)
    iApply wpc_bind_if_noclean. wpc_call_prim. rewrite bool_decide_true //.
    wpc_let_noclean.
    wpc_call. wpc_let_noclean. wpc_alloc. iIntros (r) "(?&?&Hpr&_)". simpl.
    wpc_let_noclean.

    wpc_store. iIntros "(?&?)".
    wpc_let_noclean.
    wpc_store. iIntros "(?&?)".
    simpl. rewrite !right_id left_id. wpc_val.

    iApply wpc_postpone.
    wpc_store. iIntros "(?&Hmr&_)". simpl.

    pclean x. pclean r with "Hpr". wpc_val.

    iAssert (r ↤{1/2} {[+r+]} ∗ r ↤{1/2} {[+l+]})%I with "[Hmr]" as "(?&?)".
    { iApply (mapsfrom_split with "[$]"); try done. rewrite Qz_div_2 //. }
    iDestruct "Hpr" as "(?&?)".
    iSmash. }
  { iDestruct "HL" as "[%l' (?&?&?&HS)]".
    wpc_load. iIntros "(?&?)".

    iApply wpc_bind_if_noclean. wpc_call_prim. rewrite bool_decide_false //.
    wpc_let_noclean. wpc_call.

    iDestruct "HS" as "[%l0 (?&?&?&?&?&HR)]".
    wpc_let_noclean.
    iDestruct (vmapsfrom_correct v with "[$]") as "%Hv".
    wpc_load. iIntros "(?&?)".

    wpc_let_noclean. wpc_load. iIntros "(?&?)".
    wpc_let_noclean. wpc_alloc. iIntros (r) "(?&Hmr&Hpr&_)".
    wpc_let_noclean. wpc_store.
    { intros. destruct Hv; first naive_solver. smultiset_solver. }
    iIntros "(?&?&?)".
    wpc_let_noclean.

    wpc_store. iIntros "(?&?&?)". wpc_val.
    wpc_let_noclean. wpc_store. iIntros "(?&?&?)".
    iApply wpc_postpone. wpc_store. iIntros "(?&?&?)". simpl.
    pclean x. pclean v. pclean l0. pclean l'. pclean r with "Hpr". wpc_val.
    rewrite !left_id.
    iExists l'. iFrame. iExists r. iFrame.
    iDestruct (mapsfrom_split r with "[$]") as "(?&?)"; last iFrame.
    1,2:by vm_compute. rewrite Qz_div_2 //. smultiset_solver.
    iDestruct "Hpr" as "(?&?)". iFrame. iExists _. iFrame.
    iDestruct (mapsfrom_join with "[$][$]") as "?".
    iDestruct (vmapsfrom_join with "[$]") as "?".
    rewrite !left_id.
    assert (({[-l'-]} ⊎ {[+ l'; r +]}) ≡ {[+r+]}) as -> by smultiset_solver.
    by iFrame.
  Unshelve. all:exact inhabitant. }
Qed.

Lemma cyclist_uncons_spec π x p q l xs :
  CODE (uncons [[l]])
  TID π
  SOUV {[l]}
  PRE (CycList ((x,(p,q))::xs) l)
  POST (fun (x:val) => ♢2 ∗ CycList xs l ∗ x ⟸?{p} {[π]} ∗ x ↤?{q} ∅).
Proof.
  iIntros "[%l0 (?&?&?&[% (?&?&?&?&?&HS)])]". fold (Seg xs l' l0).
  wpc_call.
  wpc_let_noclean. wpc_load. iIntros "(?&?)".
  wpc_let_noclean. wpc_load. iIntros "(?&?)".
  wpc_let_noclean. wpc_load. iIntros "(?&?)".
  destruct xs as [|(?,(?,?)) ?].
  { iDestruct "HS" as "->".
    iApply wpc_bind_if_noclean. wpc_call_prim. rewrite bool_decide_true //.
    wpc_let_noclean.

    wpc_store. iIntros "(?&_&?)". simpl.
    iDestruct (pbt_join with "[$]") as "?". rewrite Qp.div_2.
    iDestruct (confront_pbt_vpbt with "[$]") as "%". apply Qp.not_add_le_l.
    pclean l0 by ltac:(fun _ => destruct x; set_solver).
    replace ({[π; π]} ∖ {[π]}) with (∅ :gset thread_id) by set_solver.
    do 2 iDestruct (mapsfrom_join with "[$][$]") as "?".
    rewrite left_id Qz_div_2.
    assert ({[-l-]} ⊎ {[+ l0 +]} ⊎ {[+ l +]} ≡ {[+l0+]}) as -> by smultiset_solver.

    iApply wpc_tconseq.
    1:iApply (interp_free l0).
    2:iFrame. rewrite dom_psingleton //.
    iIntros "(?&_&?)".

    iApply wpc_tconseq. iApply vmapsfrom_cleanup.
    iFrame. assert (({[+ l0 +]} ⊎ {[-l0-]}) ≡ ∅) as -> by smultiset_solver.
    iIntros.  wpc_val. iFrame. }
  { iDestruct "HS" as "(?&?&[%l1 (?&?&?&?&?&?)])". fold (Seg xs l1 l0).
    iDestruct (pbt_join with "[$]") as "?".
    iDestruct (confront_pbt_pbt l0 l' with "[$]") as "%". by vm_compute.
    iApply wpc_bind_if_noclean. wpc_call_prim. rewrite bool_decide_false; last naive_solver.
    wpc_let_noclean. wpc_load. iIntros "(?&?)".
    wpc_let_noclean. wpc_load. iIntros "(?&?)".
    wpc_let_noclean.
    iDestruct (vmapsfrom_correct v with "[$]") as "%Hv".
    wpc_store.
    { intros. destruct Hv; smultiset_solver. }
    iIntros "(?&?&?)".
    wpc_let_noclean.
    wpc_store. iIntros "(?&?&?)". simpl.

    iDestruct (vmapsfrom_join with "[$]") as "?".
    do 2 iDestruct (mapsfrom_join with "[$][$]") as "?".
    rewrite !left_id right_id Qp.div_2 Qz_div_2.

    assert (({[-l0-]} ⊎ {[+ l0 +]}) ≡ ∅) as -> by smultiset_solver.
    iDestruct (confront_pbt_vpbt l' x with "[$]") as "%". apply Qp.not_add_le_l.
    pclean l' by ltac:(fun _ => destruct x; set_solver).

    iApply wpc_tconseq.
    1:iApply (interp_free l').
    2:iFrame. set_solver. iIntros "(?&_&#?)".

    iApply wpc_tconseq. iApply (mapsfrom_cleanup l1 l'). iFrame "#∗". iIntros.
    iApply wpc_tconseq. iApply (vmapsfrom_cleanup v l'). iFrame "#∗". iIntros.

    iApply wpc_conseq. iApply (vpbt_transfer x v). 3:iFrame. 1,2:set_solver. iIntros "(?&?)".

    (* LATER better lemma *)
    iApply wpc_conseq. iApply (vpbt_PBT_transfer _ _ x _ _ _ {[l0:= _]}).
    3:rewrite -pbt_PBT; iFrame. 1,2:set_solver. iIntros "(?&?)".
    iApply wpc_conseq. iApply (vpbt_PBT_transfer _ _ x _ _ _ {[l1:= _]}).
    3:rewrite -!pbt_PBT; iFrame. 1,2:set_solver. iIntros "(?&?)".
    rewrite difference_diag_L. simpl.

    assert (({[+ l'; l0 +]} ⊎ {[-l'-]}) ≡ {[+l0+]}) as -> by smultiset_solver.
    wpc_val. iFrame. iExists l0. iFrame. iExists l1. iFrame. }
  Unshelve. all:exact inhabitant.
Qed.

Definition rot1 {A:Type} (xs:list A) :=
  match xs with
  | [] => []
  | x::xs => xs ++ [x] end.

Local Lemma go xs v q q0 c c1 c2:
  v ⟸?{q} ∅ -∗
  v ↤?{q0} {[+ c +]}  -∗
  c2 ⟸{1 / 2} ∅ -∗
  Seg xs c1 c -∗
  c ↦ [v; (#c2)%V] -∗
  c ⟸{1 / 2} ∅ -∗
  c ↤{1 / 2} ∅ -∗
  c2 ↤{1 / 2} {[+ c +]} -∗
  Seg (xs ++ [(v, (q, q0))]) c1 c2.
Proof.
  iIntros "? ? ? Hxs ? ? ? ?". iInduction xs as [|(?,(?,?))] "IH" forall (c1); first done.
  { iDestruct "Hxs" as "[% (?&?&?&?&?&Hxs)]". fold (Seg xs l' c).
    simpl. iExists l'. iFrame.
    destruct xs.
    { iDestruct "Hxs" as "->". iSmash.  }
    { iDestruct "Hxs" as "(?&?&?)". iSmash. } }
Qed.

Lemma cyclist_next_spec π xs l :
  CODE (next [[l]])%I
  TID π
  SOUV {[l]}
  PRE (CycList xs l)
  POST (fun (_:unit) => CycList (rot1 xs) l).
Proof.
  iIntros "HL".
  wpc_call.
  wpc_let_noclean. destruct xs as [|(?,(?,?))].
  { wpc_load. iIntros.
    iApply wpc_bind_if_noclean. wpc_call_prim. rewrite bool_decide_true //.
    by wpc_val. }
  { iDestruct "HL" as "[%c (?&?&?&HS)]".
    wpc_load. iIntros "(?&?)".
    iApply wpc_bind_if_noclean. wpc_call_prim. rewrite bool_decide_false //.
    wpc_let_noclean.
    iDestruct "HS" as "[%c' (?&?&?&?&?&Hxs)]".
    wpc_load. iIntros "(?&?)". iApply wpc_postpone.
    wpc_store. iIntros "(?&?&?)". pclean c'. pclean c.
    wpc_val. simpl.
    iDestruct (mapsfrom_join c with "[$][$]") as "?".
    rewrite left_id.
    assert ({[-l-]} ⊎ {[+ l +]} ≡ ∅) as -> by smultiset_solver.
    rewrite /CycList. rewrite decide_False.
    2:{ by destruct xs. }
    iExists c'. iFrame.
    destruct xs.
    { iDestruct "Hxs" as "->".
      iDestruct (mapsfrom_join with "[$][$]") as "?". rewrite left_id.
      iDestruct (mapsfrom_split c _ _ _ _ {[+c+]} {[+l+]} with "[$]") as "(?&?)".
      3,4:reflexivity. 1,2:by vm_compute.
      iFrame. iExists _. by iFrame. }
    { iDestruct "Hxs" as "(?&?&HL)".
      iDestruct (mapsfrom_join c' with "[$][$]") as "?". rewrite right_id.
      iDestruct (mapsfrom_split c' _ _ _ _ {[+c+]} {[+l+]} with "[$]") as "(?&?)".
      3,4:reflexivity. 1,2:by vm_compute. iFrame. generalize (p :: xs). clear p xs. intros xs.
      iApply (go xs v q q0 c c' c' with "[$][$][$][$][$][$][$][$]"). } }
  Unshelve. all:exact inhabitant.
Qed.

Lemma seq_extract_size xs l l' :
  Seg xs l l' -∗ sizeof l 2.
Proof.
  iIntros "Hs".
  destruct xs as [|(?,(?,?))]; first done.
  iDestruct "Hs" as "[%(?&_)]".
  iApply (mapsto_extract_size with "[$]").
Qed.

Definition vmapsfromset v q (X:gset loc) : iProp Σ :=
  ∃ l, ⌜l ∈ X⌝ ∗ v ↤?{q} {[+l+]}.

Definition handles_pre X xs : iProp Σ :=
  [∗ list] x ∈ xs, let '(v,(p,q)) := x in v ⟸?{p} ∅ ∗ vmapsfromset v q X.

Lemma handles_clean X xs :
  handles_pre X xs ∗ ††X =[#]=∗ handles xs.
Proof.
  iIntros "(Hxs&#?)". iIntros.
  iInduction xs as [|(?,(?,?))] "IH"; first by iFrame.
  rewrite /handles_pre big_sepL_cons.
  iDestruct "Hxs" as "((?&[% (%&?)])&?)".
  iDestruct (daggers_extract with "[$]") as "#?". done.
  iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".
  assert (({[+ l +]} ⊎ {[-l-]}) ≡ ∅) as -> by smultiset_solver.
  iMod ("IH" with "[$][$]") as "(?&?)". by iFrame.
Qed.

Lemma seg_cloud S n1 l1 l2 xs ls :
  l1 ∈ S ->
  locs ls ⊆ S ->
  sizeof l2 2 ∗ l2 ⟸{1 / 2} ∅ ∗ l2 ↤{1/2} ∅ -∗
  ocloud S n1 ls -∗
  Seg xs l1 l2 -∗
  ∃ ls', ⌜l2 ∈ locs ls'⌝ ∗ ocloud (S ∪ locs ls') (n1 + 2*length xs) ls' ∗ handles_pre (S ∪ locs ls') xs.
Proof.
  iIntros (HS1 HS2) "(#?&?&?) ? HS".
  iInduction xs as [|(?,(?,?)) ?] "IH" forall (l1 S n1 ls HS1 HS2); first done.
  iDestruct "HS" as "[% (?&?&?&?&?&Hxs)]". fold (Seg xs l' l2).
  destruct xs as [|(?,(?,?)) ?].
  { iDestruct "Hxs" as "->".
    iDestruct (mapsfrom_join l2 with "[$][$]") as "?".
    iDestruct (pbt_join l2 with "[$]") as "?".
    rewrite right_id right_id_L Qp.div_2 Qz_div_2.
    iDestruct (ocloud_cons with "[$][$]") as "Ho". rewrite dom_psingleton. set_solver.
    iExists (l2::ls). rewrite cons_length nil_length Nat.mul_1_r Nat.add_comm.
    iSplitR; first (iPureIntro; auto_locs; set_solver).
    iSplitL "Ho".
    { iApply ocloud_extend; last iFrame. set_solver. }
    { iFrame. rewrite big_sepL_nil right_id. iExists _. iFrame. iPureIntro. set_solver. } }
  { iDestruct "Hxs" as "(?&?&?)".
    iDestruct (seq_extract_size with "[$]") as "#?".
    iDestruct (ocloud_extend _ ({[l']} ∪ S) with "[$]") as "?". set_solver.
    iDestruct ("IH" with "[%][%][$][$][$][$]") as "[% (%&?&?)]". set_solver. set_solver.

    iDestruct (mapsfrom_join l' with "[$][$]") as "?".
    iDestruct (pbt_join l' with "[$]") as "?".
    rewrite left_id left_id_L Qp.div_2 Qz_div_2.
    iDestruct (ocloud_cons with "[$][$]") as "?". rewrite dom_psingleton. set_solver.
    rewrite !cons_length.
    replace (2 + (n1 + 2 * Datatypes.S (length xs))) with (n1 + 2 * Datatypes.S (Datatypes.S (length xs))) by lia.
    replace ({[l']} ∪ S ∪ locs ls') with (S ∪ locs (l'::ls')) by (auto_locs; set_solver).
    iExists _. iFrame. iSplitR.
    { iPureIntro. auto_locs. set_solver. }
    { iExists _. iFrame.  iPureIntro. set_solver. } }
Qed.

Lemma cyclist_free l xs :
  (CycList xs l ∗ l ⟸ ∅ ∗ l ↤ ∅) =[#]=∗ ♢(1 + 2 * length xs) ∗ handles xs.
Proof.
  iIntros "(HL&?&?)". iIntros.
  destruct xs as [|x xs].
  { iMod (interp_free' with "[$][$]") as "(?&?&?&?)". iFrame. iSplitL. conclude_diamonds.
    by iApply handles_nil. }
  { iDestruct "HL" as "[%l' (?&?&?&?)]".
    iMod (interp_free' with "[$][$]") as "(?&?&_&?)".
    iMod (mapsfrom_cleanup l' l with "[$][$]") as "(?&?)".
    assert (({[+ l +]} ⊎ {[-l-]}) ≡ ∅) as -> by smultiset_solver.
    iDestruct (seq_extract_size with "[$]") as "#?".
    unshelve iDestruct (ocloud_empty {[l']}) as "?"; try apply _.
    iDestruct (seg_cloud with "[$][$][$]") as "[% (%&Ho&Ha)]". set_solver. set_solver.
    replace (({[l']} ∪ locs ls')) with (locs ls') by set_solver.
    iAssert (cloud (locs ls') (2* length (x :: xs))) with "[Ho]" as "?".
    { by iApply (ocloud_cloud with "[$]"). }
    iMod (supd_free_group with "[$][$]") as "(?&?&?)".
    iMod (handles_clean with "[$][$]") as "(?&?)".
    iFrame. conclude_diamonds. }
Qed.
End cyclist.
