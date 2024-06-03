From irisfit.examples Require Import proofmode ref list stack.

(* LATER later make_record *)

(* We encode fixed-capacity stacks as a record of an array and a size.
   We are parameterised by a capacity. *)

Module StackChunk(C:Capacity) : StackOf with
Definition capacity := Some (C.capacity).

Definition capacity := Some (C.capacity).
Definition capa := Pos.to_nat C.capacity.

Definition stack_empty : val :=
  λ: [[]],
    let: "c" := alloc 2 in
    let: "a" := alloc (capa) in
    "c".[0] <- "a" ;;
    "c".[1] <- 0;; (* The current size *)
    "c".

Definition stack_push : val :=
  λ: [["l","v"]],
    let: "size" := "l".[1] in
    let: "new_size" := 1 '+ "size" in
    let: "a" := "l".[0] in
    "a".["size"] <- "v";;
    "l".[1] <- "new_size".

Definition stack_pop : val :=
  λ: [["l"]],
    let: "size" := "l".[1] in
    let: "new_size" := "size" '- 1 in
    let: "a" := "l".[0] in
    let: "v" := "a".["new_size"] in
    "a".["new_size"] <- val_unit;; (* We remove l as an antecedent *)
    "l".[1] <- "new_size";;
    "v".

Definition stack_is_empty : val :=
  λ: [["l"]],
    let: "size" := "l".[1] in
    "size" '== 0.

Definition stack_is_full : val :=
  λ: [["l"]],
    let: "size" := "l".[1] in
    "size" '== capa.

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

Definition empty_cost : Qz := 2 + capa.
Definition cell_cost  : Qz := 0.

(* [ChunkInv A L] associates the model L with the concrete representation L. *)
Record ChunkInv (A L : list val) : Prop :=
  { chunk_front  : forall i, 0 <= i < length L -> (A !! i) = (L !! (length L - i - 1));
    chunk_tail   : forall i, length L <= i < length A -> (A !! i) = Some val_unit;
    chunk_length : length A = capa;
    chunk_correct : length L <= length A
  }.

(* [isChunk L a] *)
Definition isChunkOf `{interpGS0 Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qp * Qz))) (c:loc) : iProp Σ :=
  ∃ arr vs, c ↦ arr ∗ ⌜ChunkInv arr vs⌝ ∗ soup R {[+c+]} xs vs.

(* [Stack L s] *)
Definition StackOf `{interpGSMore Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qp * Qz))) (s:loc) : iProp Σ :=
  ∃ c i,
    s ↦ [val_loc c; val_int i] ∗ isChunkOf R xs c ∗ c ⟸ ∅ ∗ c ↤ {[+s+]} ∗ ⌜i = length xs⌝.

Ltac liago := try (subst; simpl; lia).

Ltac destruct_stack Hs :=
  iDestruct Hs as "[%c [%i (Hs & Hc & ? & ? & %Hi)]]".

Ltac destruct_chunk Ha :=
  iDestruct Ha as "[%arr [%vs [? [%AInv Hmfa]]]]".

Lemma bool_decide_iff (P : Prop) {dec : Decision P} Q :
  P <-> Q ->
  bool_decide P <-> Q.
Proof. case_bool_decide; naive_solver. Qed.

Lemma stack_is_empty_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs". destruct_stack "Hs". destruct_chunk "Hc".
  iApply wpc_noclean.
  wpc_call. wpc_let_noclean. wpc_load.
  iIntros. wpc_call_prim. iSplitR.
  { iPureIntro. apply bool_decide_iff.
    destruct xs; simpl in *. subst. done.
    split; subst; intros; try congruence. inversion H. }
  iExists _,_. iFrame. iSplitL. iExists _,_. by iFrame. done.
  Unshelve. all:exact inhabitant.
Qed.

Lemma stack_is_full_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  TID π
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs". destruct_stack "Hs". destruct_chunk "Hc".
  iApply wpc_noclean. wpc_call. wpc_let_noclean. wpc_load. iIntros.
  wpc_call_prim. simpl.
  iDestruct (big_sepL2_length with "[$]") as "%Hxs".
  iSplitR.
  { iPureIntro. destruct AInv as [_ _ ? Hco].
    apply bool_decide_iff. unfold capa in *.
    split.
    { intros Eq Hl. inversion Eq. lia. }
    { intros Hl. subst i. f_equal. lia. } }
  iSmash.
  Unshelve. all:exact inhabitant.
Qed.

Lemma ChunkInv_init :
  ChunkInv (replicate capa val_unit) nil.
Proof.
  constructor; try rewrite replicate_length; try easy; simpl.
  { intros. rewrite lookup_replicate; split; easy. }
  { lia. }
Qed.

Lemma stack_empty_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  TID π
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros.
  wpc_call.
  wpc_let_empty. rewrite /empty_cost.
  wpc_alloc. iIntros (l) "(?&?&?&_)".
  iApply (wpc_context_singleton l with "[$]").
  wpc_let_empty. wpc_alloc.
  { unfold capa. lia. }
  iIntros (l')  "(?&?&?&_)".
  wpc_let_empty. wpc_apply wpc_store. done. compute_done.
  iIntros ([]) "(?&?&_)".
  wpc_let_empty. wpc_apply wpc_store_no_loc. compute_done. compute_done.
  iIntros ([]) "?". simpl.
  pclean l'.
  wpc_val. iIntros. iFrame.
  iExists _,_. iFrame. rewrite left_id. iFrame.
  iSplitL; try easy.
  iExists _,nil. iFrame. simpl.
  iSplitR.
  { iPureIntro. rewrite /capa Nat2Z.id. apply ChunkInv_init. }
  { by iApply big_sepL2_nil. }
Qed.

Lemma ChunkInv_pop A v vs i :
  i = length vs ->
  ChunkInv A (v :: vs) ->
  ChunkInv (<[i:=()%V]> A) vs.
Proof.
  intros ? [Af At ? Ac].
  constructor.
  { intros j Hj. specialize (Af j).
    simpl in Af.
    rewrite list_lookup_insert_ne; liago.
    rewrite Af; liago.
    rewrite lookup_cons_ne_0; liago.
    f_equal. liago. }
  { intros j Hj. rewrite insert_length in Hj.
    destruct (decide (j=i)) as [->|].
    { rewrite list_lookup_insert //. liago. }
    { rewrite list_lookup_insert_ne //.
      rewrite At //. liago. } }
  { rewrite insert_length //. }

  { rewrite insert_length. simpl in *. liago. }
Qed.

Lemma stack_pop_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) s qp qz x xs :
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R ((x,(qp,qz))::xs) s)
  POST (fun v => R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  wpc_call.
  wpc_let_empty.
  wpc_load_no_loc. iIntros. simpl.
  wpc_let_empty. wpc_call_prim. simpl.
  wpc_let_empty. wpc_load. iIntros "(?&?)".
  iApply (wpc_let_vsingleton c with "[$]").
  { auto_locs. set_solver. }

  destruct_chunk "Hc".
  iDestruct (big_sepL2_length with "[$]") as "%Hl".
  assert (0 <= (S (length xs)) - 1 < length arr) as HAi.
  { destruct AInv as [_ _ _ Hco].
    subst. simpl in *. liago. }

  iDestruct (big_sepL2_cons_inv_l with "[$]") as
    "[%v [%vs' (%Heq & ((? & ? & ?) & ?))]]". subst vs.

  assert (arr !! ((S (length xs)) - 1) = Some v) as HAv.
  { destruct AInv as [Af _ _ _].
    rewrite Af. simpl in *.
    { assert ((S (length vs') - (length xs - 0) - 1) = 0) as -> by lia.
      easy. }
    { simpl in *. liago. } }
  simpl in *.

  rewrite Hi.
  wpc_apply wpc_load.
  { lia. }
  { rewrite list_lookup_total_alt Z2Nat.inj_sub; try lia. rewrite Nat2Z.id HAv //. }

  rewrite list_lookup_total_alt Z2Nat.inj_sub; try lia. rewrite Nat2Z.id HAv //.
  simpl. iFrame.
  iIntros (?) "(->&?&?) ?". rewrite left_id_L.
  iApply (wpc_context_vsingleton v with "[$]").

  wpc_let_empty. wpc_apply (wpc_store _ _ _ 1 ∅). compute_done. lia.
  iIntros (?) "(?&_&?)". simpl.
  wpc_let_empty. wpc_apply wpc_store_no_loc. compute_done. compute_done.
  iIntros. simpl. pclean c.

  iMod diamonds_zero.
  wpc_val. iIntros. iFrame.

  rewrite  !Z2Nat.inj_sub; try lia.
  rewrite list_lookup_total_alt Nat2Z.id HAv.
  iDestruct (vmapsfrom_join with "[$]") as "?".
  rewrite left_id. assert ({[-c-]} ⊎ {[+ c +]} ≡ ∅) as -> by smultiset_solver.
  unfold cell_cost. rew_qz.
  iFrame.

  iExists _,_.
  iFrame.
  iSplitL.
  2:{ iSteps. }
  iExists _,_. iFrame.

  iPureIntro.
  eapply ChunkInv_pop; eauto.
  lia.
Qed.

Lemma ChunkInv_push A v vs i :
  length vs < capa ->
  i = length vs ->
  ChunkInv A vs ->
  ChunkInv (<[i:=v]> A) (v :: vs).
Proof.
  intros ? ? [Af At ? Hc].
  constructor.
  { intros j Hj. simpl in Hj.
    destruct (decide (j=i)) as [->|].
    { rewrite list_lookup_insert; liago.
      simpl. assert ((S (length vs) - i - 1) = 0) as -> by lia.
      rewrite lookup_cons //. }
    { rewrite list_lookup_insert_ne //.
      rewrite lookup_cons_ne_0; liago.
      rewrite Af; liago.
      f_equal. liago. } }
  { intros j Hj. rewrite insert_length in Hj. simpl in Hj.
    destruct (decide (j=i)).
    { exfalso. lia. }
    { rewrite list_lookup_insert_ne //.
      rewrite At //. liago. } }
  { rewrite insert_length //. }
  { rewrite insert_length. liago. }
Qed.

Lemma stack_push_spec `{!interpGSMore Σ} π A (R:A -> val -> iProp Σ) s qp qz v x xs :
  size_lt (length xs) capacity ->
  qz ≠ 0%Qz ->
  CODE (stack_push [[s, v]])
  TID π
  SOUV {[s]}
  PRE  (♢ cell_cost ∗ StackOf R xs s ∗ R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅)
  POST (fun (_:unit) => StackOf R ((x,(qp,qz))::xs) s).
Proof.
  unfold size_lt, capacity.
  iIntros (? ?) "(_ & Hs & ? & ? & ?)".
  destruct_stack "Hs".
  wpc_call.
  wpc_let_noclean. wpc_load. iIntros.
  wpc_let_noclean. wpc_call_prim. simpl.
  wpc_let_noclean. wpc_load. iIntros "(?&?)".

  destruct_chunk "Hc".
  assert (0 <= length xs < length arr) as ?.
  { destruct AInv as [_ _ Hcl _]. unfold capa in *. liago. }

  iDestruct (big_sepL2_length with "[$]") as "%Hl".

  assert (arr !! (length xs) = Some ()%V).
  { destruct AInv as [_ -> _ _]; try easy.
    liago. }

  wpc_let_noclean. simpl.
  wpc_apply wpc_store. eauto. lia.
  iIntros (?) "(?&?&?)".
  rewrite left_id. rew_enc.

  pclean c. pclean v.

  iStep 6. iFrame.
  iSplitL; last first.
  { iPureIntro. lia. }
  iExists _,_. iFrame.
  iSplitR.
  { iPureIntro.
    apply ChunkInv_push; eauto; unfold capa; liago. }
  rewrite /soup. iFrame.
  Unshelve. all:exact inhabitant.
Qed.

Lemma soup_cleanup `{!interpGSMore Σ} A (R:A -> val -> iProp Σ) c xs vs :
  († c ∗ soup R {[+c+]} xs vs)%I =[#]=∗
  soup R ∅ xs vs.
Proof.
  iIntros "(#? & ?)".
  iInduction xs as [|(?,(?,?))] "IH" forall (vs).
  { iIntros. simpl. now iFrame. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]")
      as "[%v [%vs' (%E & (? & ?& ?) & ?)]]". subst.
    iIntros.
    iMod (vmapsfrom_cleanup with "[$] [$]") as "(? & ?)".
    rewrite disj_union_singleton_opposite.
    fold (soup R {[+c+]} xs vs').
    iMod ("IH" $! vs'  with "[$] [$]") as "(? & ?)".
    now iFrame. }
Qed.

Lemma stack_free `{!interpGSMore Σ} A (R:A -> val -> iProp Σ) s xs :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ StackOf R xs s =[#]=∗
  ♢(empty_cost+cell_cost*length xs) ∗ †s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(Hcs' & Hfs & Hs)". iIntros.
  destruct_stack "Hs".

  iMod (interp_free' s with "[$] [$]") as "(?&?&?&#Hs)"; try easy.
  iMod (mapsfrom_cleanup with "[$] [$]") as "(? & ?)".
  rewrite disj_union_singleton_opposite.

  destruct_chunk "Hc".
  iMod (interp_free with "[$] [$]") as "(? & ? & ? &?)"; try easy.
  iMod (soup_cleanup with "[$] [$]") as "(? & ?)".
  iDestruct (diamonds_join with "[$]") as "Hdiams".
  iFrame "Hs". iModIntro. iFrame.
  iSplitL "Hdiams". iFrame.
  { simpl. destruct AInv as [? ? -> ?].
    rewrite /empty_cost /cell_cost.
    conclude_diamonds. }
  { iExists _. unfold soup. iFrame. }
Qed.

End StackChunk.
