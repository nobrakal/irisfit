From Coq Require Import QArith.Qcanon.

From irisfit.examples Require Import proofmode ref list stack seqproofmode.

(* Parent & child *)
Module StackSek (P : StackOf) (C : StackOf) : StackOf.

(* We are going to define a stack as a "stack of possibly bounded stacks".

   Given a parent / outer stack implementation P and a child / inner stack
   implementation C, we construct a new stack implementation as a record of:
   + A child stack
   + A parent stack of children.

   Therefore, the final capacity is: *)

Definition capacity :=
  match C.capacity,P.capacity with
  | Some c, Some p => Some (c + c*p)%positive
  | _,_ => None end.

(* The constants empty_cost & cell_cost expose an amortized space complexity:
   The user have to pay a little more at each push to ensure enough credit for the
   creation of a parent cell when needed *)

Definition provision_step : Qz :=
  match C.capacity with
  | None => 0
  | Some c => (C.empty_cost + P.cell_cost) / pos_to_Qp c end.

Definition empty_cost : Qz :=
  2 + C.empty_cost + P.empty_cost.
Definition cell_cost : Qz :=
  C.cell_cost + provision_step.

(* Then the code itself. *)

Definition stack_empty : val :=
  λ: [[]],
    let: "stack" := alloc ^2 in
    let: "front" := C.stack_empty [] in
    let: "tail"  := P.stack_empty [] in
    "stack".[0] <- "front";;
    "stack".[1] <- "tail";;
    "stack".

Definition stack_push : val :=
  λ: [["v","stack"]],
    let: "front" := "stack".[0] in
    let: "is_full" := C.stack_is_full [["front"]] in
    if: "is_full" then
      let: "newfront" := C.stack_empty [] in
      "stack".[0] <- "newfront";;
      let: "tail" := "stack".[1] in
      P.stack_push [["front", "tail"]];;
      C.stack_push [["v", "newfront"]]
    else
      C.stack_push [["v", "front"]].

Definition stack_pop : val :=
  λ: [["stack"]],
    let: "front" := "stack".[0] in
    let: "x" := C.stack_pop [["front"]] in
    let: "front_is_empty" := C.stack_is_empty [["front"]] in
    let: "_" :=
      if: "front_is_empty" then
        let: "tail" := "stack".[1] in
        let: "tail_is_empty" := P.stack_is_empty [["tail"]] in
        if: "tail_is_empty" then val_unit else
          let: "newfront" := P.stack_pop [["tail"]] in
          "stack".[0] <- "newfront"
      else val_unit in
    "x".

Definition stack_is_empty : val :=
  λ: [["stack"]],
    let: "front" := "stack".[0] in
    C.stack_is_empty [["front"]].

Definition stack_is_full : val :=
  λ: [["stack"]],
    let: "front" := "stack".[0] in
    let: "tail" := "stack".[1] in
    let: "fi" := C.stack_is_full [["front"]] in
    let: "ft" := P.stack_is_full [["tail"]] in
    "fi" '&& "ft". (* The stack is full iff its front & tail are full *)

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

(* ------------------------------------------------------------------------ *)
(* Potential *)

Definition potential (lLF:nat) : Qz :=
  lLF * provision_step.

Lemma potential_zero : potential 0 = 0.
Proof.
  rewrite /potential. rewrite left_absorb //.
Qed.

Lemma potential_full c :
  C.capacity = Some c ->
  potential (Pos.to_nat c) = (C.empty_cost + P.cell_cost)%Qz.
Proof.
  intros Hc.
  rewrite /potential /provision_step Hc.
  assert (nat_to_Qz (Pos.to_nat c) = Qp_to_Qz (pos_to_Qp c)) as ->.
  { rewrite pos_to_qz_through_nat //. }
  rewrite Qz_mul_div_r //.
Qed.

Lemma potential_step n :
  (provision_step + potential n)%Qz = potential (1+n).
Proof.
  rewrite /potential /provision_step.
  destruct C.capacity; simpl; rew_qz; try lia.
  rewrite -Qz_mul_succ_l. rew_qz.
  easy.
Qed.

Module DP := StackDominant(P).

Definition IsFull {A} (L:list A) := Some (length L) = Pos.to_nat <$> C.capacity.

Record StackInv {A} (L LF:list A) (LS:list (list A)) : Prop :=
  make_StackInv {
      stack_items : L = LF ++ concat LS;
      stack_tail_full : Forall IsFull LS;
      stack_tail_nil : LF = nil -> LS = nil;
      stack_front_length :
      match C.capacity with None => True | Some c => length LF <= Pos.to_nat c end;
      stack_tail_length :
      match P.capacity with None => True | Some c => length LS <= Pos.to_nat c end
    }.

Definition StackOf `{!interpGS0 Σ} {A} (R:A -> val -> iProp Σ) (xs:list (A * (Qz * Qp))) (s:loc) : iProp Σ :=
  ∃ (f t:loc) (LF:list (A * (Qz * Qp))) (LT:list (list (A * (Qz * Qp)))),
    ⌜StackInv xs LF LT⌝ ∗ ♢ (potential (length LF)) ∗
    s ↦ [val_loc f;val_loc t] ∗ f ⟸ ∅ ∗ f ↤ {[+ s +]} ∗
      t ⟸ ∅ ∗ t ↤ {[+ s +]} ∗
      C.StackOf R LF f ∗
      DP.StackDominantOf (fun xs => post (C.StackOf R xs)) 1%Qp LT t.

Ltac destruct_stack Hs :=
  iDestruct Hs as
    "[%f [%t [%LF [%LT (%Hinv & Hdiams & ? & ? & ? & ? & ? & Hf & Ht)]]]]".

Lemma stack_is_empty_spec `{interpGS0 Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_empty [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> xs=nil⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs".
  destruct_stack "Hs".
  pose proof C.locs_stack_is_empty.
  wpc_call. wpc_let_empty. wpc_load.
  iIntros "(?&?)".
  iApply wpc_postpone.
  iApply (wpc_context_vsingleton (val_loc f) with "[$]").
  wpc_apply C.stack_is_empty_spec. set_solver.
  iIntros (n) "[%Hn ?] ?".
  pclean f. simpl. wpc_val.
  iSplitR.
  { destruct Hinv as [? ? Ht]. iPureIntro. subst.
    split; intros He.
    { apply Hn in He. rewrite He Ht //. }
    { apply app_nil in He; destruct He. intuition. } }
  { iExists _,_,_,_. by iFrame. }
Qed.

Lemma length_concat A c (xs:list (list A)):
  Forall (fun x => length x = c) xs ->
  length (concat xs) = c * length xs.
Proof.
  induction xs; simpl; try lia.
  intros E. apply Forall_cons_1 in E. destruct E.
  rewrite app_length IHxs //. lia.
Qed.

Lemma length_concat_full A c (xs:list (list A)):
  C.capacity = Some c ->
  Forall IsFull xs ->
  length (concat xs) = (Pos.to_nat c * length xs).
Proof.
  intros Hc ?.
  eapply length_concat; eauto.
  eapply Forall_impl; eauto.
  unfold IsFull. rewrite Hc. intros ? E. injection E. easy.
Qed.

Lemma mult_neq_zero (n m : nat) :
  n * m ≠ 0 <-> n ≠ 0 /\ m ≠ 0.
Proof. lia. Qed.

Lemma stack_is_full_correct A nf nt (xs LF : list A) LT :
  StackInv xs LF LT ->
  nf ↔ ¬ size_lt (length LF) C.capacity ->
  nt ↔ ¬ size_lt (length LT) P.capacity ->
  nf /\ nt ↔ ¬ size_lt (length xs) capacity.
Proof.
  intros [-> ? Hf Ht] Hnf Hnt.
  unfold size_lt in *.
  rewrite /capacity.
  destruct C.capacity eqn:Hc.
  2:{ naive_solver. }
  destruct P.capacity.
  2:{ naive_solver. }
  rewrite app_length. erewrite length_concat_full; eauto.
  naive_solver by nia.
Qed.

Lemma stack_is_full_spec `{interpGS0 Σ} π A (R:A -> val -> iProp Σ) xs s :
  CODE (stack_is_full [[s]])
  TID π
  SOUV {[s]}
  PRE (StackOf R xs s)
  POST (fun (b:bool) => ⌜b <-> ¬ (size_lt (length xs) capacity)⌝ ∗ StackOf R xs s).
Proof.
  iIntros "Hs".
  pose proof C.locs_stack_is_full.
  pose proof P.locs_stack_is_full.

  wpc_call. destruct_stack "Hs".
  iApply wpc_postpone.
  wpc_let_noclean. wpc_load. iIntros "(?&?)".
  wpc_let_noclean. wpc_load. iIntros "(?&?)".
  iApply (wpc_context_singleton t with "[$]").
  iApply (wpc_context_singleton f with "[$]").

  wpc_let_empty.
  wpc_apply C.stack_is_full_spec. set_solver. iIntros (?) "(%Hnf & ?)".
  simpl. wpc_let_empty.
  wpc_apply DP.stack_is_full_spec_dominant. set_solver.
  iIntros (?) "(%Hnt & ?)". wpc_call_prim. iIntros.
  pclean f. pclean t. wpc_val. iIntros.
  iSplitR.
  { simpl. rewrite andb_True. eauto using stack_is_full_correct. }
  iExists f,t,_,_. by iFrame.
Qed.

Lemma StackInv_empty A :
  @StackInv A nil nil nil.
Proof.
  constructor; try easy.
  unfold size_lt.
  destruct C.capacity; simpl in *; lia.
  destruct P.capacity; simpl in *; lia.
Qed.

Lemma stack_empty_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) :
  CODE (stack_empty [[]])
  TID π
  PRE  (♢ empty_cost)
  POST (fun s => StackOf R [] s ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros. rewrite /empty_cost.
  pose proof C.locs_stack_empty.
  pose proof P.locs_stack_empty.
  wpc_call.
  wpc_let_noclean.
  mine 2.
  2:{ rewrite -assoc Qz_add_sub Qz_add_comm //. }
  wpc_alloc. iIntros (s) "(?&?&?&_)".
  iApply (wpc_context_singleton s with "[$]").
  iApply wpc_postpone.
  wpc_let_empty.

  assert ((Z.to_nat 2 + C.empty_cost + P.empty_cost - Z.to_nat 2)%Qz = (C.empty_cost + P.empty_cost)%Qz ) as ->.
  { rewrite -assoc Qz_add_sub //. }
  iDestruct (diamonds_split with "[$]") as "(Hdc & Hdp)".
  wpc_apply (C.stack_empty_spec _ _ R). set_solver.
  iIntros (c) "(? & ? & ?)".
  iApply (wpc_context_singleton c with "[$]").

  simpl. wpc_let_empty.
  wpc_apply (DP.stack_empty_dominant_spec _ _ (λ xs : list (A * (Qz * Qp)), post (C.StackOf R xs))). set_solver.
  iIntros (p) "(? & ? & ?)".
  simpl. wpc_let_noclean. wpc_store. iIntros "(?&?&_)".
  rewrite left_id.
  wpc_let_noclean. wpc_store. iIntros "(?&?&_)". simpl.
  pclean p. wpc_val. iIntros. pclean c.
  wpc_val.
  rewrite left_id. iIntros.
  iFrame.
  iExists c,p,_,_. iFrame.
  rewrite potential_zero. iFrame.
  eauto using StackInv_empty.
Qed.

Lemma StackInv_push A x (xs LF:list A) LT :
  size_lt (length LF) C.capacity ->
  StackInv xs LF LT ->
  StackInv (x::xs) (x::LF) LT.
Proof.
  intros ? [Hi ? ? ?].
  constructor; try easy.
  rewrite Hi //.
Qed.

Lemma StackInv_push' A x (xs LF:list A) LT :
  size_lt (length LT) P.capacity ->
  IsFull LF ->
  StackInv xs LF LT ->
  StackInv (x::xs) [x] (LF::LT).
Proof.
  intros ? ? [Hi ? ? ?].
  constructor; try easy.
  { rewrite Hi //. }
  { now constructor. }
  { destruct C.capacity; simpl in *; lia. }
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
  iIntros (Hiu ?) "(? & Hs & ? & ? & ?)".
  pose proof C.locs_stack_is_full.
  pose proof C.locs_stack_empty.
  pose proof C.locs_stack_push.
  pose proof P.locs_stack_push.
  wpc_call.
  destruct_stack "Hs".

  wpc_let_noclean. wpc_load. iIntros "(?&?)".

  iApply wpc_postpone.
  iApply (wpc_let_2v (val_loc f) v with "[$][$]").
  { auto_locs. set_solver. }
  wpc_apply C.stack_is_full_spec. set_solver.
  iIntros (n) "[%Hn Hf]". iIntros.

  simpl. wpc_if.

  destruct n.
  (* The front is full, we need to push it. *)
  { assert (¬ size_lt (length LF) C.capacity) as Hcapa by naive_solver. clear Hn.
    unfold size_lt in *.
    destruct C.capacity as [c|] eqn:Hc; try easy.
    assert (length LF = Pos.to_nat c) as Hlf.
    { destruct Hinv as [_ _ _ Hlf]. rewrite Hc in Hlf. simpl in *. lia. }
    rewrite Hlf potential_full //.

    iApply (wpc_let_2v (val_loc f) v with "[$][$]").
    { auto_locs. set_solver. }

    iDestruct (diamonds_split with "[$]") as "[Hd1  Hd2]".
    wpc_apply (C.stack_empty_spec _ _ R). set_solver. iIntros (nf) "(? & ? & ?)".
    iIntros.
    iApply (wpc_context_singleton nf with "[$]").

    simpl. wpc_let_noclean. wpc_store. iIntros "(?&?&?)".

    wpc_let_noclean. wpc_load. iIntros "(?&?)".

    simpl. iApply (wpc_let_vsingleton with "[$]").
    { auto_locs. set_solver. }

    assert (size_lt (length LT) P.capacity).
    { unfold size_lt.
      rewrite /capacity Hc in Hiu.
      destruct Hinv.
      destruct P.capacity; try easy. subst.
      rewrite app_length (length_concat_full _ c) // in Hiu.
      nia. }

    iDestruct (mapsfrom_join with "[$][$]") as "?".
    assert ({[-s-]} ⊎ {[+ s +]} ≡ ∅) as -> by smultiset_solver.
    rewrite !left_id.

    iApply (wpc_context_singleton t with "[$]").
    wpc_apply DP.stack_push_dominant_spec; eauto. set_solver.
    rewrite post_loc. iFrame. iIntros.

    rewrite /cell_cost.
    iDestruct (diamonds_split with "[$]") as "(? & ?)".

    wpc_apply C.stack_push_spec.
    { set_solver. }
    { unfold size_lt. rewrite Hc. simpl in *. lia. }
    { eauto. }

    iIntros. pclean t. pclean nf. wpc_val.
    iExists _,_,_,_. iFrame.
    iSplitR.
    { iPureIntro. apply StackInv_push'; try easy. unfold IsFull.
      rewrite Hc Hlf. easy. }
    { rewrite /potential Qz_mul_1_l.
      conclude_diamonds. } }
  { rewrite /cell_cost.
    iDestruct (diamonds_split with "[$]") as "(? & ?)".

    assert (size_lt (length LF) C.capacity).
    { unfold size_lt in *. destruct C.capacity as [c|]; try easy.
      destruct (decide (length LF < Pos.to_nat c)); try easy.
      exfalso. intuition. }
    iApply (wpc_context_singleton f with "[$]").
    wpc_apply C.stack_push_spec; try easy. set_solver.
    iIntros. pclean f. wpc_val.

    iExists _,_,_,_. iFrame.
    iSplitR.
    { eauto using StackInv_push. }
    { conclude_diamonds. apply potential_step. } }
Qed.

Module MC := MoreStackOf(C).

Lemma StackInv_pop A x (xs LF:list A) LT :
  (LF = [] -> LT = []) ->
  StackInv (x::xs) (x::LF) LT ->
  StackInv xs LF LT.
Proof.
  intros ? [Hi ? ? Hf].
  simpl in *. injection Hi. intros. subst.
  constructor; try easy.
  destruct C.capacity; simpl in *; lia.
Qed.

Lemma StackInv_pop' A x (hLT:list A) tLT :
  StackInv (x :: hLT ++ concat tLT) [x] (hLT :: tLT) ->
  StackInv (hLT ++ concat tLT) hLT tLT.
Proof.
  intros [? Hf ? ?].
  apply Forall_cons_1 in Hf. destruct Hf as (Hh & ?).
  unfold IsFull in *.
  constructor; try easy.
  { intros ->.
    destruct C.capacity as [c|]; simpl in *; try easy.
    injection Hh. intros ?. pose proof (Pos2Nat.is_pos c). lia. }
  { destruct C.capacity; try easy. injection Hh. lia. }
  { destruct P.capacity; simpl in *; lia. }
Qed.

Lemma stack_pop_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) s qp qz x xs :
  CODE (stack_pop [[s]])
  TID π
  SOUV {[s]}
  PRE  (StackOf R ((x,(qz,qp))::xs) s)
  POST (fun v => R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅ ∗ StackOf R xs s ∗ ♢ cell_cost).
Proof.
  iIntros "Hs".
  pose proof C.locs_stack_is_empty.
  pose proof P.locs_stack_is_empty.
  pose proof P.locs_stack_pop.
  pose proof C.locs_stack_pop.
  wpc_call.

  destruct_stack "Hs".

  wpc_let_noclean. wpc_load. iIntros "(?&?)".

  iApply (wpc_let_vsingleton f with "[$]").
  { auto_locs. set_solver. }

  assert (LF ≠ nil).
  { destruct Hinv as [HE _ Ht _].
    intros ->. rewrite Ht in HE; easy. }

  wpc_apply MC.stack_pop_spec'.
  { set_solver. }
  eauto.
  iIntros (v) "[%x' [%LF' [%qz' [%qp' (%HE' & ? & ? & ? & Hf & Dpop)]]]] ?".

  generalize Hinv. intros [HE Hf Ht ?].
  rewrite HE' in HE. simpl in HE. injection HE. intros.
  subst x' qz' qp'.

  rewrite /cell_cost.
  assert (potential (length LF) =
            (provision_step + potential (length LF'))%Qz ) as ->.
  { rewrite /potential HE'. simpl.
    assert (nat_to_Qz (S (length LF')) = 1 + nat_to_Qz (length LF'))%Qz as ->.
    { rew_qz. lia. }
    rewrite Qz_mul_succ_l //. }
  iDestruct (diamonds_split with "[$]") as "(Dpro & Drest)".

  iDestruct (diamonds_join with "[Dpop Dpro]") as "?". iFrame "Dpop". iFrame.

  simpl. iApply (wpc_context_vsingleton with "[$]").
  iApply (wpc_let_vsingleton f with "[$]").
  { auto_locs. set_solver. }
  wpc_apply C.stack_is_empty_spec. set_solver.
  iIntros (n) "[%Hn Hf] ?".

  simpl. wpc_let_empty.
  wpc_if.

  destruct n; last first.
  (* The front chunk is not empty *)
  { pclean f. iStep 6. iIntros. iFrame.
    iExists _,_,_,_. iFrame.
    iPureIntro. subst.
    eapply StackInv_pop; eauto.
    intros ->. exfalso. destruct Hn as (_&Hn). now apply Hn. }

  (* The front chunk is now empty, we try to pop in the tail. *)
  { assert (LF' = nil) by (now apply Hn). subst LF'. clear Hn.
    wpc_let_noclean. wpc_load. iIntros "(?&?)".
    iApply (wpc_let_vsingleton t with "[$]").
    { auto_locs. set_solver. }
    wpc_apply DP.stack_is_empty_spec_dominant.
    { set_solver. }
    iIntros (nt) "[%Hnt ?]". iIntros.

    simpl. wpc_if.

    destruct nt.
    (* The tail is empty, the whole stack is now empty. *)
    { pclean t. pclean f. iStep 8. iFrame.
      rewrite /cell_cost. iFrame.
      iExists f,t,_,_. iFrame.
      iPureIntro.
      eapply StackInv_pop; naive_solver. }

    (* The tail is not empty, we pop a chunk ! *)
    { iApply (wpc_let_vsingleton t with "[$]"). set_solver.
      wpc_apply DP.stack_pop_dominant_spec'. set_solver. naive_solver.
      iIntros (vnf) "[%y [%ys [%Heys (Hpost & ? & ? & ? & ?)]]] ?".
      iDestruct "Hpost" as "[%nf [%Enf ?]]". subst vnf. iIntros.
      rew_enc. wpc_store. iIntros "(?&?&?)".

      pclean f. pclean nf. pclean t.
      rewrite left_id. simpl.
      iDestruct (mapsfrom_join with "[$][$]") as "?".
      rewrite left_id. assert (({[-s-]} ⊎ {[+ s +]}) ≡ ∅) as -> by smultiset_solver.

      iApply @wpc_tconseq.
      { iApply @C.stack_free. }
      iFrame.

      iIntros "(Dof & ? & ?)".
      iStep 6. iIntros. iFrame.
      iExists nf,t,_,_. iFrame.
      do 2 iDestruct (diamonds_join with "[$]") as "?".
      iSplitR.
      { subst. simpl in *. eauto using StackInv_pop'. }
      { conclude_diamonds.
        subst.

        rewrite potential_zero right_id right_absorb right_id.

        apply Forall_cons in Hf.
        destruct Hf as (Hy & _).
        unfold IsFull in *.
        destruct C.capacity eqn:E; simpl in *; try easy. injection Hy.
        intros ->.
        rewrite potential_full //. } } }
Qed.

Lemma soup_app `{!interpGS0 Σ} A (R:A -> val -> iProp Σ) e l r ls rs :
  soup R e l ls ∗ soup R e r rs -∗
  soup R e (l++r) (ls ++ rs).
Proof.
  iIntros  "[Hl Hr]".
  iApply (big_sepL2_app with "[Hl] [Hr]"); iFrame.
Qed.

Lemma soup_app_exists `{!interpGS0 Σ} A (R:A -> val -> iProp Σ) e l r :
  (∃ ls, soup R e l ls) ∗ (∃ rs, soup R e r rs) -∗
  ∃ lrs, soup R e (l++r) (lrs).
Proof.
  iIntros  "[[%ls ?] [%rs ?]]".
  iDestruct (soup_app _ _ _ l with "[$]") as "?".
  iExists _. iFrame.
Qed.

Lemma free_soup_children `{!interpGS0 Σ} A (R:A -> val -> iProp Σ) LT vs c :
  C.capacity = Some c ->
  Forall IsFull LT ->
  ([∗ list] x;v ∈ LT;vs, v ↤? ∅ ∗ v ⟸? ∅ ∗ post (C.StackOf R x) v) =[#]=∗
     ♢((C.empty_cost+C.cell_cost*(Pos.to_nat c)) * length LT) ∗ ∃ vs', soup R ∅ (concat LT) vs'.
Proof.
  iIntros (Hc Hf).
  iInduction LT as [|x LT] "IH" forall (vs); iIntros "?"; iIntros.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hvs".
    subst. simpl. rewrite right_absorb.
    iMod diamonds_zero. iFrame. iExists nil. by iApply big_sepL2_nil. }
  { iDestruct (big_sepL2_cons_inv_l with "[$]") as "[%v' [%vs' (%Hvs' & (Hml & Hcl & Hpost) & Hvs')]]".
    subst.
    apply Forall_cons_1 in Hf. destruct Hf as (Hx&?).
    iDestruct "Hpost" as "[%l (%Hl & Hl)]". subst. rew_enc. simpl.

    iMod ("IH" with "[%] [$] [$]") as "(Hr & Dvs' & Hs)".
    { eauto. }
    iClear "IH".

    iMod (C.stack_free _ R l x with "[$] [$]") as "(? & ? & ? & Hs')"; try iFrame.
    iModIntro.
    iDestruct (diamonds_join with "[$]") as "?".
    iDestruct (diamonds_eq with "[$]") as "?"; last iFrame.
    { rewrite /IsFull Hc in Hx. injection Hx. intros ->.
      rewrite (comm Qz_mul _  (length LT)) (comm Qz_mul _ (S (length LT))).
      rewrite -Qz_mul_succ_l. f_equal.
      now rew_qz. }
    iApply soup_app_exists. iFrame. }
Qed.

Lemma StackInv_capa_None A xs LF LT :
  C.capacity = None ->
  @StackInv A xs LF LT ->
  LT = nil /\ xs = LF.
Proof.
  intros Hc [-> Ht _ _ _].
  destruct LT; simpl.
  { rewrite right_id //. }
  { exfalso. apply Forall_cons_1 in Ht. destruct Ht as (Hf & ?).
    rewrite /IsFull Hc in Hf. inversion Hf. }
Qed.

Lemma StackInv_inv_length A xs LF LT c :
  C.capacity = Some c ->
  @StackInv A xs LF LT ->
  length xs = length LF + Pos.to_nat c * length LT.
Proof.
  intros Hc [-> Ht _ _ _].
  rewrite app_length (length_concat_full _ c) //.
Qed.

Lemma stack_free `{!interpGS0 Σ} A (R:A -> val -> iProp Σ) s xs :
  s ⟸ ∅ ∗ s ↤ ∅ ∗ StackOf R xs s =[#]=∗
  ♢(empty_cost+cell_cost*length xs) ∗ †s ∗
  (∃ vs, soup R ∅ xs vs).
Proof.
  iIntros "(? & ? & Hs)". iIntros.
  destruct_stack "Hs".

  iMod (@interp_free _ _ _ s with "[$] [$]") as "(? & Dblock &?& #Hs)"; try easy.

  iMod (mapsfrom_cleanup f s with "[$] [$]") as "(? & ?)".
  iMod (mapsfrom_cleanup t s with "[$] [$]") as "(? & ?)".
  assert (({[+ s +]} ⊎ {[-s-]}) ≡ ∅) as -> by smultiset_solver.

  iMod (C.stack_free _ R f with "[$] [$]") as "(? & Df & #Hf & ? )"; try easy.
  iMod (DP.stack_dominant_free _ _ 1%Qp LT t  with "[$] [$]") as "(? & Dt & #Ht & [%vc Hchildren] )"; try easy.

  iFrame "Hs".

  destruct C.capacity as [c|] eqn:Hc.
  { iMod (free_soup_children with "[$] [$]") as "(? & Dc & ?)". 1,2:(destruct Hinv; now eauto).
    iFrame. iModIntro.
    iSplitL "Hdiams Dblock Df Dt Dc"; last first.
    { destruct Hinv as [-> _ _ _ _]. iApply soup_app_exists. iFrame. }
    rewrite /empty_cost.
    do 2 iDestruct (diamonds_split with "[$]") as "[? ?]".
    rewrite /potential.
    rewrite /cell_cost.
    eapply StackInv_inv_length in Hinv; eauto. rewrite Hinv.
    rewrite nat_to_Qz_add Qz_mul_add_distr_l.
    do 2 rewrite Qz_mul_add_distr_r.
    rewrite (comm _ provision_step).
    repeat rewrite diamond_split_iff. iFrame.
    rewrite -diamond_split_iff.
    iDestruct (diamonds_join with "[$]") as "?".

    do 2 rewrite -Qz_mul_add_distr_r.
    rewrite nat_to_Qz_mul. rewrite (assoc Qz_mul).
    conclude_diamonds.
    f_equal.

    rewrite /provision_step Hc pos_to_qz_through_nat.
    rewrite Qz_mul_add_distr_r Qz_mul_div_l.
    rewrite (comm Qz_add P.cell_cost) assoc. f_equal.
    rewrite (comm Qz_add) //. }
  { apply StackInv_capa_None in Hinv; last easy.
    destruct Hinv. subst.
    iDestruct (big_sepL2_nil_inv_l with "[$]") as "%Hvs". subst.
    iFrame.
    rewrite /empty_cost.
    do 2 iDestruct (diamonds_split with "[$]") as "[? ?]".
    repeat rewrite diamond_split_iff. iFrame.
    do 2 iDestruct (diamonds_join with "[$]") as "?".
    conclude_diamonds.
    simpl. rewrite right_absorb right_id.
    rewrite /cell_cost /potential /provision_step Hc right_id right_absorb right_id //. }
Qed.
End StackSek.
