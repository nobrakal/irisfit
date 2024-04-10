From iris.algebra Require Import auth gset list excl_auth.
From iris.base_logic.lib Require Import gen_heap.

From iris.base_logic.lib Require Export ghost_map invariants.
From irisfit.examples Require Export proofmode.
From irisfit.examples.lockfree.michael_scott Require Export reachable ms_code.

(******************************************************************************)
(* The cmra we need *)

Canonical Structure valO := leibnizO val.
Canonical Structure locO := leibnizO loc.
Canonical Structure QzO := leibnizO Qz.
Notation modelO := (listO (prodO valO (prodO fracO QzO))).
Notation elem := (val * (Qp * Qz))%type.
Notation model  := (list elem)%type.

Class queueG Σ :=
  QueueG {
      queue_tokG : inG Σ (excl_authUR modelO);
      queue_cellsG : ghost_mapG Σ loc val;
      queue_jmmutG : ghost_mapG Σ loc (option loc);
      queue_gsetG : inG Σ (authUR (gsetUR loc));
    }.

Definition queueΣ : gFunctors :=
  #[ GFunctor (excl_authUR modelO);
     ghost_mapΣ loc (option loc);
     ghost_mapΣ loc val;
     GFunctor (authUR (gsetUR loc))
    ].

Global Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.

Global Existing Instance queue_tokG.
Global Existing Instance queue_cellsG.
Global Existing Instance queue_jmmutG.
Global Existing Instance queue_gsetG.

(******************************************************************************)
(* Ghost queue *)

(* [ghost_queue] stores all the ghost names we need. *)
Record ghost_queue :=
  mk_gq {
      m : gname;  (* the model *)
      i : gname;  (* cellsable 1 *)
      j : gname;  (* cellsable 2 *)
      s : gname;  (* sentinel *)
      t : gname;  (* tail *)
      a : gname;  (* last *)
    }.
Global Instance ghost_queue_eq_dec : EqDecision ghost_queue.
Proof. solve_decision. Qed.
Global Instance ghost_queue_countable : Countable ghost_queue.
Proof.
  apply inj_countable with
    (f:= fun x => (x.(m), x.(i), x.(j), x.(s),x.(t), x.(a)))
    (g:= fun '(x1,x2,x3,x4,x5,x6) => Some (mk_gq x1 x2 x3 x4 x5 x6)).
  intros []; eauto.
Qed.

Ltac conclude_inv ls lt la :=
  try iModIntro; iExists _,ls,lt,la,_; iFrame; iFrame "#"; iRight; iFrame.

Section MSCommon.
Context `{!interpGS0 Σ, !queueG Σ}.

Definition protect l P : iProp Σ := †l ∨ P.

(******************************************************************************)
(* cells *)
(* The inner cells of the queue are blocks of size 2, but we need to separate
   the ownership of each part. *)


Definition extract l' :=
  match l' with None => val_unit | Some x => val_loc x end.

Definition cells γ : iProp Σ :=
  ∃ (σ:gmap loc val) (ρ:gmap loc (option loc)),
    ghost_map_auth γ.(i) 1 σ ∗
    ghost_map_auth γ.(j) 1 ρ ∗
    [∗ map] l ↦ v;l' ∈ σ;ρ, l ↦ [v; extract l'].

Definition cells_pat : string :=
  "[%σ [%ρ (Hσ&Hρ&Hσρ)]]".

(* The permission to write the successor of l *)
Definition islast γ l : iProp Σ :=
  l ↪[ γ.(j) ] None.

(* The exclusive ownership of the actual value in l *)
Definition value γ l (v:val) : iProp Σ :=
   l ↪[ γ.(i) ] v.

Lemma confront_mapsto_cells l vs σ ρ :
  (l ↦ vs ∗ [∗ map] l0↦v0;l' ∈ σ;ρ, l0 ↦ [v0; extract l'])%I -∗ ⌜l ∉ dom ρ⌝.
Proof.
  iIntros "(Hl&I)". iIntros (Hl). apply elem_of_dom in Hl. destruct Hl as (?,?).
  iDestruct (big_sepM2_lookup_acc_r with "[$]") as "[% (%&?&_)]". done.
  iDestruct (mapsto.mapsto_ne with "Hl [$]") as "%". congruence.
Qed.

Lemma cells_add_last γ l v :
  cells γ ∗ l ↦ [v; val_unit] ==∗
  cells γ ∗ islast γ l ∗ value γ l v.
Proof.
  iIntros "(I&Hl)". iDestruct "I" as cells_pat.
  iDestruct (big_sepM2_dom with "Hσρ") as "%".
  iDestruct (confront_mapsto_cells with "[$]") as "%".
  iMod (ghost_map_insert l None with "Hρ") as "(?&?)". now apply not_elem_of_dom.
  iMod (ghost_map_insert l v with "Hσ") as "(?&?)". { apply not_elem_of_dom. set_solver. }
  iFrame. iModIntro. iExists _,_. iFrame. iApply (big_sepM2_insert_2 with "[Hl][$]"). done.
Qed.

Lemma cells_borrow γ ce q x :
  ce ↪[ γ.(j) ]{q} x -∗
  cells γ -∗
  ce ↪[ γ.(j) ]{q} x ∗ ∃ v, ce ↦ [v;extract x] ∗ (ce ↦ [v;extract x] -∗ cells γ).
Proof.
  iIntros "Hce I". iDestruct "I" as cells_pat.
  iDestruct (ghost_map_lookup with "Hρ Hce") as "%".
  iDestruct (big_sepM2_lookup_acc_r with "[$]") as "[% (%&X&Hb)]". done.
  iSmash.
Qed.

(******************************************************************************)
(* IsQueue *)

(* The [IsQueue] predicate is not persistent (contrary to Vindum &
   Birkedal), but this is not a problem.
   It stores various pointed-by-heap and the pointed-by-thread.

   We moreover distinguish [IsQueue] from [IsGuardedQueue] as there is
   a subtle difference between an empty queue and a non-empty queue
   (the presence of a dummy sentinel, and the relevance of the value
   stored in the last block)
 *)

Definition val_pb γ l (x:elem) : iProp Σ :=
  let '(v,(p,q)) := x in
  value γ l v ∗ v ⟸?{p} ∅ ∗ v ↤?{q} {[+l+]}.

Fixpoint IsQueue (γ:ghost_queue) (la:loc) (x:elem) (xs:model) (l:loc) (zs:list loc) : iProp Σ :=
  match xs,zs with
  | nil,nil => ⌜la=l⌝ ∗ val_pb γ l x
  | y::ys ,l'::zs => l ↪[γ.(j)]□ (Some l') ∗ val_pb γ l x ∗
               l' ↤{1/2} {[+l+]} ∗ l' ⟸ ∅ ∗
               IsQueue γ la y ys l' zs
  | _,_ => False end.

Definition IsGuardedQueue γ (la:loc) (xs:model) (l:loc) (zs:list loc) : iProp Σ :=
    match xs,zs with
    | nil,nil => ⌜la=l⌝
    | x::xs,l'::zs => l ↪[γ.(j)]□ (Some l')
                ∗ l' ↤{1/2} {[+l+]} ∗ l' ⟸ ∅
                ∗ IsQueue γ la x xs l' zs
    |  _,_ => False end.

Global Instance IsQueue_timeless γ la x xs l zs  : Timeless (IsQueue γ la x xs l zs).
Proof. revert x l zs; induction xs as [|(?,(?,?))]; intros (?,(?,?)) ? []; apply _. Qed.
Global Instance IsGuardedQueue_timeless γ la xs l zs  : Timeless (IsGuardedQueue γ la xs l zs).
Proof. destruct xs,zs; apply _. Qed.

(******************************************************************************)
(* lt_inv *)

(* The invariant on the tail lt with respects to the whole list of
   locations [zs]. This stores either nothing or an empty pointed-by.
*)

Definition lt_inv zs lt : iProp Σ :=
  ⌜lt ∈ zs /\ NoDup zs⌝ ∗
  [∗ list] l ∈ zs, ⌜l=lt⌝ ∨ l ↤{1/2} ∅.

(******************************************************************************)
(* The invariant *)

(* Being a cell is being able to reach the last node. *)

(* How we split mapsfrom for each cell:
   + (1/2) for IsQueue
   + (1/2) for lt_inv
 *)

Definition queue_nm := nroot.@"queue".

Definition queue_inv_inner γ (l:loc) : iProp Σ :=
  (* xs:model, ls:sentinel, lt:tail, la:last, xa:last val, zs:skeleton *)
  ∃ (xs:model) (ls lt la:loc) (zs:list loc),
    (* protected points-to and pointed-by *)
    protect l (l ↦ [val_loc ls; val_loc lt] ∗
      ls ↤{1/2} {[+l+]} ∗ ls ⟸ ∅ ∗ lt ↤{1/2} {[+l+]} ∗
      islast γ la) ∗
    (* We own the cells. *)
    cells γ ∗
    (* The representation predicate. *)
    IsGuardedQueue γ la xs ls zs ∗
    (* lt_inv *)
    lt_inv (ls::zs) lt ∗
    (* The model *)
    own γ.(m) (●E xs) ∗
    (* Reachability (as in Vindum & Birkedal). *)
    tie γ.(j) γ.(t) lt ∗
    tie γ.(j) γ.(s) ls ∗
    tie γ.(j) γ.(a) la ∗
    ls -r-> γ.(t)  ∗ (* The tail is reachable from the sentinel. *)
    lt -r-> γ.(a)     (* The last node is reachable from the tail. *)
.

(* A string for introducing the invariant. *)
Definition queue_intro : string -> string := fun p =>
">[%xs"+:+ p +:+" [%ls"+:+ p +:+" [%lt"+:+ p +:+" [%la"+:+ p +:+" [%zs"+:+ p +:+"(Hl"+:+ p +:+"& Hcells"+:+ p +:+" & Hqueue"+:+ p +:+" & Hltinv"+:+ p +:+"&Hmodel"+:+ p +:+" & Hnt"+:+ p +:+" & Hns"+:+ p +:+" & Hna"+:+ p +:+" & #Hls"+:+ p +:+" & #Hlta"+:+ p +:+")]]]]]".

Definition qintro := queue_intro "".
Definition qintro' := queue_intro "'".
Definition qintro_ := queue_intro "_".

Definition queue_introl : string -> string := fun p => "[?|(Hl"+:+ p +:+" & Hps"+:+ p +:+" & Hss"+:+ p +:+"& Hpl"+:+ p +:+" & Ht"+:+ p +:+")]".
Definition qintrol := queue_introl "".
Definition qintrol' := queue_introl "'".
Definition qintrol_ := queue_introl "_".

Global Instance queue_inv_timeless γ l : Timeless (queue_inv_inner γ l).
Proof. apply _. Qed.

Definition queue_inv N γ l := inv N (queue_inv_inner γ l).

Definition queue N (l:loc) : iProp Σ := ∃ γ, meta l queue_nm γ ∗ queue_inv N γ l.

(******************************************************************************)
(* The model *)

Definition queue_content (l:loc) (xs:model) : iProp Σ :=
  ∃ (γ:ghost_queue), meta l queue_nm γ ∗ own γ.(m) (◯E xs).

Lemma queue_content_open l xs γ :
  meta l queue_nm γ -∗ queue_content l xs -∗ own γ.(m) (◯E xs).
Proof.
  iIntros "? [% (?&?)]".
  iDestruct (meta_agree with "[$] [$]") as "%". subst. iFrame.
Qed.

(******************************************************************************)

Lemma use_cell γ γa l la :
  l -r-> γa  -∗
  tie γ.(j) γa la ∗ cells γ ==∗
  tie γ.(j) γa la ∗ cells γ ∗ (⌜l=la⌝ ∨ (∃ lp, lp -r-> γa ∗ l ↪[γ.(j)]□ (Some lp))).
Proof.
  iIntros "? (?&I)". iDestruct "I" as cells_pat.
  iDestruct (lookup_reach_set with "[$][$]") as "#Hr".
  rewrite reachable_eq. iDestruct "Hr" as "[%n #Hln]".
  destruct n.
  { iDestruct "Hln" as "%". iModIntro. iFrame. iSplitL. do 2 iExists _.
    iFrame "%∗#". eauto.  }
  { iDestruct "Hln" as "[% (He&?)]".
    iDestruct (ghost_map_lookup with "Hρ He") as "%".
    iDestruct (big_sepM2_lookup_acc_r with "Hσρ") as "[% (%&?&?)]". done.
    iMod (insert_reach_set _ _ lp with "[$][]") as "(?&#?)".
    { iExists _. eauto. }
    iFrame "#∗". iSplitL. iSmash. iModIntro. iRight.
    iExists _. by iFrame "#∗". }
Qed.

Lemma load_tail_spec' z N l γ π D ql Sl :
  queue_inv N γ l ∗
  (match z with | Some ls => ls -r-> γ.(t) | None => True end) ∗
  l ⟸{ql} Sl ∗ inside π D -∗
  wp ⊤ false π  (#l.[^otail]) (fun v => l ⟸{ql} Sl ∗ ∃ lt, ⌜v=val_loc lt⌝ ∗ inside π (D ∪ {[lt]})∗ lt -r-> γ.(a) ∗ lt -r-> γ.(t) ∗ (match z with | Some ls => ls ~γ.(j)~> lt | None => True end)).
Proof.
  iIntros "(HI&?&?&?)".
  iInv "HI" as qintro. solve_atomic.

  iDestruct "Hl" as qintrol.
  { not_dead l. }

  wp_apply wp_load.wp_load_inside.
  { compute_done. }
  simpl.
  iIntros (?) "(->&_&?&D)".
  iMod (insert_reach_set (j γ) (t γ) lt with "[$][]" ) as "(?&#?)".
  { iApply reachable_refl. }
  iModIntro.

  iAssert (match z with | Some ls => ls ~γ.(j)~> lt | None => True end)%I as"#?".
  { destruct z as [z|]; eauto.
    iDestruct (lookup_reach_set _ z with "[$][$]") as "#?". eauto. }

  iSplitR "D".
  { conclude_inv ls lt la. }
  iExists lt. auto_locs. iSmash.
Qed.

Lemma IsQueue_acc ln γ la x xs ls zs :
  ls ~γ.(j)~> ln -∗
  IsQueue γ la x xs ls zs -∗
  islast γ la -∗
  ⌜ln ∈ (ls::zs)⌝ ∗ (⌜ln=la⌝ ∨ ∃ z, ln ↪[ γ.(j) ]□ (Some z)).
Proof.
  rewrite reachable_eq.
  iIntros "[%n Hln] Hq Ha".
  iInduction n as [|] "IH" forall (ls zs xs x); destruct x as (?,(?,?)).
  { iDestruct "Hln" as "%". subst.
     destruct xs as [|(?,(?,?))],zs; eauto.
    { iDestruct "Hq" as "(%&?)". subst. iSplitR; eauto. iPureIntro. set_solver.  }
    iDestruct "Hq" as "(?&?&?&?)".
    iSplitR. iPureIntro. set_solver. eauto. }
  destruct xs,zs; eauto.
  { simpl. iDestruct "Hq" as "(%&?)". subst.
    iDestruct "Hln" as "[% (?&?)]".
    iDestruct (ghost_map_elem_agree with "Ha [$]") as "%".
    congruence.  }
  simpl.
  iDestruct "Hq" as "(?&?&?&?&?)".
  iDestruct "Hln" as "[%(?&?)]".
  iDestruct (ghost_map_elem_agree ls with "[$][$]") as "%E". inversion E. subst.
  iDestruct ("IH" with "[$][$][$]") as "(%&#?)".
  iSplitR. iPureIntro. set_solver. eauto.
Qed.

Lemma IsGuardedQueue_acc ln γ la xs ls zs :
  ls ~γ.(j)~> ln -∗
  IsGuardedQueue γ la xs ls zs -∗
  islast γ la -∗
  ⌜ln ∈ (ls::zs)⌝ ∗ (⌜ln=la⌝ ∨ ∃ z, ln ↪[ γ.(j) ]□ (Some z)).
Proof.
  rewrite reachable_eq.
  iIntros "[%n Hln] Hq ?".
  destruct n.
  { iDestruct "Hln" as "%". subst.
    destruct xs,zs; eauto.
    { iDestruct "Hq" as "%". subst. iSplitR; eauto. iPureIntro. set_solver.  }
    iDestruct "Hq" as "(?&?)".
    iSplitR. iPureIntro. set_solver. eauto. }
  { simpl. iDestruct "Hln" as "[%(?&Hln)]".
    destruct xs,zs;eauto.
    iDestruct "Hq" as "%". subst.
    { iDestruct (ghost_map_elem_agree with "[$][$]") as "%".
      congruence. }
    iDestruct "Hq" as "(?&?&?&?)".
    iDestruct (ghost_map_elem_agree ls with "[$][$]") as "%E". inversion E. subst.
    iDestruct (IsQueue_acc with "[Hln][$][$]") as "(%&#?)".
    { iExists _. iFrame. }
    iSplitR. iPureIntro. set_solver. eauto. }
Qed.

Local Lemma use_lt_inv zs lt lz :
  lt ≠ lz -> lz ∈ zs ->
  lt_inv zs lt -∗
  (lz ↤{1/2} ∅ ∗ (lt ↤{1/2} ∅ -∗ lt_inv zs lz ) ).
Proof.
  iIntros (? Hj) "((%Hlt&%Hlz)&Hinv)".  generalize Hj. intros Hj'.
  apply elem_of_list_lookup_1 in Hj. destruct Hj as [j Hj].
  rewrite (big_sepL_delete _ _ j); last eauto.
  iDestruct "Hinv" as "([%|?]&Hinv)"; try congruence.
  iFrame. iIntros.
  iSplitR; eauto.
  apply elem_of_list_lookup_1 in Hlt. destruct Hlt as [i Hlt].
  iApply (big_sepL_delete _ _ i); eauto.
  iSplitR "Hinv". eauto.

  assert (i≠j) by naive_solver.

  iApply (big_sepL_impl with "[$]").
  iModIntro. iIntros (k l Hk) "H".
  do 2 case_decide; try congruence.
  { subst. iLeft. iPureIntro. naive_solver. }
  { eauto. }
  { iDestruct "H" as "[% | ?]"; eauto.
    exfalso. subst. rewrite NoDup_alt in Hlz.
    eauto. }
Qed.

(* "advancing" the tail pointer to a successor is always safe. *)
Lemma advance_tail_pointer N π l γ lt ln ql Sl :
  queue_inv N γ l ∗
  lt ~γ.(j)~> ln ∗ ln -r-> γ.(a) ∗
  l ⟸{ql} Sl -∗ (* Like a souvenir, but we lack them in the simple "wp" mode. *)
  wp ⊤ false π (tm_cas l otail lt ln)%T (fun v => ∃ b, ⌜v=val_bool b⌝ ∗ l ⟸{ql} Sl).
Proof.
  iIntros "(#HI&#?&?&?)".
  iInv "HI" as qintro'. solve_atomic.
  iDestruct "Hl'" as qintrol.
  { not_dead l. }
  destruct_decide (decide (lt' =lt)); subst; last first.
  { wp_apply wp_cas.wp_cas_fail.
    { simpl. reflexivity. }
    { by vm_compute. }
    { naive_solver. }
    iIntros (?) "(%&_&?)". iModIntro.
    iSplitL; last iSmash. iModIntro.
    conclude_inv ls' lt' la'. }
  { (* Strange case, presumably never happens. *)
    destruct_decide (decide (ln=lt)); subst.
    { iDestruct (mapsfrom_split_half_empty lt with "[$]") as "(?&?)".
      wp_apply wp_cas.wp_cas_suc.
      1-3:naive_solver by vm_compute.
      iIntros (?) "(->&_&?&?&?)". simpl.
      iDestruct (mapsfrom_join with "[$][$]") as "?".
      iDestruct (mapsfrom_join with "[$][$]") as "?".
      replace (1 / 2 / 2 + 0 + 1 / 2 / 2)%Qz with (1/2)%Qz by compute_done.
      assert (({[+ l +]} ⊎ smultiset.singletonNS l ⊎ {[+ l +]}) ≡ {[+l+]}) as -> by smultiset.smultiset_solver.
      iModIntro. iSplitL; last iSmash.
      conclude_inv ls' lt la'. }
    iDestruct (lookup_reach_set _ ls' with "[$][$]") as "#?".
    iDestruct (IsGuardedQueue_acc ln with "[][$][$]") as "(%&#?)".
    { iApply (reachable_trans with "[$][$]"). }
    iDestruct (use_lt_inv with "[$]") as "(?&Hb)". eauto. set_solver.
    wp_apply wp_cas.wp_cas_suc.
    1-3:naive_solver by vm_compute.
    iIntros (?) "(->&_&?&?&?)". simpl.
    iDestruct (mapsfrom_join lt with "[$][$]") as "?".
    rewrite left_id.
    assert (smultiset.singletonNS l ⊎ {[+ l +]} ≡ ∅) as -> by smultiset.smultiset_solver.
    iSpecialize ("Hb" with "[$]").
    iDestruct (lookup_reach_set _ ln with "[$][$]") as "#?".
    iMod (reach_set_advance _ γ.(t) lt ln with "[$][$]") as "(?&?)".
    iMod (insert_reach_set (j γ) (a γ) ln with "[$][$]") as "(?&?)".
    iModIntro. iSplitL; last iSmash. iModIntro.
    iExists xs',ls',ln,la',zs'. iFrame "∗ #". iRight. iFrame. }
Qed.

End MSCommon.
