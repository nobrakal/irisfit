From iris.base_logic.lib Require Export invariants gen_heap ghost_map boxes.
From iris.algebra Require Import auth excl gset numbers csum.
From iris.bi.lib Require Import atomic.

From irisfit Require Import wpc_logatom.
From irisfit.examples Require Import proofmode spawn_join pair par faa ignore.

Definition af_alloc : val :=
  λ: [[]], let: "x" := alloc 1 in "x".[0] <- 0;; "x".

Definition af_async : val :=
  λ: [["l","f"]],
    faa [["l",0,1]];;
    fork (call_clo "f" [[]];; ignore [faa [["l",0,(-1)%Z]]]).

Definition af_finish : val :=
  μ: "self", [["l"]],
      let: "tasks" := "l".[0] in
      let: "b" := "tasks" '== 0 in
      if: "b"
      then val_unit
      else "self" [["l"]].

Record ghost_af :=
  mk_gaf {
      res : gname; (* registered *)
      sta : gname; (* status *)
      int : gname; (* intermediate *)
  }.
Global Instance ghost_stack_eq_dec : EqDecision ghost_af.
Proof. solve_decision. Qed.
Global Instance ghost_stack_countable : Countable ghost_af.
Proof.
  apply inj_countable with
    (f:= fun x => (x.(res), x.(sta), x.(int)))
    (g:= fun '(x1,x2,x3) => Some (mk_gaf x1 x2 x3)).
  intros []; eauto.
Qed.

Local Notation stateR := (csumR (csumR (exclR unitR) (prodR fracR (agreeR natR))) (agreeR unitR)).

Class AFG Σ :=
  mkaf {
      af_box : boxG Σ;
      af_ghmap : ghost_mapG Σ gname nat;
      af_gset : inG Σ (authUR (gset_disjUR gname));
      af_stat : inG Σ stateR;
    }.
Local Existing Instance af_box.
Local Existing Instance af_ghmap.
Local Existing Instance af_gset.
Local Existing Instance af_stat.

Definition AFΣ : gFunctors :=
  #[ boxΣ;
     ghost_mapΣ gname nat;
     GFunctor (authUR (gset_disjUR gname));
     GFunctor stateR ].

Global Instance subG_boxΣ Σ : subG AFΣ Σ → AFG Σ.
Proof. solve_inG. Qed.

(******************************************************************************)
(* [count the truths ] This could be generalized to an arbitrary predicate *)

Definition count_true (M:gmap gname bool) := size (filter (fun '(_,x) => x = true) M).

Lemma size_length_nodup {A:Type} `{Countable K} (M:gmap K A) (ord:list K) :
  NoDup ord ->
  dom M = list_to_set ord ->
  size M = length ord.
Proof.
  intros ? Hd.
  replace (size M) with (size (dom M)).
  2:{ rewrite size_dom //. }
  rewrite Hd. rewrite size_list_to_set //.
Qed.

Lemma count_true_le_size M :
  count_true M ≤ size M.
Proof. apply map_size_filter. Qed.

(* LATER move to iris. *)
Lemma map_size_filter_eq_inv {A} `{Countable K} `{!∀ x, Decision (P x)} (M:gmap K A) :
  size M = size (filter P M) ->
  map_Forall (fun x y => P (x,y)) M.
Proof.
  pattern M. apply map_ind; first easy.
  intros i x M' Hi IH Hsize.
  rewrite map_size_insert Hi in Hsize.
  rewrite map_filter_insert in Hsize.
  case_decide.
  2:{ exfalso.
      rewrite map_filter_delete map_size_delete in Hsize.
      rewrite map_lookup_filter Hi in Hsize. simpl in Hsize.
      pose proof (map_size_filter P M'). lia. }
  rewrite map_size_insert map_lookup_filter Hi in Hsize. simpl in Hsize.
  apply map_Forall_insert; eauto.
Qed.

Lemma size_count_true_eq_inv M :
  size M = count_true M ->
  map_Forall (fun _ b => b=true) M.
Proof. intros E. apply map_size_filter_eq_inv in E. eauto. Qed.

(******************************************************************************)
(* [half_pow n] is (1/2)^n *)

Definition half_pow (n:nat) : Qp := 1/(pos_to_Qp (Pos.of_nat (Nat.pow 2 n))).

Lemma half_pow_succ n :
  half_pow n = (half_pow (S n) + half_pow (S n))%Qp.
Proof.
  rewrite /half_pow.
  rewrite -Qp.div_add_distr.
  rewrite Nat.pow_succ_r'.
  rewrite Nat2Pos.inj_mul //.
  2:{ apply Nat.pow_nonzero. lia. }
  rewrite -pos_to_Qp_mul.
  replace (1+1)%Qp with (2*1)%Qp by compute_done.
  replace (pos_to_Qp (Pos.of_nat 2))%Qp with 2%Qp by compute_done.
  rewrite Qp.div_mul_cancel_l //.
Qed.

Section AF.

Context `{interpGS0 Σ, !AFG Σ}.
Context (N:namespace).

Definition Nbox : namespace := N.@"box".
Definition Ninv : namespace := N.@"inv".

(******************************************************************************)
(* [tie] ties the various ghost state *)

Record tie (M:gmap gname bool) (M':gmap gname nat) (ord:list gname) :=
  mktie {
      tie_dom : dom M = list_to_set ord;
      tie_nodup : NoDup ord;
      tie_all : (forall ι x, M' !! ι = Some x <-> (M !! ι = Some false /\ ord !! x = Some ι));
    }.

Lemma tie_insert M U ord ι ta :
  M !! ι = None ->
  ta = length ord ->
  tie M U ord ->
  tie (<[ι:=false]> M) (<[ι:=ta]> U) (ord ++ [ι]).
Proof.
  intros HM ? [Hd ? tieall].
  assert (ι ∉ ord).
  { assert (ι ∉ dom M) as P. apply not_elem_of_dom. eauto.
    rewrite Hd in P. rewrite elem_of_list_to_set in P. eauto. }
  constructor.
  { rewrite dom_insert_L list_to_set_app_L. set_solver. }
  { apply NoDup_app. split_and !; eauto using NoDup_singleton.
    intros x Hx. intros Eq. apply elem_of_list_singleton in Eq. subst. eauto. }
  { intros x i. destruct_decide (decide (x=ι)); subst.
    { rewrite !lookup_insert.
      split.
      { intros E. injection E. intros <-. split; eauto.
        rewrite lookup_app_r // Nat.sub_diag //. }
      { intros (_&T). apply lookup_app_Some in T.
        destruct T as [T|(?&T)].
        { apply elem_of_list_lookup_2 in T. naive_solver. }
        { apply list_lookup_singleton_Some in T. f_equal. destruct T. lia. } } }
    { rewrite !lookup_insert_ne //.
      split.
      { intros T. apply tieall in T. destruct T as (?&T).
        split; eauto. rewrite lookup_app_l //. eapply lookup_lt_Some; eauto. }
      { intros (?&T). apply tieall. split; eauto. rewrite lookup_app in T.
        destruct (ord !! i); eauto.
        exfalso. apply list_lookup_singleton_Some in T. naive_solver. } } }
Qed.

Lemma tie_update_true M U ord ι :
  M !! ι = Some false ->
  tie M U ord ->
  tie (<[ι:=true]> M) (delete ι U) ord.
Proof.
  intros ? [Hd ? ?].
  constructor; eauto.
  { rewrite dom_insert_L -Hd. assert (ι ∈ dom M). now apply elem_of_dom.
    set_solver. }
  { intros ι' ?.
    destruct_decide (decide (ι'=ι)); subst.
    { rewrite lookup_delete lookup_insert. naive_solver. }
    { rewrite lookup_delete_ne // lookup_insert_ne //. } }
Qed.

(* We are going to store a geometrical progression of pbt. We use a
   list for the ordering, and a map to allow borrowing of the fractions. *)
Definition fracs l (M:gmap gname bool) (ord:list gname) : iProp Σ :=
  [∗ list] n ↦ ι ∈ ord,
    ∃ (b:bool), ⌜M !! ι = Some b⌝ ∗
    if b then l ⟸{half_pow (2+n)} ∅ ∗ £1 else True.

Lemma fracs_add l M ord ι :
  M !! ι = None ->
  fracs l M ord -∗
  fracs l (<[ι:=false]> M) (ord ++ [ι]).
Proof.
  iIntros (?) "?".
  iApply big_sepL_snoc.
  iSplitL; last first.
  { iExists false. rewrite lookup_insert //. }
  iApply (big_sepL_impl with "[$]").
  iModIntro. iIntros (? ? ?) "[% (%&?)]".
  iExists b.
  assert (x ≠ ι) by naive_solver.
  rewrite lookup_insert_ne //. iFrame "%∗".
Qed.

Lemma fracs_insert l M U ord ι n :
  tie M U ord ->
  U !! ι = Some n ->
  fracs l M ord -∗
  l ⟸{half_pow (S (S n))} ∅ ∗ £1 -∗
  fracs l (<[ι:=true]> M) ord.
Proof.
  iIntros (Htie HU) "? Hl". rewrite /fracs.
  destruct Htie as [? ? tieall].
  apply tieall in HU. destruct HU as (?&?).
  iDestruct (big_sepL_lookup_acc_impl with "[$]") as "(_&HB)". eauto.
  iApply "HB"; last first.
  { iExists true. rewrite lookup_insert //. by iFrame. }
  { iModIntro. iIntros (?? ? Hf) "[%b (?&?)]".
    iExists b. rewrite lookup_insert_ne. iFrame.
    intros ?. subst. apply Hf. eapply NoDup_lookup; eauto. }
Qed.

Lemma sum_credits {A:Type} (ord:list A) :
  ([∗ list] _ ∈ ord, £ 1) ==∗
  £ (length ord).
Proof.
  iIntros "HL". iInduction ord as [|] "IH".
  { simpl. iApply lc_zero. }
  iDestruct "HL" as "(?&?)".
  iMod ("IH" with "[$]") as "?". iDestruct (lc_split with "[$]") as  "?".
  rewrite Nat.add_1_r. by iFrame.
Qed.

Lemma fracs_all_true l M ord :
  map_Forall (fun _ b => b=true) M ->
  fracs l M ord ==∗
  £(length ord) ∗ [∗ list] k↦v ∈ ord, l ⟸{half_pow (2 + k)} ∅.
Proof.
  iIntros (HM) "HL".
  iAssert ([∗ list] k↦v ∈ ord, l ⟸{half_pow (2 + k)} ∅ ∗ £1)%I with "[HL]" as "HL".
  { iApply (big_sepL_impl with "[$]").
    iModIntro. iIntros (? ? ?) "[%b (%Hb&?)]".
    assert (b=true) by eauto. subst b.
    iFrame. }
  rewrite big_sepL_sep. iDestruct "HL" as "(?&?)".
  iFrame. by iApply sum_credits.
Qed.

Lemma fracs_dealloc i l M ord :
  i = length ord ->
  map_Forall (fun _ b => b=true) M ->
  l ⟸{half_pow (S i)} ∅ -∗
  fracs l M ord ==∗
  £i ∗l ⟸{1/2} ∅.
Proof.
  iIntros (-> HM) "Hl Hfracs".
  iMod (fracs_all_true with "[$]") as "(?&Hfracs)". eauto. clear M HM. iFrame. iModIntro.
  iInduction ord as [|] "IH" using rev_ind.
  { simpl. rewrite /half_pow. replace (pos_to_Qp (Pos.of_nat (Nat.pow 2 1)))%Qp with 2%Qp by compute_done.
    by iFrame. }
  rewrite big_sepL_snoc. iDestruct "Hfracs" as "(?&?)".
  rewrite app_length cons_length nil_length Nat.add_1_r.
  iDestruct (pbt_join with "[$]") as "?".
  rewrite -half_pow_succ left_id_L.
  iApply ("IH" with "[$][$]").
Qed.

Global Instance fracs_timeless l M ord : Timeless (fracs l M ord).
Proof.
  apply big_sepL_timeless.
  intros. apply bi.exist_timeless.
  intros []; apply _.
Qed.

(******************************************************************************)
(* The 3 states of our invariant. *)

Definition state0 γ := own γ (Cinl (Cinl (Excl tt))).
Definition state1 γ q i := own γ (Cinl (Cinr (q,to_agree i))).
Definition state2 γ := own γ (Cinr (to_agree tt)).

Lemma state0_to_state1 γ i :
  state0 γ ==∗ state1 γ (1/2)%Qp i ∗ state1 γ (1/2)%Qp i.
Proof.
  iIntros. iApply own_op. iApply (own_update with "[$]").
  apply cmra_update_exclusive. apply pair_valid.
  split.
  { rewrite frac_op Qp.div_2 //. }
  { rewrite to_agree_op_valid_L //. }
Qed.

Lemma state1_to_state2 γ i i' :
  state1 γ (1/2)%Qp i -∗ state1 γ (1/2)%Qp i' ==∗
  ⌜i=i'⌝ ∗ state2 γ.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as "%Hv".
  rewrite Cinl_valid Cinr_valid pair_valid in Hv.
  destruct Hv as (_&Hv). simpl in *. apply to_agree_op_valid_L in Hv.
  iFrame "%". iApply (own_update_2 with "[$][$]").
  subst. rewrite -Cinl_op -Cinr_op -pair_op frac_op Qp.div_2.
  apply cmra_update_exclusive. easy.
Qed.

Ltac confront_state :=
  iIntros "(H1&H2)"; iDestruct (own_valid_2 with "H1 H2") as "%Hv"; inversion Hv.

Lemma state1_not_state2 γ q i :
  state2 γ ∗ state1 γ q i -∗ False.
Proof. confront_state. Qed.

Lemma state0_not_state2 γ :
  state2 γ ∗ state0 γ -∗ False.
Proof. confront_state. Qed.

(* + M stores each task (identified by a gname) and its completion status.
   + O stores the mapping of tasks to their "borrowed" par of pbt of l.
     indeed, they all temporarily points to l.
   + ord defines the ordering. We do not know in advance how many tasks we will spawn,
     hence, we adapt a geometrical progression.
   + P is an artefact of [box]
   + tasks is the current number of forked tasks
   + finished is the current the number of finished tasks. We always have finished <= tasks.
 *)

Definition af_inv (γ:ghost_af) (l:loc) : iProp Σ :=
  ∃ (M:gmap gname bool) (O:gmap gname nat) (ord:list gname) (P:iProp Σ) (tasks finished:nat),
    ⌜size M = tasks /\ count_true M = finished⌝ ∗
    ghost_map_auth (sta γ) 1 O ∗ own (res γ) (● GSet (dom M)) ∗
    box Nbox M P ∗
    (   (state0 (int γ) ∗  l ↦ [val_int (tasks-finished)] ∗ fracs l M ord ∗ l ⟸?{half_pow (S tasks)} ∅ ∗ ⌜tie M O ord⌝)
     ∨ (∃ tid, state1 (int γ) (1/2)%Qp tid ∗ l ⟸ {[tid]} ∗ £(size (dom M)) ∗ ⌜finished = tasks /\ tie M O ord⌝)
     ∨ (state2 (int γ) ∗ (†l ∨ ∃ x, l ↦ [x] ∗ l ⟸ ∅) ∗ £(size (dom M)) ∗ ⌜finished = tasks⌝)).

Definition af_open_pat : list string :=
  ["[%M";" [%U";" [%ord"; " [%P"; "[%ta"; " [%fi"; "(>%Hpure" ; " & >HM"; " & >HS & Hbox & >Hor )]]]]]]"].
Definition af_open_prim := fun x => String.concat x af_open_pat.
Definition af_open := af_open_prim "".
Definition af_open1 := af_open_prim "1".
Definition af_open2 := af_open_prim "2".

Definition af_nm := nroot.@"af".

(* The actual invariant *)
Definition af l : iProp Σ := ∃ γ, meta l af_nm γ ∗ inv Ninv (af_inv γ l).

Lemma af_alloc_spec i :
  CODE (af_alloc [[]])
  TID i
  PRE (♢1)
  POST (fun l => af l ∗ l ↤ ∅ ∗ l ⟸{1/2} {[i]}).
Proof.
  iIntros.
  wpc_call.
  iApply wpc_fupd.
  wpc_let_empty. wpc_alloc. iIntros (l) "(Hl&Hml&?&?)".
  wpc_let_noclean.
  wpc_apply wpc_store_no_loc. 1-2:naive_solver. iIntros ([]) "?". simpl.
  iDestruct (pbt_split_half_empty with "[$]") as "(Hpltid&Hpl)".
  iMod (own_alloc (● GSet ∅)) as "[%γ1 ?]".
  { apply auth_auth_valid. easy. }
  iMod (ghost_map_alloc_empty) as "[%γ2 ?]".
  iMod (own_alloc (Cinl (Cinl (Excl tt)))) as "[%γ3 ?]". easy.

  iMod (meta_set _ l (mk_gaf γ1 γ2 γ3)  af_nm with "[$]") as "#?".
  { solve_ndisj. }

  iMod (inv_alloc Ninv ⊤ (af_inv (mk_gaf γ1 γ2 γ3) l) with "[-Hml Hpltid]") as "#?".
  { iModIntro. iExists ∅,∅,nil,True%I,0%nat,0%nat. rewrite dom_empty_L. simpl. iFrame.
    iSplitR.
    { iPureIntro. split_and !. 1,2:compute_done. }
    iSplitR. { by iApply box_alloc. }
    iLeft. iFrame. iSplit. by iApply big_sepL_nil.
    iPureIntro.
    { constructor. compute_done. constructor.
      intros. rewrite lookup_empty lookup_nil. naive_solver. } }
  iSteps.
Qed.

Definition spawned {A:Type} l (P:A -> iProp Σ) : iProp Σ :=
  ∃ (γ:ghost_af), meta l af_nm γ ∗ ∃ ι, own (res γ) (◯ (GSet ({[ι]}))) ∗ slice Nbox ι (∃ v, P v).

Lemma af_async_spec (A:Type) (EA:Enc A) i l f p (Q:A -> iProp Σ) :
  CODE (af_async [[l, f]])
  TID i
  SOUV {[l]}
  PRE (af l ∗ f ⟸{p} {[i]} ∗ (∀ j, f ⟸{p} {[j]} -∗ wpc ⊤ j (Some {[l]}) (call_clo f [[]])%T Q))
  POST (fun (_:unit) => spawned l Q).
Proof.
  iIntros "(#[%γ (?&Hi)]&?&Hwp)".
  wpc_call. simpl.
  iApply (wpc_let_vsingleton f with "[$]"). set_solver.
  iApply (wpc_frame_wand with "Hwp").

  iApply wpc_split_ctx. iIntros (X HX) "HPBT".
  iApply (wpc_weak {[l]}). set_solver.
  iApply wpc_convertible. iApply faa_spec_weak. 1,2:done.
  iAuIntro.
  iInv "Hi" as af_open.
  iDestruct "Hor" as "[ (Hlive&Hl&Hfrac&Hpow&%Htie) | [[% (?&?&?)] | (_&E&_) ]]".
  2:{ iDestruct (confront_pbt_PBT with "[$]") as "%". exfalso. set_solver. }
  2:{ iDestruct "E" as "[?|[%(?&?)]]".
      { destruct (X !! l) eqn:EX.
        2:{ exfalso. apply not_elem_of_dom in EX. set_solver. }
        iDestruct (PBT_borrow_pbt with "[$]") as "(?&_)". done.
        not_dead l. }
      iDestruct (confront_pbt_PBT with "[$]") as "%". exfalso. set_solver. }

  unshelve iAaccIntro with "[Hl]"; first (by eexists [(^(ta - fi))%V],_).
  { by iFrame. }
  { iIntros "(_&?)". simpl. iModIntro. iFrame "HPBT". iModIntro.
    iExists _,_,_,_,_,_. iFrame "% HM HS Hbox". iLeft. iFrame. }
  iIntros "(Hl&?)". simpl.
  destruct Hpure as (?&?).
  iMod (lc_fupd_elim_later with "[$][$]") as "?".

  iMod (slice_insert_empty _ _ true _ (∃ v, Q v)%I with "[$]") as "[%ι (%Hι&#HR&?)]".
  iMod (ghost_map_insert ι ta with "HM") as "(?&HF)".
  { destruct Htie as [? ? tieall]. destruct (U!!ι) eqn:Eq; eauto.
    exfalso. apply tieall in Eq. destruct Eq as (Hι'&_). rewrite Hι in Hι'. congruence. }
  assert ({[ι]} ## dom M).
  { assert (ι ∉ dom M). apply not_elem_of_dom. eauto. set_solver. }
  iMod (own_update with "HS") as "(?&Hι)".
  { apply auth_update_alloc.
    now apply gset_disj_alloc_local_update with (Z:={[ι]}). }
  iModIntro. rewrite right_id_L.
  rewrite half_pow_succ. iDestruct "Hpow" as "(Hpow1&Hpow2)".
  iSplitR "HR HF Hι Hpow1 HPBT".
  { iModIntro. iExists _,_,(ord ++ [ι]),_,(S ta),fi. iFrame.
    rewrite dom_insert_L -gset_disj_union //. iFrame.
    iSplitR.
    { iPureIntro. split_and !; eauto.
      { rewrite map_size_insert Hι //. lia. }
      { rewrite /count_true map_filter_insert. simpl.
        rewrite map_filter_delete map_size_delete map_lookup_filter Hι //. } }
    iLeft. iFrame.
    assert ((1%nat + (ta - fi))%Z = (S ta - fi)%Z) as ->.
    { pose proof (count_true_le_size M). lia. }
    iFrame.
    iSplitL. iApply (fracs_add with "[$]"). eauto. iPureIntro.
    { apply tie_insert; eauto. inversion Htie. subst. eauto using size_length_nodup. }  }
  iIntros (?) "->". iFrame. iIntros "Hwp H".
  papprox l.
  simpl. rewrite !pbt_PBT. iDestruct (PBT_union with "[$]") as "?".
  iApply wpc_postpone_val. simpl.
  iApply (wpc_mono with "[-Hι]").
  { iApply (@wpc_fork with "[$]").
    { rewrite gmap.dom_op dom_singleton_L. set_solver. }
    iIntros. iDestruct (PBT_split with "[$]") as "(?&?)".
    iIntros. rewrite !subst_call_clo. simpl. rewrite -!pbt_PBT.
    iSpecialize ("Hwp" with "[$]").
    iApply (wpc_let_vsingleton l with "[$]"). set_solver.
    rewrite left_id_L. auto_locs.
    iApply (wpc_mono_val with "Hwp").
    iIntros (?) "HQ Hp". simpl.

    unshelve iApply wpc_convertible.
    4:iApply ignore_spec. apply _.

    iApply (wpc_convertible Z).
    clear dependent M U ord P.

    iDestruct (pbt_split_half_empty with "Hp") as "(?&Hp)".
    iApply (faa_spec _ j l _ with "[$]"). lia.
    iAuIntro. iInv "Hi" as af_open1.
    iDestruct "Hor" as "[ (Hlive&Hl&Hfrac&Hpow&%Htie)| [[% (?&?&?)] | (_&E&_) ]]".
    2:{ iDestruct (confront_pbt_pbt with "[$]") as "%". apply Qp.not_add_le_l. exfalso. congruence. }
    2:{ iDestruct "E" as "[?|[% (?&?)]]". not_dead l.
        iDestruct (confront_pbt_pbt with "[$]") as "%". apply Qp.not_add_le_l. exfalso. congruence. }

    unshelve iAaccIntro with "[Hl]"; first (by eexists [(^(ta1 - fi1))%V],_).
    { by iFrame. }
    { simpl. iIntros "(_&?)". iModIntro. iFrame. iModIntro.
      iExists _,_,_,_,_,_. iSplitR; first iFrame "%".
      iFrame "HM1 HS Hbox". iLeft. by iFrame. }
    iIntros "(Hl&Hp'&?)".
    iDestruct (pbt_join with "[Hp Hp']") as "?". iFrame. rewrite Qp.div_2 left_id_L.
    iDestruct (ghost_map_lookup with "[$][$]") as "%Hfalse".
    iMod (ghost_map_delete with "[$][$]") as "?".

    assert (M1 !! ι = Some false) as Hι1.
    { destruct Hpure1 as (?&?). destruct Htie. naive_solver. }
    assert (ι ∈ dom M1) by now apply elem_of_dom.

    iMod (lc_fupd_elim_later with "[$][$]") as "?".
    iAssert (▷ (∃ v, Q v))%I with "[HQ]" as "HQ". { iSmash. }
    iMod (slice_fill _ _ false with "HR HQ [$]"). solve_ndisj. eauto.

    iModIntro. iSplitL; last iSmash.
    iExists (<[ι:=true]> M1), (delete ι U1), ord1, _, ta1, (S fi1).
    iFrame. iSplitR.
    { iPureIntro. split_and !; eauto.
      { rewrite map_size_insert Hι1. naive_solver. }
      { rewrite /count_true map_filter_insert. simpl.
        rewrite map_size_insert map_lookup_filter Hι1. naive_solver. } }
    rewrite dom_insert_L subseteq_union_1_L. 2:set_solver. iFrame. iModIntro.
    iLeft. iFrame. simpl.
    assert ((-1 + (ta1 - fi1))%Z = (ta1 - S fi1)%Z) as ->. lia. iFrame.
    iSplitL. iApply (fracs_insert with "[$][$]"); eauto.
    iPureIntro. { apply tie_update_true; naive_solver. } }
  iSmash. Unshelve. apply _.
Qed.

Definition finished l : iProp Σ :=
  ∃ γ, meta l af_nm γ ∗ inv Ninv (af_inv γ l) ∗ state2 (int γ).

Lemma af_finish_spec l tid :
  CODE (af_finish [[l]])
  TID tid
  PRE (af l ∗ l ⟸{1/2} {[tid]})
  POST (fun (_:unit) => finished l ).
Proof.
  iIntros "(#[% (?&Hi)]&Hpbt)". iLöb as "IH".

  wpc_call.

  wpc_let_noclean.
  iInv "Hi" as af_open. solve_atomic.
  iDestruct "Hor" as "[ (Hlive&Hl&Hfrac&Hpow&%Htie) | [[% (?&?&?)] | (_&E&_) ]]".
  2:{ iDestruct (confront_pbt_pbt with "[$]") as "%". by vm_compute. congruence. }
  2:{ iDestruct "E" as "[?|[% (?&?)]]". not_dead l.
      iDestruct (confront_pbt_pbt with "[$]") as "%". by vm_compute. congruence. }

  wpc_apply wpc_load_no_loc. 1-3:naive_solver.
  iIntros (?) "(->&Hl)".

  destruct_decide (decide (ta = fi)); subst.
  (* end of things *)
  { destruct Hpure.
    iMod (fracs_dealloc with "Hpow Hfrac") as "(?&?)".
    { destruct Htie. subst. eauto using size_length_nodup. }
    { apply size_count_true_eq_inv. naive_solver. }
    iMod (state0_to_state1 _ tid with "[$]") as "(Hd1&Hd2)".

    iDestruct (pbt_join with "[$]") as "?".
    rewrite Qp.div_2 left_id_L.

    iModIntro.
    iSplitR "Hl Hd1".
    { iModIntro. iExists M,U,ord,P,fi,fi. iFrame "∗ %". iSplitR; first eauto.
      iRight. iLeft. iExists tid. rewrite size_dom. subst. by iFrame. }

    rewrite Z.sub_diag. simpl.
    wpc_let_noclean. wpc_call_prim. wpc_if.

    iInv "Hi" as af_open2.
    iDestruct "Hor" as "[ (?&Hfrac&Hpow&Hlive) | [[%tid' (?&?&?&%&%)] | (?&_) ]]".
    { iExFalso. iDestruct (own_valid_2 (int γ) with "[$][$]") as "%Hval".
      inversion Hval. }
    2:{ iExFalso. iApply state1_not_state2. iFrame. }
    iMod (state1_to_state2 with "[$][$]") as "(%&#?)". subst.
    pclean l. wpc_val. exact tt.
    iModIntro. iFrame.
    iSplitL. iModIntro. iExists M2,U2,ord2,P2,ta2,ta2. iFrame.
    iFrame "%∗". iSteps. iSmash. }
  { iModIntro. iSplitR "Hpbt".
    { iModIntro. iExists M,U,ord,P,ta,fi. iFrame "%∗". iSmash. }
    wpc_let_noclean. wpc_call_prim. wpc_if.
    simpl. rewrite bool_decide_false //.
    2:{ destruct Hpure. pose proof (count_true_le_size M). subst.
        naive_solver by lia. }
    iApply ("IH" with "[$]").  }
Qed.

Lemma own_gset_confront_update γ (M:gmap gname bool) (ι:gname) :
  own γ (◯ GSet {[ι]}) -∗
  own γ (● GSet (dom M)) ==∗
  ⌜ι ∈ dom M⌝ ∗ own γ (● GSet (dom (delete ι M))).
Proof.
  iIntros "Hf Ha".
  iDestruct (own_valid_2 with "Ha Hf") as "%Hv".
  apply auth_both_valid_discrete in Hv. destruct Hv as (Hv&_).
  apply gset_disj_included in Hv.
  iSplitR. { iPureIntro. set_solver. }
  iApply (own_update_2 with "Ha Hf").
  apply auth_update_dealloc.
  rewrite dom_delete_L.
  apply gset_disj_dealloc_local_update.
Qed.

Lemma get_lc `{Countable K} A ι (M:gmap K A) :
  ι ∈ dom M ->
  £(size (dom M)) -∗ £1 ∗ £(size (dom (delete ι M))).
Proof.
  iIntros.
  replace (dom M) with ({[ι]} ∪ dom M ∖ {[ι]}).
  2:{ rewrite comm_L difference_union_L. set_solver. }
  rewrite size_union. 2:set_solver. iApply lc_split.
  rewrite size_singleton dom_delete_L //.
Qed.

Lemma redeem {A:Type} l (Q:A -> iProp Σ) :
  finished l ∗ spawned l Q ={↑N}=∗ ∃ v, Q v.
Proof.
  iIntros "(#[%γ (?&Hi&?)]&[%γ' (?&[%ι (?&?)])])".
  iDestruct (meta_agree _ _ γ' γ with "[$][$]") as "%". subst.

  iInv "Hi" as af_open.
  iDestruct "Hor" as "[(?&_) | [ [% (?&_)] | (_&?&?&%)]]".
  { iExFalso. iApply state0_not_state2. iFrame "∗#". }
  { iExFalso. iApply state1_not_state2. iFrame "∗#". }
  subst.

  iMod (own_gset_confront_update with "[$][$]") as "(%Hι&?)".
  apply elem_of_dom in Hι.
  destruct Hι as (b,Hι).
  assert (b=true).
  { destruct Hpure as (P1&P2).
    subst. symmetry in P2. apply size_count_true_eq_inv in P2.
    apply P2 in Hι. eauto. } subst b.
  iMod (slice_delete_full _ _ true with "[$][$]") as "[% (HQ&_&?)]". solve_ndisj. eauto.
  iDestruct (get_lc with "[$]") as "(?&?)". { now apply elem_of_dom. }
  iMod (lc_fupd_elim_later with "[$] HQ") as "HQ". iFrame "HQ".
  iSplitL. 2:easy.
  do 2 iModIntro. iExists (delete ι M), U, ord,_,(ta-1),(ta-1). iFrame.
  iSplitR.
  { iPureIntro.
    destruct Hpure as (?&P2). rewrite /count_true map_filter_delete !map_size_delete.
    rewrite map_lookup_filter !Hι. simpl. split; try lia. rewrite -P2 /count_true. lia. }
  { iRight. iRight. iFrame "#". iFrame. eauto. }
Qed.

Lemma free_finish l X1 X2 X3 :
  finished l ∗ l ↤ ∅ =[↑N|X1|X2|X3]=∗ ♢1.
Proof.
  iIntros "(#[% (?&Hi&?)]&?)". iIntros.
  iInv "Hi" as af_open.
  iDestruct "Hor" as "[(?&_) | [ [% (?&_)] | (_&Hor&?&%)]]".
  { iExFalso. iApply state0_not_state2. iFrame "∗#". }
  { iExFalso. iApply state1_not_state2. iFrame "∗#". }

  iDestruct "Hor" as "[ ? | [% (?&?)]]".
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(?&%)". compute_done. exfalso. easy. }
  iMod (interp_free' with "[$][$]") as "(?&?&?)". iFrame.
  iSplitL. 2:easy.
  do 2 iModIntro. iExists M,U,ord,_,ta,fi. iFrame "%∗". iSmash.
Qed.
End AF.
