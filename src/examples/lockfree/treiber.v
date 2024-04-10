From iris.base_logic.lib Require Export ghost_map gen_heap.
From iris.algebra Require Import numbers auth list gset.

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

(******************************************************************************)
(* The cmras we need. *)

Canonical Structure valO := leibnizO val.
Canonical Structure locO := leibnizO loc.
Canonical Structure QzO := leibnizO Qz.
Notation modelO := (listO (prodO valO (prodO fracO QzO))).
Notation elem := (val * (Qp * Qz))%type.

Class stackG Σ :=
  StackG {
      stack_bonesG : inG Σ (authUR (gsetUR locO));
      stack_protectG : ghost_mapG Σ nat (loc*loc);
    }.

Local Existing Instances stack_bonesG stack_protectG.

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

  To allow for private cells, we use a mechanism of "bones".
  Inner cells are bones. Each bone is either deallocated or pointed
  by some locations.
  These locations appears in the codomain of a ghost protection map.
 *)

Definition isbone  (γ:gname) (l:loc) : iProp Σ :=
  own γ (◯ {[l]}).

Definition protect γ v l : iProp Σ :=
  isbone γ v ∗ sizeof l 2 ∗
  ((l ↤ ∅ ∗ l ⟸ ∅) ∨ († v ∗ †l ∗ ♢2)).

Definition protection (γ:gname) (M:gmap nat (loc*loc)) : iProp Σ :=
  [∗ map] π ↦ x ∈ M, protect γ x.1 x.2.

Definition stamped (v:loc) (L:gmultiset loc) (M:gmap nat (loc*loc)) :=
  forall l', l' ∈ L <-> exists π, M !! π = Some (v,l').

Definition nodup `{Countable A} (X:gmultiset A) :=
  forall l, multiplicity l X <= 1.

Definition bone M l : iProp Σ :=
  †l ∨
  (∃ L, l ↤{1/2} (smultiset.of_gmultiset L) ∗
        ⌜stamped l L M /\ nodup L⌝).

Definition bones (γ:gname) (M:gmap nat (loc*loc)) : iProp Σ :=
  ∃ (A:gset loc),
    own γ (● A) ∗ [∗ set] l ∈ A, bone M l.

Fixpoint spine (γ:gname) (xs:list (val*(Qp*Qz))) (v:val) : iProp Σ :=
  match xs with
  | nil => ⌜v=val_unit⌝
  | (x,(p,q))::xs =>
      ∃ l v', ⌜v=val_loc l⌝ ∗
      l ↦□ [x; v'] ∗ l ⟸ ∅ ∗ isbone γ l ∗
      (* One half of pointedby here, the other half in bones. *)
      v' ↤?{1/2} {[+l+]} ∗ x ⟸?{p} ∅ ∗ x ↤?{q} {[+l+]} ∗
      spine γ xs v' end.

Global Instance spine_timeless γ xs v : Timeless (spine γ xs v).
Proof. revert v; induction xs as [|(?&?&?)]; apply _. Qed.

Definition phys_stack γ (s:loc) (xs:list elem) : iProp Σ :=
  †s ∨ ∃ v, s ↦ [v] ∗ v ↤?{1/2} {[+s+]} ∗ spine γ xs v.

Definition visbone (γ:gname) (v:val) : iProp Σ :=
  ⌜v=val_unit⌝ ∨ (∃ l, ⌜v=val_loc l⌝ ∗ isbone γ l).

Lemma spine_visbone γ xs v :
  spine γ xs v -∗ visbone γ v.
Proof.
  destruct xs as [|(?&?&?)].
  { iIntros "->". by iLeft. }
  { iIntros "[%[% (->&?&?&?&_)]]". iRight. iExists _. by iFrame. }
Qed.

Definition kindofinj (M:gmap nat (loc*loc)) :=
  forall i1 i2 v1 v2 l,
    M !! i1 = Some (v1,l) ->
    M !! i2 = Some (v2,l) ->
    i1 = i2.

Definition nm := nroot.@"treiber".

Definition stack (s:loc) (xs:list elem) : iProp Σ :=
  ∃ (g:gstack) (M:gmap nat (loc*loc)),
    meta s nm g ∗
    ⌜kindofinj M⌝ ∗
    phys_stack g.(gb) s xs ∗
    ghost_map_auth g.(gp) 1 M ∗
    protection g.(gb) M ∗
    bones g.(gb) M.

Lemma open_stack_inv_meta s g xs :
  meta s nm g -∗
  stack s xs -∗
  ∃ (M:gmap nat (loc*loc)),
    ⌜kindofinj M⌝ ∗
    phys_stack g.(gb) s xs ∗
    ghost_map_auth g.(gp) 1 M ∗
    protection g.(gb) M ∗
    bones g.(gb) M.
Proof.
  iIntros "Hmeta (%&%&Hmeta'&?)".
  iDestruct (meta_agree with "Hmeta Hmeta'") as "->".
  iExists _. by iFrame.
Qed.

Lemma create_spec π :
  ♢1 -∗
  wpc ⊤ π (Some ∅) (create [[]])%T
    (fun (s:loc) => stack s [] ∗ s ⟸ {[π]} ∗ s ↤ ∅).
Proof.
  iIntros.
  wpc_call.

  iApply wpc_postpone.
  wpc_alloc.
  iIntros (s) "(?&X1&X2&?)".

  iMod (own_alloc (● ∅)) as "[%γ2 H2]".
  { by apply auth_auth_valid. }

  iMod ghost_map_alloc_empty  as "[%γ3 ?]".

  pose (g := mk_gs γ2 γ3).
  iMod (meta_set _ s g nm with "[$]") as "#?". solve_ndisj.

  iAssert (stack s nil) with "[-X1 X2]" as "Hs".
  { iExists _,_. subst g. simpl. iFrame "#∗".
    iSplitR.
    { iPureIntro. intros ?????. rewrite lookup_empty. naive_solver. }
    iSplitR "H2".
    { iRight. iExists _. by iFrame. }
    iSplitR "H2".
    { by iApply big_sepM_empty. }
    { iExists _. iFrame. by iApply big_sepS_empty. } }

  wpc_val. iFrame.
Qed.

Definition reg γ (i:nat) (v:val) (l':loc) : iProp Σ :=
  (⌜v=val_unit⌝ ∗ l' ↤ ∅ ∗ l' ⟸ ∅)
  ∨ (∃ l, ⌜v=val_loc l⌝ ∗ i ↪[γ] (l,l')).

Lemma register_aux (v:loc) l γ γ' M :
  isbone γ' v -∗
  ghost_map_auth γ 1 M -∗
  protection γ' M -∗
  sizeof l 2 ∗ l ↤ ∅ ∗ l ⟸ ∅ ==∗
  ∃ i, ⌜i ∉ dom M⌝ ∗ ghost_map_auth γ 1 (<[i:=(v,l)]>M) ∗ protection γ' (<[i:=(v,l)]>M) ∗ i ↪[γ] (v,l).
Proof.
  iIntros  "H1 H2 H3 (?&?&?)". iExists (fresh (dom M)).
  assert (fresh (dom M) ∉ dom M) by apply is_fresh.
  iMod (ghost_map_insert (fresh (dom M)) with "[$]") as "(?&?)"; last iFrame.
  { by apply not_elem_of_dom. }
  iSplitR. done.
  iApply big_sepM_insert. by apply not_elem_of_dom.
  iFrame. iLeft. by iFrame.
Qed.

Lemma update_set_bone M M' A :
  (forall (l:loc) L, l ∈ A -> stamped l L M -> stamped l L M') ->
  ([∗ set] y ∈ A, bone M y)%I -∗
  [∗ set] y ∈ A, bone M' y.
Proof.
  iIntros. iApply (big_sepS_impl with "[$]").
  iModIntro. iIntros (??) "[?|[%(?&%&%)]]".
  by iLeft.
  iRight. iExists _. iFrame. iPureIntro. eauto.
Qed.

Lemma bones_update γ M M':
  (forall (l:loc) L, stamped l L M -> stamped l L M') ->
  bones γ M -∗ bones γ M'.
Proof.
  iIntros (?) "[% (?&?)]". iExists _. iFrame.
  iApply (update_set_bone with "[$]"); eauto.
Qed.

Lemma stamped_insert_fresh (v v':loc) l' L M π :
  v ≠ v' ->
  π ∉ dom M ->
  stamped v L M ->
  stamped v L (<[π:=(v',l')]> M).
Proof.
  intros ? ? E1 l0. rewrite E1. split.
  { intros (i,Hi). exists i. rewrite lookup_insert_ne //.
    intros ->. eauto using elem_of_dom. }
  { intros (i,Hi). rewrite lookup_insert_case in Hi. case_decide; eauto.
    exfalso. inversion Hi. subst. congruence. }
Qed.

Lemma confront_protect_pbt γ l v A :
  l ⟸ A ∗ protect γ v l -∗ False.
Proof.
  iIntros "(?&(_&_&[(?&?)|(?&?&?)]))".
  { iDestruct (pbt_valid2 with "[$][$]") as "%Hv". exfalso. by vm_compute. }
  { iApply (confront_pbt_dag with "[$]"). }
Qed.

Definition vdead v : iProp Σ :=
  ∃ l, ⌜v=val_loc l⌝ ∗ †l.

Lemma register l' γ γ' v M :
  kindofinj M ->
  visbone γ' v -∗
  sizeof l' 2 ∗ l' ↤ ∅ ∗ l' ⟸ ∅ -∗
  bones γ' M -∗
  ghost_map_auth γ 1 M -∗
  protection γ' M ==∗
  ∃ i M', ⌜kindofinj M'⌝ ∗ ghost_map_auth γ 1 M' ∗ protection γ' M' ∗ reg γ i v l' ∗
  ((vdead v ∗ bones γ' M')
  ∨  (v ↤?{(1/4)%Qz} ∅ ∗ ((v ↤?{1/4} {[+l'+]}) -∗ bones γ' M'))).
Proof.
  iIntros (Hk) "#Hb (E1&E2&E3) Hbones H1 H2".
  iAssert (⌜∀ v i l0, M !! i = Some (v,l0) -> l0 ≠ l'⌝ )%I as "%X".
  { iIntros (??? HM ->).
    iDestruct (big_sepM_lookup with "[$]") as "?". apply HM. simpl.
    iDestruct (confront_protect_pbt with "[$]") as "?". done. }

  iDestruct "Hb" as "[ -> | [%l (->&?)]]".
  { iExists 0,M. iFrame. iSmash. }

  iMod (register_aux with "[$][$][$][$]") as "[%i [%M' (?&?&Hr)]]".
  iModIntro. iExists i,(<[i:=(l,l')]> M). iFrame.
  iSplit.
  { iIntros (????? E1 E2). rewrite lookup_insert_case in E1.
    case_decide; subst.
    { rewrite lookup_insert_case in E2. case_decide; subst.
      { iPureIntro. naive_solver. }
      { inversion E1. subst. naive_solver. } }
    { rewrite lookup_insert_case in E2. case_decide; subst.
      { inversion E2. subst. naive_solver. }
      { eauto. } } }

  iDestruct "Hbones" as "[%A (Hba&Hs)]".
  iDestruct (more_cmras.elem_of_gset with "Hba [$]") as "%".
  replace A with ({[l]} ∪ A ∖ {[l]}).
  2:{ rewrite union_comm_L difference_union_L. set_solver. }
  rewrite big_sepS_insert. 2:set_solver.

  iSplitL "Hr". iSmash.
  iDestruct "Hs" as "(Hb&Hs)".

  iDestruct "Hb" as "[#?|[% (Hl&(%E2&%E3))]]".
  { iLeft. simpl. iSplitR. iExists _. by iFrame "#".
    iExists _. iFrame. rewrite big_sepS_insert. 2:set_solver.
    iFrame. iFrame "#".
    iApply (update_set_bone with "[$]").
    intros. eapply stamped_insert_fresh; eauto. set_solver. }

  iRight.
  replace (1 / 2)%Qz with (1/4 + 1/4)%Qz by compute_done.
  rewrite -(left_id _ _ L).
  iDestruct (mapsfrom_split with "[$]") as "(Hx&?)". 3:done.
  1,2:intros E; exfalso; by vm_compute.
  { rewrite of_gmultiset_disj_union. done. }
  rewrite of_gmultiset_empty. iFrame. iIntros.
  iExists _. iFrame "Hba". rewrite big_sepS_insert. 2:set_solver.
  iSplitR "Hs".
  { iRight. iExists ({[+ l' +]} ⊎ L). iFrame. iSplitL; last eauto.
    replace (1 / 2)%Qz with (1/4 + 1/4)%Qz by compute_done.
    rewrite of_gmultiset_disj_union of_gmultiset_singleton.
    iApply (mapsfrom_join with "[$][$]").
    iPureIntro. split_and !; eauto.
    { intros l0. rewrite gmultiset_elem_of_disj_union gmultiset_elem_of_singleton.
      destruct_decide (decide (l0=l')); subst.
      { split. intros _. exists i. rewrite lookup_insert //. eauto. }
      rewrite E2. split.
      { intros [|(i',Hi)]; first congruence. exists i'. rewrite lookup_insert_ne //.
        intros ->. naive_solver. }
      intros (i',Hi). right. exists i'. rewrite lookup_insert_case in Hi.
      case_decide; eauto. inversion Hi. done. }
    { assert (l' ∉ L).
      { intros R. apply E2 in R. destruct R. naive_solver. }
      unfold nodup in *. intros. rewrite multiplicity_disj_union.
      multiset_solver. } }
  { iApply (update_set_bone with "[$]"). intros.
    eapply stamped_insert_fresh; eauto. set_solver. }
Qed.

Definition sentenced l n : iProp Σ :=
  (l ⟸ ∅ ∗ l ↤ ∅) ∨ (†l ∗ ♢n).

Lemma stamped_delete (l:loc) M π v (l':loc) L :
  v ≠ l ->
  M !! π = Some (v, l') ->
  stamped l L M →
  stamped l L (delete π M).
Proof.
  intros ? ? E l0. rewrite E.
  split; intros (i,Hi).
  { exists i. rewrite lookup_delete_ne //. intros ->. naive_solver. }
  { apply lookup_delete_Some in Hi. naive_solver. }
Qed.

Lemma kindofinj_delete M π :
  kindofinj M ->
  kindofinj (delete π M).
Proof.
  intros ??????. rewrite !lookup_delete_Some. naive_solver.
Qed.

Lemma nodup_remove `{Countable A} (X Y:gmultiset A) :
  nodup X -> nodup (X ∖ Y).
Proof.
  intros E l'. specialize (E l'). rewrite multiplicity_difference. multiset_solver.
Qed.

Definition schrodinger γ M v l : iProp Σ :=
  ((vdead v ∗ bones γ M ∗ sentenced l 2) ∨
    l ↤ ∅ ∗ l ⟸ ∅ ∗ v ↤?{1/4}{[+l+]} ∗ (v ↤?{1/4} ∅ -∗ bones γ M )).

Lemma unreg l' γ γ' i v M :
  kindofinj M ->
  ghost_map_auth γ 1 M ∗
  protection γ' M ∗
  bones γ' M ∗
  visbone γ' v ∗
  reg γ i v l' =[#]=∗
  ∃ M', ⌜kindofinj M'⌝ ∗
        ghost_map_auth γ 1 M' ∗ protection γ' M' ∗ schrodinger γ' M' v l'.
Proof.
  iIntros (Hk) "(Ha&Hp&Hb&Hi&Hf)". iIntros.
  iDestruct "Hf" as "[ [-> (?&?)] | [%l (->&Hf)]]".
  { iFrame. iModIntro. iExists _. iFrame "%∗". iSmash. }
  iDestruct (ghost_map_lookup with "Ha Hf") as "%".
  iMod (ghost_map_delete with "Ha Hf").

  rewrite /protection big_sepM_delete //.
  iDestruct "Hp" as "((#?&#?&X)&?)". simpl.

  iDestruct "Hi" as "[%|[%l0 (%Eq&Hf)]]". congruence.
  inversion Eq. subst l0.
  iDestruct "Hb" as "[% (Ha&Hx)]".
  iDestruct (more_cmras.elem_of_gset with "Ha Hf") as "%Hv".
  replace A with ({[l]} ∪ A ∖ {[l]}).
  2:{ rewrite union_comm_L difference_union_L. set_solver. }
  rewrite big_sepS_insert. 2:set_solver. iDestruct "Hx" as "(U&Hx)".
  iDestruct "U" as "[#?|[%(?&%E2&%E3)]]".
  { iModIntro. iFrame "#∗".
    iExists (delete i M). iFrame. iSplitR. eauto using kindofinj_delete.
    iLeft. iSplitR. iSmash. iSplitR "X".
    { iExists _. iFrame "Ha". rewrite big_sepS_insert. 2:set_solver.
      iSplitR. by iLeft. iApply (update_set_bone with "[$]").
      { intros. eapply stamped_delete; eauto. set_solver. } }
    { iDestruct "X" as "[(?&?) | (?&?)]"; [iLeft | iRight]; iFrame "#∗". } }

  iDestruct "X" as "[(?&?) | (?&_)]"; last first.
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(?&?)". compute_done.
    done. }
  iFrame. iModIntro.
  iExists (delete i M). iFrame "#∗". iSplitR. eauto using kindofinj_delete.
  iRight. iFrame.
  rewrite (gmultiset_disj_union_difference' l' L).
  2:{ apply E2. eauto. }
  replace (1 / 2)%Qz with (1/4 + 1/4)%Qz by compute_done.
  rewrite of_gmultiset_disj_union.
  iDestruct (mapsfrom_split with "[$]") as "(?&?)".
  3,4:done. 1,2:by vm_compute.
  rewrite of_gmultiset_singleton. iFrame.

  iIntros.
  iDestruct (mapsfrom_join with "[$][$]") as "?".
  replace  (1/4 + 1/4)%Qz with (1 / 2)%Qz  by compute_done.
  rewrite left_id. iExists _. iFrame "Ha".
  rewrite big_sepS_insert. 2:set_solver.
  iSplitR "Hx".
  { iRight. iExists _. iFrame. iPureIntro. split_and !.
    { intros l0. destruct_decide (decide (l0 = l')); subst. split.
      { intros H'. exfalso. specialize (E3 l'). multiset_solver. }
      { intros (i',Hi). apply lookup_delete_Some in Hi. destruct Hi as (?&?).
        exfalso. apply H1; eauto. }
      split.
      { intros E. assert (l0 ∈ L) by multiset_solver.
        apply E2 in H2. destruct H2. exists x. rewrite lookup_delete_ne //.
        intros  ->. naive_solver. }
      { intros (i',Hi). apply lookup_delete_Some in Hi. destruct Hi as (?&Hi).
        assert (l0 ∈ L). apply E2. eauto. multiset_solver. } }
    { by apply nodup_remove. } }
  { iApply (update_set_bone with "[$]").
    { intros. eapply stamped_delete; eauto. set_solver. } }
Qed.

Lemma add_bone h γ M L :
  (∀ i v, ⌜M !! i = Some (h, v)⌝ -∗ isbone γ h) ∗
  bones γ M ∗
  h ↤ L =[#]=∗
  bones γ M ∗ h ↤{1/2} L ∗ isbone γ h.
Proof.
  iIntros "(#Hf&[%A (Ha&Hs)]&Hh)". iIntros.
  destruct_decide (decide (h ∈ A)).
  { iDestruct (big_sepS_elem_of with "[$]") as "X". done.
    iDestruct "X" as "[? | [% (?&_)]]".
    { iMod (confront_mapsfrom_dag with "[$][$]") as "(?&?)". done. done. }
    { iDestruct (mapsfrom_confront with "[$][$]") as "%". by vm_compute.
      congruence. } }

  iAssert (⌜forall i v, M !! i = Some (h,v) -> False⌝)%I as "%".
  { iIntros (???). iSpecialize ("Hf" with "[%//]").
    iDestruct (more_cmras.elem_of_gset with "Ha [$]") as "%".
    congruence. }
  iMod (own_update with "Ha") as "(?&?)".
  { apply auth_update_alloc. apply gset_local_add. }
  rewrite left_id. iFrame. rewrite comm_L. iModIntro.

  iAssert ( h ↤{1/2} L ∗ h ↤{1/2} ∅)%I with "[Hh]" as "(?&?)".
  { iApply (mapsfrom_split with "[$]"). 1,2: naive_solver. compute_done. rewrite right_id //. }
  iFrame.
  iExists _. iFrame. iApply big_sepS_insert. done. iFrame.
  iRight. iExists ∅. rewrite of_gmultiset_empty. iFrame.
  iPureIntro. split_and !.
  { intros l. split; first set_solver. naive_solver. }
  { rewrite /nodup => ?. rewrite multiplicity_empty. lia. }
Qed.

Lemma schrodinger_kill γ M v l' π  S:
  sizeof l' 2 ∗
  inside π S ∗ schrodinger γ M v l' =[#]=∗
  inside π (S∪locs v ∪ {[l']}) ∗ †l' ∗ ♢2 ∗ bones γ M.
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

Lemma open_phys_stack s p Π γ xs :
  s ⟸{p} Π ∗ phys_stack γ s xs -∗
  s ⟸{p} Π ∗ ∃ v, s ↦ [v] ∗ v ↤?{1/2} {[+s+]} ∗ spine γ xs v.
Proof.
  iIntros "(?&[?|?])"; last by iFrame.
  iDestruct (confront_pbt_dag with "[$]") as "%". done.
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
  <<< stack s ((x,(p,q))::xs) | (fun r => ⌜r=val_unit⌝)  >>>.
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

  iApply @wpc_enter. iIntros (k) "%Ek Hk D".
  apply dom_singleton_inv_L in Ek. destruct Ek as (p'&->).

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
  iDestruct "I" as "[%g [%M (#Hmeta&%Hi&I1&I2&I3&I4)]]".
  rewrite -{1}pbt_PBT.
  iDestruct (open_phys_stack with "[$]") as "(HS&[%h (S1&S2&S3)])".
  iDestruct (spine_visbone with "S3") as "#T1".

  iApply wp_tconseq. iApply (tupd_clean_debt h'). iFrame. iIntros "(H7&D)".
  rewrite left_id_L difference_diag_L.

  iDestruct (mapsto_extract_size h' with "[$]") as "#?". simpl.

  wp_apply wp_load_inside. compute_done.
  iIntros (?) "(->&_&?&D)".
  iAssert (stack s xs0) with "[-H2 AU H3 D H5 H6 H7 HS]" as "GO".
  { iExists g,M. iFrame "#%∗". iRight. iExists _. iFrame. }
  iMod ("AU" with "GO") as "AU". iModIntro.
  clear dependent xs0 M.

  iIntros "_". simpl.

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
  iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (%&I1&I2&I3&I4)]".
  rewrite difference_diag_L.
  iMod (register h' with "[$][$][$][$][$]") as
    "[%i [%M' (%&?&?&Hreg&Hcase)]]".
  done.

  iDestruct "Hcase" as "[ (dag&?) | (Hmf&Hback)]".
  (* h was reclaimed by a concurrent [pop] *)
  { iDestruct "dag" as "[%l (->&#?)]".

    iApply wp_tconseq. iApply unreg. done. iFrame "∗#".
    iIntros "[%M'' (%&R1&R2&Hcase)]".
    iApply wp_tconseq. iApply schrodinger_kill. iFrame "∗#".
    iIntros "(D&#?&R3&?)".

    wp_apply wp_store_dead. compute_done.
    iIntros (?) "(->&_&_)".
    iMod ("AU" with "[-H2 H3 D HS R3]") as "AU".
    { iExists _,_. iFrame "#∗". eauto. }
    iIntros "!> _".
    clear dependent xs0 M M' M''.

    iApply wp_let_noclean.
    iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
    iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (%&I1&I2&I3&I4)]".

    iDestruct (open_phys_stack with "[$]") as "(HS&[%h (S1&S2&S3)])".
    destruct_decide (decide (h=l)).
    { subst. iApply wp_tconseq. simpl.
      iApply (confront_mapsfrom_dag _ l). 2:iFrame. compute_done.
      iFrame "#". iIntros. done. }

    wp_apply wp_cas_fail. 1-3:done.
    iIntros (?) "(->&_&?)".
    iMod ("AU" with "[-H2 H3 D HS R3]") as "AU".
    { iExists _,_. iFrame "#∗%". iRight. iExists _. by iFrame. }

    iIntros "!> _". simpl. iApply wp_if. iIntros "!> _".
    iApply wp_tconseq. iApply (vmapsfrom_cleanup x h'). iFrame "#∗". iIntros.
    assert ({[+ h' +]} ⊎ {[-h'-]} ≡ ∅) as -> by smultiset_solver.

    iApply wp_tconseq. iApply (debt_vtransfer x). iFrame. iIntros "(?&?)".
    iApply wp_tconseq. iApply (debt_vtransfer s). iFrame. iIntros "(?&?)".
    rewrite union_idemp_L.

    clean_debt π.
    iApply wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L.
    rewrite -pbt_PBT. iFrame.
    iApply ("IH" with "[$][$][$][$]"). }

  (* h is still allocated, we proceed. *)
  wp_apply wp_store. intros. compute_done. compute_done.

  iIntros (?) "(->&_&H5&X&_)".
  rewrite left_id.
  iSpecialize ("Hback" with "[$]").
  iMod ("AU" with "[-H2 H3 H5 Hreg D HS]") as "AU".
  { iExists _,M'. iFrame "#%∗". }

  clear dependent xs0 M M'.
  iIntros "!> _". simpl.

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&AU)". solve_atomic.
  iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (%&I1&I2&I3&I4)]".
  iDestruct (open_phys_stack with "[$]") as "(HS&[%h0 (S1&S2&S3)])".

  iApply wp_tconseq. iApply unreg. done. iFrame "#∗".
  iIntros "[%M' (%&R1&R2&Hcase)]".

  destruct_decide (decide (h=h0)); try subst h0.
  (* CAS will succeed. *)
  { iDestruct "Hcase" as "[ ([% (->&?)]&_) | (X1&X2&X3&Hback)]".
    { iApply wp_tconseq. iApply confront_mapsfrom_dag.
      2:iFrame. compute_done. iIntros "?". done. }

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

    iAssert (∀ i v, ⌜M' !! i = Some (h', v)⌝ -∗ isbone (gb g) h')%I as "#Hok".
    { iIntros (?? Hi). simpl.
      iDestruct (big_sepM_lookup with "R2") as "(?&_)".
      apply Hi. done. }

    iApply wp_tconseq. iApply add_bone. iFrame "#∗". iIntros "(?&Hh&#?)".
    iApply wp_val.

    iDestruct "AU" as "[_ AU]".
    iMod ("AU" with "[-D HS]") as "HPOST".
    { iExists _,_. iFrame "%∗ Hmeta".
      iRight. iExists _. iFrame. simpl. iFrame.
      iExists h',h. iFrame "∗#". eauto. }

    iIntros "!> _". iApply wp_if. iModIntro. iIntros "_".
    clean_debt π.
    iApply wpc_exit; last iFrame. set_solver. rewrite pbt_PBT. iFrame.
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
    { iExists _,_. iFrame "Hmeta %∗". iRight. iExists _. iFrame. }
    iIntros "!> _". simpl. iApply wp_if. iModIntro. iIntros "_".

    iApply wp_tconseq. iApply (debt_vtransfer x). iFrame. iIntros "(?&?)".
    iApply wp_tconseq. iApply (debt_vtransfer s). iFrame. iIntros "(?&?)".
    rewrite union_idemp_L.
    clean_debt π.
    iApply wpc_exit; last iFrame. set_solver. rewrite dom_singleton_L -pbt_PBT. iFrame.
    iApply ("IH" with "[$][$][$][$]"). }
Qed.

Lemma free_protected (l:loc) γ L M :
  nodup L ->
  (forall (l':loc), l' ∈ L -> ∃ π, M !! π = Some (l, l')) ->
  protection γ M ∗
  l ↤ of_gmultiset L =[#]=∗
  (l ↤ ∅ ∗ (†l -∗ protection γ M)).
Proof.
  iIntros (E2 E3) "(Hp&?)". iIntros.
  iInduction L as [|l' L] "IH" using gmultiset_ind forall (M E2 E3).
  { rewrite of_gmultiset_empty.
    iFrame. iModIntro. eauto. }

  rewrite of_gmultiset_disj_union of_gmultiset_singleton.
  assert (∃ (π:thread_id), M !! π = Some (l, l')) as (i,Hi).
  { apply E3. multiset_solver. }

  rewrite {3}/protection. rewrite big_sepM_delete //. simpl.
  iDestruct "Hp" as "(X&Hp)".
  iDestruct "X" as "(#?&#?&[(?&?)|(?&_)])"; last first.
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(_&?)"; last done.
    by vm_compute. }

  iMod (interp_free'' with "[$][$]") as "(?&?&#?)".
  iMod (mapsfrom_cleanup with "[$][$]") as "(?&?)".
  assert (({[+ l' +]} ⊎ of_gmultiset L ⊎ {[-l'-]}) ≡ of_gmultiset L) as -> by smultiset_solver.

  iMod ("IH" with "[%][%][$][$][$]") as "(?&?&Hb)".
  { intros l0. specialize (E2 l0). rewrite multiplicity_disj_union in E2. multiset_solver. }
  { intros l0 E. destruct (E3 l0). multiset_solver.
    exists x. rewrite lookup_delete_ne //. intros ->.
    rewrite Hi in H0. inversion H0. subst. specialize (E2 l0).
    rewrite multiplicity_disj_union in E2. multiset_solver. }

  iFrame. iModIntro. iIntros.
  iSpecialize ("Hb" with "[$]"). iApply big_sepM_delete. done.
  iFrame. simpl. iFrame "#∗".
Qed.

Lemma free_bone γ l M :
  sizeof l 2 ∗
  isbone γ l ∗
  l ⟸ ∅ ∗ l ↤{1/2} ∅ ∗
  protection γ M ∗
  bones γ M =[#]=∗
  †l ∗ ♢2 ∗ protection γ M ∗ bones γ M.
Proof.
  iIntros "(?&?&?&Hp&Hl&[% (Ha&X)])". iIntros.
  iDestruct (more_cmras.elem_of_gset with "Ha [$]") as "%Hv".
  replace (A) with ({[l]} ∪ A ∖ {[l]}).
  2:{ rewrite union_comm_L difference_union_L. set_solver. }
  rewrite big_sepS_insert. 2:set_solver.

  iDestruct "X" as "([?|[% (?&%E2&%E3)]]&?)".
  { iMod (confront_mapsfrom_dag with "[$][$]") as "(_&?)"; last done. by vm_compute. }
  iDestruct (mapsfrom_join with "[$][$]") as "?". rewrite Qz_div_2 right_id.

  iMod (free_protected with "[$][$]") as "(?&?&Hb)".
  { done. }
  { intros. by eapply E2. }
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

  iApply @wpc_enter. iIntros (k) "%Ek Hk D".
  apply dom_singleton_inv_L in Ek. destruct Ek as (p'&->).

  iApply wp_let_noclean.
  iMod "AU" as (xs0) "(I&[AU _])". solve_atomic.
  iDestruct "I" as "[%g [%M (#Hmeta&%Hi&I1&I2&I3&I4)]]".
  rewrite -{1}pbt_PBT.
  iDestruct (open_phys_stack with "[$]") as "(HS&[%h (S1&S2&S3)])".

  (* XXX copy/pasted *)
  iAssert (visbone g.(gb) h) as "#T1".
  { destruct xs0 as [|(?&?&?)]. iDestruct "S3" as "->". by iLeft.
    iDestruct "S3" as "[%[% (->&?&?&?&?)]]". iRight. iExists _.
    by iFrame. }

  wp_apply wp_load_inside. compute_done.
  iIntros (?) "(->&_&?&D)".

  iAssert (⌜h=val_unit⌝ ∨ ∃ l x h', ⌜h=val_loc l⌝ ∗ l ↦□ [x;h'] ∗ visbone _ h')%I as "#Hcase".
  { destruct xs0 as [|(?&?&?)].
    { iDestruct "S3" as "->". eauto. }
    { iDestruct "S3" as "[%[% (->&?&?&?&?&?&?&?)]]". iRight. iExists _,_,_.
      iDestruct (spine_visbone with "[$]") as "?". by iFrame. } }

  iMod ("AU" with "[-D HS]") as "AU".
  { iExists _,_. iFrame "Hmeta ∗%". iRight. iExists _. iFrame. }
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
  iDestruct (open_stack_inv_meta with "Hmeta I") as "[%M (%Hi&I1&I2&I3&I4)]".
  iDestruct (open_phys_stack with "[$]") as "(HS&[%h0 (S1&S2&S3)])".

  destruct_decide (decide (h0=l)).
  { subst.

    iDestruct "AU" as "[_ AU]". rename xs0 into xs.

    destruct xs as [|(v,(p,q)) xs].
    { iDestruct "S3" as "%". congruence. }
    iDestruct "S3" as "[%[% (%Eq&?&?&Hv&R1&R2&R3&?)]]". inversion Eq. subst l0. clear Eq.
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
    iApply wp_tconseq. iApply free_bone. iFrame.
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

Lemma free_spine γ l xs M :
  spine γ xs l ∗ l ↤?{1/2} ∅ ∗
  protection γ M ∗
  bones γ M =[#]=∗
  ♢(2*length xs) ∗ protection γ M ∗ bones γ M ∗
  handles xs.
Proof.
  iIntros "(Hs&?&?&?)". iIntros.

  iInduction xs as [|(x,(p,q)) xs] "IH" forall (l).
  { simpl. rewrite right_absorb.
    iMod diamonds_zero. rewrite handles_nil. iSmash. }
  iDestruct "Hs" as "[%[% (->&?&?&?&?&?&?&?)]]".
  iDestruct (mapsto_extract_size with "[$]") as "?".
  iMod (free_bone with "[$][$]") as "(?&#?&?&?&?)".
  iMod (vmapsfrom_cleanup x with "[$][$]") as "(?&?)".
  iMod (vmapsfrom_cleanup v' with "[$][$]") as "(?&?)".
  assert (({[+ l0 +]} ⊎ {[-l0-]}) ≡ ∅) as -> by smultiset_solver.
  iMod ("IH" with "[$][$][$][$][$]") as "(?&?&?&?&?)".
  iFrame. iModIntro. simpl.
  conclude_diamonds.
Qed.

Lemma treiber_free s xs :
  stack s xs ∗ s ↤ ∅ ∗ s ⟸ ∅ =[#]=∗
  ♢(1 + 2*length xs) ∗ handles xs.
Proof.
  iIntros "(I&?&?)". iIntros.
  iDestruct "I" as "[%g [%M (_&%Hi&I1&I2&I3&I4)]]".
  iDestruct (open_phys_stack with "[$]") as "(HS&[%h0 (S1&S2&S3)])".
  iMod (interp_free' s with "[$][$]") as "(?&C1&?&#?)".
  iMod (vmapsfrom_cleanup with "[$][$]") as "(?&?)".

  assert (({[+ s +]} ⊎ {[-s-]}) ≡ ∅) as -> by smultiset_solver.
  iMod (free_spine with "[$][$]") as "(?&C2&?&?&?)". iFrame.
  conclude_diamonds.
Qed.

End Treiber_proof.
