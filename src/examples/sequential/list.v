From irisfit.examples Require Import proofmode.

(* ------------------------------------------------------------------------ *)
(* Definition of lists and functions on them.
   In particular, we define ListOf, which abstracts the item, and
   List using ListOf.

   Empty lists are represented with the _unit_ constructor.
 *)

Definition list_is_nil : val :=
  λ: [["l"]], "l" '== val_unit.

Definition list_head : val :=
  λ: [["l"]], "l".[0].

Definition list_tail : val :=
  λ: [["l"]], "l".[1].

Definition list_nil : val :=
  λ: [[]], val_unit.

Definition list_cons : val :=
  λ: [["x","xs"]] ,
    let: "l" := alloc 2 in
    "l".[0] <- "x" ;;
    "l".[1] <- "xs";;
    "l".

Definition soup `{!interpGS0 Σ} {A} (R:A -> val -> iProp Σ)
  (r:smultiset loc) (xs:list (A * (Qz * Qp))) (vs:list val) : iProp Σ :=
  ([∗ list] x;v ∈ xs;vs,
     let '(x,(qz,qp)) := x in (R x v ∗ v ⟸?{qp} ∅ ∗ v ↤?{qz} r)).

Module ListsOf.

Fixpoint ListOf `{!interpGS0 Σ} {A} (R:A -> val -> iProp Σ) (xs : list (A * (Qz * Qp))) (l : val) : iProp Σ :=
  match xs with
  | [] => ⌜l=val_unit⌝
  | (x,(qz,qp)) :: xs =>
    ∃ l0 v l',  ⌜l=val_loc l0⌝ ∗ l0 ↦ [ v; l'] ∗ R x v ∗ v ⟸?{qp} ∅ ∗ v ↤?{qz} {[+l0+]} ∗ l' ⟸? ∅ ∗ l' ↤? {[+l0+]} ∗ ListOf R xs l'
end.

Lemma ListOf_eq `{!interpGS0 Σ} {A} (R:A -> val -> iProp Σ) (xs : list (A * (Qz * Qp))) (l:val) :
  ListOf R xs l = ( match xs with
  | [] => ⌜l=val_unit⌝
  | (x,(qz,qp)) :: xs =>
    ∃ l0 v l',  ⌜l=val_loc l0⌝ ∗ l0 ↦ [ v; l'] ∗ R x v ∗ v ⟸?{qp} ∅ ∗ v ↤?{qz} {[+l0+]} ∗ l' ⟸? ∅ ∗ l' ↤? {[+l0+]} ∗ ListOf R xs l' end)%I.
Proof. destruct xs; easy. Qed.

Lemma list_nil_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) :
  CODE (list_nil [[]])
  TID π
  PRE (True)
  POST (fun (l:val) => ListOf R [] l ∗ l ⟸? {[π]} ∗ l ↤? ∅).
Proof. iSmash. Qed.

(* This spec is a "debt" as, to recover the List predicate in post, the user has
   to cancel the mapsfrom given in arguments by giving the opposite. Thank you smultiset *)
(* We can still derive the usual spec, see below. *)

Lemma list_cons_spec_debt `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) l qz r x v xs :
  (is_loc v -> qz ≠ 0%Qz) ->
  CODE (list_cons [[v,l]])
  TID π
  PRE  (♢2 ∗ ListOf R xs l ∗ l ⟸? {[π]} ∗ l ↤? r ∗ R x v ∗ v ↤?{qz} ∅)
  POST (fun (l':val) => l' ⟸? {[π]} ∗ l' ↤? ∅ ∗ (∀ qp, v ⟸?{qp} ∅ -∗ l ↤?{0} (opposite r) -∗ ListOf R ((x,(qz,qp))::xs) l')).
Proof.
  iIntros (?) "(? & ? & ? & ? & ? & ?)".
  wpc_call. wpc_let_noclean. wpc_alloc.
  iIntros (l') "(?&?&Hl'&_)". simpl.
  wpc_let_noclean. iSteps.
  wpc_let_noclean. iStep 8.

  iDestruct (confront_pbt_vpbt with "[$]") as "%".
  { by vm_compute. }
  pclean l by ltac:(fun _ => destruct l; set_solver).

  iStep 2. iFrame. iIntros.
  iExists l',v,l. iFrame.
  rewrite left_id. iFrame.
  iSplitR; first done.
  iDestruct (vmapsfrom_join with "[$]") as "?".
  rewrite left_id.
  assert (opposite r ⊎ (r ⊎ {[+ l' +]}) ≡ {[+ l' +]}) as -> by smultiset_solver.
  iFrame.
Qed.

(* XXX *)
Lemma vmapsfrom_split_empty `{!interpGS0 Σ} v q L :
  v ↤?{q} L -∗ v ↤?{q} L ∗ v ↤?{0} ∅.
Proof.
  iIntros. iDestruct (vmapsfrom_correct with "[$]") as "%".
  iApply vmapsfrom_split.
  { set_solver. }
  { smultiset_solver. }
  by do 2 rewrite right_id.
Qed.

Lemma list_cons_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) l qz qp x v xs :
  (is_loc v -> qz ≠ 0%Qz) ->
  CODE (list_cons [[v,l]])
  TID π
  PRE  (♢2 ∗ ListOf R xs l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ R x v ∗ v ⟸?{qp} {[π]} ∗ v ↤?{qz} ∅)
  POST (fun (l':val) => ListOf R ((x,(qz,qp))::xs) l' ∗ l' ⟸? {[π]} ∗ l' ↤? ∅).
Proof.
  iIntros (?) "(?&?&?&Hfl&?&?&?)".
  iDestruct (vmapsfrom_split_empty l with "[$]") as "(?&?)".
  iApply wpc_postpone.
  iDestruct (list_cons_spec_debt _ A R l qz with "[$]") as "?".
  { easy. }
  iApply (wpc_mono with "[$]").
  iIntros (?) "(?&?&Hf)".
  iDestruct (confront_vpbt_vpbt with "[$]") as "%".
  { apply Qp.not_add_le_l. }
  pclean v. iApply wpc_val. iFrame. iApply ("Hf" with "[$]").
  assert (opposite ∅ ≡ ∅) as -> by set_solver.
  done.
Qed.

Lemma list_is_nil_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) l vs :
  CODE (list_is_nil [[l]])
  TID π
  PRE (ListOf R vs l)
  POST (fun (b:bool) => ⌜b <-> vs = nil⌝ ∗ ListOf R vs l).
Proof.
  iIntros "Hl".
  wpc_call. wpc_call_prim.
  destruct vs as [|(?,(?,?))]; simpl.
  { iDestruct "Hl" as "%". subst. done. }
  { iDestruct "Hl" as "[%[%[%[% (?&?&?&?&?&?&?)]]]]". subst.
    iSmash. }
Qed.

Definition Beheaded `{!interpGS0 Σ} {A} (R:A -> val -> iProp Σ) (v:val) qz xs (l:val) : iProp Σ:=
  ∃ (l0:loc) (l':val), ⌜l=val_loc l0⌝ ∗ l0 ↦ [ v; l'] ∗ v ↤?{qz} {[+l0+]} ∗ l' ⟸? ∅ ∗ l' ↤? {[+l0+]} ∗ ListOf R xs l'.

Lemma list_head_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) l qz qp x xs :
  CODE (list_head [[l]])
  TID π
  PRE  (ListOf R ((x,(qz,qp))::xs) l)
  POST (fun v => R x v ∗ v ⟸?{qp} {[π]} ∗ Beheaded R v qz xs l).
Proof.
  iIntros "[%[%[% (->&?&?&?&?&?&?&?)]]]".
  wpc_call. wpc_load. iIntros "(?&?)".
  iSmash.
Qed.

(* LATER is there a better spec for tail ? *)
Lemma list_tail_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) v l qz xs :
  CODE (list_tail [[l]])
  TID π
  PRE  (Beheaded R v qz xs l)
  POST (fun (l':val) => ∃ (l0:loc), ⌜l=val_loc l0⌝ ∗ ListOf R xs l' ∗ l' ⟸? {[π]} ∗ l' ↤? {[+l0+]} ∗ l0 ↦ [ v ; l'] ∗ v ↤?{qz} {[+l0+]}).
Proof.
  iIntros "[%[% (->&?&?&?&?&?)]]".
  wpc_call. wpc_load. iSmash.
Qed.

Lemma list_free `{!interpGS0 Σ} A (R:A -> val -> iProp Σ) l xs :
  l ⟸? ∅ ∗ l ↤? ∅ ∗ ListOf R xs l =[#]=∗
  ♢(2*length xs) ∗ ∃ vs, soup R ∅ xs vs.
Proof.
  revert l.
  induction xs as [|(x,(qz,qp)) vs]; intros l.
  { iIntros "(?&?&->)". iIntros. iFrame. rewrite nil_length right_absorb.
    iMod diamonds_zero. iFrame.
    iExists nil. by iApply big_sepL2_nil. }
  { iIntros "(?&?& [%l0 [%v [%l' (->&?&?&?&?&?&?&?)]]])". iIntros.
    iMod (interp_free with "[$][$]") as "(?&?&?&#?)". done.
    simpl.
    fold (ListOf R vs l').
    iMod (vmapsfrom_cleanup l' with "[$] [$]") as "(?&?)".
    iMod (vmapsfrom_cleanup v with "[$] [$]") as "(?&?)".
    rewrite disj_union_singleton_opposite.

    iMod (IHvs with "[$] [$]") as "(?&?&[%vs' ?])"; try easy.
    iFrame.
    iDestruct (diamonds_join with "[$]") as "Hdiams".
    iSplitL "Hdiams".
    { conclude_diamonds. }
    { iExists (v::vs'). by iFrame. } }
Qed.

Global Opaque ListOf.

End ListsOf.

Module Lists.
Import ListsOf.
Definition List `{!interpGS0 Σ} (xs:list (val*(Qz*Qp))) l : iProp Σ :=
  ListOf (fun x y => ⌜x=y⌝)%I xs l.

(* OLD
Lemma List_nil `{!interpGS0 Σ} l :
  (l ↦ BBlock [ ^0 ])%I ≡ List nil l.
Proof. easy. Qed.
Lemma List_cons `{!interpGS0 Σ} x qz qp xs l :
  (∃ l', l ↦ BBlock [ ^1; x; #l'] ∗ vStackable x qp ∗ x ↤?{qz} {[+l+]} ∗ Stackable l' 1%Qp ∗ l' ↤ {[+l+]} ∗ List xs l')%I ≡ List ((x,(qz,qp))::xs) l.
Proof.
  iSplit. iSteps. iApply ListOf_cons. iSteps.
  unfold List. rewrite -ListOf_cons. iSteps.
Qed.
*)

Lemma list_nil_spec `{!interpGS0 Σ} π :
  CODE (list_nil [[]])
  TID π
  PRE  (True)
  POST (fun (l:val) => List [] l ∗ l ⟸? {[π]}∗ l ↤? ∅).
Proof.
  iIntros.
  wpc_apply (@list_nil_spec _ _ _ val (fun x y => ⌜x=y⌝)%I).
  iIntros. simpl. rewrite left_id. iIntros. iFrame.
Qed.

Lemma list_cons_spec `{!interpGS0 Σ} π A (R:A -> val -> iProp Σ) l qz qp x xs :
  (is_loc x -> qz ≠ 0%Qz) ->
  CODE (list_cons [[x,l]])
  TID π
  PRE  (♢2 ∗ List xs l ∗ l ⟸? {[π]} ∗ l ↤? ∅ ∗ x ⟸?{qp} {[π]} ∗ x ↤?{qz} ∅)
  POST (fun (l':val) => List ((x,(qz,qp))::xs) l' ∗ l' ⟸? {[π]} ∗ l' ↤? ∅).
Proof.
  iIntros (?) "(?&?&?&?&?&?)".
  wpc_apply (@list_cons_spec _ _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Lemma list_is_nil_spec `{!interpGS0 Σ} π l xs :
  CODE (list_is_nil [[l]])
  TID π
  PRE (List xs l)
  POST (fun (b:bool) => ⌜b <-> xs = nil⌝ ∗ List xs l).
Proof.
  iIntros.
  wpc_apply (@list_is_nil_spec _ _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Definition Beheaded `{!interpGS0 Σ} (v:val) qz xs (l:val) : iProp Σ:=
  ∃ (l0:loc) (l':val), ⌜l=val_loc l0⌝ ∗ l0 ↦ [ v; l'] ∗ v ↤?{qz} {[+l0+]} ∗ l' ⟸? ∅ ∗ l' ↤? {[+l0+]} ∗ List xs l'.

Lemma list_head_spec `{!interpGS0 Σ} π l qz qp x xs :
  CODE (list_head [[l]])
  TID π
  PRE  (List ((x,(qz,qp))::xs) l)
  POST (fun v => ⌜x=v⌝ ∗ v ⟸?{qp} {[π]} ∗ Beheaded v qz xs l).
Proof.
  iIntros.
  wpc_apply (@list_head_spec _ _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Lemma list_tail_spec `{!interpGS0 Σ} π v qz l xs :
  CODE (list_tail [[l]])
  TID π
  PRE (Beheaded v qz xs l)
  POST (fun (l':val) => ∃ (l0:loc), ⌜l=val_loc l0⌝ ∗ List xs l' ∗ l' ⟸? {[π]} ∗ l' ↤? {[+l0+]} ∗ l0 ↦ [ v ; l'] ∗ v ↤?{qz} {[+l0+]}).
Proof.
  iIntros.
  wpc_apply (@list_tail_spec _ _ _ val (fun x y => ⌜x=y⌝)%I); eauto.
Qed.

Lemma list_free `{!interpGS0 Σ} l xs :
  l ⟸? ∅ ∗ l ↤? ∅ ∗ List xs l =[#]=∗
  ♢(2*length xs) ∗ ∃ vs, soup (fun x y => ⌜x=y⌝)%I ∅ xs vs.
Proof.
  apply list_free.
Qed.
End Lists.
