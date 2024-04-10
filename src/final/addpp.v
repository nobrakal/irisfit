From Coq Require Import ssreflect Wellfounded.
From stdpp Require Import base binders gmap gmultiset ssreflect.

From irisfit Require Import syntax notation.
From irisfit.final Require Import common mcs instances.

(* [addpp t] adds a polling point before every call.
   It goes under lambdas. *)
Fixpoint addpp (t:tm) : tm :=
  match t with
  | tm_var _ | tm_enter | tm_exit | tm_poll => t
  | tm_val v => tm_val (addpp_val v)
  | tm_call t1 xs => tm_poll;; tm_call (addpp t1) (addpp <$> xs)
  | tm_call_prim p t1 t2 => tm_call_prim p (addpp t1) (addpp t2)
  | tm_let y t1 t2 => tm_let y (addpp t1) (addpp t2)
  | tm_if t1 t2 t3 => tm_if (addpp t1) (addpp t2) (addpp t3)
  | tm_alloc t1 => tm_alloc (addpp t1)
  | tm_load t1 t2 => tm_load (addpp t1) (addpp t2)
  | tm_store t1 t2 t3 => tm_store (addpp t1) (addpp t2) (addpp t3)
  | tm_fork t1 => tm_fork (addpp t1)
  | tm_cas t1 t2 t3 t4 => tm_cas (addpp t1) (addpp t2) (addpp t3) (addpp t4)
  end
with addpp_val v :=
   match v with
   | val_code x y t => val_code x y (addpp t)
   | _ => v end
.

Lemma addpp_val_inv t v :
  addpp t = tm_val v ->
  exists (v':val), t = v' /\ v = addpp_val v'.
Proof.
  destruct t; inversion 1. eauto.
Qed.

Definition is_let_call E :=
  match E with
  | ctx_let BAnon (tm_call _ _) => true
  | _ => false end.

Lemma val_ok_no_code (v:val) :
  (match v with val_code _ _ _ => False | _ => True end) ->
  tm_val v = addpp v.
Proof. by destruct v. Qed.

Lemma commute_ok (xs:list val) :
  (addpp <$> (tm_val <$> xs)) = tm_val <$> (addpp_val <$> xs).
Proof.
  induction xs; try done.
  rewrite !fmap_cons. rewrite IHxs. f_equal.
Qed.

Lemma subst_addpp_val x v t :
  (subst x (addpp_val v) (addpp t)) = addpp (subst x v t).
Proof.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; simpl; eauto.
  { f_equal. erewrite <- H. 2:simpl; lia.
    f_equal.
    induction l. done. rewrite !fmap_cons. f_equal.
    { apply H. simpl. lia. }
    { apply IHl. intros ??. apply H. simpl in *. unfold "<$>" in *. lia. } }
  { f_equal. all:apply H; simpl; lia. }
  { case_decide; f_equal. }
  { case_decide; subst; simpl; f_equal.
    all:apply H; simpl; lia. }
  { f_equal. all:apply H; simpl; lia. }
  { f_equal.
    erewrite <- H. 2:simpl; lia. f_equal. }
  { f_equal. all:apply H; simpl; lia. }
  { f_equal. all:apply H; simpl; lia. }
  { f_equal. all:apply H; simpl; lia. }
  { f_equal. all:apply H; simpl; lia. }
Qed.

Lemma subst'_addpp_val x v t :
  (subst' x (addpp_val v) (addpp t)) = addpp (subst' x v t).
Proof.
  destruct x. done. simpl. apply subst_addpp_val.
Qed.

Lemma substs'_addpp_val xs ys t :
  substs' (zip xs (addpp_val <$> ys)) (addpp t) =
  addpp (substs' (zip xs ys) t).
Proof.
  revert ys. induction xs; intros ys.
  done. simpl. destruct ys; try done. simpl.
  rewrite -subst'_addpp_val. f_equal. eauto.
Qed.
