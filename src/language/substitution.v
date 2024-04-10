From Coq Require Import Wellfounded.

From stdpp Require Import base binders sets stringmap.

From irisfit.language Require Import syntax.

(* ------------------------------------------------------------------------ *)
(* Substitution. *)

(* Usual substitution, avoiding capture. *)
Fixpoint subst (x:string) (v:val) (t:tm) : tm :=
  match t with
  | tm_val v =>
      t (* We do not substitute inside code pointers. *)
  | tm_call t1 xs => tm_call (subst x v t1) ((subst x v) <$> xs)
  | tm_call_prim p t1 t2 => tm_call_prim p (subst x v t1) (subst x v t2)
  | tm_var y =>
      if (decide (BNamed x=y)) then tm_val v else t
  | tm_let y t1 t2 =>
      let st1 := subst x v t1 in
      if (decide (BNamed x=y)) then tm_let y st1 t2 else tm_let y st1 (subst x v t2)
  | tm_if t1 t2 t3 => tm_if (subst x v t1) (subst x v t2) (subst x v t3)
  | tm_alloc t1 =>  tm_alloc (subst x v t1)
  | tm_load t1 t2 => tm_load (subst x v t1) (subst x v t2)
  | tm_store t1 t2 t3 => tm_store (subst x v t1) (subst x v t2) (subst x v t3)
  | tm_fork t1 => tm_fork (subst x v t1)
  | tm_cas t1 t2 t3 t4 => tm_cas (subst x v t1) (subst x v t2) (subst x v t3) (subst x v t4)
  | tm_enter | tm_exit | tm_poll => t
  end.

Definition subst' (mx : binder) (v : val) : tm → tm :=
  match mx with BNamed x => subst x v | BAnon => id end.

(* Iterated substitution *)
Definition substs (xlvs : list (string * val)) (i : tm) : tm :=
  foldr (fun '(x, lv) => subst x lv) i xlvs.

Definition substs' (xlvs : list (binder * val)) (i : tm) : tm :=
  foldr (fun '(x, lv) => subst' x lv) i xlvs.

(* ------------------------------------------------------------------------ *)
(* FV *)

Definition binder_set (b : binder) : stringset :=
  match b with
  | BAnon => ∅
  | BNamed s => {[s]}
  end.

Definition set_of_args (args : list binder) := ⋃ (List.map binder_set args).

Fixpoint free_variables (t:tm) : stringset :=
  match t with
  | tm_val v => ∅ (* No free variables in code pointers *)
  | tm_enter | tm_exit | tm_poll => ∅
  | tm_call t ts => free_variables t ∪ ⋃ (List.map free_variables ts)
  | tm_var x => binder_set x
  | tm_alloc t => free_variables t
  | tm_load t1 t2 | tm_call_prim _ t1 t2 => free_variables t1 ∪ free_variables t2
  | tm_if t1 t2 t3 | tm_store t1 t2 t3 => free_variables t1 ∪ free_variables t2 ∪ free_variables t3
  | tm_cas t1 t2 t3 t4 =>
      free_variables t1 ∪ free_variables t2 ∪ free_variables t3 ∪ free_variables t4
  | tm_let x t1 t2 => free_variables t1 ∪ (free_variables t2 ∖ binder_set x)
  | tm_fork t1 => free_variables t1
  end.

(* ------------------------------------------------------------------------ *)
(* Facts about substitution *)

Lemma substs_app ls1 ls2 t :
  substs (ls1 ++ ls2) t = substs ls1 (substs ls2 t).
Proof. unfold substs. now rewrite foldr_app. Qed.

Lemma substs'_app ls1 ls2 t :
  substs' (ls1 ++ ls2) t = substs' ls1 (substs' ls2 t).
Proof. unfold substs'. now rewrite foldr_app. Qed.

Lemma substs_let_notin ls (x:string) t1 t2 :
  x ∉ ls.*1 ->
  substs ls (tm_let x t1 t2) = tm_let (BNamed x) (substs ls t1) (substs ls t2).
Proof.
  revert x t1 t2.
  induction ls as [|(?,?)]; intros ? ? ? Hx; try easy.
  simpl. rewrite IHls.
  2:{ simpl in *. set_solver. }
  simpl. case_decide as Heq; try easy. simpl in *.
  set_solver.
Qed.

Lemma substs_let_anon ls t1 t2 :
  substs ls (tm_let BAnon t1 t2) = tm_let BAnon (substs ls t1) (substs ls t2).
Proof.
  revert t1 t2. induction ls as [|(?,?)]; intros; try easy.
  simpl. now rewrite IHls.
Qed.

Lemma subst_not_in x v t :
  x ∉ free_variables t ->
  subst x v t = t.
Proof.
  intros.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; simpl; eauto.
  { f_equal. apply H0. simpl; lia. set_solver.
    induction l; simpl; try easy.
    unfold "<$>" in *. f_equal.
    { apply H0. simpl; lia. set_solver. }
    apply IHl. intros. apply H0. simpl in *.
    pose proof (tm_size_non_zero a). unfold "<$>" in *. lia.
    set_solver. set_solver. }
  2:{ case_decide; set_solver. }
  2:{ simpl in *. case_decide; try set_solver.
    { f_equal; apply H0; simpl; try lia; try set_solver. }
    { f_equal; apply H0; simpl; try lia; try set_solver.
      destruct b; simpl in *; set_solver. } }
  all: f_equal; apply H0; simpl; try lia; try set_solver.
Qed.

Lemma substs_free_variables_empty ls t :
  free_variables t = ∅ ->
  substs ls t = t.
Proof.
  revert t. induction ls as [|(b,?)]; intros; try easy.
  simpl. rewrite IHls; try easy.
  rewrite subst_not_in; try easy.
  set_solver.
Qed.

Lemma subst_subst_commut x1 v1 x2 v2 t :
  x1 ≠ x2 ->
  subst x1 v1 (subst x2 v2 t) = subst x2 v2 (subst x1 v1 t).
Proof.
  intros.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; simpl; try easy.
  { f_equal. apply H0. simpl. lia.
    induction l; try easy.
    simpl. f_equal.
    { apply H0. simpl. lia. }
    apply IHl. intros. apply H0. simpl in *. pose proof (tm_size_non_zero a). unfold "<$>" in *. lia. }
  2:{ do 2 case_decide; subst; simpl; try congruence.
    1,2: rewrite decide_True; try easy.
    do 2 (rewrite decide_False; try easy). }
  2:{ do 2 case_decide; subst; simpl; try congruence.
    { rewrite decide_False; try easy. rewrite decide_True; try easy.
      f_equal. apply H0. simpl. lia. }
    { rewrite decide_True; try easy. rewrite decide_False; try easy.
      f_equal. apply H0. simpl. lia. }
    { do 2 (rewrite decide_False; try easy). f_equal; apply H0; simpl; lia. } }
  all: f_equal; apply H0; simpl; lia.
Qed.

Lemma subst_substs_commut x v fs t :
  x ∉ fs.*1 ->
  subst x v (substs fs t) = substs fs (subst x v t).
Proof.
  intros.
  induction fs as [|(b,?)]; try easy.
  simpl. rewrite (subst_subst_commut x v). rewrite IHfs.
  easy.
  all:set_solver.
Qed.

Lemma subst_substs'_commut x v fs t :
  x ∉ set_of_args fs.*1 ->
  subst x v (substs' fs t) = substs' fs (subst x v t).
Proof.
  intros.
  induction fs as [|(b,?)]; try easy.
  destruct b; simpl; try easy.
  { apply IHfs. set_solver. }
  simpl. rewrite (subst_subst_commut x v). rewrite IHfs.
  easy.
  set_solver. simpl in *. unfold set_of_args in *. set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* Locs *)

Local Ltac rewih H t :=
  rewrite (H t) by (simpl; lia).

Lemma locs_subst_precise x v t :
  locs (subst x v t) = locs t ∪ if (decide (x ∈ free_variables t)) then locs v else ∅.
Proof.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; simpl; auto_locs;
    try (rewih H t); try (rewih H t1);
    try (rewih H t2); try (rewih H t3); try (rewih H t4); try (rewih H t5); try (rewih H t6).
  1:set_solver.
  { induction l.
    { repeat case_decide; set_solver. }
    { assert  (∀ y : tm, tm_size y < tm_size (tm_call t l) → locs (subst x v y) = locs y ∪ (if decide (x ∈ free_variables y) then locs v else ∅)) as IHt.
    { intros ? Ht. apply H.
      transitivity (tm_size (tm_call t l)); try easy.
      simpl. pose proof (tm_size_non_zero a). unfold "<$>". lia. }
    simpl. repeat rewih H a. clear H.
    apply IHl in IHt.
    clear IHl.
    destruct (decide (x ∈ free_variables t)).
    { rewrite decide_True in IHt by set_solver.
      destruct (decide (x ∈ free_variables a)).
      { rewrite decide_True by set_solver. set_solver. }
      { rewrite decide_True by set_solver. set_solver. } }
    { destruct (decide (x ∈ free_variables a)).
      { rewrite decide_True by set_solver.
        destruct (decide (x ∈ free_variables t ∪ ⋃ map free_variables l)).
        all:set_solver. }
      { destruct (decide (x ∈ free_variables t ∪ ⋃ map free_variables l)).
        { rewrite decide_True by set_solver. set_solver. }
        { rewrite decide_False by set_solver. set_solver. } } } } }
  1,2:repeat case_decide; set_solver.
  { destruct (decide (BNamed x=b)); auto_locs; rewih H t1.
    { repeat rewrite <- assoc_L; try apply _. f_equal.
      repeat case_decide; set_solver. }
    { rewih H t2. clear H. repeat case_decide; destruct b; set_solver. } }
  all: clear H. 7,8,9:compute_done.
  1-5:repeat case_decide; set_solver.
  { rewrite <- !assoc_L. 2-11:apply _. f_equal.

    Ltac go_comm n :=
      do n (rewrite assoc_L; only 2:apply _);
      rewrite (comm_L _ _ (locs_tm _));
      do n (rewrite <- assoc_L; only 2:apply _); f_equal.

   go_comm ltac:(1).
   go_comm ltac:(2).
   go_comm ltac:(3).
   repeat case_decide; set_solver. }
Qed.

Lemma locs_subst x v t :
  locs (subst x v t) ⊆ locs v ∪ locs t.
Proof.
  rewrite locs_subst_precise.
  case_decide; set_solver.
Qed.

Lemma locs_substs ls t :
  locs (substs ls t) ⊆ locs (snd <$> ls) ∪ locs t.
Proof.
  induction ls as [|(x,v) ls].
  { set_solver. }
  pose proof (locs_subst x v (substs ls t)).
  set_solver.
Qed.

Lemma locs_substs' ls t :
  locs (substs' ls t) ⊆ locs (snd <$> ls) ∪ locs t.
Proof.
  induction ls as [|(x,v) ls].
  { set_solver. }
  destruct x as [|x]; try set_solver.
  pose proof (locs_subst x v (substs' ls t)).
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* size *)

Lemma size_subst x v t :
  tm_size (subst x v t) = tm_size t.
Proof.
  intros.
  induction t using (well_founded_induction (wf_inverse_image _ nat _ tm_size PeanoNat.Nat.lt_wf_0)).
  destruct t; simpl; try (rewrite (H t)); try (rewrite (H t1)); try (rewrite (H t2)); try (rewrite (H t3)); try (rewrite (H t4)).
  all:simpl; try lia.
  { do 2 f_equal. induction l; try done.
    rewrite !fmap_cons. simpl. rewrite H. 2:simpl;lia.
    f_equal. apply IHl. intros. apply H. simpl in *. unfold "<$>" in *. lia. }
  { case_decide; simpl; lia. }
  { case_decide; simpl; try (rewrite (H t)); try (rewrite (H t1)); try (rewrite (H t2)); simpl; lia. }
Qed.

Lemma size_subst' x v t :
  tm_size (subst' x v t) = tm_size t.
Proof. destruct x; try done. apply size_subst. Qed.

Lemma size_substs' xs t :
  tm_size (substs' xs t) = tm_size t.
Proof.
  induction xs as [|(?,?)]; simpl.
  done. rewrite size_subst'. done.
Qed.
