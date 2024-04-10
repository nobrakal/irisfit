From Coq Require Import Wellfounded.
From Coq Require Import ssreflect.

From stdpp Require Import base binders gmap gmultiset.

(* ------------------------------------------------------------------------ *)
(* loc *)

(* Locations are modeled with Z, any countable set would work. *)
Inductive loc := to_loc : Z -> loc.
Definition of_loc : loc -> Z := fun '(to_loc x) => x.

(* We inherit various instances form Z. *)
#[export] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.
#[export] Instance loc_countable : Countable loc.
Proof. apply inj_countable' with of_loc to_loc. now intros []. Qed.
#[export] Instance loc_infinite : Infinite loc.
Proof. apply inj_infinite with to_loc (fun x => Some (of_loc x)). easy. Qed.

(* ------------------------------------------------------------------------ *)
(* Syntax of SpaceLambda *)

Inductive int_op := IntAdd | IntMul | IntSub | IntDiv.
Inductive bool_op2 := BoolAnd | BoolOr.

Inductive prim :=
| prim_eq : prim
| prim_neq : prim
| prim_bool_op : bool_op2 -> prim
| prim_int_op : int_op -> prim.

(* Values and terms are mutually recursive, as we model code pointers as
   closed terms. *)
Inductive val : Type :=
| val_loc : loc -> val
| val_bool : bool -> val
| val_int : Z -> val
| val_unit : val
| val_code : binder -> list binder -> tm -> val
with
tm : Type :=
(* values *)
| tm_val : val -> tm
(* call *)
| tm_call : tm -> list tm -> tm
| tm_call_prim : prim -> tm -> tm -> tm
(* let *)
| tm_var : string -> tm
| tm_let : binder -> tm -> tm -> tm
| tm_if : tm -> tm -> tm -> tm
(* Blocks *)
| tm_alloc : tm -> tm
| tm_load  : tm -> tm -> tm
| tm_store : tm -> tm -> tm -> tm
(* Concurrency *)
| tm_fork : tm -> tm
| tm_cas : tm -> tm -> tm -> tm -> tm
| tm_enter : tm
| tm_exit : tm
| tm_poll : tm
.

Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion val_bool : bool >-> val.
Coercion tm_val : val >-> tm.
Coercion tm_var : string >-> tm.

Global Instance inhabited_val : Inhabited val := populate val_unit.
Global Instance inhabited_tm  : Inhabited tm  := populate (tm_val inhabitant).

(* ------------------------------------------------------------------------ *)
(* Eq and Countable instances *)
Global Instance prim_eq_dec : EqDecision prim.
Proof. intros ? ?. unfold Decision. repeat decide equality. Qed.
Global Instance prim_countable : Countable prim.
Proof.
  refine
    (inj_countable'
       (λ op,
         match op with
         | prim_eq => 0
         | prim_neq => 1
         | prim_bool_op x =>
             match x with
             | BoolAnd => 2
             | BoolOr => 3 end
         | prim_int_op x =>
             match x with
             | IntAdd => 4
             | IntMul => 5
             | IntSub => 6
             | IntDiv => 7
             end end)
       (λ n,
         match n with
         | 1 => prim_neq
         | 2 => prim_bool_op BoolAnd
         | 3 => prim_bool_op BoolOr
         | 4 => prim_int_op IntAdd
         | 5 => prim_int_op IntMul
         | 6 => prim_int_op IntSub
         | 7 => prim_int_op IntDiv
         | _ => prim_eq end) _).
  intros x. destruct x as [ | | [] | []]; eauto.
Qed.

Lemma eq_val : forall (x y : val), {x = y} + {x ≠ y}
with  eq_tm : forall (x y : tm), {x = y} + {x ≠ y}.
Proof.
  { decide equality.
    { apply loc_eq_dec. }
    { apply bool_eq_dec. }
    { apply Z.eq_dec. }
    { apply list_eq_dec. intros. apply binder_dec_eq. }
    { apply binder_dec_eq. } }
  { decide equality.
    { apply list_eq_dec. intros. easy. }
    { apply prim_eq_dec. }
    { apply string_eq_dec. }
    { apply binder_dec_eq. } }
Defined.

Global Instance val_eq_dec : EqDecision val := eq_val.
Global Instance tm_eq_dec : EqDecision tm := eq_tm.

(* Intermediate to help for countable of tm *)
Inductive lit :=
| Lloc : loc -> lit
| Lbool : bool -> lit
| Lint : Z -> lit
| Lunit : lit
| Lprim : prim -> lit.

Global Instance lit_eq_dec : EqDecision lit.
Proof.
  intros ??. unfold Decision. decide equality.
  apply loc_eq_dec. apply bool_eq_dec. apply Z.eq_dec.
  apply prim_eq_dec.
Qed.

Global Instance lit_countable : Countable lit.
Proof.
  refine (inj_countable' (fun op => match op with
  | Lloc l => inl (inl (inl l))
  | Lbool b => inl (inl (inr b))
  | Lint n => inl (inr n)
  | Lunit => inr (inl tt)
  | Lprim p => inr (inr p)
  end) (λ n, match n with
             | inl (inl (inl l)) => Lloc l
             | inl (inl (inr b)) => Lbool b
             | inl (inr n) => Lint n
             | inr (inl tt) => Lunit
             | inr (inr p) => Lprim p end) _).
  intros []; eauto.
Qed.

Definition leaf_binder x : gen_tree (list binder + lit) :=
  GenLeaf (inl [x]).

Local Fixpoint enct (t:tm) :=
  match t with
  | tm_val v => GenNode 0 [encv v]
  | tm_call t ts => GenNode 1 [enct t; GenNode 2 (enct <$> ts)]
  | tm_call_prim p t1 t2 => GenNode 3 [GenLeaf (inr (Lprim p)); enct t1; enct t2]
  | tm_var x => GenNode 4 [GenLeaf (inl [BNamed x])]
  | tm_let x t1 t2 => GenNode 5 [leaf_binder x; enct t1; enct t2]
  | tm_if t1 t2 t3 => GenNode 6 [enct t1; enct t2; enct t3]
  | tm_alloc t1 => GenNode 7 [enct t1]
  | tm_load t1 t2 => GenNode 8 [enct t1; enct t2]
  | tm_store t1 t2 t3 => GenNode 9 [enct t1; enct t2; enct t3]
  | tm_fork t1 => GenNode 10 [enct t1]
  | tm_cas t1 t2 t3 t4 => GenNode 11 [enct t1; enct t2; enct t3; enct t4]
  | tm_enter => GenNode 12 []
  | tm_exit => GenNode 13 []
  | tm_poll => GenNode 14 []
  end
with encv (v:val) :=
  match v with
  | val_loc l => GenLeaf (inr (Lloc l))
  | val_bool b => GenLeaf (inr (Lbool b))
  | val_int n => GenLeaf (inr (Lint n))
  | val_unit => GenLeaf (inr Lunit)
  | val_code x xs t =>
      GenNode 15 [enct t; GenLeaf (inl [x]); GenLeaf (inl xs)] end.

Local Fixpoint dect (t:gen_tree (list binder + lit)) : tm :=
  match t with
  | GenNode 0 [v] => tm_val (decv v)
  | GenNode 1 [t;GenNode 2 ts] => tm_call (dect t) (dect <$> ts)
  | GenNode 3 [GenLeaf (inr (Lprim p)); t1; t2] => tm_call_prim p (dect t1) (dect t2)
  | GenNode 4 [GenLeaf (inl [BNamed x])] => tm_var x
  | GenNode 5 [GenLeaf (inl [x]); t1; t2] => tm_let x (dect t1) (dect t2)
  | GenNode 6 [t1; t2; t3] => tm_if (dect t1) (dect t2) (dect t3)
  | GenNode 7 [t1] => tm_alloc (dect t1)
  | GenNode 8 [t1; t2] => tm_load (dect t1) (dect t2)
  | GenNode 9 [t1; t2; t3] => tm_store (dect t1) (dect t2) (dect t3)
  | GenNode 10 [t1] => tm_fork (dect t1)
  | GenNode 11 [t1; t2; t3; t4] => tm_cas (dect t1) (dect t2) (dect t3) (dect t4)
  | GenNode 12 [] => tm_enter
  | GenNode 13 [] => tm_exit
  | GenNode 14 [] => tm_poll
  | _ => tm_val val_unit end
with decv (v:gen_tree (list binder + lit)) :=
  match v with
  | GenLeaf (inr (Lloc l)) => val_loc l
  | GenLeaf (inr (Lbool b)) => val_bool b
  | GenLeaf (inr (Lint n)) => val_int n
  | GenLeaf (inr Lunit) => val_unit
  | GenNode 15 [t; GenLeaf (inl [x]); GenLeaf (inl xs)] =>
      val_code x xs (dect t)
  | _ => val_unit end.

Definition to_val (t:tm) : option val :=
  match t with
  | tm_val v => Some v
  | _ => None end.

Lemma to_val_Some t v :
  to_val t = Some v ->
  t = v.
Proof. destruct t; naive_solver. Qed.

Global Instance tm_countable : Countable tm.
Proof.
  refine (inj_countable' enct dect _).
  refine (fix go (t:tm) {struct t} := _ with gov (v:val) {struct v} := _ for go).
  - destruct t as [ v | | | | | | | | | | | | | ]; simpl; f_equal; try done.
    exact (gov v).
    { clear t. induction l. done. simpl. f_equal. apply go. apply IHl. }
  - destruct v; simpl.
    1-4: easy.
    { f_equal. apply go. }
Qed.
Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable tm_val to_val  _).
  intros []; eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* For well founded recursion. *)

(* A size function for well founded recursion over tm. *)
Fixpoint tm_size (t : tm):= 1 +
  match t with
  | tm_var _ | tm_val _ => 0
  | tm_enter | tm_exit | tm_poll => 1
  | tm_call t1 xs => tm_size t1 + list_sum (tm_size <$> xs)
  | tm_let _ t1 t2 | tm_load t1 t2 | tm_call_prim _ t1 t2   => tm_size t1 + tm_size t2
  | tm_alloc t1 => tm_size t1
  | tm_store t1 t2 t3 | tm_if t1 t2 t3 => tm_size t1 + tm_size t2 + tm_size t3
  | tm_cas t1 t2 t3 t4 => tm_size t1 + tm_size t2 + tm_size t3 + tm_size t4
  | tm_fork t1  => 1 + tm_size t1 (* Adding one so  size () + size t < size (fork t) *)
  end.

Lemma tm_size_non_zero t :
  tm_size t ≠ 0.
Proof. destruct t; simpl; lia. Qed.

(* ------------------------------------------------------------------------ *)
(* Contexts. *)

Inductive ctx :=
| ctx_let : binder -> tm -> ctx (* let x = ◻ in t *)
| ctx_call1 : list tm -> ctx (* call ◻ ts *)
| ctx_call2 : val -> list val -> list tm -> ctx (* call v (vs ++ ◻ :: ts) *)
| ctx_call_prim1 : prim -> tm -> ctx (* call_prim p ◻ t *)
| ctx_call_prim2 : prim -> val -> ctx (* call_prim p v ◻ *)
| ctx_if : tm -> tm -> ctx (* if ◻ then t1 else t2 *)
| ctx_alloc : ctx (* alloc ◻ *)
| ctx_load1 : tm -> ctx (* load ◻ t *)
| ctx_load2 : val -> ctx (* load v ◻ *)
| ctx_store1 : tm -> tm -> ctx (* store ◻ t1 t2 *)
| ctx_store2 : val -> tm -> ctx (* store v ◻ t *)
| ctx_store3 : val -> val -> ctx (* store v1 v2 ◻ *)
| ctx_cas1 : tm -> tm -> tm -> ctx (* cas ◻ t1 t2 t3 *)
| ctx_cas2 : val -> tm -> tm -> ctx (* cas v ◻ t1 t2 *)
| ctx_cas3 : val -> val -> tm -> ctx (* cas v1 v2 ◻ t *)
| ctx_cas4 : val -> val -> val -> ctx (* cas v1 v2 v3 ◻ *)
.

Definition fill_item (E:ctx) (t:tm) : tm :=
  match E with
  | ctx_let x t2 => tm_let x t t2
  | ctx_call1 xs => tm_call t xs
  | ctx_call2 t1 xs ys => tm_call t1 ((tm_val <$> xs) ++ t :: ys)
  | ctx_call_prim1 p t2 => tm_call_prim p t t2
  | ctx_call_prim2 p v => tm_call_prim p (tm_val v) t
  | ctx_if t2 t3 => tm_if t t2 t3
  | ctx_alloc => tm_alloc t
  | ctx_load1 t2 => tm_load t t2
  | ctx_load2 v => tm_load (tm_val v) t
  | ctx_store1 t1 t2 => tm_store t t1 t2
  | ctx_store2 v t2 => tm_store (tm_val v) t t2
  | ctx_store3 v1 v2 => tm_store (tm_val v1) (tm_val v2) t
  | ctx_cas1 t1 t2 t3 => tm_cas t t1 t2 t3
  | ctx_cas2 v t2 t3 => tm_cas (tm_val v) t t2 t3
  | ctx_cas3 v1 v2 t3 => tm_cas (tm_val v1) (tm_val v2) t t3
  | ctx_cas4 v1 v2 v3 => tm_cas (tm_val v1) (tm_val v2) (tm_val v3) t
  end.

Lemma tm_size_ctx_lt E t :
  tm_size t < tm_size (fill_item E t).
Proof.
  destruct E; simpl; try lia.
  rewrite fmap_app list_sum_app. simpl. lia.
Qed.

Lemma to_val_fill_item E t :
  to_val (fill_item E t) = None.
Proof. now destruct E. Qed.

Lemma ctx_list_length xs xs' t t' ys ys' :
  to_val t = None ->
  to_val t' = None ->
  (tm_val <$> xs) ++ t :: ys = (tm_val <$> xs') ++ t' :: ys' ->
  length xs = length xs'.
Proof.
  revert xs' t t' ys ys'.
  induction xs; intros xs' t t' ys ys' ? ? Heq; simpl in *.
  { destruct xs'; try easy.
    injection Heq. intros. subst. easy. }
  { destruct xs'.
    { exfalso. simpl in *. injection Heq. intros. subst. easy. }
    { simpl. injection Heq. intros Heq' ?. f_equal. subst. eapply IHxs.
      3:eauto. all:eauto. } }
Qed.

Lemma middle_list {A:Type} (l:list A) x l1 l2 :
  l = l1 ++ x::l2 ->
  l !! length l1 = Some x.
Proof.
  intros ->.
  rewrite list_lookup_middle; easy.
Qed.

(* If t and t' are not values, then fill_item is injective. *)
Lemma fill_item_inj E t E' t' :
  to_val t = None ->
  to_val t' = None ->
  fill_item E t = fill_item E' t' ->
  E = E' /\ t = t'.
Proof.
  intros ? ? Heq.
  assert (Inj eq eq tm_val) as Hinj.
  { intros ? ? Heq'. injection Heq'. easy. }
  revert E' Heq. induction E; intros [] Heq; simpl in *; try congruence; injection Heq; intros; subst; try easy.
  { assert (length l = length l1).
    { eauto using ctx_list_length. }
    apply app_inj_1 in H1; last rewrite !fmap_length //.
    destruct H1 as (Hl1&Hl2). injection Hl2. clear Hl2. intros -> ->.
    split; try easy.
    apply list_fmap_eq_inj in Hl1; subst; easy. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Implicit Types *)
Implicit Type v : val.
Implicit Type t : tm.
Implicit Type E : ctx.

(* ------------------------------------------------------------------------ *)
(* Locations of a value *)

(* The base function, return the list of pointers followed by the GC
   in a value *)
Definition val_pointer_list (v:val) : list loc :=
  match v with
  | val_loc l => [l]
  | val_unit | val_int _ | val_bool _ => []
  (* We consider code pointers, without any outgoing pointers.
     This is coherent with the substitution defined above, which does not
     substitute inside code pointers. *)
  | val_code _ _ _ => [] end.

(* We define a typeclass to define [locs],
   a function returning a set of locations.*)
Class Location A := locs : A -> gset loc.

Global Instance location_loc : Location loc := gset_singleton.

Lemma locs_loc (l:loc) : locs l = {[l]}.
Proof. easy. Qed.

Definition locs_val (v:val) : gset loc :=
  list_to_set (val_pointer_list v).

Global Instance location_val : Location val := locs_val.

Lemma locs_val_alt v :
  locs_val v = match v with | val_loc l => {[l]} | _ => ∅ end.
Proof.
  destruct v; try easy.
  unfold locs_val. simpl.
  rewrite right_id_L; try easy.
Qed.

Lemma locs_val_unit : locs_val (val_unit) = ∅.
Proof. easy. Qed.

Lemma locs_val_nat n : locs_val (val_int n) = ∅.
Proof. easy. Qed.

Lemma locs_val_code self args body : locs_val (val_code self args body) = ∅.
Proof. easy. Qed.

Lemma locs_val_loc l :
  locs_val (val_loc l) = {[l]}.
Proof. now rewrite locs_val_alt. Qed.

#[export] Hint Rewrite
 locs_val_unit locs_val_nat locs_val_code locs_val_loc locs_loc : rew_locs_val.
Ltac auto_locs_val :=
  autorewrite with rew_locs_val.

Global Instance location_option (A:Type) :
  Location A -> Location (option A) :=
  fun locs x =>
    match x with None => ∅ | Some x => locs x end.

Definition locs_list `{Location A} (ls:list A) : gset loc :=
  ⋃ (locs <$> ls).

Global Instance location_list `{Location A} : Location (list A) := locs_list.

Fixpoint locs_tm (t:tm) : gset loc :=
  match t with
  | tm_val v => locs_val v
  | tm_call t1 xs => locs_tm t1 ∪ ⋃ (locs_tm <$> xs)
  | tm_call_prim _ t1 t2 => locs_tm t1 ∪ locs_tm t2
  | tm_let _ t1 t2 => locs_tm t1 ∪ locs_tm t2
  | tm_var _ | tm_enter | tm_exit | tm_poll => ∅
  | tm_if t1 t2 t3 => locs_tm t1 ∪ locs_tm t2 ∪ locs_tm t3
  | tm_alloc t1 => locs_tm t1
  | tm_load t1 t2 => locs_tm t1 ∪ locs_tm t2
  | tm_store t1 t2 t3 => locs_tm t1 ∪ locs_tm t2 ∪ locs_tm t3
  | tm_fork t1 => locs_tm t1
  | tm_cas t1 t2 t3 t4 => locs_tm t1 ∪ locs_tm t2 ∪ locs_tm t3 ∪ locs_tm t4
  end.

Global Instance location_tm : Location tm := locs_tm.

Definition locs_ctx (k:ctx) : gset loc :=
  match k with
  | ctx_let _ t2 => locs_tm t2
  | ctx_call1 xs => ⋃ (locs_tm <$> xs)
  | ctx_call2 t1 xs ys => locs_tm t1 ∪ ⋃ (locs_val <$> xs) ∪ ⋃ (locs_tm <$> ys)
  | ctx_call_prim1 _ t2 => locs_tm t2
  | ctx_call_prim2 _ v => locs_val v
  | ctx_if t2 t3 => locs_tm t2 ∪ locs_tm t3
  | ctx_alloc => ∅
  | ctx_load1 t2 => locs_tm t2
  | ctx_load2 v => locs_val v
  | ctx_store1 t1 t2 => locs_tm t1 ∪ locs_tm t2
  | ctx_store2 v t2 => locs_val v ∪ locs_tm t2
  | ctx_store3 v1 v2 => locs_val v1 ∪ locs_val v2
  | ctx_cas1 t1 t2 t3 => locs_tm t1 ∪ locs_tm t2 ∪ locs_tm t3
  | ctx_cas2 v t2 t3 => locs_val v ∪ locs_tm t2 ∪ locs_tm t3
  | ctx_cas3 v1 v2 t3 => locs_val v1 ∪ locs_val v2 ∪ locs_tm t3
  | ctx_cas4 v1 v2 v3 => locs_val v1 ∪ locs_val v2 ∪ locs_tm v3
  end.

Global Instance location_ctx : Location ctx := locs_ctx.

Lemma locs_to_val t v :
  to_val t = Some v ->
  locs t = locs v.
Proof.
  intros E.
  destruct t; simpl in E; try congruence.
  injection E. intros ->.
  easy.
Qed.

Lemma locs_fmap_vals (vs:list val) :
  ⋃ (locs_tm <$> (tm_val <$> vs))%stdpp = locs vs.
Proof.
  induction vs; set_solver.
Qed.

Lemma locs_fill_item E t :
  locs (fill_item E t) = locs E ∪ locs t.
Proof.
  revert t; induction E; intros; try set_solver;
    unfold locs, location_tm; simpl.
  rewrite fmap_app fmap_cons.
  rewrite union_list_app_L union_list_cons.
  rewrite locs_fmap_vals.
  set_solver.
Qed.

Ltac auto_locs :=
  unfold locs, location_list, location_ctx, location_tm, location_val, locs_list in *;
  simpl;
  rewrite ?locs_fill_item ?locs_fmap_vals;
  auto_locs_val.

Lemma locs_elem_subseteq bs n v:
  bs !! n = Some v ->
  locs_val v ⊆ locs bs.
Proof.
  intros Hn.
  auto_locs. unfold location_list, locs_list.
  rewrite <- (take_drop_middle _ _ _ Hn).
  rewrite fmap_app fmap_cons union_list_app.
  set_solver.
Qed.

(* ------------------------------------------------------------------------ *)
(* A simple helper *)

Definition is_loc v :=
  match v with
  | val_loc _ => true
  | _ => false end.

Lemma locs_val_no_loc v :
  ¬ is_loc v -> locs_val v = ∅.
Proof. destruct v; auto_locs; easy. Qed.

Lemma locs_no_loc v :
  ¬ is_loc v -> locs v = ∅.
Proof. intros. auto_locs. rewrite locs_val_no_loc; easy. Qed.
