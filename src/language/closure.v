From stdpp Require Import binders gmap stringmap.
From irisfit Require Import syntax notation.

Open Scope Z_scope.

(* foldr + an index of the current element. *)
Fixpoint foldri {A B} i (f:nat -> B → A → A) (e:A) (xs:list B) : A :=
  match xs with
  | nil => e
  | x::xs => f i x (foldri (S i) f e xs) end.

Definition stores_from (i:nat) clo_blk init fvi :=
  foldri i
    (fun i binder term =>
       tm_let BAnon (tm_store clo_blk (val_int (Z.of_nat i)) (tm_var binder))
         term)
    init fvi.
Definition stores clo_blk init fvi :=
  stores_from 1 clo_blk init fvi.

Definition loads_from i clo_name code fvi :=
  foldri i
    (fun i binder term =>
       tm_let (BNamed binder) (tm_load clo_name (val_int (Z.of_nat i))) term)
    code fvi.
Definition loads clo_name code fvi :=
  loads_from 1 clo_name code fvi.

Definition code_clo (self:string) args code fvi :=
  let inner_code := loads self code fvi in
  val_code BAnon (BNamed self :: args) inner_code.

Definition init_clo clo_blk code fvi :=
  let init := tm_store clo_blk 0%Z code in
  stores clo_blk init fvi.

Definition fv_clo self args code : list string :=
  elements (free_variables code ∖ ({[self]} ∪ set_of_args args)).

Definition mk_clo_aux (self:string) (args:list binder) (code:tm) : tm :=
  (* We compute the list of free variables *)
  let fv := fv_clo self args code in
  (* The code of our closure. *)
  let code := code_clo self args code fv in

  (* Actual term. *)
  let: self := tm_alloc (1 + (Z.of_nat (List.length fv)))%Z in
  (init_clo self code fv);;
  self.

Definition extract_self self args code :=
  match self with
  | BAnon => fresh_string_of_set "self" (free_variables code ∪ set_of_args args)
  | BNamed self => self end.

Definition mk_clo (self:binder) (args:list binder) (code:tm) : tm :=
  let self' := extract_self self args code in
  mk_clo_aux self' args code.

Lemma mk_clo_eq self args code :
  mk_clo self args code =
    let self' := extract_self self args code in
    mk_clo_aux self' args code.
Proof. easy. Qed.

Definition call_clo (clo:tm) (args:list tm) : tm :=
  tm_call (clo.[0%Z]) (clo::args).

Lemma call_clo_eq clo args :
  call_clo clo args =
    (tm_call (clo.[0%Z]) (clo::args))%T.
Proof. easy. Qed.

Lemma locs_stores i (r t : tm) fv:
  locs (stores_from i r t fv) ⊆ locs r ∪ locs t.
Proof.
  revert i r t.
  induction fv; intros; auto_locs; set_solver.
Qed.

Lemma locs_mk_clo self args code :
  locs_tm (mk_clo self args code) = ∅.
Proof.
  auto_locs. unfold init_clo,stores.
  remember (extract_self self args code) as self'.
  pose proof (locs_stores 1 self' (self'.[^0] <- (code_clo self' args code (fv_clo self' args code))) (fv_clo self' args code)).
  auto_locs.
  simpl in *.
  set_solver.
Qed.

Lemma subst_call_clo x v t args :
  subst x v (call_clo t args) = call_clo (subst x v t) (subst x v <$> args).
Proof. easy. Qed.

(*
Definition test : tm :=
  let: "x" := 2 in
  let: "f" :=
    mk_clo "self" ["y" : binder]
      (if: "y" then "x" else call_clo "self" [[("y" '- 1)]])%T in
  call_clo "f" [tm_val (val_nat 1)].

Eval vm_compute in test.
*)
