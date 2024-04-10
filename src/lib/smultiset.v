(* This file introduces signed multisets (also know as hybrid sets or shadow sets),
   which generalise multisets by allowing for negative membership. *)

From stdpp Require Export countable.
From stdpp Require Import gmap options.
From stdpp Require gmultiset.

(* A notation for negative singletons *)
Class SingletonNS A B := singletonNS: A → B.
Global Hint Mode SingletonNS - ! : typeclass_instances.
Global Instance: Params (@singletonNS) 3 := {}.
Notation "{[- x -]}" := (singletonNS x) (at level 1, format "{[- x -]}") : stdpp_scope.
Notation "{[- x ; y ; .. ; z -]}" :=
  (disj_union .. (disj_union (singletonNS x) (singletonNS y)) .. (singletonNS z))
  (at level 1, format "{[- x ; y ; .. ; z -]}") : stdpp_scope.

Record smultiset A `{Countable A} := Smultiset { smultiset_car : gmap A Z }.
Global Arguments Smultiset {_ _ _} _ : assert.
Global Arguments smultiset_car {_ _ _} _ : assert.

Global Instance smultiset_eq_dec `{Countable A} : EqDecision (smultiset A).
Proof. solve_decision. Defined.

Global Program Instance smultiset_countable `{Countable A} :
    Countable (smultiset A) := {|
  encode X := encode (smultiset_car X); decode p := Smultiset <$> decode p
|}.
Next Obligation. intros ? ? ? [?]; simpl. by rewrite decode_encode. Qed.

(* A notation for opposite *)
Class Opposite A:= opposite : A -> A.
Global Hint Mode Opposite ! : typeclass_instances.
Global Instance: Params (@opposite) 1 := {}.

Open Scope Z_scope.

Section definitions.
  Context `{Countable A}.

  Local Open Scope Z_scope.

  (* We allow elements with multiplicity 0 in the multiset.
     We sadly loose canonicity of the representation. *)
  Definition multiplicity (x : A) (X : smultiset A) : Z :=
    match smultiset_car X !! x with
    | Some x => x
    | None => 0 end.

  (* x is an element of the multiset is it has a non-zero multiplicity *)
  Global Instance smultiset_elem_of : ElemOf A (smultiset A) := λ x X,
      multiplicity x X <> 0.

  (* X is a sub-signed-multiset of Y if and only if:
     ∀ x ∈ X, x ∈ Y ∧ multiplicity x X ≤  multiplicity x Y *)
  Global Instance smultiset_subseteq : SubsetEq (smultiset A) := λ X Y, ∀ x,
    multiplicity x X <> 0 -> multiplicity x Y <> 0 /\ Z.le (multiplicity x X) (multiplicity x Y).

  (* Two signed multisets are equivalent if all elements have the same multiplicity. *)
  Global Instance smultiset_equiv : Equiv (smultiset A) := λ X Y, ∀ x,
    (multiplicity x X) = (multiplicity x Y).

  Global Instance smultiset_elements : Elements A (smultiset A) := λ X,
    let (X) := X in '(x,n) ← map_to_list X; replicate (Z.to_nat (Z.abs n)) x.
  Global Instance smultiset_size : Size (smultiset A) := length ∘ elements.

  Global Instance smultiset_empty : Empty (smultiset A) := Smultiset ∅.
  Global Instance smultiset_singletonMS : SingletonMS A (smultiset A) := λ x,
      Smultiset {[ x := 1 ]}.
  Global Instance smultiset_singletonNS : SingletonNS A (smultiset A) := λ x,
      Smultiset {[ x := -1 ]}.
  Global Instance smultiset_singleton : SingletonM A Z (smultiset A) := λ x n,
      Smultiset {[ x := n ]}.

  Lemma psingleton_singletons l :
    ({[+ l +]} : smultiset A) = {[ l := 1 ]}.
  Proof. easy. Qed.
  Lemma nsingleton_singletons l :
    ({[- l -]} : smultiset A) = {[ l := -1 ]}.
  Proof. easy. Qed.

  Definition union_aux (x y:Z) :=
    if decide (x = 0) then y else
      if decide (y = 0) then x else
        x `max` y.

  Lemma union_aux_l y :
    union_aux 0 y = y.
  Proof. unfold union_aux; by rewrite decide_True. Qed.

  Lemma union_aux_r x :
    union_aux x 0 = x.
  Proof. unfold union_aux. destruct (decide (x = 0)); intros; subst; easy. Qed.

  Lemma union_aux_lr x y :
    x <> 0 -> y <> 0 ->
    union_aux x y = x `max` y.
  Proof. unfold union_aux; intros; by do 2 (rewrite decide_False; try easy). Qed.

  Lemma union_aux_non_neg x y :
    union_aux x y <> 0 <-> x <> 0 \/ y <> 0.
  Proof.
    unfold union_aux.
    split; intros E.
    { destruct (decide (x=0)); subst; firstorder. }
    { destruct E.
      { rewrite decide_False; try lia.
        destruct (decide (y=0)); subst; firstorder. lia. }
      { destruct (decide (x=0)); subst; firstorder.
        rewrite decide_False; lia. } }
  Qed.

  Definition inter_aux (x y:Z) :=
    if decide (x = 0) then 0 else
      if decide (y = 0) then 0 else
        x `min` y.

  Lemma inter_aux_l y :
    inter_aux 0 y = 0.
  Proof. unfold inter_aux; by rewrite decide_True. Qed.

  Lemma inter_aux_r x :
    inter_aux x 0 = 0.
  Proof. unfold inter_aux. destruct (decide (x = 0)); intros; subst; easy. Qed.

  Lemma inter_aux_lr x y :
    x <> 0 -> y <> 0 ->
    inter_aux x y = x `min` y.
  Proof. unfold inter_aux; intros; by do 2 (rewrite decide_False; try easy). Qed.

  Lemma inter_aux_non_neg x y :
    inter_aux x y <> 0 <-> x <> 0 /\ y <> 0.
  Proof.
    unfold inter_aux.
    split; intros E.
    { destruct (decide (x=0)), (decide (y=0)); subst; firstorder. }
    { destruct E.
      do 2 (rewrite decide_False; try lia). }
  Qed.

  Global Instance smultiset_union : Union (smultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    Smultiset $ union_with (fun x y => Some (union_aux x y)) X Y.
  Global Instance smultiset_intersection : Intersection (smultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    Smultiset $ intersection_with (fun x y => Some (inter_aux x y)) X Y.

  (** Often called the "sum" *)
  Global Instance smultiset_disj_union : DisjUnion (smultiset A) := λ X Y,
      let (X) := X in let (Y) := Y in
      Smultiset $ union_with (λ x y, Some (x + y)) X Y.

  Global Instance smultiset_opposite : Opposite (smultiset A) := λ X,
      let (X) := X in Smultiset $ fmap (λ x, (-x)) X.

  Global Instance smultiset_difference_instance : Difference (smultiset A) := λ X Y,
      X ⊎ opposite Y.

  Lemma smultiset_difference (X Y : smultiset A) :
    X ∖ Y = X ⊎ opposite Y.
  Proof. easy. Qed.

  Global Instance smultiset_dom : Dom (smultiset A) (gset A) := λ X,
      let (X) := X in dom (filter (fun '(_,x) => x <> 0) X).

  Definition negative_part (X:smultiset A) :=
    let (X) := X in Smultiset (filter (fun '(_,x) => x < 0) X).

  Definition positive_part (X:smultiset A) :=
    let (X) := X in Smultiset (filter (fun '(_,x) => x > 0) X).
End definitions.

#[export] Typeclasses Opaque smultiset_elem_of smultiset_subseteq.
#[export] Typeclasses Opaque smultiset_elements smultiset_size.
#[export] Typeclasses Opaque smultiset_empty.
#[export] Typeclasses Opaque smultiset_singleton smultiset_singletonNS smultiset_union.
#[export] Typeclasses Opaque smultiset_dom.

Section basic_lemmas.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : smultiset A.

  Local Open Scope Z_scope.

  Global Instance smultiset_equiv_equivalence : Equivalence (≡@{smultiset A}).
  Proof.
    constructor; try easy.
    intros ? ? ? Hxy ? u.
    now rewrite (Hxy u).
  Qed.

  (* Multiplicity *)
  Lemma multiplicity_empty x : multiplicity x ∅ = 0.
  Proof. done. Qed.
  Lemma multiplicity_psingleton x : multiplicity x {[+ x +]} = 1.
  Proof. unfold multiplicity; simpl. by rewrite lookup_singleton. Qed.
  Lemma multiplicity_psingleton_ne x y: x <> y -> multiplicity x {[+ y +]} = 0.
  Proof. intros. unfold multiplicity; simpl. by rewrite lookup_singleton_ne. Qed.
  Lemma multiplicity_nsingleton x : multiplicity x {[- x -]} = -1.
  Proof. unfold multiplicity; simpl. by rewrite lookup_singleton. Qed.
  Lemma multiplicity_nsingleton_ne x y: x <> y -> multiplicity x {[- y -]} = 0.
  Proof. intros. unfold multiplicity; simpl. by rewrite lookup_singleton_ne. Qed.
  Lemma multiplicity_singletons x n : multiplicity x {[ x := n ]} = n.
  Proof. unfold multiplicity; simpl. by rewrite lookup_singleton. Qed.
  Lemma multiplicity_singletons_ne x y n : x ≠ y → multiplicity x {[ y := n ]} = 0.
  Proof. intros. unfold multiplicity; simpl. by rewrite lookup_singleton_ne. Qed.
  Lemma multiplicity_singletons_case x y n :
    multiplicity x {[ y := n ]} = if decide (x = y) then n else 0.
  Proof.
    destruct (decide _) as [->|].
    - by rewrite multiplicity_singletons.
    - by rewrite multiplicity_singletons_ne.
  Qed.
  Lemma multiplicity_psingleton_case x y :
    multiplicity x {[+ y +]} = if decide (x = y) then 1 else 0.
  Proof.
    by rewrite psingleton_singletons, multiplicity_singletons_case.
  Qed.
  Lemma multiplicity_nsingleton_case x y :
    multiplicity x {[- y -]} = if decide (x = y) then -1 else 0.
  Proof.
    by rewrite nsingleton_singletons, multiplicity_singletons_case.
  Qed.

  Lemma multiplicity_union X Y x :
    multiplicity x (X ∪ Y) = union_aux (multiplicity x X) (multiplicity x Y).
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_union_with. destruct (X !! _), (Y !! _); simpl; try lia;
      by first [rewrite union_aux_r | rewrite union_aux_l].
  Qed.

  Lemma multiplicity_intersection X Y x :
    multiplicity x (X ∩ Y) = inter_aux (multiplicity x X) (multiplicity x Y).
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_intersection_with. destruct (X !! _), (Y !! _); simpl; try lia;
      by first [rewrite inter_aux_r | rewrite inter_aux_l].
  Qed.

  Lemma multiplicity_disj_union X Y x :
    multiplicity x (X ⊎ Y) = multiplicity x X + multiplicity x Y.
  Proof.
    destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
    rewrite lookup_union_with. destruct (X !! _), (Y !! _); simpl; lia.
  Qed.

  Lemma multiplicity_opposite X x :
    multiplicity x (opposite X) = - (multiplicity x X).
  Proof.
    destruct X as [X]; unfold multiplicity; simpl.
    rewrite lookup_fmap. destruct (X !! _); simpl; lia.
  Qed.

  Lemma multiplicity_difference X Y x :
    multiplicity x (X ∖ Y) = multiplicity x X - multiplicity x Y.
  Proof.
    now rewrite smultiset_difference, multiplicity_disj_union, multiplicity_opposite.
  Qed.

  Lemma multiplicity_positive_part X x :
    multiplicity x (positive_part X) = 0 `max` multiplicity x X.
  Proof.
    destruct X as [X].
    unfold positive_part, multiplicity. simpl.
    rewrite map_lookup_filter.
    destruct (X!!x) as [z|]; try easy. simpl.
    destruct (decide (z > 0)); simpl.
    { rewrite option_guard_True; lia. }
    { rewrite option_guard_False; lia. }
  Qed.

  Lemma multiplicity_negative_part X x :
    multiplicity x (negative_part X) = 0 `min` multiplicity x X.
  Proof.
    destruct X as [X].
    unfold negative_part, multiplicity. simpl.
    rewrite map_lookup_filter.
    destruct (X!!x) as [z|]; try easy. simpl.
    destruct (decide (z < 0)); simpl.
    { rewrite option_guard_True; lia. }
    { rewrite option_guard_False; lia. }
  Qed.

  (* Set *)
  Lemma elem_of_multiplicity x X : x ∈ X ↔ multiplicity x X <> 0.
  Proof. done. Qed.
  Lemma smultiset_elem_of_empty x : x ∈@{smultiset A} ∅ ↔ False.
  Proof. rewrite elem_of_multiplicity, multiplicity_empty. lia. Qed.
  Lemma smultiset_elem_of_singleton x y n :
    n <> 0 -> (x ∈@{smultiset A} {[ y := n ]} ↔ x = y).
  Proof.
    intros ?.
    rewrite elem_of_multiplicity, multiplicity_singletons_case.
    case_decide; try naive_solver lia.
  Qed.

  Lemma smultiset_elem_of_union X Y x : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y.
  Proof.
    rewrite !elem_of_multiplicity, multiplicity_union.
    apply union_aux_non_neg.
  Qed.

  Lemma smultiset_elem_of_disj_union X Y x :
    x ∈ X ⊎ Y -> (x ∈ X ∨ x ∈ Y).
  Proof.
    rewrite !elem_of_multiplicity, multiplicity_disj_union; lia.
  Qed.

  Lemma smultiset_elem_of_intersection X Y x : x ∈ X ∩ Y -> x ∈ X ∧ x ∈ Y.
  Proof.
    rewrite !elem_of_multiplicity, multiplicity_intersection.
    apply inter_aux_non_neg.
  Qed.

  Global Instance smultiset_elem_of_dec : RelDecision (∈@{smultiset A}).
  Proof. refine (λ x X, cast_if (decide (multiplicity x X <> 0))); done. Defined.
End basic_lemmas.

(** * A solver for multisets *)
(** We define a tactic [smultiset_solver] that solves goals involving multisets.
The strategy of this tactic is as follows:

1. Turn all equalities ([=]), equivalences ([≡]), inclusions ([⊆] and [⊂]),
   and set membership relations ([∈]) into arithmetic (in)equalities
   involving [multiplicity]. The multiplicities of [∅], [⊎] and [opposite]
   are turned into [0], [+], and [-], respectively.
2. Decompose the goal into smaller subgoals through intuitionistic reasoning.
3. Instantiate universally quantified hypotheses in hypotheses to obtain a
   goal that can be solved using [lia].
4. Simplify multiplicities of singletons [{[ x ]}].

Step (1) and (2) are implemented using the [set_solver] tactic, which internally
calls [naive_solver] for step (2). Step (1) is implemented by extending the
[SetUnfold] mechanism with a class [MultisetUnfold].

Step (3) is implemented using the tactic [multiset_instantiate], which
instantiates universally quantified hypotheses [H : ∀ x : A, P x] in two ways:

- If the goal or some hypothesis contains [multiplicity y X] it adds the
  hypothesis [H y].
- If [P] contains a multiset singleton [{[ y ]}] it adds the hypothesis [H y].
  This is needed, for example, to prove [¬ ({[ x ]} ⊆ ∅)], which is turned
  into hypothesis [H : ∀ y, multiplicity y {[ x ]} ≤ 0] and goal [False]. The
  only way to make progress is to instantiate [H] with the singleton appearing
  in [H], so variable [x].

Step (4) is implemented using the tactic [multiset_simplify_singletons], which
simplifies occurences of [multiplicity x {[ y ]}] as follows:

- First, we try to turn these occurencess into [1] or [0] if either [x = y] or
  [x ≠ y] can be proved using [done], respectively.
- Second, we try to turn these occurences into a fresh [z ≤ 1] if [y] does not
  occur elsewhere in the hypotheses or goal.
- Finally, we make a case distinction between [x = y] or [x ≠ y]. This step is
  done last so as to avoid needless exponential blow-ups.
*)
Class SmultisetUnfold `{Countable A} (x : A) (X : smultiset A) (n : Z) :=
  { smultiset_unfold : multiplicity x X = n }.
Global Arguments smultiset_unfold {_ _ _} _ _ _ {_} : assert.
Global Hint Mode SmultisetUnfold + + + - + - : typeclass_instances.

Section smultiset_unfold.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : smultiset A.

  Global Instance nsmultiset_unfold_default x X :
    SmultisetUnfold x X (multiplicity x X) | 1000.
  Proof. done. Qed.
  Global Instance smultiset_unfold_empty x : SmultisetUnfold x ∅ 0.
  Proof. constructor. by rewrite multiplicity_empty. Qed.
  Global Instance smultiset_unfold_singletons x z :
    SmultisetUnfold x {[ x := z ]} z.
  Proof. constructor. by rewrite multiplicity_singletons. Qed.
  Global Instance smultiset_unfold_singleton x :
    SmultisetUnfold x {[+ x +]} 1.
  Proof. constructor. by rewrite multiplicity_psingleton. Qed.
  Global Instance smultiset_unfold_nsingleton x :
    SmultisetUnfold x {[- x -]} (-1).
  Proof. constructor. by rewrite multiplicity_nsingleton. Qed.
  Global Instance smultiset_unfold_disj_union x X Y n m :
    SmultisetUnfold x X n → SmultisetUnfold x Y m →
    SmultisetUnfold x (X ⊎ Y) (n + m).
  Proof. intros [HX] [HY]; constructor. by rewrite multiplicity_disj_union, HX, HY. Qed.
  Global Instance smultiset_unfold_opposite x X n :
    SmultisetUnfold x X n →
    SmultisetUnfold x (opposite X) (-n).
  Proof. intros [HX]; constructor. by rewrite multiplicity_opposite, HX. Qed.
  Global Instance smultiset_unfold_difference x X Y n m :
    SmultisetUnfold x X n → SmultisetUnfold x Y m →
    SmultisetUnfold x (X ∖ Y) (n - m).
  Proof. intros [HX] [HY]; constructor. by rewrite multiplicity_difference, HX, HY. Qed.

  Global Instance smultiset_unfold_positive_part x X n :
    SmultisetUnfold x X n →
    SmultisetUnfold x (positive_part X) (0 `max` n).
  Proof. intros [HX]; constructor. by rewrite multiplicity_positive_part, HX. Qed.

  Global Instance smultiset_unfold_negative_part x X n :
    SmultisetUnfold x X n →
    SmultisetUnfold x (negative_part X) (0 `min` n).
  Proof. intros [HX]; constructor. by rewrite multiplicity_negative_part, HX. Qed.

  Global Instance set_unfold_multiset_equiv X Y f g :
    (∀ x, SmultisetUnfold x X (f x)) → (∀ x, SmultisetUnfold x Y (g x)) →
    SetUnfold (X ≡ Y) (∀ x, f x = g x) | 0.
  Proof.
    constructor. apply forall_proper; intros x.
    by rewrite (smultiset_unfold x X (f x)), (smultiset_unfold x Y (g x)).
  Qed.
  Global Instance set_unfold_multiset_subseteq X Y f g :
    (∀ x, SmultisetUnfold x X (f x)) → (∀ x, SmultisetUnfold x Y (g x)) →
    SetUnfold (X ⊆ Y) (∀ x, f x <> 0 -> g x <> 0 /\ (f x ≤ g x)) | 0.
  Proof.
    constructor. apply forall_proper; intros x.
    by rewrite (smultiset_unfold x X (f x)), (smultiset_unfold x Y (g x)).
  Qed.
  Global Instance set_unfold_multiset_subset X Y f g :
    (∀ x, SmultisetUnfold x X (f x)) → (∀ x, SmultisetUnfold x Y (g x)) →
    SetUnfold (X ⊂ Y) ((∀ x, f x <> 0 -> (g x <> 0 /\ f x ≤ g x)) ∧ (¬∀ x, g x <> 0 -> (f x <> 0 /\ g x ≤ f x))) | 0.
  Proof.
    constructor. unfold strict. f_equiv.
    - by apply set_unfold_multiset_subseteq.
    - f_equiv. by apply set_unfold_multiset_subseteq.
  Qed.

  Global Instance set_unfold_multiset_elem_of X x n :
    SmultisetUnfold x X n → SetUnfoldElemOf x X (n <> 0) | 100.
  Proof. constructor. by rewrite <-(smultiset_unfold x X n). Qed.

  Global Instance set_unfold_smultiset_empty x :
    SetUnfoldElemOf x (∅ : smultiset A) False.
  Proof. constructor. apply smultiset_elem_of_empty. Qed.
  Global Instance set_unfold_smultiset_singleton x y :
    SetUnfoldElemOf x ({[+ y +]} : smultiset A) (x = y).
  Proof. constructor; apply smultiset_elem_of_singleton. lia. Qed.
End smultiset_unfold.

(** Step 3: instantiate hypotheses *)
Ltac smultiset_instantiate :=
  repeat match goal with
  | H : (∀ x : ?A, @?P x) |- _ =>
     let e := mk_evar A in
     lazymatch constr:(P e) with
     | context [ {[+ ?y +]} ] => unify y e; learn_hyp (H y)
     end
  | H : (∀ x : ?A, _), _ : context [multiplicity ?y _] |- _ => learn_hyp (H y)
  | H : (∀ x : ?A, _) |- context [multiplicity ?y _] => learn_hyp (H y)
  end.

(** Step 4: simplify singletons *)
Local Lemma multiplicity_psingleton_forget `{Countable A} x y :
  ∃ (n:Z), multiplicity (A:=A) x {[+ y +]} = n ∧ (0 <= n) /\ (n ≤ 1).
Proof.
  rewrite psingleton_singletons, multiplicity_singletons_case.
  case_decide; eauto with lia.
Qed.

Local Lemma multiplicity_nsingleton_forget `{Countable A} x y :
  ∃ (n:Z), multiplicity (A:=A) x {[- y -]} = n ∧ (-1 ≤ n) /\ (n <= 0).
Proof.
  rewrite nsingleton_singletons, multiplicity_singletons_case.
  case_decide; eauto with lia.
Qed.


Ltac smultiset_simplify_singletons :=
  repeat match goal with
  | H : context [multiplicity ?x {[+ ?y +]}] |- _ =>
     first
       [progress rewrite ?multiplicity_psingleton, ?multiplicity_psingleton_ne in H by done
       |destruct (multiplicity_psingleton_forget x y) as (?&->&?); clear y
       |rewrite multiplicity_psingleton_case in H; destruct (decide (x = y)); simplify_eq/=]
  | H : context [multiplicity ?x {[- ?y -]}] |- _ =>
      first
        [progress rewrite ?multiplicity_nsingleton, ?multiplicity_nsingleton_ne in H by done
        |destruct (multiplicity_nsingleton_forget x y) as (?&->&?); clear y
        |rewrite multiplicity_nsingleton_case in H; destruct (decide (x = y)); simplify_eq/=]
  | |- context [multiplicity ?x {[+ ?y +]}] =>
     first
       [progress rewrite ?multiplicity_psingleton, ?multiplicity_psingleton_ne by done
       |destruct (multiplicity_psingleton_forget x y) as (?&->&?); clear y
       |rewrite multiplicity_psingleton_case; destruct (decide (x = y)); simplify_eq/=]
  | |- context [multiplicity ?x {[- ?y -]}] =>
     first
       [progress rewrite ?multiplicity_nsingleton, ?multiplicity_nsingleton_ne by done
       |destruct (multiplicity_nsingleton_forget x y) as (?&->&?); clear y
       |rewrite multiplicity_nsingleton_case; destruct (decide (x = y)); simplify_eq/=]
  | |- context [multiplicity ?x {[ ?y := ?z ]}] =>
     first
       [progress rewrite ?multiplicity_singletons, ?multiplicity_singletons_ne by done
       |rewrite multiplicity_singletons_case; destruct (decide (x = y)); simplify_eq/=]
  | |- context [multiplicity ?x {[ ?y := ?z ]}] =>
     first
       [progress rewrite ?multiplicity_singletons, ?multiplicity_singletons_ne by done
       |rewrite multiplicity_singletons_case; destruct (decide (x = y)); simplify_eq/=]
  end.

(** Putting it all together *)
Ltac smultiset_solver :=
  set_solver by (smultiset_instantiate; smultiset_simplify_singletons; lia).

Section more_lemmas.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : smultiset A.

  Lemma singleton_empty x :
    {[ x := 0 ]} ≡ (∅ : smultiset A).
  Proof. smultiset_solver. Qed.

  (** For disjoint union (aka sum) *)
  Global Instance smultiset_disj_union_comm : Comm (≡@{smultiset A}) (⊎).
  Proof. unfold Comm. smultiset_solver. Qed.
  Global Instance smultiset_disj_union_assoc : Assoc (≡@{smultiset A}) (⊎).
  Proof. unfold Assoc. smultiset_solver. Qed.
  Global Instance smultiset_disj_union_left_id : LeftId (≡@{smultiset A}) ∅ (⊎).
  Proof. unfold LeftId. smultiset_solver. Qed.
  Global Instance smultiset_disj_union_right_id : RightId (≡@{smultiset A}) ∅ (⊎).
  Proof. unfold RightId. smultiset_solver. Qed.

  Global Instance smultiset_disj_union_proper : Proper ((≡) ==> (≡) ==> (≡@{smultiset A})) (⊎).
  Proof.
    intros ? ? I1 ? ? I2 ?.
    repeat rewrite multiplicity_disj_union.
    now rewrite I1, I2.
  Qed.

  Global Instance smultiset_disj_union_inj_1 X : Inj (≡) (≡) (X ⊎.).
  Proof. unfold Inj. smultiset_solver. Qed.

  Global Instance smultiset_disj_union_inj_2 X : Inj (≡) (≡) (.⊎ X).
  Proof. unfold Inj. smultiset_solver. Qed.

  (** For opposite *)
  Global Instance smultiset_opposite_proper : Proper ((≡) ==> (≡@{smultiset A})) opposite.
  Proof. intros ? ?. smultiset_solver. Qed.

  Lemma opposite_disj_union (X Y:smultiset A) :
    opposite (X ⊎ Y) ≡ opposite X ⊎ opposite Y.
  Proof. smultiset_solver. Qed.
  Lemma opposite_opposite (X:smultiset A) :
    opposite (opposite X) ≡ X.
  Proof. smultiset_solver. Qed.

  (** Empty *)
  Lemma disj_union_idemp_inv_l X Y :
    X ⊎ Y ≡ X ->
    Y ≡ ∅.
  Proof.
    intros HE k.
    specialize (HE k).
    rewrite multiplicity_disj_union in HE.
    rewrite multiplicity_empty. lia.
  Qed.

  (** Opposite *)
  Lemma opposite_cancel X : X ⊎ opposite X ≡ ∅.
  Proof. smultiset_solver. Qed.

  (** Element of operation *)
  Lemma smultiset_not_elem_of_empty x : x ∉@{smultiset A} ∅.
  Proof. easy. Qed.
  Lemma smultiset_not_elem_of_singleton x y : x ∉@{smultiset A} {[+ y +]} ↔ x ≠ y.
  Proof. smultiset_solver. Qed.

  Lemma elem_of_disj_union (X Y:smultiset A) x :
    x ∈ (X ⊎ Y) ->
    x ∈ X \/ x ∈ Y.
  Proof. smultiset_solver. Qed.

  Global Instance elem_of_proper x : Proper (equiv ==> iff) (@elem_of A (smultiset A) _ x).
  Proof. intros ??. smultiset_solver. Qed.

  (** Order stuff *)
  Global Instance smultiset_pro : PreOrder (⊆@{smultiset A}).
  Proof.
    split; intros ? ?; try lia.
    smultiset_solver.
  Qed.

  Global Instance smultiset_incl_proper : Proper ((≡) ==> (≡) ==> iff) (⊆@{smultiset A}).
  Proof.
    intros ? ? I1 ? ? I2.
    split; intros E ?.
    - rewrite <- I1, <- I2; apply E.
    - rewrite I1, I2; apply E.
  Qed.

  Lemma smultiset_empty_subseteq X : ∅ ⊆ X.
  Proof. smultiset_solver. Qed.

  Lemma smultiset_elem_of_dom (X:smultiset A) (i:A) :
    i ∈ dom X <-> (multiplicity i X <> 0).
  Proof.
    unfold dom, smultiset_dom in *.
    unfold multiplicity.
    destruct X as [X]; simpl in *.
    split; intros Hi.
    { apply elem_of_dom in Hi.
      destruct Hi as (?,Hi).
      apply map_lookup_filter_Some in Hi.
      by destruct Hi as (->&?). }
    { apply elem_of_dom.
      destruct (X!!i) as [Xi|] eqn:E; simpl in *; try lia.
      exists Xi. by apply map_lookup_filter_Some. }
  Qed.

  Global Instance dom_proper : Proper ((≡) ==> eq) (@dom (smultiset A) _ smultiset_dom).
  Proof.
    intros ? ? E.
    apply leibniz_equiv. intros ?.
    rewrite !smultiset_elem_of_dom.
    rewrite E. easy.
  Qed.

  Definition delete (l:A) (X:smultiset A) := X ⊎ ({[l := - multiplicity l X]}).

  Lemma multiplicity_delete l X i :
    multiplicity i (delete l X) =
      if (decide (i=l)) then 0 else multiplicity i X.
  Proof.
    unfold delete.
    rewrite multiplicity_disj_union.
    rewrite multiplicity_singletons_case.
    case_decide; subst; lia.
  Qed.

  Lemma dom_delete l X : dom (delete l X) = dom X ∖ {[l]}.
  Proof.
    apply leibniz_equiv. intros e.
    rewrite smultiset_elem_of_dom.
    rewrite multiplicity_delete.
    case_decide; only 1: set_solver.
    rewrite <- smultiset_elem_of_dom.
    set_solver.
  Qed.

  Lemma subseteq_dom (X Y:smultiset A) :
    X ⊆ Y ->
    dom X ⊆ dom Y.
  Proof.
    intros Hincl. intros i Hi.
    specialize (Hincl i).
    apply smultiset_elem_of_dom in Hi.
    apply smultiset_elem_of_dom.
    lia.
  Qed.

  Lemma dom_empty :
    dom (∅ : smultiset A) = ∅.
  Proof. smultiset_solver. Qed.

  Lemma dom_empty_inv X :
    dom X = ∅ ->
    X ≡ ∅.
  Proof.
    intros ? i.
    destruct_decide (decide (multiplicity i X = 0)) as E.
    { smultiset_solver. }
    { apply smultiset_elem_of_dom in E. set_solver. }
  Qed.

  Lemma dom_disj_union (X Y:smultiset A) :
    dom (X ⊎ Y) ⊆ dom X ∪ dom Y.
  Proof.
    intros e. rewrite elem_of_union.
    rewrite !smultiset_elem_of_dom.
    rewrite multiplicity_disj_union. lia.
  Qed.

  Lemma dom_singletons (l:A) (n:Z) :
    n≠0 ->
    dom ( ({[l:=n]}) : smultiset A) = {[l]}.
  Proof.
    intros ?.
    apply leibniz_equiv. intros e.
    rewrite smultiset_elem_of_dom.
    destruct (decide (l=e)); subst; try smultiset_solver.
    rewrite multiplicity_singletons. set_solver.
  Qed.

  Lemma dom_psingleton (l:A) :
    dom ( ({[+l+]}) : smultiset A)  = {[l]}.
  Proof. rewrite psingleton_singletons, dom_singletons; easy. Qed.

  Lemma dom_nsingleton (l:A) :
    dom ( ({[-l-]}) : smultiset A)  = {[l]}.
  Proof. rewrite nsingleton_singletons, dom_singletons; easy. Qed.

  Lemma subseteq_elem_of (X Y:smultiset A) :
    X ⊆ Y ->
    forall i, i ∈ X -> i ∈ Y.
  Proof. smultiset_solver. Qed.

  Lemma opposite_singleton (l:A) :
    opposite {[+l+]} ≡@{smultiset A} {[-l-]}.
  Proof. smultiset_solver. Qed.

  Lemma disj_union_singleton_opposite l :
    {[+l+]} ⊎ {[-l-]} ≡ (∅ : smultiset A).
  Proof. smultiset_solver. Qed.

  Lemma smultiset_decompose X :
    X ≡ positive_part X ⊎ negative_part X.
  Proof. smultiset_solver. Qed.

  Global Instance positive_part_proper : Proper (equiv ==> equiv) (@positive_part A _ _).
  Proof. intros ??. smultiset_solver. Qed.

  Global Instance negative_part_proper : Proper (equiv ==> equiv) (@negative_part A _ _).
  Proof. intros ??. smultiset_solver. Qed.

  Lemma elem_of_negative_part_disj_union (X Y:smultiset A) (x:A) :
    x ∈ negative_part (X ⊎ Y) ->
    x ∈ negative_part X \/ x ∈ negative_part Y.
  Proof. smultiset_solver. Qed.

  Lemma elem_of_negative_part_weak (X:smultiset A) x :
    x ∈ negative_part X ->
    x ∈ X.
  Proof. smultiset_solver. Qed.

  Lemma elem_of_opposite (X:smultiset A) x :
    x ∈ opposite X <-> x ∈ X.
  Proof. smultiset_solver. Qed.
End more_lemmas.

Section PosNeg.
  Context `{Countable A}.
  Implicit Type X Y Z : smultiset A.

  (** All-positive Signed Multiset *)
  Definition AllPos (X:smultiset A) : Prop := forall x, (0 <= multiplicity x X).

  Global Instance set_unfold_AllPos X f :
    (∀ x, SmultisetUnfold x X (f x)) →
    SetUnfold (AllPos X) (∀ x, 0 <= f x).
  Proof.
    intros. constructor. split.
    { intros ? x. rewrite <- (smultiset_unfold x X (f x)). eauto. }
    { intros ? x. rewrite (smultiset_unfold x X (f x)). eauto. }
  Qed.

  Global Instance AllPos_proper : Proper (equiv ==> iff) AllPos.
  Proof.
    intros X Y E. smultiset_solver.
  Qed.

  Lemma AllPos_empty : AllPos (∅:smultiset A).
  Proof. smultiset_solver. Qed.

  Lemma AllPos_disj_union X Y :
    AllPos X -> AllPos Y -> AllPos (X ⊎ Y).
  Proof. smultiset_solver. Qed.

  Lemma negative_part_of_positive (X:smultiset A) :
    AllPos X ->
    negative_part X ≡ ∅.
  Proof. smultiset_solver. Qed.

  (** All-negative Signed Multiset *)
  Definition AllNeg (X:smultiset A) : Prop := forall x, (multiplicity x X <= 0).

  Global Instance set_unfold_AllNeg X f :
    (∀ x, SmultisetUnfold x X (f x)) →
    SetUnfold (AllNeg X) (∀ x, f x <= 0).
  Proof.
    intros. constructor. split.
    { intros ? x. rewrite <- (smultiset_unfold x X (f x)). eauto. }
    { intros ? x. rewrite (smultiset_unfold x X (f x)). eauto. }
  Qed.

  Global Instance AllNeg_proper : Proper (equiv ==> iff) AllNeg.
  Proof. intros ? ? ?. smultiset_solver. Qed.

  Lemma AllNeg_empty : AllNeg (∅:smultiset A).
  Proof. smultiset_solver. Qed.

  Lemma AllNeg_nsingleton l : AllNeg {[-l-]}.
  Proof. smultiset_solver. Qed.

  Lemma AllNeg_disj_union X Y :
    AllNeg X -> AllNeg Y -> AllNeg (X ⊎ Y).
  Proof. smultiset_solver. Qed.

  Lemma AllNeg_delete l X :
    AllNeg X -> AllNeg (delete l X).
  Proof. smultiset_solver. Qed.

  Lemma negative_part_AllNeg X :
  AllNeg X ->
  negative_part X ≡ X.
  Proof. smultiset_solver. Qed.

  Lemma oppositeAllPos X :
    AllPos X -> AllNeg (opposite X).
  Proof. smultiset_solver. Qed.

  Lemma AllNegIncl X Y :
    AllPos (X ⊎ Y) ->
    AllNeg Y ->
    X ⊎ Y ⊆ X.
  Proof. smultiset_solver. Qed.

  Lemma AllPos_mono X Y Z:
    X ≡ Y ⊎ Z ->
    AllPos X ->
    AllNeg Z ->
    AllPos Y.
  Proof. smultiset_solver. Qed.

  Lemma AllNeg_disj_union_empty X Y :
    AllNeg X ->
    AllNeg Y ->
    X ⊎ Y ≡ ∅ <-> (X ≡ ∅ /\ Y ≡ ∅).
  Proof. smultiset_solver. Qed.

End PosNeg.

Section Gmultiset.
  Context `{Countable A}.

  Definition of_gmultiset (M:gmultiset.gmultiset A) : smultiset A :=
    let (M) := M in
    Smultiset (fmap (fun (p:positive) => Zpos p) M).

  Lemma multiplicity_of_gmultiset x (M:gmultiset.gmultiset A) :
    multiplicity x (of_gmultiset M) = Z.of_nat (gmultiset.multiplicity x M).
  Proof.
    unfold of_gmultiset,multiplicity,gmultiset.multiplicity.
    destruct M as [M]. simpl.
    rewrite lookup_fmap.
    destruct (M !! x); simpl; lia.
  Qed.

  Global Instance smultiset_unfold_of_gmultiset x X n :
    gmultiset.MultisetUnfold x X n →
    SmultisetUnfold x (of_gmultiset X) (Z.of_nat n).
  Proof. intros []. constructor. rewrite multiplicity_of_gmultiset. by f_equal. Qed.

  Lemma AllPos_of_gmultiset  (M:gmultiset.gmultiset A) :
    AllPos (of_gmultiset M).
  Proof. smultiset_solver. Qed.

  Lemma of_gmultiset_empty :
    of_gmultiset (∅ : gmultiset.gmultiset A) ≡ (∅ : smultiset A).
  Proof. smultiset_solver. Qed.

  Lemma of_gmultiset_singleton (x:A) :
    of_gmultiset {[+ x +]} ≡ {[+ x +]}.
  Proof.
    intros y.
    rewrite multiplicity_of_gmultiset.
    destruct (decide (y=x)); subst.
    { rewrite gmultiset.multiplicity_singleton. smultiset_solver. }
    { rewrite gmultiset.multiplicity_singleton_ne; try easy.
      smultiset_solver. }
  Qed.

  Lemma of_gmultiset_disj_union (M N: gmultiset.gmultiset A) :
    of_gmultiset (M ⊎ N) ≡ of_gmultiset M ⊎ of_gmultiset N.
  Proof. smultiset_solver. Qed.

  Definition to_gmultiset (M:smultiset A) : gmultiset.gmultiset A :=
    let (M) := M in
    gmultiset.GMultiSet (omap (fun n => if decide (n <= 0) then None else Some (Pos.of_nat (Z.to_nat n))%nat) M).

  Lemma multiplicity_to_gmultiset x (M:smultiset A) :
    gmultiset.multiplicity x (to_gmultiset M) = Z.to_nat (multiplicity x M).
  Proof.
    unfold of_gmultiset,multiplicity,gmultiset.multiplicity.
    destruct M as [M]. simpl.
    rewrite lookup_omap.
    destruct (M !! x); simpl; try easy.
    destruct (decide (z ≤ 0)); lia.
  Qed.

  Global Instance smultiset_unfold_to_gmultiset x X n :
    SmultisetUnfold x X n ->
    gmultiset.MultisetUnfold x (to_gmultiset X) (Z.to_nat n).
  Proof. intros []. constructor. rewrite multiplicity_to_gmultiset. by f_equal. Qed.

  Lemma to_gmultiset_empty : to_gmultiset (∅:smultiset A) = ∅.
  Proof. compute_done. Qed.

  Lemma of_to_equiv ps ls :
    of_gmultiset ps ≡ ls -> ps ≡ to_gmultiset ls.
  Proof.
    intros E x.
    specialize (E x).
    rewrite multiplicity_to_gmultiset.
    rewrite multiplicity_of_gmultiset in E.
    lia.
  Qed.

  Definition of_gmultiset_neg (M:gmultiset.gmultiset A) : smultiset A :=
    opposite (of_gmultiset M).

  Lemma multiplicity_of_gmultiset_neg x (M:gmultiset.gmultiset A) :
    multiplicity x (of_gmultiset_neg M) = (- Z.of_nat (gmultiset.multiplicity x M)).
  Proof.
    unfold of_gmultiset_neg.
    by rewrite multiplicity_opposite, multiplicity_of_gmultiset.
  Qed.

  Global Instance smultiset_unfold_of_gmultiset_neg x X n :
    gmultiset.MultisetUnfold x X n →
    SmultisetUnfold x (of_gmultiset_neg X) (- Z.of_nat n).
  Proof. intros []. constructor. rewrite multiplicity_of_gmultiset_neg. subst. by f_equal. Qed.

  Lemma AllNeg_of_gmultiset_neg (M:gmultiset.gmultiset A) : AllNeg (of_gmultiset_neg M).
  Proof. smultiset_solver. Qed.

  Lemma AllPos_of_to X :
    AllPos X ->
    of_gmultiset (to_gmultiset X) ≡ X.
  Proof. smultiset_solver. Qed.

  Lemma of_gmultiset_difference X Y:
    Y ⊆ X ->
    of_gmultiset (X ∖ Y) ≡ of_gmultiset X ⊎ of_gmultiset_neg Y.
  Proof.
    intros Hincl i.
    rewrite multiplicity_of_gmultiset.
    rewrite gmultiset.multiplicity_difference.
    specialize (Hincl i).
    rewrite multiplicity_disj_union.
    rewrite multiplicity_of_gmultiset.
    rewrite multiplicity_of_gmultiset_neg.
    lia.
  Qed.

  Lemma of_gmultiset_neg_singleton l :
    of_gmultiset_neg {[+ l +]} ≡ {[- l -]}.
  Proof.
    intros l'.
    rewrite multiplicity_of_gmultiset_neg.
    destruct (decide (l' = l)); subst.
    { rewrite multiplicity_nsingleton. rewrite gmultiset.multiplicity_singleton. lia. }
    { rewrite multiplicity_nsingleton_ne; try easy.
      rewrite gmultiset.multiplicity_singleton_ne; try done. }
  Qed.

  Lemma dom_to_gmultiset (X:smultiset A) :
    dom (to_gmultiset X) ⊆ dom X.
  Proof.
    destruct X as [X].
    induction X as [] using map_ind; simpl in *.
    { rewrite omap_empty, map_filter_empty.
      by do 2 rewrite dom_empty_L. }
    { rewrite omap_insert, map_filter_insert.
      destruct (decide (x <= 0)); simpl.
      { destruct (decide (x=0)).
        { rewrite decide_False; try lia.
          rewrite map_filter_delete.
          do 2 rewrite dom_delete_L.
          set_solver. }
        { rewrite decide_True; try lia.
          rewrite dom_delete_L, dom_insert_L.
          set_solver. } }
      { rewrite decide_True; try lia.
        do 2 rewrite dom_insert_L.
        set_solver. } }
  Qed.

End Gmultiset.
