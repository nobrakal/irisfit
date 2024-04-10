From stdpp Require Import gmap.

(** This file defines a simple fixed point construction for functions on
    finite sets [gset]s, as long as the function is extensive ([X ⊆ f X]) and
    preserves a bound. We use it do define the reachability set, in order to
    show that reachability is decidable. *)

Lemma subset_size_eq `{Countable L} (X Y : gset L) : X ⊆ Y -> size Y <= size X -> X = Y.
Proof.
  intros Hl Heq.
  rewrite (union_difference_L X Y Hl).
  cut (Y ∖ X ≡ ∅); [ set_solver | ].
  apply size_empty_inv.
  pose proof size_union_alt X Y as Hunion.
  destruct (subseteq_union_L X Y) as [e _].
  rewrite (e Hl) in Hunion.
  lia.
Qed.

Section gset_fixpoint.

  (* It is tempting to generalize the construction by adding the exact
     hypotheses ([FinSet L, SubsetEq L, Size L,] etc.) in the [Context]
     instead of using the direct implementation [gset], but then we would need
     to declare many section variables in each [Proof using] *)

  Context `{Countable L}.

  (* [f] is the function being iterated, [X0] is the starting set, [B] is the
     bound for [X0] and [f] *)

  Variable f : gset L -> gset L.
  Variable X0 : gset L.
  Variable B : gset L.

  Variable f_extensive : forall X, X ⊆ f X.
  Variable X0_bounded : X0 ⊆ B.
  Variable f_bounded : forall X, X ⊆ B -> f X ⊆ B.

  (** [1 + size B] iterations of [f] are enough to reach [f]'s fixed point *)

  Fixpoint gset_iter (n : nat) : gset L :=
    match n with
    | O => X0
    | S n => f (gset_iter n)
    end.

  Definition gset_fixpoint := gset_iter (1 + size B).

  Lemma gset_iter_bounded n : gset_iter n ⊆ B.
  Proof using X0_bounded f_bounded.
    induction n; intuition; simpl; now apply f_bounded.
  Qed.

  Lemma gset_fixpoint_init : X0 ⊆ gset_fixpoint.
  Proof using f_extensive.
    unfold gset_fixpoint; induction (1 + _); auto. etransitivity; eauto.
  Qed.

  (* If the size does not increase, we have reached stability *)

  Lemma gset_iter_increment n :
    size (gset_iter (1 + n)) <= size (gset_iter n)
    <-> gset_iter n = gset_iter (1 + n).
  Proof using f_extensive.
    split; [ | now intros <- ].
    apply subset_size_eq, f_extensive.
  Qed.

  (* Hence, if the size increases, it must have increases at all the previous
     steps *)

  Lemma gset_iter_size' n :
    size (gset_iter n) < size (gset_iter (1 + n)) ->
    forall i, i <= n -> size (gset_iter i) < size (gset_iter (1 + i)).
  Proof using f_extensive.
    intros D i Hi.
    rewrite <-Nat.nle_gt, gset_iter_increment in *.
    intros E. apply D. clear D.
    replace n with ((n - i) + i) by lia.
    induction (n - i) as [ | j IHj]; auto.
    simpl.
    now rewrite IHj at 1.
  Qed.

  (* Therefore, the size after [n] iterations is at least [n], if the current
     iteration increased the size *)

  Lemma gset_iter_size n :
    size (gset_iter n) < size (gset_iter (1 + n)) ->
    size (gset_iter n) >= n.
  Proof using f_extensive.
    intros Hn.
    pose proof gset_iter_size' _ Hn as Hi. clear Hn.
    induction n; try lia.
    apply Nat.le_trans with (1 + size (gset_iter n)).
    - apply le_n_S, IHn. intros i ?; apply Hi; lia.
    - apply Hi; lia.
  Qed.

  (* This cannot go on more than [1 + size B] times, so we have stability from
     there on *)

  Lemma gset_fixpoint_limit : f gset_fixpoint = gset_fixpoint.
  Proof using f_bounded f_extensive X0_bounded.
    symmetry; apply subset_size_eq; eauto.
    apply Nat.nlt_ge; intros Hl.
    apply gset_iter_size in Hl.
    pose proof gset_iter_bounded (1 + size B) as I.
    apply subseteq_size in I.
    lia.
  Qed.

  (* The fixed point is equal to all subsequent iterations *)

  Lemma gset_fixpoint_after n : 1 + size B <= n -> gset_iter n = gset_fixpoint.
  Proof using f_bounded f_extensive X0_bounded.
    intros Hl.
    replace n with (n - (1 + size B) + 1 + size B) by lia.
    induction (n - _) as [ | i IHi]; auto.
    simpl. rewrite IHi. apply gset_fixpoint_limit.
  Qed.

  (* The fixed point is above all iterations *)

  Lemma gset_fixpoint_before n : n <= 1 + size B -> gset_iter n ⊆ gset_fixpoint.
  Proof using f_bounded f_extensive X0_bounded.
    unfold gset_fixpoint.
    induction (1 + size B) as [ | i IHi ]; intros Hi.
    - inversion Hi; auto.
    - assert (n = S i \/ n <= i) as [-> | Hl] by lia; auto.
      transitivity (gset_iter i); auto.
  Qed.

  Lemma gset_fixpoint_upper n : gset_iter n ⊆ gset_fixpoint.
  Proof using f_bounded f_extensive X0_bounded.
    assert (n <= 1 + size B \/ 1 + size B <= n) as [ | ] by lia.
    - now apply gset_fixpoint_before.
    - now rewrite gset_fixpoint_after.
  Qed.

  (* An inductive principle for the fixed point: a property true on the
     starting set and stable by [f] is true on all [gset_fixpoint] *)

  Lemma gset_fixpoint_ind (P : L -> Prop) :
    (forall x, x ∈ X0 -> P x) ->
    (forall X, (forall x, x ∈ X -> P x) -> (forall x, x ∈ f X -> P x)) ->
    (forall x, x ∈ gset_fixpoint -> P x).
  Proof using f_bounded f_extensive X0_bounded.
    intros H0 IH. unfold gset_fixpoint.
    induction (1 + _); intros x; auto.
    simpl; apply IH; auto.
  Qed.

End gset_fixpoint.
