From Coq Require Import ssreflect.
From stdpp Require Import base option relations.

Section temporal.
Context {A:Type} (step:A -> A -> Prop).

(* ------------------------------------------------------------------------ *)
(* [Always] *)

Definition Always ρ (P:A -> Prop) :=
  forall ρ', rtc step ρ ρ' -> P ρ'.

Lemma always_middle ρ ρ' P :
  rtc step ρ ρ' ->
  Always ρ  P ->
  Always ρ' P.
Proof.
  intros Hrtc Hal. intros ??. apply Hal.
  by etrans.
Qed.

Lemma always_mono ρ (P P':A -> Prop) :
  (forall ρ', P ρ' -> P' ρ') ->
  Always ρ P ->
  Always ρ P'.
Proof.
  intros ????. eauto.
Qed.

(* ------------------------------------------------------------------------ *)
(* [AfterAtMost]. The standard temporal logic definition, asserting that there
   always exists a successor *)

Inductive AfterAtMost (P:A -> Prop) : nat -> A -> Prop :=
| HoldsNow : forall n X,
    P X ->
    AfterAtMost P n X
| HoldsAfter : forall n X,
    (exists X', step X X') ->
    (forall X', step X X' -> AfterAtMost P n X') ->
    AfterAtMost P (S n) X
.

Lemma after_at_most_le n1 n2 (P:A -> Prop) X :
  n1 <= n2 ->
  AfterAtMost P n1 X ->
  AfterAtMost P n2 X.
Proof.
  intros Hn He. revert n2 Hn.
  induction He; intros n2 Hn; eauto using HoldsNow.
  destruct n2; first lia.
  apply HoldsAfter; eauto.
  naive_solver lia.
Qed.

Lemma after_at_most_mono n (P1 P2:A -> Prop) X :
  (forall x, P1 x -> P2 x) ->
  AfterAtMost P1 n X ->
  AfterAtMost P2 n X.
Proof.
  intros ?. induction 1; eauto using HoldsNow,HoldsAfter.
Qed.

Definition Eventually (P:A -> Prop) (X:A) : Prop :=
  ∃ n, AfterAtMost P n X.


Lemma eventually_mono (P1 P2:A -> Prop) X :
  (forall x, P1 x -> P2 x) ->
  Eventually P1 X ->
  Eventually P2 X.
Proof.
  intros ? (?&?). unfold Eventually. eauto using after_at_most_mono.
Qed.

(* ------------------------------------------------------------------------ *)
(* [AfterAtMostWeak]. It is "weak" in the sense that the recursive case does not
   assert the existence of a step. *)

Inductive AfterAtMostWeak (P:A -> Prop) : nat -> A -> Prop :=
| HoldsWNow : forall n X,
    P X ->
    AfterAtMostWeak P n X
| HoldsWLater : forall n X,
    (forall X', step X X' -> AfterAtMostWeak P n X') ->
    AfterAtMostWeak P (S n) X
.

Lemma after_at_most_weak_le n1 n2 (P:A -> Prop) X :
  n1 <= n2 ->
  AfterAtMostWeak P n1 X ->
  AfterAtMostWeak P n2 X.
Proof.
  intros Hn He. revert n2 Hn.
  induction He; intros n2 Hn; eauto using HoldsWNow.
  destruct n2; first lia.
  apply HoldsWLater; eauto.
  naive_solver lia.
Qed.

Definition EventuallyWeak (P:A -> Prop) (X:A) : Prop :=
  ∃ n, AfterAtMostWeak P n X.
End temporal.
