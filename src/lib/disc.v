From stdpp Require Import countable.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes csum agree local_updates.
From iris.prelude Require Import options.

Definition discR A B := csumR A (agreeR B).

Section disc.
  Context {A B:cmra}.
  Implicit Type a:A.
  Implicit Type b:B.

  Definition live (a:A) : discR A B := Cinl a.
  Definition discarded (b:B) : discR A B := Cinr (to_agree b).

  Lemma disc_cmra_mixin : CmraMixin (discR A B).
  Proof. apply csum_cmra_mixin. Qed.

  Lemma live_valid a : ✓ (live a) <-> ✓a.
  Proof. rewrite Cinl_valid //. Qed.

  Lemma live_valid_op_inv a (c:discR A B) : ✓(live a ⋅ c) -> exists a', c = live a'.
  Proof. destruct c; intros?; try naive_solver. all:exfalso; naive_solver. Qed.

  Lemma discarded_valid b : ✓ (discarded b).
  Proof. rewrite Cinr_valid. rewrite -(agree_idemp (to_agree b)).
         rewrite to_agree_op_valid //. Qed.

  Lemma live_op a a' : live (a ⋅ a') = live a ⋅ live a'.
  Proof. rewrite -Cinl_op //. Qed.

  Lemma live_included a a' : live a ≼ live a' ↔ a ≼ a'.
  Proof. apply Cinl_included. Qed.

  Lemma discarded_included b b' : discarded b ≼ discarded b' ↔ b ≡ b'.
  Proof. rewrite Cinr_included to_agree_included //. Qed.

  Global Instance live_discrete a : Discrete a -> Discrete (live a).
  Proof.  apply _. Qed.
  Global Instance discarded_discrete b : Discrete b -> Discrete (discarded b).
  Proof.  apply _. Qed.

  Global Instance discarded_core_id b : CoreId (discarded b).
  Proof. apply Cinr_core_id. apply _. Qed.

  Lemma live_local_update (a1 a2 a1' a2' : A) :
    (a1,a2) ~l~> (a1',a2') → (live a1,live a2) ~l~> (live a1',live a2').
  Proof. apply csum_local_update_l. Qed.

  Lemma live_discard `{!Exclusive a2} a1 b :
    (live a1,live a2) ~l~> (discarded b, discarded b).
  Proof. apply exclusive_local_update. apply discarded_valid. Qed.
End disc.
