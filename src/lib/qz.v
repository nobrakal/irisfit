(* Fractions with zero *)

From Coq Require Export EqdepFacts PArith NArith ZArith.
From Coq Require Import QArith Qcanon.
From stdpp Require Export base decidable countable option numbers.

Declare Scope Qz_scope.
Delimit Scope Qz_scope with Qz.

(* A small work around to avoid ProofIrrelevance *)
(* Indeed, we need a proof irrelevant x <= y, to have Qz_to_Qc_inj_iff *)
Definition qcile (x y : Qc) :=
  if decide (x <= y)%Qc then true else false.

Lemma qcile_corr x y : qcile x y <-> (x <= y)%Qc.
Proof.
  unfold qcile.
  split; intros E;
    by destruct (decide (x<=y)%Qc).
Qed.

Lemma qcile_corr' x y : qcile x y -> (x <= y)%Qc.
Proof. apply qcile_corr. Qed.

Ltac qdestruct x :=
  let pi := fresh "qcile" in
  destruct x as [x pi];
  pose proof (qcile_corr' 0%Qc x pi).

(* The actual formalization *)

Record Qz := mk_Qz { Qz_to_Qc : Qc ; Qz_prf : (qcile 0 Qz_to_Qc)%Qc }.
Add Printing Constructor Qz.
Bind Scope Qz_scope with Qz.
Global Arguments Qz_to_Qc _%Qz : assert.

Program Definition Qp_to_Qz (x:Qp) :=
  mk_Qz (Qp_to_Qc x) _.
Next Obligation.
  destruct x; try easy.
  apply qcile_corr.
  eauto using Qclt_le_weak.
Qed.

Coercion Qp_to_Qz : Qp >-> Qz.

Local Open Scope Qz_scope.

Lemma Qz_to_Qc_inj_iff p q : Qz_to_Qc p = Qz_to_Qc q ↔ p = q.
Proof.
  split; [|by intros ->].
  destruct p, q; intros; simplify_eq/=.
  f_equal. eapply proof_irrel.
Qed.

Global Instance Qz_eq_dec : EqDecision Qz.
Proof.
  refine (λ p q, cast_if (decide (Qz_to_Qc p = Qz_to_Qc q)));
    by rewrite <-Qz_to_Qc_inj_iff.
Defined.
Global Program Instance Qz_countable : Countable Qz :=
  inj_countable
    Qz_to_Qc
    (λ p : Qc, guard (qcile 0 p) as Hp; Some (mk_Qz p Hp)) _.
Next Obligation.
  intros [p Hp]. unfold mguard, option_guard; simpl.
  case_match; [|done]. f_equal. by apply Qz_to_Qc_inj_iff.
Qed.

Program Definition Qz_add (p q : Qz) : Qz :=
  let 'mk_Qz p Hp := p in let 'mk_Qz q Hq := q in
  mk_Qz (p + q) _.
Next Obligation.
  intros. apply qcile_corr, Qcplus_nonneg_nonneg; by apply qcile_corr.
Qed.
Global Arguments Qz_add : simpl never.

Program Definition nat_to_Qz (n : nat) : Qz := mk_Qz (Qc_of_Z $ Z.of_nat n) _.
Next Obligation. intros n. apply qcile_corr. rewrite <-Z2Qc_inj_0, <-Z2Qc_inj_le. lia. Qed.
Global Arguments nat_to_Qz : simpl never.
Coercion nat_to_Qz : nat >-> Qz.

Program Definition Qz_sub (p q : Qz) : Qz :=
  let 'mk_Qz p Hp := p in let 'mk_Qz q Hq := q in
  let pq := (p - q)%Qc in
  if (decide (0 <= pq)%Qc)
  then mk_Qz pq _ else 0.
Next Obligation.
  intros. by apply qcile_corr.
Qed.
Global Arguments Qz_sub : simpl never.

Program Definition Qz_mul (p q : Qz) : Qz :=
  let 'mk_Qz p Hp := p in let 'mk_Qz q Hq := q in
  mk_Qz (p * q) _.
Next Obligation.
  intros. apply qcile_corr, Qcmult_nonneg_nonneg; by apply qcile_corr.
Qed.
Global Arguments Qz_mul : simpl never.

Definition Qz_div (p : Qz) (q : Qp) : Qz := Qz_mul p (Qp_to_Qz (Qp.inv q)).
#[export] Typeclasses Opaque Qz_div.
Global Arguments Qz_div : simpl never.

Infix "+" := Qz_add : Qz_scope.
Infix "-" := Qz_sub : Qz_scope.
Infix "*" := Qz_mul : Qz_scope.
Notation "/ q" := (Qp_to_Qz (/ q)%Qp) : Qz_scope.
Infix "/" := Qz_div : Qz_scope.

Lemma Qp_to_Qz_mul_distr (p q:Qp) : Qp_to_Qz (p * q)%Qp = p * q.
Proof. destruct p,q. now apply Qz_to_Qc_inj_iff.
Qed.

Lemma Qp_to_Qz_plus_distr (p q:Qp) : Qp_to_Qz (p + q)%Qp = p + q.
Proof.
  destruct p,q.
  now apply Qz_to_Qc_inj_iff.
Qed.

Lemma Qz_to_Qc_inj_add p q : (Qz_to_Qc (p + q) = Qz_to_Qc p + Qz_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.
Lemma Qz_to_Qc_inj_mul (p q : Qz) : (Qz_to_Qc (p * q) = Qz_to_Qc p * Qz_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.

Notation "0" := (nat_to_Qz 0) : Qz_scope.
Notation "1" := (nat_to_Qz 1) : Qz_scope.
Notation "2" := (nat_to_Qz 2) : Qz_scope.
Notation "3" := (nat_to_Qz 3) : Qz_scope.
Notation "4" := (nat_to_Qz 4) : Qz_scope.

Definition Qz_le (p q : Qz) : Prop :=
  let 'mk_Qz p _ := p in let 'mk_Qz q _ := q in (p ≤ q)%Qc.
Definition Qz_lt (p q : Qz) : Prop :=
  let 'mk_Qz p _ := p in let 'mk_Qz q _ := q in (p < q)%Qc.

Infix "≤" := Qz_le : Qz_scope.
Infix "<" := Qz_lt : Qz_scope.
Notation "p ≤ q ≤ r" := (p ≤ q ∧ q ≤ r) : Qz_scope.
Notation "p ≤ q < r" := (p ≤ q ∧ q < r) : Qz_scope.
Notation "p < q < r" := (p < q ∧ q < r) : Qz_scope.
Notation "p < q ≤ r" := (p < q ∧ q ≤ r) : Qz_scope.
Notation "p ≤ q ≤ r ≤ r'" := (p ≤ q ∧ q ≤ r ∧ r ≤ r') : Qz_scope.
Notation "(≤)" := Qz_le (only parsing) : Qz_scope.
Notation "(<)" := Qz_lt (only parsing) : Qz_scope.

Global Hint Extern 0 (_ ≤ _)%Qz => reflexivity : core.

Lemma pos_to_qz_through_nat c :
  nat_to_Qz (Pos.to_nat c) = Qp_to_Qz (pos_to_Qp c).
Proof. apply Qz_to_Qc_inj_iff. simpl. f_equal. lia. Qed.

Lemma Qz_to_Qc_inj_le p q : p ≤ q ↔ (Qz_to_Qc p ≤ Qz_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.
Lemma Qz_to_Qc_inj_lt p q : p < q ↔ (Qz_to_Qc p < Qz_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.

Global Instance Qz_le_dec : RelDecision (≤).
Proof.
  refine (λ p q, cast_if (decide (Qz_to_Qc p ≤ Qz_to_Qc q)%Qc));
    by rewrite Qz_to_Qc_inj_le.
Qed.
Global Instance Qz_lt_dec : RelDecision (<).
Proof.
  refine (λ p q, cast_if (decide (Qz_to_Qc p < Qz_to_Qc q)%Qc));
    by rewrite Qz_to_Qc_inj_lt.
Qed.
Global Instance Qz_lt_pi p q : ProofIrrel (p < q).
Proof. destruct p, q; apply _. Qed.

Definition Qz_max (q p : Qz) : Qz := if decide (q ≤ p) then p else q.
Definition Qz_min (q p : Qz) : Qz := if decide (q ≤ p) then q else p.

Infix "`max`" := Qz_max : Qz_scope.
Infix "`min`" := Qz_min : Qz_scope.

Global Instance Qz_inhabited : Inhabited Qz := populate 1.

Global Instance Qz_add_assoc : Assoc (=) Qz_add.
Proof. intros [p ?] [q ?] [r ?]; apply Qz_to_Qc_inj_iff, Qcplus_assoc. Qed.
Global Instance Qz_add_comm : Comm (=) Qz_add.
Proof. intros [p ?] [q ?]; apply Qz_to_Qc_inj_iff, Qcplus_comm. Qed.
Global Instance Qz_add_inj_r p : Inj (=) (=) (Qz_add p).
Proof.
  destruct p as [p ?].
  intros [q1 ?] [q2 ?]. rewrite <-!Qz_to_Qc_inj_iff; simpl. apply (inj (Qcplus p)).
Qed.
Global Instance Qz_add_inj_l p : Inj (=) (=) (λ q, q + p).
Proof.
  destruct p as [p ?].
  intros [q1 ?] [q2 ?]. rewrite <-!Qz_to_Qc_inj_iff; simpl. apply (inj (λ q, q + p)%Qc).
Qed.

Global Instance Qz_add_0_l : LeftId (=) 0 Qz_add.
Proof.
  intros []; apply Qz_to_Qc_inj_iff, Qcplus_0_l.
Qed.
Global Instance Qz_add_0_r : RightId (=) 0 Qz_add.
Proof.
  intros []; apply Qz_to_Qc_inj_iff, Qcplus_0_r.
Qed.

Lemma Qc_add_eq_zero (p q: Qc) :
  (0 <= p)%Qc -> (0 <= q)%Qc -> (p+q = 0)%Qc -> p=0%Qc /\ q=0%Qc.
Proof.
  intros Hp Hq Hpq.
   destruct (decide (q=0%Qc)); destruct (decide (p=0%Qc)); subst; try easy; exfalso.
  { by rewrite Qcplus_0_r in Hpq. }
  { by rewrite Qcplus_0_l in Hpq. }
  { apply Qcle_lt_or_eq in Hp; destruct Hp; try congruence.
    apply Qcle_lt_or_eq in Hq; destruct Hq; try congruence.
    assert (0 < p + q)%Qc as E by (now apply Qcplus_pos_pos).
    apply Qclt_not_eq in E. congruence. }
Qed.

Lemma rew_0_qc : Qc_of_Z (Z.of_nat 0) = 0%Qc.
Proof. compute_done. Qed.

Lemma Qz_add_eq_zero p q : p+q = 0 -> p=0 /\ q=0.
Proof.
  qdestruct p. qdestruct q.
  intros E.
  apply Qz_to_Qc_inj_iff in E. simpl in *.
  rewrite rew_0_qc in E.
  apply Qc_add_eq_zero in E; try easy. destruct E. subst.
  compute_done.
Qed.

Lemma Qc_add_eq_same (p q: Qc) :
  (p = p+q)%Qc -> q=0%Qc.
Proof.
  intros Hpq.
  apply (@f_equal _ _ (fun x => x + (- p))%Qc) in Hpq.
  rewrite Qcplus_opp_r in Hpq. rewrite Hpq.
  ring.
Qed.

Lemma Qz_add_eq_same p q :
  p = p+q -> q=0.
Proof.
  qdestruct p. qdestruct q.
  intros E.
  apply Qz_to_Qc_inj_iff in E. simpl in *.
  apply Qz_to_Qc_inj_iff.
  apply Qc_add_eq_same in E. subst.
  compute_done.
Qed.

Global Instance Qz_mul_assoc : Assoc (=) Qz_mul.
Proof. intros [p ?] [q ?] [r ?]. apply Qz_to_Qc_inj_iff, Qcmult_assoc. Qed.
Global Instance Qz_mul_comm : Comm (=) Qz_mul.
Proof. intros [p ?] [q ?]; apply Qz_to_Qc_inj_iff, Qcmult_comm. Qed.

Global Instance zero_LeftAbsorb_mul : LeftAbsorb (=) 0%Qz Qz_mul.
Proof.
  intros x. qdestruct x. apply Qz_to_Qc_inj_iff. compute_done.
Qed.

Global Instance zero_RightAbsorb_mul : RightAbsorb (=) 0%Qz Qz_mul.
Proof.
  intros x. rewrite (comm _ x). rewrite left_absorb. easy. apply _.
Qed.

Global Instance mul_inj_r q : q ≠ 0%Qz -> Inj (=) (=) (Qz_mul q).
Proof.
  intros Hq [x ?] [y ?] He.
  apply Qz_to_Qc_inj_iff. simpl.
  apply Qz_to_Qc_inj_iff in He.
  qdestruct q. simpl in *.
  assert (Q2Qc 0 < q)%Qc.
  { apply Qcle_lt_or_eq  in H. destruct H; try easy.
    exfalso. apply Hq. subst. compute_done. }
  apply (anti_symm Qcle); apply (Qcmult_le_mono_pos_l _ _ q); eauto; now rewrite He.
Qed.
Global Instance mul_inj_l q : q ≠ 0%Qz -> Inj (=) (=) (λ p, p * q).
Proof.
  intros ? q1 q2 Hpq. apply (mul_inj_r q). easy. by rewrite !(comm_L Qz_mul q).
Qed.

Lemma Qz_mul_add_distr_l p q r : p * (q + r) = p * q + p * r.
Proof. destruct p, q, r; by apply Qz_to_Qc_inj_iff, Qcmult_plus_distr_r. Qed.
Lemma Qz_mul_add_distr_r p q r : (p + q) * r = p * r + q * r.
Proof. destruct p, q, r; by apply Qz_to_Qc_inj_iff, Qcmult_plus_distr_l. Qed.
Lemma Qz_mul_1_l p : 1 * p = p.
Proof. destruct p; apply Qz_to_Qc_inj_iff, Qcmult_1_l. Qed.
Lemma Qz_mul_1_r p : p * 1 = p.
Proof. destruct p; apply Qz_to_Qc_inj_iff, Qcmult_1_r. Qed.

Lemma Qz_mul_inv_eq_zero p q : p * q = 0 -> p = 0 \/ q = 0.
Proof.
  qdestruct p. qdestruct q.
  intros He.
  apply Qz_to_Qc_inj_iff in He. simpl in *. rewrite rew_0_qc in He.
  apply Qcmult_integral in He.
  destruct He as [-> | ->].
  { left. compute_done. }
  { right. compute_done. }
Qed.

Lemma Qz_mul_succ_l p q :
  (1 + p) * q = q + p * q.
Proof. by rewrite Qz_mul_add_distr_r, Qz_mul_1_l. Qed.

Lemma Qz_1_1 : 1 + 1 = 2.
Proof. compute_done. Qed.
Lemma Qz_add_diag p : p + p = 2 * p.
Proof. by rewrite <-Qz_1_1, Qz_mul_add_distr_r, !Qz_mul_1_l. Qed.

Lemma Qz_mul_inv_l p : /p * p = 1.
Proof.
  destruct p as [p ?]; apply Qz_to_Qc_inj_iff; simpl.
  rewrite Qcmult_inv_l. compute_done.
  by apply not_symmetry, Qclt_not_eq.
Qed.
Lemma Qz_mul_inv_r p : (Qp_to_Qz p) * /p = 1.
Proof. by rewrite (comm_L Qz_mul), Qz_mul_inv_l. Qed.
Lemma Qz_inv_mul_distr p q : /(p * q) = /p * /q.
Proof. by rewrite Qp.inv_mul_distr, Qp_to_Qz_mul_distr. Qed.
Lemma Qz_inv_involutive p : / /p = p.
Proof.
  rewrite <-(Qz_mul_1_l (/ /p)), <-(Qz_mul_inv_r p), <-(assoc_L _).
  by rewrite Qz_mul_inv_r, Qz_mul_1_r.
Qed.
Lemma Qz_inv_1 : /1 = 1.
Proof. compute_done. Qed.
Lemma Qz_inv_half_half : /2 + /2 = 1.
Proof. compute_done. Qed.
Lemma Qz_inv_quarter_quarter : /4 + /4 = /2.
Proof. compute_done. Qed.

Lemma Qz_div_diag (p:Qp) : p / p = 1.
Proof. apply Qz_mul_inv_r. Qed.
Lemma Qz_mul_div_l p q : (p / q) * q = p.
Proof. unfold Qz_div. by rewrite <-(assoc_L _), Qz_mul_inv_l, Qz_mul_1_r. Qed.
Lemma Qz_mul_div_r p (q:Qp) : q * (p / q) = p.
Proof. by rewrite (comm_L Qz_mul q), Qz_mul_div_l. Qed.
Lemma Qz_div_add_distr p q r : (p + q) / r = p / r + q / r.
Proof. apply Qz_mul_add_distr_r. Qed.
Lemma Qz_div_div p q r : (p / q) / r = p / (q * r).
Proof. unfold Qz_div. by rewrite Qz_inv_mul_distr, (assoc_L _). Qed.
Lemma Qz_div_mul_cancel_l p q (r:Qp) : (r * p) / (r * q) = p / q.
Proof.
  rewrite <-Qz_div_div. f_equiv. unfold Qz_div.
  by rewrite (comm_L Qz_mul r), <-(assoc_L _), Qz_mul_inv_r, Qz_mul_1_r.
Qed.
Lemma Qz_div_mul_cancel_r p q (r:Qp) : (p * r) / (q * r) = p / q.
Proof.
  rewrite <-!(comm_L Qz_mul r).
  rewrite <-!(comm_L Qp.mul r).
  now rewrite Qz_div_mul_cancel_l.
Qed.
Lemma Qz_div_1 p : p / 1 = p.
  rewrite <- (Qz_mul_1_r (p / 1)).
  assert (nat_to_Qz 1 = Qp_to_Qz 1) as -> by compute_done.
  now rewrite Qz_mul_div_l.
Qed.
Lemma Qz_div_2 p : p / 2 + p / 2 = p.
Proof.
  rewrite <-Qz_div_add_distr, Qz_add_diag.
  rewrite <-(Qp.mul_1_r 2).
  assert (nat_to_Qz 2 = Qp_to_Qz 2) as -> by compute_done.
  rewrite Qz_div_mul_cancel_l.
  now rewrite Qz_div_1.
Qed.

(*
Lemma Qz_div_2_mul p q : p / (2 * q) + p / (2 * q) = p / q.
Proof. by rewrite <-Qz_div_add_distr, Qz_add_diag, Qz_div_mul_cancel_l. Qed.
Lemma Qz_half_half : 1 / 2 + 1 / 2 = 1.
Proof. compute_done. Qed.
Lemma Qz_quarter_quarter : 1 / 4 + 1 / 4 = 1 / 2.
Proof. compute_done. Qed.
Lemma Qz_quarter_three_quarter : 1 / 4 + 3 / 4 = 1.
Proof. compute_done. Qed.
Lemma Qz_three_quarter_quarter : 3 / 4 + 1 / 4 = 1.
Proof. compute_done. Qed.
Global Instance Qz_div_inj_r p : Inj (=) (=) (Qz_div p).
Proof. unfold Qz_div; apply _. Qed.
Global Instance Qz_div_inj_l p : Inj (=) (=) (λ q, q / p)%Qz.
Proof. unfold Qz_div; apply _. Qed.
 *)

Global Instance Qz_le_po : PartialOrder (≤)%Qz.
Proof.
  split; [split|].
  - intros p. by apply Qz_to_Qc_inj_le.
  - intros p q r. rewrite !Qz_to_Qc_inj_le. by etrans.
  - intros p q. rewrite !Qz_to_Qc_inj_le, <-Qz_to_Qc_inj_iff. apply Qcle_antisym.
Qed.
Global Instance Qz_lt_strict : StrictOrder (<)%Qz.
Proof.
  split.
  - intros p ?%Qz_to_Qc_inj_lt. by apply (irreflexivity (<)%Qc (Qz_to_Qc p)).
  - intros p q r. rewrite !Qz_to_Qc_inj_lt. by etrans.
Qed.
Global Instance Qz_le_total: Total (≤)%Qz.
Proof. intros p q. rewrite !Qz_to_Qc_inj_le. apply (total Qcle). Qed.

Lemma Qz_lt_le_incl p q : p < q → p ≤ q.
Proof. rewrite Qz_to_Qc_inj_lt, Qz_to_Qc_inj_le. apply Qclt_le_weak. Qed.
Lemma Qz_le_lteq p q : p ≤ q ↔ p < q ∨ p = q.
Proof.
  rewrite Qz_to_Qc_inj_lt, Qz_to_Qc_inj_le, <-Qz_to_Qc_inj_iff. split.
  - intros [?| ->]%Qcle_lt_or_eq; auto.
  - intros [?| ->]; auto using Qclt_le_weak.
Qed.
Lemma Qz_lt_ge_cases p q : {p < q} + {q ≤ p}.
Proof.
  refine (cast_if (Qclt_le_dec (Qz_to_Qc p) (Qz_to_Qc q)%Qc));
    [by apply Qz_to_Qc_inj_lt|by apply Qz_to_Qc_inj_le].
Defined.
Lemma Qz_le_lt_trans p q r : p ≤ q → q < r → p < r.
Proof. rewrite !Qz_to_Qc_inj_lt, Qz_to_Qc_inj_le. apply Qcle_lt_trans. Qed.
Lemma Qz_lt_le_trans p q r : p < q → q ≤ r → p < r.
Proof. rewrite !Qz_to_Qc_inj_lt, Qz_to_Qc_inj_le. apply Qclt_le_trans. Qed.

Lemma Qz_le_ngt p q : p ≤ q ↔ ¬q < p.
Proof.
  rewrite !Qz_to_Qc_inj_lt, Qz_to_Qc_inj_le.
  split; auto using Qcle_not_lt, Qcnot_lt_le.
Qed.
Lemma Qz_lt_nge p q : p < q ↔ ¬q ≤ p.
Proof.
  rewrite !Qz_to_Qc_inj_lt, Qz_to_Qc_inj_le.
  split; auto using Qclt_not_le, Qcnot_le_lt.
Qed.

Lemma Qz_add_le_mono_l p q r : p ≤ q ↔ r + p ≤ r + q.
Proof. rewrite !Qz_to_Qc_inj_le. destruct p, q, r; apply Qcplus_le_mono_l. Qed.
Lemma Qz_add_le_mono_r p q r : p ≤ q ↔ p + r ≤ q + r.
Proof. rewrite !(comm_L Qz_add _ r). apply Qz_add_le_mono_l. Qed.
Lemma Qz_add_le_mono q p n m : q ≤ n → p ≤ m → q + p ≤ n + m.
Proof. intros. etrans; [by apply Qz_add_le_mono_l|by apply Qz_add_le_mono_r]. Qed.

Lemma Qz_add_lt_mono_l p q r : p < q ↔ r + p < r + q.
Proof. by rewrite !Qz_lt_nge, <-Qz_add_le_mono_l. Qed.
Lemma Qz_add_lt_mono_r p q r : p < q ↔ p + r < q + r.
Proof. by rewrite !Qz_lt_nge, <-Qz_add_le_mono_r. Qed.
Lemma Qz_add_lt_mono q p n m : q < n → p < m → q + p < n + m.
Proof. intros. etrans; [by apply Qz_add_lt_mono_l|by apply Qz_add_lt_mono_r]. Qed.

Lemma Qz_pos_neq_zero p : p ≠ 0 <-> 0 < p.
Proof.
  qdestruct p.
  apply Qcle_lt_or_eq in H.
  split; intros Hp.
  { destruct H; try easy.
    exfalso. apply Hp. subst. compute_done. }
  { intros E. rewrite E in Hp.
    now apply Qclt_not_eq in Hp. }
Qed.

Lemma Qz_lt_add_l p q : q ≠ 0 -> p < p + q.
Proof.
  qdestruct p; qdestruct q.
  intros Hq.
  apply Qz_to_Qc_inj_lt; simpl.
  rewrite <- (Qcplus_0_r p) at 1.
  rewrite <- Qcplus_lt_mono_l.
  apply Qz_pos_neq_zero, Qz_to_Qc_inj_lt in Hq.
  easy.
Qed.

(*
Lemma Qz_mul_le_mono_l p q r : p ≤ q ↔ r * p ≤ r * q.
Proof.
  rewrite !Qz_to_Qc_inj_le. destruct p, q, r; by apply Qcmult_le_mono_nonneg_l.
Qed.
Lemma Qz_mul_le_mono_r p q r : p ≤ q ↔ p * r ≤ q * r.
Proof. rewrite !(comm_L Qz_mul _ r). apply Qz_mul_le_mono_l. Qed.
Lemma Qz_mul_le_mono q p n m : q ≤ n → p ≤ m → q * p ≤ n * m.
Proof. intros. etrans; [by apply Qz_mul_le_mono_l|by apply Qz_mul_le_mono_r]. Qed.
*)

(*
Lemma Qz_mul_lt_mono_l p q r : p < q ↔ r * p < r * q.
Proof.
  rewrite !Qz_to_Qc_inj_lt. destruct p, q, r; by apply Qcmult_lt_mono_nonneg_l.
Qed.
Lemma Qz_mul_lt_mono_r p q r : p < q ↔ p * r < q * r.
Proof. rewrite !(comm_L Qz_mul _ r). apply Qz_mul_lt_mono_l. Qed.
Lemma Qz_mul_lt_mono q p n m : q < n → p < m → q * p < n * m.
Proof. intros. etrans; [by apply Qz_mul_lt_mono_l|by apply Qz_mul_lt_mono_r]. Qed.
*)

Lemma Qz_le_sum p q : p ≤ q ↔ ∃ r, q = p + r.
Proof.
  qdestruct p. qdestruct q. rewrite Qz_to_Qc_inj_le; simpl.
  split.
  - intros Hle%Qcle_minus_iff. eexists (mk_Qz (q - p) _).
    apply Qz_to_Qc_inj_iff; simpl. unfold Qcminus.
    by rewrite (Qcplus_comm q), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
    Unshelve. by apply qcile_corr.
  - intros [r ?%Qz_to_Qc_inj_iff]; simplify_eq/=.
    qdestruct r.
    rewrite <-(Qcplus_0_r p) at 1. by apply Qcplus_le_mono_l.
Qed.

Lemma Qz_le_add_l p q : p ≤ p + q.
Proof.
  qdestruct p. qdestruct q. rewrite Qz_to_Qc_inj_le; simpl.
  rewrite <- (Qcplus_0_r p) at 1. by rewrite <-Qcplus_le_mono_l.
Qed.

Lemma Qz_le_add_r p q : q ≤ p + q.
Proof. rewrite (comm_L Qz_add). apply Qz_le_add_l. Qed.

Lemma Qz_le_zero p : p ≤ 0 -> p = 0.
Proof.
  intros. qdestruct p.
  by apply Qz_to_Qc_inj_iff,Qcle_antisym.
Qed.

Lemma Qz_lt_zero p : p < 0 -> False.
Proof.
  intros Hp. apply Qz_lt_nge in Hp. qdestruct p.
  easy.
Qed.

Lemma Qz_to_Qc_inj_sub (p q : Qz) :
  Qz_le q p ->
  (Qz_to_Qc (p - q)%Qz = Qz_to_Qc p - Qz_to_Qc q)%Qc.
Proof.
  qdestruct p. qdestruct q. simpl.
  intros Hle. unfold Qz_sub.
  case_decide as Hpq.
  { easy. }
  { exfalso. apply Hpq.
    apply Qcle_minus_iff in Hle.
    easy. }
Qed.

Lemma Qz_sub_add p q : q ≤ p → p - q + q = p.
Proof.
  qdestruct p. qdestruct q.
  intros Hle. unfold Qz_sub.
  case_decide as Hpq.
  { apply Qz_to_Qc_inj_iff. simpl. ring. }
  { exfalso. apply Hpq.
    apply Qz_to_Qc_inj_le in Hle. simpl in *.
    apply Qcle_minus_iff in Hle.
    easy. }
Qed.

Lemma Qz_add_sub (p q : Qz) :
  (p+q)-p = q.
Proof.
  apply Qz_to_Qc_inj_iff.
  rewrite Qz_to_Qc_inj_sub; eauto using Qz_le_add_l.
  rewrite Qz_to_Qc_inj_add.
  ring.
Qed.

Lemma Qp_to_Qz_ne_zero (p:Qp) : Qp_to_Qz p ≠ 0%Qz.
Proof.
  destruct p as [? Hp].
  intros E.
  injection E. clear E. intros E.
  replace (Qc_of_Z (Z.of_nat 0)) with (Q2Qc 0) in E by compute_done.
  subst. apply irreflexivity in Hp; eauto.
  apply _.
Qed.

(*
Lemma Qz_lt_sum p q : p < q ↔ ∃ r, q = p + r.
Proof.
  destruct p as [p Hp], q as [q Hq]. rewrite Qz_to_Qc_inj_lt; simpl.
  split.
  - intros Hlt%Qclt_minus_iff. exists (mk_Qz (q - p) Hle).
    apply Qz_to_Qc_inj_iff; simpl. unfold Qcminus.
    by rewrite (Qcplus_comm q), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
  - intros [[r ?] ?%Qz_to_Qc_inj_iff]; simplify_eq/=.
    rewrite <-(Qcplus_0_r p) at 1. by apply Qcplus_lt_mono_l.
Qed.


Lemma Qz_sub_None p q : p - q = None ↔ p ≤ q.
Proof.
  rewrite Qz_le_ngt, Qz_lt_sum, eq_None_not_Some.
  by setoid_rewrite <-Qz_sub_Some.
Qed.
Lemma Qz_sub_diag p : p - p = None.
Proof. by apply Qz_sub_None. Qed.
Lemma Qz_add_sub p q : (p + q) - q = Some p.
Proof. apply Qz_sub_Some. by rewrite (comm_L Qz_add). Qed.

Lemma Qz_inv_lt_mono p q : p < q ↔ /q < /p.
Proof.
  revert p q. cut (∀ p q, p < q → / q < / p).
  { intros help p q. split; [apply help|]. intros.
    rewrite <-(Qz_inv_involutive p), <-(Qz_inv_involutive q). by apply help. }
  intros p q Hpq. apply (Qz_mul_lt_mono_l _ _ q). rewrite Qz_mul_inv_r.
  apply (Qz_mul_lt_mono_r _ _ p). rewrite <-(assoc_L _), Qz_mul_inv_l.
  by rewrite Qz_mul_1_l, Qz_mul_1_r.
Qed.
Lemma Qz_inv_le_mono p q : p ≤ q ↔ /q ≤ /p.
Proof. by rewrite !Qz_le_ngt, Qz_inv_lt_mono. Qed.

Lemma Qz_div_le_mono_l p q r : q ≤ p ↔ r / p ≤ r / q.
Proof. unfold Qz_div. by rewrite <-Qz_mul_le_mono_l, Qz_inv_le_mono. Qed.
Lemma Qz_div_le_mono_r p q r : p ≤ q ↔ p / r ≤ q / r.
Proof. apply Qz_mul_le_mono_r. Qed.
Lemma Qz_div_lt_mono_l p q r : q < p ↔ r / p < r / q.
Proof. unfold Qz_div. by rewrite <-Qz_mul_lt_mono_l, Qz_inv_lt_mono. Qed.
Lemma Qz_div_lt_mono_r p q r : p < q ↔ p / r < q / r.
Proof. apply Qz_mul_lt_mono_r. Qed.

Lemma Qz_div_lt p q : 1 < q → p / q < p.
Proof. by rewrite (Qz_div_lt_mono_l _ _ p), Qz_div_1. Qed.
Lemma Qz_div_le p q : 1 ≤ q → p / q ≤ p.
Proof. by rewrite (Qz_div_le_mono_l _ _ p), Qz_div_1. Qed.
*)

Lemma Qz_div_eq_zero (q:Qz) p :
  ((q / p) = 0)%Qz -> q = 0%Qz.
Proof.
  intros Hqp.
  apply (@f_equal _ _ (Qz_mul p)) in Hqp.
  rewrite Qz_mul_div_r in Hqp. subst.
  rewrite right_absorb; try easy. apply _.
Qed.

Lemma Qz_div_neq_zero (q:Qz) (p:Qp) :
  q ≠ 0 -> (q / p)%Qz ≠ 0.
Proof. eauto using Qz_div_eq_zero. Qed.

(*
Lemma Qz_lower_bound q1 q2 : ∃ q q1' q2', q1 = q + q1' ∧ q2 = q + q2'.
Proof.
  revert q1 q2. cut (∀ q1 q2 : Qz, q1 ≤ q2 →
    ∃ q q1' q2', q1 = q + q1' ∧ q2 = q + q2').
  { intros help q1 q2.
    destruct (Qz_lt_ge_cases q2 q1) as [Hlt|Hle]; eauto.
    destruct (help q2 q1) as (q&q1'&q2'&?&?); eauto using Qz_lt_le_incl. }
  intros q1 q2 Hq. exists (q1 / 2)%Qz, (q1 / 2)%Qz.
  assert (q1 / 2 < q2) as [q2' ->]%Qz_lt_sum.
  { eapply Qz_lt_le_trans, Hq. by apply Qz_div_lt. }
  eexists; split; [|done]. by rewrite Qz_div_2.
Qed.

Lemma Qz_lower_bound_lt q1 q2 : ∃ q : Qz, q < q1 ∧ q < q2.
Proof.
  destruct (Qz_lower_bound q1 q2) as (qmin & q1' & q2' & [-> ->]).
  ∃ qmin. split; eapply Qz_lt_sum; eauto.
Qed.

Lemma Qz_cross_split a b c d :
  a + b = c + d →
  ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d.
Proof.
  intros H. revert a b c d H. cut (∀ a b c d : Qz,
    a < c → a + b = c + d →
    ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d)%Qz.
  { intros help a b c d Habcd.
    destruct (Qz_lt_ge_cases a c) as [?|[?| ->]%Qz_le_lteq].
    - auto.
    - destruct (help c d a b); [done..|]. naive_solver.
    - apply (inj (Qz_add a)) in Habcd as →.
      destruct (Qz_lower_bound a d) as (q&a'&d'&->&->).
      ∃ a', q, q, d'. repeat split; done || by rewrite (comm_L Qz_add). }
  intros a b c d [e ->]%Qz_lt_sum. rewrite <-(assoc_L _). intros ->%(inj (Qz_add a)).
  destruct (Qz_lower_bound a d) as (q&a'&d'&->&->).
  eexists a', q, (q + e)%Qz, d'; split_and?; [by rewrite (comm_L Qz_add)|..|done].
  - by rewrite (assoc_L _), (comm_L Qz_add e).
  - by rewrite (assoc_L _), (comm_L Qz_add a').
Qed.

Lemma Qz_bounded_split p r : ∃ q1 q2 : Qz, q1 ≤ r ∧ p = q1 + q2.
Proof.
  destruct (Qz_lt_ge_cases r p) as [[q ->]%Qz_lt_sum|?].
  { by ∃ r, q. }
  ∃ (p / 2)%Qz, (p / 2)%Qz; split.
  + trans p; [|done]. by apply Qz_div_le.
  + by rewrite Qz_div_2.
Qed.
*)

Lemma Qz_max_spec q p : (q < p ∧ q `max` p = p) ∨ (p ≤ q ∧ q `max` p = q).
Proof.
  unfold Qz_max.
  destruct (decide (q ≤ p)) as [[?| ->]%Qz_le_lteq|?]; [by auto..|].
  right. split; [|done]. by apply Qz_lt_le_incl, Qz_lt_nge.
Qed.

Lemma Qz_max_spec_le q p : (q ≤ p ∧ q `max` p = p) ∨ (p ≤ q ∧ q `max` p = q).
Proof. destruct (Qz_max_spec q p) as [[?%Qz_lt_le_incl?]|]; [left|right]; done. Qed.

Global Instance Qz_max_assoc : Assoc (=) Qz_max.
Proof.
  intros q p o. unfold Qz_max. destruct (decide (q ≤ p)), (decide (p ≤ o));
    try by rewrite ?decide_True by (by etrans).
  rewrite decide_False by done.
  by rewrite decide_False by (apply Qz_lt_nge; etrans; by apply Qz_lt_nge).
Qed.
Global Instance Qz_max_comm : Comm (=) Qz_max.
Proof.
  intros q p.
  destruct (Qz_max_spec_le q p) as [[?->]|[?->]],
    (Qz_max_spec_le p q) as [[?->]|[?->]]; done || by apply (anti_symm (≤)).
Qed.

Lemma Qz_max_id q : q `max` q = q.
Proof. by destruct (Qz_max_spec q q) as [[_->]|[_->]]. Qed.

Lemma Qz_le_max_l q p : q ≤ q `max` p.
Proof. unfold Qz_max. by destruct (decide (q ≤ p)). Qed.
Lemma Qz_le_max_r q p : p ≤ q `max` p.
Proof. rewrite (comm_L Qz_max q). apply Qz_le_max_l. Qed.

Lemma Qz_max_add q p : q `max` p ≤ q + p.
Proof.
  unfold Qz_max.
  destruct (decide (q ≤ p)); [apply Qz_le_add_r|apply Qz_le_add_l].
Qed.

Lemma Qz_max_lub_l q p o : q `max` p ≤ o → q ≤ o.
Proof. unfold Qz_max. destruct (decide (q ≤ p)); [by etrans|done]. Qed.
Lemma Qz_max_lub_r q p o : q `max` p ≤ o → p ≤ o.
Proof. rewrite (comm _ q). apply Qz_max_lub_l. Qed.

Lemma Qz_min_spec q p : (q < p ∧ q `min` p = q) ∨ (p ≤ q ∧ q `min` p = p).
Proof.
  unfold Qz_min.
  destruct (decide (q ≤ p)) as [[?| ->]%Qz_le_lteq|?]; [by auto..|].
  right. split; [|done]. by apply Qz_lt_le_incl, Qz_lt_nge.
Qed.

Lemma Qz_min_spec_le q p : (q ≤ p ∧ q `min` p = q) ∨ (p ≤ q ∧ q `min` p = p).
Proof. destruct (Qz_min_spec q p) as [[?%Qz_lt_le_incl ?]|]; [left|right]; done. Qed.

Global Instance Qz_min_assoc : Assoc (=) Qz_min.
Proof.
  intros q p o. unfold Qz_min.
  destruct (decide (q ≤ p)), (decide (p ≤ o)); eauto using decide_False.
  - by rewrite !decide_True by (by etrans).
  - by rewrite decide_False by (apply Qz_lt_nge; etrans; by apply Qz_lt_nge).
Qed.
Global Instance Qz_min_comm : Comm (=) Qz_min.
Proof.
  intros q p.
  destruct (Qz_min_spec_le q p) as [[?->]|[?->]],
    (Qz_min_spec_le p q) as [[? ->]|[? ->]]; done || by apply (anti_symm (≤)).
Qed.

Lemma Qz_min_id q : q `min` q = q.
Proof. by destruct (Qz_min_spec q q) as [[_->]|[_->]]. Qed.
Lemma Qz_le_min_r q p : q `min` p ≤ p.
Proof. by destruct (Qz_min_spec_le q p) as [[?->]|[?->]]. Qed.

Lemma Qz_le_min_l p q : p `min` q ≤ p.
Proof. rewrite (comm_L Qz_min p). apply Qz_le_min_r. Qed.

Lemma Qz_min_l_iff q p : q `min` p = q ↔ q ≤ p.
Proof.
  destruct (Qz_min_spec_le q p) as [[?->]|[?->]]; [done|].
  split; [by intros ->|]. intros. by apply (anti_symm (≤)).
Qed.
Lemma Qz_min_r_iff q p : q `min` p = p ↔ p ≤ q.
Proof. rewrite (comm_L Qz_min q). apply Qz_min_l_iff. Qed.

(* Nat2Qz *)
Lemma nat_to_Qz_inj n m : nat_to_Qz n = nat_to_Qz m → n = m.
Proof. injection 1. intros. lia. Qed.

Lemma nat_to_Qz_inj_iff n m : nat_to_Qz n = nat_to_Qz m ↔ n = m.
Proof. split; [apply nat_to_Qz_inj | by intros ->]. Qed.

Lemma nat_to_Qz_inj_le (x y : nat) :
  (Qz_le (nat_to_Qz x) (nat_to_Qz y))%Qz <-> (x <= y)%nat.
Proof.
  unfold Qz_le, nat_to_Qz.
  rewrite <- Z2Qc_inj_le.
  lia.
Qed.

Lemma nat_to_Qz_to_Qc x : Qz_to_Qc (nat_to_Qz x) = Qc_of_Z (Z_of_nat x).
Proof. easy. Qed.

Lemma nat_to_Qz_add (x y:nat) : nat_to_Qz (x+y) = (nat_to_Qz x + nat_to_Qz y)%Qz.
Proof.
  apply Qz_to_Qc_inj_iff.
  rewrite Qz_to_Qc_inj_add ,nat_to_Qz_to_Qc.
  simpl. rewrite <-  Z2Qc_inj_add.
  f_equal. lia.
Qed.

Lemma nat_to_Qz_mul (x y:nat) : nat_to_Qz (x*y) = (nat_to_Qz x * nat_to_Qz y)%Qz.
Proof.
  apply Qz_to_Qc_inj_iff.
  rewrite Qz_to_Qc_inj_mul, nat_to_Qz_to_Qc.
  simpl. rewrite <- Z2Qc_inj_mul.
  f_equal. lia.
Qed.

Lemma nat_to_Qz_sub (x y:nat) :
  (Peano.le y x) ->
  nat_to_Qz (x-y) = (nat_to_Qz x - nat_to_Qz y)%Qz.
Proof.
  intros ?.
  apply Qz_to_Qc_inj_iff.
  rewrite Qz_to_Qc_inj_sub.
  2:{ now apply nat_to_Qz_inj_le. }
  rewrite nat_to_Qz_to_Qc.
  simpl. rewrite <- Z2Qc_inj_sub.
  f_equal. lia.
Qed.

(* This tries to move a Qz equality to nat. *)
Ltac rew_qz_step tac :=
  first [ rewrite <- nat_to_Qz_mul
        | rewrite <- nat_to_Qz_add
        | rewrite <- nat_to_Qz_sub; [|tac]
    ].
Ltac rew_qz_rel_step tt :=
  first [ rewrite nat_to_Qz_inj_iff
        | rewrite nat_to_Qz_inj_le ].

Ltac rew_qz tac :=
  repeat (rew_qz_step tac);
  repeat (rew_qz_rel_step tt).

Tactic Notation "rew_qz" "by" tactic(tac) := rew_qz tac.
Tactic Notation "rew_qz" := rew_qz by ltac:(lia).

Local Close Scope Qz_scope.
