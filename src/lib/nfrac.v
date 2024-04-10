From stdpp Require Export sets countable.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates big_op.
From iris.prelude Require Import options.

From irisfit Require Import qz qz_cmra.

Class IsNegligible (A:ucmra) (negligible:A -> Prop) := mk_negligible
  { negligible_proper : Proper (equiv ==> iff) negligible;
    negligible_op : forall X Y, negligible X -> negligible Y -> negligible (X ⋅ Y);
    negligible_unit : negligible ε;
  }.

Record nfrac (A:ucmra) (negligible:A -> Prop) `{IsNegligible A negligible} :=
    mk_nf { frac : Qz;
            supp : A;
            neglz : frac = 0%Qz -> negligible supp; }.

Global Arguments mk_nf {_ _ _} _ _ _ : assert.
Global Arguments frac {_ _ _} _ : assert.
Global Arguments supp {_ _ _} _ : assert.
Global Arguments neglz {_ _ _} _ _ : assert.

Section NFrac.

  Context `{IsNegligible A negligible}.
  Implicit Types x y : nfrac A negligible.

  (* Two nfrac are equivalents if their fraction and support are equivalent. *)
  Global Instance nfrac_equiv_instance : Equiv (nfrac A negligible) :=
    fun x y => frac x ≡ frac y /\ supp x ≡ supp y.

  Lemma nfrac_equiv x y : (x ≡ y) = (frac x ≡ frac y /\ supp x ≡ supp y).
  Proof. easy. Qed.

  Global Instance nfrac_equivalence : Equivalence (≡@{nfrac A negligible}).
  Proof.
    constructor; try easy.
    { intros [] []. firstorder. }
    { intros [] [a b] [] [] []. simpl in *; constructor; simpl.
      { now transitivity a. }
      { now transitivity b. } }
  Qed.

  Lemma nfrac_equiv_frac x y : x ≡ y -> frac x ≡ frac y.
  Proof. rewrite nfrac_equiv. by intros []. Qed.

  Lemma nfrac_equiv_supp x y : x ≡ y -> supp x ≡ supp y.
  Proof. rewrite nfrac_equiv. by intros []. Qed.

  Canonical Structure nfracO := discreteO (nfrac A negligible).

  Global Instance proper_nfrac_supp : Proper (equiv ==> equiv) supp.
  Proof. intros ? ?. apply nfrac_equiv_supp. Qed.

  Global Instance proper_nfrac_frac : Proper (equiv ==> eq) frac.
  Proof. intros ? ?. apply nfrac_equiv_frac. Qed.

  (* The operator of the camera: the sum of fractions and the op of supports. *)
  Program Definition nfrac_op x y : (nfrac A negligible) :=
    mk_nf ((frac x+frac y)%Qz) (supp x ⋅ supp y) _.

  Next Obligation.
    intros ? ? E. apply Qz_add_eq_zero in E. destruct E.
    apply negligible_op; eauto using neglz.
  Qed.

  Global Instance nfrac_op_assoc : Assoc equiv nfrac_op.
  Proof.
    intros [[]] [[]] [[]].
    unfold nfrac_op. simpl.
    constructor; simpl; now rewrite assoc.
  Qed.
 Instance nfrac_op_comm : Comm equiv nfrac_op.
  Proof.
    intros [[]] [[]].
    unfold nfrac_op. simpl.
    constructor; simpl; now apply comm, _.
  Qed.

  (* The unit element *)
  Definition nfrac_unit :=
    mk_nf 0%Qz ε (fun _ => negligible_unit).

  Local Instance nfrac_unit_instance : Unit (nfrac A negligible) := nfrac_unit.

  Global Instance nfrac_left_unit : LeftId equiv ε nfrac_op.
  Proof.
    intros ?.
    rewrite nfrac_equiv.
    constructor; simpl; by rewrite left_id.
  Qed.

  Local Instance nfrac_validN_instance : ValidN (nfrac A negligible) :=
    λ n x, ✓{ n } (frac x) /\ ✓{ n } (supp x).
  Local Instance nfrac_valid_instance : Valid (nfrac A negligible) :=
    λ x, ✓(frac x) /\  ✓ (supp x).

  Local Instance nfrac_op_instance : Op (nfrac A negligible) := nfrac_op.
  Local Instance nfrac_pcore_instance : PCore (nfrac A negligible) :=
    fun _ => (Some nfrac_unit).

  Global Instance proper_op : Proper (equiv ==> equiv ==> equiv) nfrac_op.
  Proof.
    intros [] [] [E11 E12] [] [] [E21 E22]. simpl in *.
    constructor; simpl.
    { rewrite E11 E21 //. }
    { rewrite E12 E22 //. }
  Qed.

  Lemma nfrac_valid_alt X : ✓ X <-> ✓(frac X) /\ ✓ (supp X).
  Proof. easy. Qed.

  Lemma nfrac_op_alt x y : (x ⋅ y) = nfrac_op x y.
  Proof. easy. Qed.

  Lemma nfrac_pcore_alt X : pcore X = Some nfrac_unit.
  Proof. easy. Qed.

  Lemma nfrac_core_alt X : core X = nfrac_unit.
  Proof. easy. Qed.

  Lemma core_ok (X:nfrac A negligible) : core X ⋅ X ≡ X.
  Proof. by rewrite left_id. Qed.

  Lemma nfrac_ra_mixin : RAMixin (nfrac A negligible).
  Proof.
    apply ra_total_mixin; eauto; try apply _; try easy.
    { intros [] [] [Hs1 Hs2]. do 2 rewrite nfrac_valid_alt.
      simpl in *. by rewrite Hs1 Hs2. }
    { apply core_ok. }
    { intros. rewrite nfrac_core_alt. exists ε.
      by rewrite core_ok. }
    { intros [] []. do 2 rewrite nfrac_valid_alt. simpl.
      rewrite -gfrac_op.
      intros (E1 & E2); split.
      - now apply cmra_valid_op_l in E1.
      - now apply cmra_valid_op_l in E2. }
  Qed.

  Canonical Structure nfracR :=
    discreteR (nfrac A negligible) nfrac_ra_mixin.

  Global Instance nfrac_cmra_discrete : CmraDiscrete nfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma nfrac_ucmra_mixin : UcmraMixin (nfrac A negligible).
  Proof.
    split; try apply _; try done.
    unfold ε, nfrac_unit_instance.
    rewrite nfrac_valid_alt. split; try apply ucmra_unit_valid.
    easy.
  Qed.

  Canonical Structure nfracUR : ucmra := Ucmra (nfrac A negligible) nfrac_ucmra_mixin.

  (* The most important lemma: *)
  Lemma from_full x y :
      frac x = frac y ->
      x ≼ y ->
      exists z, y ≡ x ⋅ z /\ frac z = 0%Qz /\ negligible (supp z).
  Proof.
    destruct x,y; simpl.
    intros -> [z []]; simpl in *.
    exists z.
    split; try constructor; eauto using neglz, Qz_add_eq_same.
  Qed.

  Lemma nfrac_frac_le x y :
      x ≼ y ->
      (frac x ≤ frac y)%Qz.
  Proof.
    destruct x,y; simpl; intros ([],(Hi,_)).
    simpl in *. rewrite Hi.
    now apply Qz_le_add_l.
  Qed.
End NFrac.

Global Arguments nfracO _ {_ _}.
Global Arguments nfracR _ {_ _}.
Global Arguments nfracUR _ {_ _}.
