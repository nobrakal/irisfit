From iris.proofmode Require Import base proofmode classes.
From iris.algebra Require Import gmap auth.
From stdpp Require Import gmap gmultiset.

From irisfit.spacelang Require Import predecessors.
From irisfit.language Require Import language notation.
From irisfit.lib Require Import qz qz_cmra.
From irisfit.program_logic Require Import ph wp interp.

From irisfit.language Require Export language notation closure.
From irisfit.program_logic Require Export more_interp pbt wpc wpc_more.

Definition triple `{interpGS sz Σ} `{Enc A} E i (r:option (gset loc)) (H:iProp Σ) (t:tm) (Q:A -> iProp Σ) : Prop :=
  (H ⊢ wpc E i r t Q)%I.

Declare Scope triple_scope.
Open Scope triple_scope.

Notation "'CODE' t 'TID' i 'WITH' E 'SOUV' r 'PRE' H 'POST' Q" :=
  (triple E i (Some r) H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODE'  t  '/' 'TID' i 'WITH' E 'SOUV'  r  '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.

Notation "'CODE' t 'TID' i 'WITH' E 'PRE' H 'POST' Q" :=
  (triple E i (Some ∅) H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODE'  t  '/' 'TID'  i 'WITH'  E  '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.

Notation "'CODE' t 'TID' i 'PRE' H 'POST' Q" :=
  (triple ⊤ i (Some ∅) H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODE'  t  '/' 'TID'  i   '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.

Notation "'CODEFF' t 'TID' i 'PRE' H 'POST' Q" :=
  (triple ⊤ i None H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODEFF'  t  '/' 'TID'  i   '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.

Notation "'CODE' t 'TID' i 'SOUV' r 'PRE' H 'POST' Q" :=
  (triple ⊤ i (Some r) H%I t%T Q%I)
  (at level 39, t at level 0,
  format "'[v' 'CODE'  t  '/' 'TID'  i  'SOUV' r  '/' 'PRE'  '[' H ']' '/' 'POST'  Q ']'") : triple_scope.
