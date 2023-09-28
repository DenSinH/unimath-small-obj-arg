Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.

Local Open Scope cat.

Definition Chains (C : category) : UU := 
    ∏ (d : chain C), ColimCocone d.

Definition chain_mor0 {C : category} (d : chain C) : 
    ∏ v, ∑ (f : dob d 0 --> dob d (S v)), (∏ (x : C) (cc : cocone d x), f · coconeIn cc (S v) = coconeIn cc 0).
Proof.
  intro v.
  use tpair.
  -  use chain_mor.
    apply natgthsn0.
  - intros ? ?.
    apply chain_mor_coconeIn.
Defined.
