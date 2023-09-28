Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.


Definition identity_diagram {C : category} (c : C) (g : graph) :
    diagram g C.
Proof.
  use tpair.
  - intro. exact c.
  - intros _ _ _. exact (identity _).
Defined.

Lemma colim_identity {C : category} (c : C) {g : graph} :
    UU.