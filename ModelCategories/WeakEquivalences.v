Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import CategoryTheory.ModelCategories.MorphismClass.

Section weakeqv.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope logic.

Definition weq_comp_ax {M : category} (W : morphism_class M) : UU :=
    ∀ x y z (f : x --> y) (g : y --> z), 
      (W _ _) f ⇒ (W _ _) g ⇒ (W _ _) (f · g).
Definition weq_cancel_left_ax {M : category} (W : morphism_class M) : UU :=
    ∀ (x y z : M) (f : x --> y) (g : y --> z), 
      (W _ _) f ⇒ (W _ _) (f · g) ⇒ (W _ _) g.
Definition weq_cancel_right_ax {M : category} (W : morphism_class M) : UU :=
    ∀ (x y z : M) (f : x --> y) (g : y --> z), 
      (W _ _) g ⇒ (W _ _) (f · g) ⇒ (W _ _) f.

Definition is_weak_equivalences {M : category} (W : morphism_class M) : UU :=
    weq_comp_ax W × weq_cancel_left_ax W × weq_cancel_right_ax W.

Definition weak_equivalences (M : category) : UU :=
    ∑ (W : morphism_class M), is_weak_equivalences W.

Definition weq_class {M : category} (W : weak_equivalences M) := pr1 W.
Definition weq_is_weq {M : category} (W : weak_equivalences M) := (pr2 W).
Definition is_weq_comp {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := (pr1 (weq)).
Definition is_weq_cancel_left {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := pr12 weq.
Definition is_weq_cancel_right {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := pr22 weq.

Definition weq_comp {M : category} (W : weak_equivalences M) := is_weq_comp (weq_is_weq W).
Definition weq_cancel_left {M : category} (W : weak_equivalences M) := is_weq_cancel_left (weq_is_weq W).
Definition weq_cancel_right {M : category} (W : weak_equivalences M) := is_weq_cancel_right (weq_is_weq W).

Lemma isaprop_is_weak_equivalences {M : category} (W : morphism_class M) : isaprop (is_weak_equivalences W).
Proof.
  idtac; 
    repeat apply isapropdirprod; 
    do 3 (apply impred_isaprop; intro);
    apply propproperty.
Qed.

End weakeqv.