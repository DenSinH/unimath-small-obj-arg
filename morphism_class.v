Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import Coq.Classes.RelationClasses.

Section morphism_class.

Local Open Scope cat.


(* A subset in Coq is like (A : hSet) : A -> Prop *)
Definition morphism_class (C : category) : UU := ∏ (X Y : C), (X --> Y) -> hProp.

Definition morphism_class_containedIn (C : category) (S T : morphism_class C) : hProp :=
    ∀ (X Y : C) (f : X --> Y), ((S _ _) f ⇒ (T _ _) f)%logic.

Variable C : category.

Definition morphism_class_univ : (morphism_class C) :=
    λ X Y f, htrue.

Definition morphism_class_isos : (morphism_class C) :=
    λ X Y f, make_hProp (is_iso f) (isaprop_is_iso _ _ _).

Notation "S ⊆ T" := (morphism_class_containedIn C S T) (at level 70).

Lemma morphism_class_equal_cond (S T : morphism_class C) : (S ⊆ T) × (T ⊆ S) <-> S = T.
Proof.
    admit.
Admitted.
    
End morphism_class.