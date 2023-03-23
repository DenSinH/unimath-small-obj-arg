Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Setoid.

Declare Scope morcls.
Delimit Scope morcls with morcls.

Local Open Scope morcls.

Local Open Scope cat.

(* See UniMath/MoreFoundations/Subtypes.v *)

(* A subset in Coq is like (A : hSet) : A -> Prop *)
Definition morphism_class (C : category) : UU :=
    ∏ (X Y : C), hsubtype (X --> Y).

Lemma isasetmorphism_class {C : category} : isaset (morphism_class C).
Proof.
  change (isofhlevel 2 (morphism_class C)).
  apply impred; intro x.
  apply impred; intro t.
  exact (isasethsubtype _).
Defined.

Definition morphism_class_set (C : category) : hSet := 
    make_hSet (morphism_class C) (isasetmorphism_class (C := C)).

Definition morphism_class_containedIn {C : category} : hrel (morphism_class_set C) :=
    λ S T, ∀ (X Y : C) (f : X --> Y), ((S _ _) f ⇒ (T _ _) f)%logic.

Notation "S ⊆ T" := (morphism_class_containedIn S T) (at level 70) : morcls.

(* Definition morphism_class_notContainedIn : hrel (morphism_class_set C) :=
    λ S T, ∃ (X Y : C) (f : X --> Y), ((S _ _) f × ¬(T _ _) f)%logic. *)

Lemma morphism_class_ext {C : category} {I J : morphism_class C}
  (h : ∏ x y (f : x --> y), ((I _ _) f <-> (J _ _) f)) : I = J.
Proof.
  do 3 (apply (funextsec _ _ _); intro).
  (* now rewrite (h x x0 x1). *)
  admit.
Admitted.

Lemma morphism_class_subset_antisymm {C : category} {I J : morphism_class C} (h : I ⊆ J) (h' : J ⊆ I) : I = J.
Proof.
  apply morphism_class_ext.
  intros x y f.
  split.
  - exact (h _ _ _).
  - exact (h' _ _ _).
Qed.

Definition morphism_class_intersection {C : category} (S T : morphism_class C) : morphism_class C:=
    λ X Y f, (S _ _ f) ∧ (T _ _ f).

Notation "S ∩ T" := (morphism_class_intersection S T) (at level 50) : morcls.

(* Back to morphism_class.lean *)
Definition morphism_class_univ (C : category) : (morphism_class C) :=
    λ X Y f, htrue.

Definition morphism_class_isos (C : category) : (morphism_class C) :=
    λ X Y f, make_hProp (is_iso f) (isaprop_is_iso _ _ _).
