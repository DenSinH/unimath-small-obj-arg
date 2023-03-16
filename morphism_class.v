Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Section morphism_class.

Local Open Scope cat.

(* A subset in Coq is like (A : hSet) : A -> Prop *)
Definition morphism_class (C : category) : UU := ∏ (X Y : C), (X --> Y) -> hProp.

Definition morphism_class_containedIn (C : category) (S T : morphism_class C) : hProp :=
    ∀ (X Y : C) (f : X --> Y), ((S _ _) f ⇒ (T _ _) f)%logic.

End morphism_class.