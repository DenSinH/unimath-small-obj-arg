Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

From Model Require Import morphism_class.

Section weakeqv.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope logic.

(* todo: in lean this is also a hProp *)
Record is_weak_equivalences {M : category} (W : morphism_class M) := {
    weq_of_iso : ∀ x y (i : x --> y) (h : is_iso i), (W _ _) i;
    (* two out of three properties *)
    weq_comp : ∀ x y z (f : x --> y) (g : y --> z), (W _ _) f ⇒ (W _ _) g ⇒ (W _ _) (g ∘ f);
    weq_cancel_left : ∀ {x y z} {f : x --> y} {g : y --> z}, (W _ _) f ⇒ (W _ _) (g ∘ f) ⇒ (W _ _) g;
    weq_cancel_right : ∀ {x y z} {f : x --> y} {g : y --> z}, (W _ _) g ⇒ (W _ _) (g ∘ f) ⇒ (W _ _) f;
}.


End weakeqv.