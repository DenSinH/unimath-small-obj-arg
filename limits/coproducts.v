Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.coproducts.

Local Open Scope cat.

Definition CoproductOfArrowsInclusion {I J : UU} {C : category}
    (incl : I -> J) {a : I -> C} (CCab : Coproduct _ _ a) {c : J -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c (incl i)) :
          CoproductObject _ _ CCab --> CoproductObject _ _ CCcd :=
  CoproductArrow _ _ CCab (λ i, f i · CoproductIn _ _ CCcd (incl i)).

  
(* non-implicit I/C for backwards compatibility *)
Definition CoproductOfArrows' (I : UU) (C : category)
    {a : I -> C} (CCab : Coproduct _ _ a) {c : I -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c i) :
        CoproductObject _ _ CCab --> CoproductObject _ _ CCcd :=
  CoproductOfArrowsInclusion (idfun I) CCab CCcd f.

Lemma CoproductOfArrowsInclusionIn {I J : UU} {C : category} 
    (incl : I -> J) {a : I -> C} (CCab : Coproduct _ _ a) {c : J -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c (incl i)) :
  ∏ i, CoproductIn _ _ CCab i · CoproductOfArrowsInclusion incl CCab CCcd f = f i · CoproductIn _ _ CCcd (incl i).
Proof.
  unfold CoproductOfArrows; intro i.
  apply CoproductInCommutes.
Qed.

(* non-implicit I/C for backwards compatibility *)
Lemma CoproductOfArrows'In (I : UU) (C : category)
    {a : I -> C} (CCab : Coproduct _ _ a) {c : I -> C}
    (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c i) :
  ∏ i, CoproductIn _ _ CCab i · CoproductOfArrows' _ _ CCab CCcd f = f i · CoproductIn _ _ CCcd i.
Proof.
  apply CoproductOfArrowsInclusionIn.
Qed.

Lemma precompWithCoproductArrowInclusion {I J : UU} {C : category}
  (incl : I -> J) {a : I -> C} (CCab : Coproduct _ _ a) {c : J -> C}
  (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c (incl i))
  {x : C} (k : ∏ i, c i --> x) :
      CoproductOfArrowsInclusion incl CCab CCcd f · CoproductArrow _ _ CCcd k =
       CoproductArrow _ _ CCab (λ i, f i · k (incl i)).
Proof.
  apply CoproductArrowUnique; intro i.
  now rewrite assoc, CoproductOfArrowsInclusionIn, <- assoc, CoproductInCommutes.
Qed.

(* non-implicit I/C for backwards compatibility *)
Lemma precompWithCoproductArrow' (I : UU) (C : category)
  {a : I -> C} (CCab : Coproduct _ _ a) {c : I -> C}
  (CCcd : Coproduct _ _ c) (f : ∏ i, a i --> c i)
  {x : C} (k : ∏ i, c i --> x) :
      CoproductOfArrows' _ _ CCab CCcd f · CoproductArrow _ _ CCcd k =
       CoproductArrow _ _ CCab (λ i, f i · k i).
Proof.
  apply precompWithCoproductArrowInclusion.
Qed.

Definition CoproductOfArrowsInclusion_comp {I J K: UU} {C : category}
    {a : I -> C} {b : J -> C} {c : K -> C}
    (CCI : Coproducts I C) (CCJ : Coproducts J C) (CCK : Coproducts K C)
    {inclI : I -> J} {inclJ : J -> K}
    (f : ∏ i, a i --> b (inclI i)) (g : ∏ j, b j --> c (inclJ j)) :
    CoproductOfArrowsInclusion inclI (CCI _) (CCJ _) f · 
        CoproductOfArrowsInclusion inclJ (CCJ _) (CCK _) g
    = CoproductOfArrowsInclusion (λ i, inclJ (inclI i)) (CCI _) (CCK _) (λ i, f i · g (inclI i)).
Proof.
  apply CoproductArrowUnique; intro i.
  rewrite assoc, CoproductOfArrowsInclusionIn.
  now rewrite <- assoc, CoproductOfArrowsInclusionIn, assoc.
Qed.

(* non-implicit I/C for backwards compatibility *)
Definition CoproductOfArrows'_comp (I : UU) (C : category) (CC : Coproducts I C)
  (a b c : I -> C) (f : ∏ i, a i --> b i) (g : ∏ i, b i --> c i) :
   CoproductOfArrows' _ _ _ _ f · CoproductOfArrows' _ _ (CC _) (CC _) g
   = CoproductOfArrows' _ _ (CC _) (CC _)(λ i, f i · g i).
Proof.
  apply CoproductOfArrowsInclusion_comp.
Qed.
