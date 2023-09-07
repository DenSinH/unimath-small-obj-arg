Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.

Local Open Scope cat.


(* helper for showing section_disp_axioms *)
Lemma section_disp_on_eq_morphisms {C : category} 
    (F : section_disp (three_disp C))
    {f f' : arrow C} {γ γ': f --> f'} 
    (H00 : arrow_mor00 γ = arrow_mor00 γ')
    (H11 : arrow_mor11 γ = arrow_mor11 γ') :
  pr1 (section_disp_on_morphisms (section_disp_data_from_section_disp F) γ) =
    pr1 (section_disp_on_morphisms (section_disp_data_from_section_disp F) γ').
Proof.
  assert (Heq : γ = γ').
  {
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    - exact H00.
    - exact H11.
  }
  rewrite Heq.
  reflexivity.
Qed.

Lemma section_disp_on_eq_morphisms' {C : category} 
    (F : section_disp (three_disp C)) {f f' : arrow C} {γ : f --> f'} 
    (H : arrow_mor00 γ · f' = f · arrow_mor11 γ) :
  let alternate := ((arrow_mor00 γ,, arrow_mor11 γ),, H) : f --> f' in
  pr1 (section_disp_on_morphisms (section_disp_data_from_section_disp F) alternate) =
    pr1 (section_disp_on_morphisms (section_disp_data_from_section_disp F) γ).
Proof.
  use section_disp_on_eq_morphisms.
  - reflexivity.
  - reflexivity.
Qed.

Lemma pr1_transportf_const {A : UU} {B : UU} {P : ∏ (a : A), B -> UU}
    {a a' : A} (e : a = a') (xs : ∑ b : B, P a b) :
    pr1 (transportf (λ x, ∑ b : B, P _ b) e xs) = pr1 xs.
Proof.
  rewrite pr1_transportf.
  rewrite transportf_const.
  reflexivity.
Qed.