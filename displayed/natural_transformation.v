Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition section_nat_trans_disp_data 
    {C : category} 
    {D : disp_cat C} 
    (F F' : section_disp D) : UU :=
  ∏ (x : C), F x -->[identity _] F' x.

Definition section_nat_trans_disp_axioms 
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp_data F F') : UU :=
  ∏ x x' (f : x --> x'), 
      transportf _
      (id_right _ @ !(id_left _)) 
      (section_disp_on_morphisms F f ;; nt x') =
    nt x ;; section_disp_on_morphisms F' f.

Definition section_nat_trans_disp 
    {C : category}
    {D : disp_cat C} 
    (F F': section_disp D) : UU :=
  ∑ (nt : section_nat_trans_disp_data F F'), section_nat_trans_disp_axioms nt.

Definition section_nt_disp_data_from_section_nt_disp
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : section_nat_trans_disp_data F F'
  := pr1 nt.
    
Definition section_nat_trans_data_from_section_nat_trans_disp_funclass 
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
  ∏ x : ob C, F x -->[identity _]  F' x := section_nt_disp_data_from_section_nt_disp nt.
Coercion section_nat_trans_data_from_section_nat_trans_disp_funclass :
    section_nat_trans_disp >-> Funclass.
  
Definition section_nt_disp_axioms_from_section_nt_disp
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : section_nat_trans_disp_axioms nt
  := pr2 nt.

Definition section_nat_trans_data
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
      nat_trans_data (section_functor F) (section_functor F').
Proof.
  intro.
  exists (identity _).
  exact (nt x).
Defined.

Definition section_nat_trans_axioms
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F') :
      is_nat_trans (section_functor F) (section_functor F') (section_nat_trans_data nt).
Proof.
  intros x x' f.
  use total2_paths_f.
  - simpl. now rewrite id_left, id_right.
  - simpl. 
    rewrite <- (section_nt_disp_axioms_from_section_nt_disp nt).
    apply transportf_paths.
    apply homset_property.
Defined.

Definition section_nat_trans
    {C : category}
    {D : disp_cat C} 
    {F F': section_disp D}
    (nt : section_nat_trans_disp F F')
    : nat_trans (section_functor F) (section_functor F') :=
  section_nat_trans_data nt,, section_nat_trans_axioms nt.
