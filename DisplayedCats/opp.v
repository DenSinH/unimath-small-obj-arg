Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.

Definition op_disp_cat_ob_mor {C : category} (D : disp_cat C) : disp_cat_ob_mor (op_cat C).
Proof.
  use make_disp_cat_ob_mor.
  - intro x.
    exact (D x).
  - intros x y xx yy m.
    exact (yy -->[rm_opp_mor m] xx).
Defined.

Definition op_disp_cat_id_comp {C : category} (D : disp_cat C) : disp_cat_id_comp _ (op_disp_cat_ob_mor D).
Proof.
  split.
  - intros. exact (id_disp _).
  - intros x y z f g xx yy zz ff gg.
    exact (comp_disp (D := D) gg ff).
Defined.

Definition op_disp_cat_data {C : category} (D : disp_cat C) : disp_cat_data (op_cat C) :=
    (op_disp_cat_ob_mor D,, op_disp_cat_id_comp D).

Definition op_disp_cat_axioms {C : category} (D : disp_cat C) : disp_cat_axioms _ (op_disp_cat_data D).
Proof.
  repeat split; intros; cbn.
  * exact (id_right_disp (D:=D) ff).
  * exact (id_left_disp (D:=D) ff).
  * etrans.
    exact (assoc_disp_var (D:=D) hh gg ff).
    unfold transportb.
    apply maponpaths_2.
    apply homset_property.
  * apply homsets_disp.
Defined.

Definition op_disp_cat {C : category} (D : disp_cat C) : disp_cat (op_cat C) :=
    (_,, op_disp_cat_axioms D).
