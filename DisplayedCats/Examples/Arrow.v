Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
(* The Structure Identity Principle (HoTT book, chapter 9.8) *)
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp.

Section Arrow_Disp.

Context (C:category).

Definition arrow_base := category_binproduct C C.

Definition arrow_disp : disp_cat arrow_base.
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ xy, pr1 xy --> pr2 xy).
  - simpl.
    intros xx' yy' g h ff'.
    exact (pr1 ff' · h = g · pr2 ff').
  - abstract (
      intros;
      use homset_property
    ).
  - abstract (
      simpl;
      intros;
      now rewrite id_left, id_right
    ).
  - abstract (
      simpl;
      intros;
      rewrite assoc, <- X;
      symmetry;
      now rewrite <- assoc, <- X0, assoc
    ).
Defined.

Definition arrow : category := total_category arrow_disp.

End Arrow_Disp.

Definition arrow_dom {C : category} (f : arrow C) : C := pr11 f.
Definition arrow_cod {C : category} (f : arrow C) : C := pr21 f.
Coercion arrow_mor {C : category} (f : arrow C) := pr2 f.

Definition arrow_mor00 {C : category} {f g : arrow C} (F : f --> g) := pr11 F. 
Definition arrow_mor11 {C : category} {f g : arrow C} (F : f --> g) := pr21 F. 
Definition arrow_mor_comm {C : category} {f g : arrow C} (F : f --> g) := pr2 F. 

Coercion mor_to_arrow_ob {C : category} {x y : C} (f : x --> y) : arrow C :=
    (make_dirprod x y,, f).

Definition mors_to_arrow_mor {C : category} {a b x y : C} (f : a --> b) (g : x --> y) 
    (h : a --> x) (k : b --> y) (H : g ∘ h = k ∘ f) : (mor_to_arrow_ob f) --> (mor_to_arrow_ob g).
Proof.
  use tpair.
  - exact (make_dirprod h k).
  - abstract (exact H).
Defined.

Definition opp_arrow {C : category} (g : arrow C) : arrow (op_cat C) :=
    (make_dirprod (arrow_cod g) (arrow_dom g),, arrow_mor g).

(* Lemma arrow_eq {C : category} {g g' : arrow C} {f f' : g --> g'} :
    pr1 f = pr1 f' -> f = f'.
Proof.
  intro H.
  apply subtypePath; [intro; apply homset_property|].
  exact H.
Qed. *)

(* base_paths : equality in pr1 of ∑-type (paths in base category)
    pathsdirprodweq : _ × _ = _ × _ -> equality of terms
*)
Definition top_square {C : category}
    {f f' : arrow C} {mor mor1' : f --> f'} (H : mor = mor1') := 
  dirprod_pr1 (pathsdirprodweq (base_paths _ _ H)).
Definition bottom_square {C : category}
    {f f' : arrow C} {mor mor1' : f --> f'} (H : mor = mor1') := 
  dirprod_pr2 (pathsdirprodweq (base_paths _ _ H)).