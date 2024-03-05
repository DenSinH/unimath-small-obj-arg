Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.

Require Import CategoryTheory.DisplayedCats.natural_transformation.
Require Import CategoryTheory.DisplayedCats.Examples.MonadAlgebras.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.

Lemma eq_symm 
    (x y : nat) 
    (H : x = y) :
  y = x.
Proof.
  rewrite H.
  reflexivity.
Qed.

Lemma eq_symm' 
    (y : nat) 
    (x := y) :
    y = x.
Proof.
  reflexivity.
Qed.

(* from the natural numbers game: *)
Inductive mynat : Set :=
| O : mynat
| S : mynat -> mynat.

Fixpoint add (n m : mynat) : mynat :=
    match m with
    | O => n
    | S p => S (add n p)
    end.

Infix "+" := add.
Notation "(+)" := add (only parsing).
Notation "( f +)" := (add f) (only parsing).
Notation "(+ f )" := (fun g => add g f) (only parsing).

Notation "0" := O.

Fact add_zero (n : mynat) : n + 0 = n.
Proof.
  trivial.
Qed.

Fact add_succ (m n : mynat) : n + (S m) = S (n + m).
Proof.
  trivial.
Qed.

Lemma zero_add (n : mynat) : 0 + n = n.
Proof.
    induction n as [| ? H].
    - rewrite add_zero.
      reflexivity.
    - rewrite add_succ.
      rewrite H.
      reflexivity.
Qed.

Lemma zero_add' (n : mynat) : 0 + n = n.
Proof.
    induction n as [| ? H].
    - rewrite add_zero.
      reflexivity.
    - rewrite add_succ.
      rewrite H.
      reflexivity.
Defined.

Eval cbv in zero_add.
Eval cbv in zero_add'.

Section Face_maps.

Context (C : category).

(* face map 1 now rolls out just as the projection *)
Definition face_map_1 : three C ⟶ arrow C := pr1_category _.

(* we have to define face maps 0 and 2 as proper functors,
since we need the factorization to obtain an object in the arrow
category. *)
Definition face_map_0_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob1 xxx) (three_ob2 xxx)).
    * exact (three_mor12 xxx).
  - intros xxx yyy fff.
    (* simpl. *)
    (* for morphisms we simply forget the 0th morphism *)
    use mors_to_arrow_mor.
    * exact (three_mor11 fff).
    * exact (three_mor22 fff).
    * (* commutativity is just commutativity in the lower diagram *)
      abstract (
        apply pathsinv0;
        exact (pr2 (three_mor_comm fff))
      ).
Defined.

Definition face_map_0_axioms : is_functor face_map_0_data.
Proof.
  split.
  - (* unfold functor_idax. *)
    intro.
    apply subtypePath; [intro; apply homset_property|].
    reflexivity.
  - (* unfold functor_compax. *)
    intros a b c f g.
    apply subtypePath; [intro; apply homset_property|].
    reflexivity.
Qed.

Definition face_map_0 : three C ⟶ arrow C :=
    (_,, face_map_0_axioms).

Definition face_map_2_data : functor_data (three C) (arrow C).
Proof.
  use make_functor_data.
  - intro xxx.
    use tpair.
    * exact (make_dirprod (three_ob0 xxx) (three_ob1 xxx)).
    * simpl.
      exact (three_mor01 xxx).
  - intros xxx yyy fff.
    use mors_to_arrow_mor.
    * exact (three_mor00 fff).
    * exact (three_mor11 fff).
    * abstract (
        exact (pathsinv0 (pr1 (three_mor_comm fff)))
      ).
Defined.

Definition face_map_2_axioms : is_functor face_map_2_data.
Proof.
  split.
  - (* unfold functor_idax. *)
    intro.
    apply subtypePath; [intro; apply homset_property|].
    trivial.
  - (* unfold functor_compax. *)
    intros a b c f g.
    apply subtypePath; [intro; apply homset_property|].
    trivial.
Qed.

Definition face_map_2 : three C ⟶ arrow C :=
    (_,, face_map_2_axioms).

(* verify that they are indeed compatible *)
Lemma face_compatibility (fg : three C) : 
    arrow_mor (face_map_2 fg) · arrow_mor (face_map_0 fg) 
    = arrow_mor (face_map_1 fg).
Proof.
  exact (three_comp fg).
Defined.

Definition c_21_data : nat_trans_data face_map_2 face_map_1.
Proof.
  (* this natural transformation boils down to square
    0 ===== 0
    |       |
    |       |
    1 ----> 2
  *)
  intro xxx.
  simpl.
  exists (make_dirprod (identity _) (three_mor12 xxx)).
  abstract (
    simpl;
    rewrite id_left;
    apply pathsinv0;
    exact (three_comp xxx)
  ).
Defined.

Definition c_21_axioms : is_nat_trans _ _ c_21_data.
Proof.
  (* natural transformation commutativity axiom *)
  intros xxx yyy ff.

  (* use displayed properties to turn path in total category
  into path in base category, given our displayed properties

  subtypePath: equality on ∑ x : X, P x is the same as equality
  on X if P is a predicate (maps to a prop).
  In the total category, objects are ∑ c : C, D c
  i.e., objects with displayed data. Morphisms are morphisms
  with displayed data. Our morphisms displayed data is indeed
  propositional: commutative diagram.
  *)
  apply subtypePath.
  * (* For any map in the base category, the induced map
    on the displayed category is a property.

    This is because the induced map is a commuting square,
    so an equality between maps. Therefore, the homset property
    says this is a property. *)
    intro.
    apply homset_property.
  * (* We are left to prove the commutativity in the base category,
    given our displayed properties. This is effectively just commutativity
    in the bottom square. *)
    apply pathsdirprod.
    + etrans. apply id_right.
      apply pathsinv0.
      apply id_left.
    + apply pathsinv0.
      exact (pr2 (three_mor_comm ff)).
Qed.

Definition c_21 : face_map_2 ⟹ face_map_1 :=
    (_,, c_21_axioms).

Definition c_10_data : nat_trans_data face_map_1 face_map_0.
Proof.
  (* this natural transformation boils down to square
    0 ----> 1
    |       |
    |       |
    2 ===== 2
  *)
  intro xxx.
  exists (make_dirprod (three_mor01 xxx) (identity _)).
  abstract (
    simpl;
    rewrite id_right;
    exact (three_comp xxx)
  ).
Defined.

Definition c_10_axioms : is_nat_trans _ _ c_10_data.
Proof.
  intros xxx yyy ff.
  apply subtypePath.
  - intro x.
    apply homset_property.
  - apply pathsdirprod.
    * apply pathsinv0.
      exact (pr1 (three_mor_comm ff)).
    * etrans. apply id_right.
      apply pathsinv0.
      apply id_left.
Qed.

Definition c_10 : face_map_1 ⟹ face_map_0 :=
    (_,, c_10_axioms).

End Face_maps.

Arguments face_map_0 {_}.
Arguments face_map_1 {_}.
Arguments face_map_2 {_}.

(* Lemma face_map_1_preserves_dom {C : category} : ∏ g : three C, arrow_dom (face_map_1 g) = three_ob0 g.
Proof.
  trivial.
Defined.

Lemma face_map_1_preserves_cod {C : category} : ∏ g : three C, arrow_cod (face_map_1 g) = three_ob2 g.
Proof.
  trivial.
Defined. *)

(* Definition face_map_1_section_data (C : category) : functor_data (arrow C) (three C).
Proof.
  use tpair.
  - intros
Defined. *)

(* We can't really do this with the "naive definition" of three C, since then we need
the middle object for the section. We would have to define our own theory.  *)
Definition functorial_factorization (C : category) := section_disp (three_disp C).
Coercion fact_section {C : category} (F : functorial_factorization C)
    := section_disp_data_from_section_disp F.
Definition fact_functor {C : category} (F : functorial_factorization C) : arrow C ⟶ three C :=
    section_functor F.
Coercion fact_functor : functorial_factorization >-> functor.

(* Functorial factorizations indeed split face map 1 (d1) *)
Lemma functorial_factorization_splits_face_map_1 {C : category} (F : functorial_factorization C) :
    F ∙ face_map_1 = functor_identity (arrow C).
Proof.
  apply functor_eq; trivial.
  apply homset_property.
Qed.

Definition fact_L {C : category} (F : functorial_factorization C) :
    arrow C ⟶ arrow C :=
  F ∙ face_map_2.
Definition fact_R {C : category} (F : functorial_factorization C) : 
    arrow C ⟶ arrow C :=
  F ∙ face_map_0.

(* At least now it knows they are compatible *)
Lemma LR_compatibility {C : category} (F : functorial_factorization C) :
    ∏ (f : arrow C), (fact_L F f) · (fact_R F f) = f.
Proof.
  intro.
  apply three_comp.
Qed.

Definition functorial_factorization' (C : category) :=
  ∑ F : (arrow C ⟶ three C), 
    F ∙ face_map_1 = functor_identity (arrow C).

Definition fact_L' {C : category} (F : functorial_factorization' C) :
    arrow C ⟶ arrow C :=
  (pr1 F) ∙ face_map_2.
Definition fact_R' {C : category} (F : functorial_factorization' C) : 
    arrow C ⟶ arrow C :=
  (pr1 F) ∙ face_map_0.

Lemma L_dom_eq {C : category} (F' : functorial_factorization' C) (f : arrow C) :
    arrow_dom f = arrow_dom (fact_L' F' f).
Proof.
  assert (Hf : f = (functor_composite (pr1 F') face_map_1) f).
  {
    rewrite (pr2 F').
    reflexivity.
  }

  etrans. apply maponpaths.
          exact Hf.
  reflexivity.
Qed.

Lemma R_cod_eq {C : category} (F' : functorial_factorization' C) (f : arrow C) :
    arrow_cod f = arrow_cod (fact_R' F' f).
Proof.
  assert (Hf : f = (functor_composite (pr1 F') face_map_1) f).
  {
    rewrite (pr2 F').
    reflexivity.
  }

  etrans. apply maponpaths.
          exact Hf.
  reflexivity.
Qed.

Lemma LR_compatibility' 
    {C : category} (F' : functorial_factorization' C) :
  ∏ (f : arrow C), 
    (fact_L' F' f) · (fact_R' F' f) 
    = z_iso_inv (idtoiso (L_dom_eq F' f)) 
    · f 
    · idtoiso (R_cod_eq F' f).
Proof.
  intro.
  etrans. apply three_comp.
  apply pathsinv0.
  etrans. exact (pathsinv0 (double_transport_idtoiso _ _ _ _ _ _ _ f)).
  unfold double_transport.
  

Admitted.
