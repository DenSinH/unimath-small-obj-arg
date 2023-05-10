Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.


Local Open Scope cat.

Definition hset_functorial_factorization_data : section_disp_data (three_disp HSET).
Proof.
  use tpair.
  - intro f.
    simpl.
    set (cop := BinCoproductsHSET (arrow_dom f) (arrow_cod f)).
    exists (BinCoproductObject cop).
    exists (BinCoproductIn1 cop).
    exists (BinCoproductArrow cop f (identity _)).
    exact (BinCoproductIn1Commutes _ _ _ cop _ _ _).
  - intros f g γ.
    simpl.
    use tpair.
    * (* arrow dom f ∐ cod f --> dom g ∐ cod g
         simply given by γ: f --> g *)
      intro F.
      destruct F as [p|p].
      + left.  exact (arrow_mor00 γ p).
      + right. exact (arrow_mor11 γ p).
    * repeat split.
      cbn.
      apply funextsec.
      intro p.
      destruct p; cbn; [|reflexivity].
      change ((f · arrow_mor11 γ) p = (arrow_mor00 γ · g) p).

      (* can't just use maponpaths or rewrite for some reason,
         have to use this separate lemma *)
      assert (∏ (a b : hSet) (h h' : a -> b) (q : a), h = h' -> h q = h' q) as H.
      {
        intros ? ? ? ? ? H.
        now rewrite H.
      }
      apply H.
      exact (pathsinv0 (arrow_mor_comm γ)).
Defined.

Definition hset_functorial_factorization_axioms : 
    section_disp_axioms hset_functorial_factorization_data.
Proof.
  split; intros.
  - apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    apply funextsec.
    intro p.
    destruct p; reflexivity.
  - apply subtypePath; [intro; apply isapropdirprod; apply homset_property|].
    apply funextsec.
    intro p.
    destruct p; reflexivity.
Qed.

Definition hset_functorial_factorization : functorial_factorization HSET :=
    (_,, hset_functorial_factorization_axioms).


