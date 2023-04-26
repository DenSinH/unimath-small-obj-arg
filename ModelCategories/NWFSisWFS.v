Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.
Require Import CategoryTheory.ModelCategories.WFS.
Require Import CategoryTheory.ModelCategories.NWFS.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope morcls.

(* we can obtain a wfs from an nwfs *)
(* the existence of an algebra map is exactly ||nwfs_R_maps_disp f|| *)
Definition nwfs_R_maps_class {C : category} (n : nwfs C) : morphism_class C :=
    λ (x y : C) (f : x --> y), ∥nwfs_R_maps n f∥.
Definition nwfs_L_maps_class {C : category} (n : nwfs C) : morphism_class C :=
    λ (x y : C) (f : x --> y), ∥nwfs_L_maps n (opp_mor f)∥.

Lemma L_map_class_R_map_class_lp {C : category} {n : nwfs C} {a b c d : C}
    {f : a --> b} {g : c --> d} (hf : nwfs_L_maps_class n _ _ f)
    (hg : nwfs_R_maps_class n _ _ g) : lp_hProp f g.
Proof.
  use (hf); clear hf; intro hf.
  use (hg); clear hg; intro hg.
  intros h k Hhk.
  apply hinhpr.
  exact (L_map_R_map_elp hf hg h k Hhk).
Qed.

Lemma nwfs_L_maps_subs_llp_R_maps {C : category} (n : nwfs C) :
    nwfs_L_maps_class n ⊆ llp (nwfs_R_maps_class n).
Proof.
  intros a b f hf.
  intros c d g hg.
  exact (L_map_class_R_map_class_lp hf hg).
Qed.

(* dual to above statement *)
Lemma nwfs_R_maps_subs_rlp_L_maps {C : category} (n : nwfs C) :
    nwfs_R_maps_class n ⊆ rlp (nwfs_L_maps_class n).
Proof.
  intros c d g hg.
  intros a b f hf.
  exact (L_map_class_R_map_class_lp hf hg).
Qed.

Lemma nwfs_L_maps_cl_subs_llp_R_maps_cl {C : category} (n : nwfs C) :
    (nwfs_L_maps_class n)^cl ⊆ llp ((nwfs_R_maps_class n)^cl).
Proof.
  intros a b f Hf.
  intros c d g Hg.
  
  use (Hf).
  intro H.
  destruct H as [x [y [f' [Lf' Retff']]]].

  use (Hg).
  intro H.
  destruct H as [z [w [g' [Rg' Retgg']]]].

  use (lp_of_retracts Retff' Retgg').
  exact (nwfs_L_maps_subs_llp_R_maps n _ _ _ Lf' _ _ _ Rg').
Qed.

Lemma nwfs_R_maps_cl_subs_rlp_L_maps_cl {C : category} (n : nwfs C) :
    (nwfs_R_maps_class n)^cl ⊆ rlp ((nwfs_L_maps_class n)^cl).
Proof.
  intros c d g Hg.
  intros a b f Hf.
  
  use (Hf).
  intro H.
  destruct H as [x [y [f' [Lf' Retff']]]].

  use (Hg).
  intro H.
  destruct H as [z [w [g' [Rg' Retgg']]]].

  use (lp_of_retracts Retff' Retgg').
  exact (nwfs_R_maps_subs_rlp_L_maps n _ _ _ Rg' _ _ _ Lf').
Qed.

Lemma nwfs_Lf_is_L_map {C : category} (n : nwfs C) :
    ∏ f : arrow C, (nwfs_L_maps_class n) _ _ (arrow_mor (fact_L n f)).
Proof.
  intro f.

  (* unfold nwfs_L_maps_class, isCoAlgebra. *)
  apply hinhpr.
  exists (nwfs_Σ n f).

  split; use subtypePath; try (intro; apply homset_property); cbn.
  - apply pathsdirprod.
    * etrans.
      apply maponpaths_2.
      exact (nwfs_Σ_top_map_id n f).
      now rewrite id_right.
    * exact (nwfs_Σ_bottom_map_inv n f).
  - apply pathsdirprod.
    * apply cancel_precomposition.
      (* rhs is just pr11 nwfs_Σ n f
         unfold three_mor00; simpl. *)
      apply pathsinv0.
      etrans.
      exact (nwfs_Σ_top_map_id n f).
      apply pathsinv0.
      exact (nwfs_Σ_top_map_id n (mor_to_arrow_ob _)).
    * exact (nwfs_Σ_bottom_map_L_is_middle_map_of_Σ _ _).
Qed.

(* dual statement *)
Lemma nwfs_Rf_is_R_map {C : category} (n : nwfs C) :
    ∏ f : arrow C, (nwfs_R_maps_class n) _ _ (arrow_mor (fact_R n f)).
Proof.
  intro f.

  (* unfold nwfs_R_maps_class, isAlgebra. *)
  apply hinhpr.
  exists (nwfs_Π n f).

  split; use subtypePath; try (intro; apply homset_property); cbn.
  - apply pathsdirprod.
    * exact (nwfs_Π_top_map_inv n f).
    * etrans.
      apply maponpaths.
      exact (nwfs_Π_bottom_map_id n f).
      now rewrite id_right.
  - apply pathsdirprod.
    * exact (nwfs_Π_bottom_map_R_is_middle_map_of_Π _ _).
    * apply cancel_postcomposition.
      (* rhs is just pr21 nwfs_Π n f
        unfold three_mor22; simpl. *)
      apply pathsinv0.
      etrans.
      exact (nwfs_Π_bottom_map_id n f).
      apply pathsinv0.
      exact (nwfs_Π_bottom_map_id n (mor_to_arrow_ob _)).
Qed.

(**
Lemma nwfs_llp_R_maps_subs_L_maps {C : category} (n : nwfs C) :
    llp (nwfs_R_maps_class n) ⊆ nwfs_L_maps_class n.
Proof.
  (* Want to construct α using lift *)
  intros a b f hf.

  set (Lf := arrow_mor (fact_L n (mor_to_arrow_ob f))).
  set (Rf := arrow_mor (fact_R n (mor_to_arrow_ob f))).
  cbn in Rf.

  (* f ∈ llp (R-Map), so has llp with Rf *)
  (* the lift gives us precisely the map we need for α *)
  use (hf _ _ Rf).

  - exact (nwfs_Rf_is_R_map _ _).
  - exact Lf.
  - exact (identity _).
  - rewrite id_right.
    (* or: three_comp (n (mor_to_arrow_ob f)) *)
    exact (LR_compatibility n (mor_to_arrow_ob f)).
  - intro hl.
    destruct hl as [l [hl0 hl1]].

    (* unfold nwfs_L_maps_class, isCoAlgebra. *)
    apply hinhpr.
    (* 
      A ===== A
      |       |
    f |       | λf
      v       v
      B ----> Kf
          l
    *)
    assert (identity a · Lf = f · l) as αcomm.
    {
      rewrite id_left.
      exact (pathsinv0 hl0).
    }

    set (α := mors_to_arrow_mor f Lf (identity _) l αcomm).
    exists α.
    split.
    * (* η · α = id *)
      simpl.
      apply subtypePath; [intro; apply homset_property|].
      cbn.
      (* top map is just identity for both *)
      apply pathsdirprod; [now rewrite id_left|].
      exact hl1.
    * (* μ · α = T (α) · α  (flipped in comonad)*)
      (* ~ α · Σ = α · L (α)*)
      apply subtypePath; [intro; apply homset_property|].
      cbn.
      apply pathsdirprod.
      + (* top maps are both identity *)
        apply cancel_precomposition.
        exact (nwfs_Σ_top_map_id n (mor_to_arrow_ob f)).
      + (* commutativity in bottom maps *)
        (* We consider the diagram induced by applying the functorial
        factorization to α, i.e. f --> λf (id, l).
        Only the bottom half is interesting.
          A ====== A
          |        |
          |        |
          v  α11   v
         Kf ----> KLf
          |        | ^
       ρf |    ρλf | | σf
          v        v |
          B -----> Kf
              l

        where l · ρf = id and σf · ρλf = id.
        We need to show that σf = α11, which is the same as showing
        that l is an inverse for ρf and σf is an inverse for ρ_{λf}.
        *)
        apply cancel_precomposition.

        set (σf := arrow_mor11 (nwfs_Σ n (mor_to_arrow_ob (opp_mor f)))).
        set (α11 := three_mor11 (functor_on_morphisms n α)).
        change (σf = α11).

        assert (is_z_isomorphism σf) as σf_is_iso.
        {
          exists (arrow_mor (fact_R n (fact_L n (mor_to_arrow_ob (opp_mor f))))).
          unfold is_inverse_in_precat.
          split.
          - exact (nwfs_Σ_bottom_map_inv n (mor_to_arrow_ob f)).
          - (* inverese of nwfs_Σ_bottom_map_inv *)
            admit.
        }
        set (σfiso := make_z_iso' σf σf_is_iso).

        set (α3comm := dirprod_pr2 (three_mor_comm (functor_on_morphisms n α))).
        simpl in α3comm.

        assert (Rf · l = identity _) as Rflid.
        {
          (* inverse of hl1 *)
          admit.
        }
        specialize (pathscomp0 (pathsinv0 Rflid) α3comm) as α3comm'.

        assert (z_iso_mor (z_iso_inv σfiso) = three_mor12 (n (mor_to_arrow_ob Lf))) as σfinv.
        {
          apply pathsinv0.
          apply inv_z_iso_unique'.
          unfold precomp_with.

          exact (nwfs_Σ_bottom_map_inv n (mor_to_arrow_ob f)).
        }
        
        assert (α11 · (z_iso_inv σfiso) = identity _) as α3comm''.
        {
          etrans.
          apply maponpaths.
          exact σfinv.
          exact (pathsinv0 α3comm').
        }

        assert (α11 = z_iso_inv (z_iso_inv σfiso)) as H.
        {
          apply (post_comp_with_z_iso_is_inj (z_iso_inv σfiso)).
          apply pathsinv0.
          etrans.
          exact (z_iso_after_z_iso_inv ((z_iso_inv σfiso))).
          exact (pathsinv0 α3comm'').
        }

        rewrite z_iso_inv_z_iso_inv in H.
        exact (pathsinv0 H).
Admitted.
*)

Lemma nwfs_llp_R_maps_cl_subs_L_maps_cl {C : category} (n : nwfs C) :
    llp ((nwfs_R_maps_class n)^cl) ⊆ ((nwfs_L_maps_class n)^cl).
Proof.
  (* Want to construct retract to L-map using lift.
     The L-map will be Lf *)
  intros a b f Hf.

  set (Lf := arrow_mor (fact_L n f)).
  set (Rf := arrow_mor (fact_R n f)).
  cbn in Rf.

  (* f ∈ llp ((R-Map)^cl), so has llp with Rf *)
  (* the lift gives us precisely the map we need for the retract *)
  use (Hf _ _ Rf).
  - apply in_morcls_retc_if_in_morcls.
    exact (nwfs_Rf_is_R_map _ _).
  - exact Lf.
  - exact (identity _).
  - rewrite id_right.
    (* or: three_comp (n (mor_to_arrow_ob f)) *)
    exact (LR_compatibility n f).
  - intro hl.
    destruct hl as [l [hl0 hl1]].

    apply hinhpr.
    exists _, _, Lf.
    split.
    * exact (nwfs_Lf_is_L_map n f).
    (* 
      A ===== A ===== A
      |       |       |
    f |       | λf    | f
      v       v       v
      B ----> Kf ---> B
          l       ρf
    *)
    * use make_retract.
      + exact (identity _).
      + exact (identity _).
      + exact l.
      + exact Rf.
      + use make_is_retract.
        -- now rewrite id_right.
        -- exact hl1.
        -- rewrite id_left.
           exact (pathsinv0 hl0).
        -- rewrite id_left.
           apply pathsinv0.
           exact (LR_compatibility n f).
Qed.

(**
(* dual statement *)
Lemma nwfs_rlp_L_maps_subs_R_maps {C : category} (n : nwfs C) :
    rlp (nwfs_L_maps_class n) ⊆ nwfs_R_maps_class n.
Proof.
  (* Want to construct α using lift *)
  intros a b f hf.

  set (Lf := arrow_mor (fact_L n (mor_to_arrow_ob f))).
  set (Rf := arrow_mor (fact_R n (mor_to_arrow_ob f))).
  cbn in Lf, Rf.

  (* f ∈ rlp (L-Map), so has rlp with Lf *)
  (* the lift gives us precisely the map we need for α *)
  use (hf _ _ Lf).

  - exact (nwfs_Lf_is_L_map n (mor_to_arrow_ob f)).
  - exact (identity _).
  - exact Rf.
  - rewrite id_left.
    apply pathsinv0.
    (* or: three_comp (n (mor_to_arrow_ob f)) *)
    exact (LR_compatibility n (mor_to_arrow_ob f)).
  - intro hl.
    destruct hl as [l [hl0 hl1]].

    (* unfold nwfs_R_maps_class, isAlgebra. *)
    apply hinhpr.
    use tpair.
    * use mors_to_arrow_mor.
      + exact l.
      + exact (identity _).
      + rewrite id_right.
        exact hl1.
    * simpl.
      split.
      + (* η · α = id *)
        simpl.
        apply subtypePath; [intro; apply homset_property|].
        cbn.
        (* top map is just identity for both *)
        apply pathsdirprod; [|now rewrite id_left].
        exact hl0.
      + (* μ · α = T (α) · α  (flipped in comonad)*)
        (* ~ Π · α = L (α) · α*)
        apply subtypePath; [intro; apply homset_property|].
        cbn.
        apply pathsdirprod.
        -- (* commutativity in top maps *)
           (* we probably should NOT do cancel_postcomposition here *)
           unfold three_mor11.
           simpl.
           (* π_f · l = three_map11 (#n (l, id)) · l *)
           (* since: pr1: three_map11
              section_disp_on_morphisms n : #n
              from three_mor12 to f ... : ρ_f -> f
              (internal_paths_rew_r ...) : commutativity *)
           admit.
        -- (* bottom maps are both identity *)
           apply cancel_postcomposition.
           exact (nwfs_Π_bottom_map_id n (mor_to_arrow_ob f)).
Admitted.
*)
Lemma nwfs_rlp_L_maps_cl_subs_R_maps_cl {C : category} (n : nwfs C) :
    rlp ((nwfs_L_maps_class n)^cl) ⊆ ((nwfs_R_maps_class n)^cl).
Proof.
  (* Want to construct R-map with retract from f using lift. 
     The map will be Rf *)
  intros a b f hf.

  set (Lf := arrow_mor (fact_L n f)).
  set (Rf := arrow_mor (fact_R n f)).
  cbn in Lf, Rf.

  (* f ∈ rlp (L-Map), so has rlp with Lf *)
  (* the lift gives us precisely the map we need for the retract *)
  use (hf _ _ Lf).

  - apply in_morcls_retc_if_in_morcls.
    exact (nwfs_Lf_is_L_map n f).
  - exact (identity _).
  - exact Rf.
  - rewrite id_left.
    apply pathsinv0.
    (* or: three_comp (n (mor_to_arrow_ob f)) *)
    exact (LR_compatibility n f).
  - intro hl.
    destruct hl as [l [hl0 hl1]].

    apply hinhpr.
    exists _, _, Rf.
    split.
    * exact (nwfs_Rf_is_R_map n f).
    (* 
         λf       l
      A ---> Kf ----> A
      |       |       |
    f |       | ρf    | f
      v       v       v
      B ===== B ===== B
    *)
    * use make_retract.
      + exact Lf.
      + exact l.
      + exact (identity _).
      + exact (identity _).
      + use make_is_retract.
        -- exact hl0.
        -- now rewrite id_left.
        -- rewrite id_right.
           exact (LR_compatibility n f).
        -- rewrite id_right.
           exact hl1.
Qed.

Lemma nwfs_is_wfs {C : category} (n : nwfs C) : wfs C.
Proof.
  use make_wfs.
  - exact ((nwfs_L_maps_class n)^cl).
  - exact ((nwfs_R_maps_class n)^cl).
  - use make_is_wfs.
    * apply morphism_class_subset_antisymm.
      + exact (nwfs_L_maps_cl_subs_llp_R_maps_cl _).
      + exact (nwfs_llp_R_maps_cl_subs_L_maps_cl _).
    * apply morphism_class_subset_antisymm.
      + exact (nwfs_R_maps_cl_subs_rlp_L_maps_cl _).
      + exact (nwfs_rlp_L_maps_cl_subs_R_maps_cl _).
    * intros x y f.
      apply hinhpr.

      set (fact := n f).
      set (f01 := three_mor01 fact).
      set (f12 := three_mor12 fact).
      cbn in f01, f12.

      exists (three_ob1 fact), f01, f12.

      repeat split.
      + apply in_morcls_retc_if_in_morcls.
        exact (nwfs_Lf_is_L_map n (three_mor02 fact)).
      + apply in_morcls_retc_if_in_morcls.
        exact (nwfs_Rf_is_R_map n (three_mor02 fact)).
      + exact (three_comp fact).
Defined.
