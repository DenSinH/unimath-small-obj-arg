Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

From Model Require Import morphism_class retract.
From Model.model Require Import wfs weak_equivalences.

Section modelcat.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.

Record is_model_category {M : category} (W C F : morphism_class M) := {
    weq : is_weak_equivalences W;
    caf : is_wfs C (F ∩ W);
    acf : is_wfs (C ∩ W) F;
}.

Lemma is_model_category_mk' {M : category} {W C AF AC F : morphism_class M}
    (weq : is_weak_equivalences W)
    (caf : is_wfs C AF) (acf : is_wfs AC F)
    (hAF : AF = F ∩ W) (hAC : AC ⊆ W) :
    is_model_category W C F.
Proof.
  split.
  - assumption. (* W are still the weak equivalences *)
  - rewrite hAF in caf. (* C and AF = F ∩ W is a WFS by assumption (caf) *)
    assumption.
  - (* suffices to show C ∩ W ⊆ AC *)
    enough (C ∩ W ⊆ AC) as cw_sac.
    {
      (* since then C ∩ W = AC *)
      assert (C ∩ W = AC) as cw_ac.
      {
        (* only need to show other inclusion *)
        apply (morphism_class_subset_antisymm cw_sac).
        (* take f ∈ AC *)
        intros a b f hf.
        split.
        - (* AC = llp F *)
          rewrite (acf.(wfs_llp _ _)) in hf.
          (* C = llp AF *)
          rewrite (caf.(wfs_llp _ _)).
          (* so now goal is llp F ⊆ llp AF *)
          revert a b f hf.
          (* use antisymmetry of llp to convert goal into AF ⊆ F *)
          apply llp_anti.
          intros x y g hg.
          (* this is trivial, since AF = F ∩ W, but requires some work in UniMath *)
          rewrite hAF in hg.
          destruct hg as [hgf ?].
          exact hgf.
        - (* f ∈ AC ⊆ W (by hAC) *)
          exact (hAC _ _ _ hf).
      }
      (* C ∩ W = AC and F are a WFS by assumption (acf) *)
      rewrite cw_ac.
      exact acf.
    }
    {
      (* we show that indeed, C ∩ W ⊆ AC *)
      intros a b f hf.
      destruct hf as [f_c f_w].

      (* factorize f through c, g : a --> c ∈ AC, h : c --> b ∈ F *)
      unshelve eapply (hinhuniv _ (acf.(wfs_fact _ _) _ _ f)).
      intro H.
      destruct H as [c [g [h [g_ac [h_f gh]]]]].

      (* h ∈ W by 2 out of 3 property (h ∘ g = f) *)
      assert (h_w : (W _ _) h).
      {
        (* g ∈ AC ⊆ W *)
        specialize (hAC _ _ _ g_ac) as g_w.
        apply (weq.(weq_cancel_left _) _ _ _ _ _ g_w).
        rewrite gh.
        exact f_w.
      }
      
      (* h ∈ AF because AF = F ∩ W and h ∈ F by definition *)
      assert (h_af : (AF _ _) h).
      {
         rewrite hAF.
         split.
         - exact h_f.
         - exact h_w.
      }
      
      (* extract lift l from
            g
        a ----> c
        | l   / |
      f |   /   | h
        v /     v
        b ===== b
      *)
      specialize (is_wfs'lp caf f_c h_af g (identity b)) as test.
      unshelve epose proof (test _) as H.
      {
        (* commutativity of diagram *)
        rewrite id_right.
        exact gh.
      }

      (* todo: this really needs to be cleaner *)
      unshelve eapply (hinhuniv _ H).
      intro H1.
      destruct H1 as [l [hl1 hl2]].

      (* this uses the retract argument
        a ===== a ===== a
        |       |       |
      f |       | g     | f
        v       v       v
        b ----> c ----> b
            l       h
        to show that f is a retract of g
      *)
      assert (r : retract g f).
      {
        split with (identity a) (identity a) l h.
        - now rewrite id_left.
        - assumption.
        - rewrite id_left. now symmetry.
        - rewrite id_left. now symmetry.
      }

      (* so since g ∈ AC in a WFS acf = (AC, F), so must f be *)
      exact (is_wfs'retract acf r g_ac).
    }
Defined.


End modelcat.