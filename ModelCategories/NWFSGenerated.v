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
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.pushouts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.

Require Import CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import CategoryTheory.DisplayedCats.Examples.Three.
Require Import CategoryTheory.ModelCategories.MorphismClass.
Require Import CategoryTheory.ModelCategories.Retract.
Require Import CategoryTheory.ModelCategories.Lifting.
Require Import CategoryTheory.ModelCategories.NWFS.
Require Import CategoryTheory.ModelCategories.NWFSisWFS.

Require Import CategoryTheory.DisplayedCats.algebras.
Require Import CategoryTheory.limits.coproducts.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.
Local Open Scope morcls.

Context {C : category}.

(* 
Definition morcls_disp : disp_cat (arrow C).
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ g, J _ _ g).
  - intros g g' d d' m.
    (* todo: only identity maps, unit gives all maps *)
    
    exact (∑ (H : g = g'), m = transportf _ H (identity _)).
  - intros.
    simpl in *.
    apply isaproptotal2.
    * intro. admit.
    * intros.
      admit.
  - intros.

  - intros.
    exact tt.
Defined.
*)

Definition morcls_disp (J : morphism_class C) : disp_cat (arrow C) :=
    disp_full_sub (arrow C) (λ g, J _ _ g).

Definition right_lifting_data (J : morphism_class C) (g : arrow C) : UU :=
    ∏ (f : arrow C), (J _ _ (arrow_mor f)) -> elp f g.

Lemma right_lifting_data_retract (J : morphism_class C) {g g' : arrow C}
    (Rgg' : retract g g') : 
  right_lifting_data J g -> right_lifting_data J g'.
Proof.
  intros rldJg f Jf.
  apply (elp_of_retracts (retract_self f) (Rgg')).
  exact (rldJg f Jf).
Defined.

(* filler lifting problem f --> g commutes with mn and the filler of
   f --> g --> g' in the right way *)
Definition right_lifting_data_comp {J : morphism_class C} {g g' : arrow C}
    (δ : right_lifting_data J g) (δ' : right_lifting_data J g') (mn : g --> g') : UU :=
  ∏ (f : arrow C) (H : J _ _ (arrow_mor f)) (S : f --> g),
  (filler_map (δ f H _ _ (arrow_mor_comm S))) · (arrow_mor00 mn) = 
    filler_map (δ' f H _ _ (arrow_mor_comm (S · mn))).

Lemma isaprop_lifting_data_comp {J : morphism_class C} {g g'} 
    (δ : right_lifting_data J g) (δ' : right_lifting_data J g') (mn : g --> g') :
  isaprop (right_lifting_data_comp δ δ' mn).
Proof.
  do 3 (apply impred; intro).
  apply homset_property.
Qed.

Definition rlp_morcls_disp (J : morphism_class C) : disp_cat (arrow C).
Proof.
  use disp_cat_from_SIP_data.
  - exact (λ g, right_lifting_data J g).
  - intros g g' δ δ' mn. 
    simpl in *.

    (* commutativity of lifting data:
       solution of lifting problem S must commute with mn: g --> g':
                   m
       a ----> x ----> x'
       |       |       |
     f |  S   g|       |
       v       v       v
       b ----> y ----> y'
                   n
      δ : b --> x
      δ': b --> x'
    *)
    exact (right_lifting_data_comp δ δ' mn).
  - (* propositional morphism data *)
    intros.
    apply isaprop_lifting_data_comp.
  - (* identity *)
    intros x a f H S.
    do 2 rewrite id_right.
    reflexivity.
  - (* associativity *)
    intros g g' g'' δ δ' δ'' S0 S1 mn mn' g2 g2' S2.
    
    (* associativity of taking the 00 morphism of an arrow morphism *)
    assert (arrow_mor00 (S0 · S1) = arrow_mor00 S0 · arrow_mor00 S1) as X.
    {
      trivial.
    }
    rewrite X, assoc.
    rewrite mn, mn', assoc.
    reflexivity.
Defined.

Definition rlp_morcls (J : morphism_class C) : category := 
    total_category (rlp_morcls_disp J).

(* needed later *)
(* all lifting problems of J wrt. g *)
Definition morcls_lp (J : morphism_class C) (g : arrow C) : UU :=
    ∑ (f : total_category (morcls_disp J)), (pr1 f) --> g.

Context (n : nwfs C).
Definition morcls_L_map_structure (J : morphism_class C) : UU := 
  disp_functor (functor_identity _) (op_disp_cat (morcls_disp J)) (nwfs_L_maps n).

Context {J : morphism_class C}.

Definition R_map_rlp_morcls_structure_on_objects (η : morcls_L_map_structure J) : 
    ∏ x, (nwfs_R_maps n) x -> (rlp_morcls_disp J) ((functor_identity _) x).
Proof.
  (* map on displayed objects (send arrow to itself, with lifting data) *)
  intros f Rf.
  intros g hg h k S.

  (* add structure to f through η *)
  unfold morcls_L_map_structure in η.
  set (Lg := η g hg).
  
  intros.
  (* since η lies over (identity _), 
     Lg is actually just g (with structure), and it is an L-Map
     the filler follows from the fact that NWFS L-Maps and R-Maps
     form a WFS *)
  apply (L_map_R_map_elp Lg Rf).
Defined.

Definition R_map_rlp_morcls_structure_on_displayed_mors (η : morcls_L_map_structure J) : 
    ∏ x y (xx : (nwfs_R_maps n) x) (yy : (nwfs_R_maps n) y) (f : x --> y),
      (xx -->[f] yy) -> (R_map_rlp_morcls_structure_on_objects η _ xx -->[ f ] R_map_rlp_morcls_structure_on_objects η _ yy).
Proof.
  (* map on displayed objects respects morphism property *)
  intros f f' ff ff' S Sisalg g Jg Sgf.
  unfold morcls_L_map_structure in η.
  simpl.

  unfold three_mor11.
  simpl.
  (* cancel precomposition with  
    pr211 η g Jg := Lift of g vs ρg (map from cod g --> three_ob1 (n g)) *)
  do 3 rewrite assoc'.
  apply cancel_precomposition.

  (* cancel precomposition with 
    three_mor11 (#n Sgf)*)
  apply pathsinv0.
  etrans. apply maponpaths_2, maponpaths.
          apply (section_disp_comp (nwfs_fact n)).
  simpl.

  rewrite assoc'.
  apply cancel_precomposition.

  destruct ff as [αf αflaws].
  destruct ff' as [αf' αf'laws].
  set (S11 := three_mor11 ((# n)%Cat S)).
  change (S11 · arrow_mor00 αf' = arrow_mor00 αf · arrow_mor00 S).

  (*         S00
      ++++> +++++>
    |      |      |
    |   λf |      |λf'
    |      v S11  v
  ρf | αf    +++++> +++++++>
    |      |      |        |
    |   ρf |      |ρf' αf' | f'
    v      v      v        v
      ===== -----> ========
            S22
  Need to show that the +++> maps are equal
  This follows from the fact that S is an algebra map (Sisalg)
  *)

  simpl in Sisalg.
  unfold is_Algebra_mor in Sisalg.
  set (top_line := dirprod_pr1 (pathsdirprodweq (base_paths _ _ Sisalg))).
  simpl in top_line.
  exact (pathsinv0 top_line).
Qed.


(* "this assignation extends to a functor θ: R-Map ⟶ J□", Garner 2007, p18 *)
Definition R_map_rlp_morcls_structure_data (η : morcls_L_map_structure J) : 
    disp_functor_data (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp J) :=
  (R_map_rlp_morcls_structure_on_objects η,, R_map_rlp_morcls_structure_on_displayed_mors η).

Definition R_map_rlp_morcls_structure_axioms (η : morcls_L_map_structure J) :
    disp_functor_axioms (R_map_rlp_morcls_structure_data η).
Proof.
  unfold disp_functor_axioms.
  split; intros; apply isaprop_lifting_data_comp.
Qed.

Definition R_map_rlp_morcls_structure (η : morcls_L_map_structure J) : 
    disp_functor (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp J) :=
  (_,, R_map_rlp_morcls_structure_axioms η).

(* Garner 2008, Definition 3.9 / Garner 2007, p18*)
(* we say that n := (L, R, Δ) is cofibrantly generated by (J, η) if θ is
   an isomorphism of categories *)
Definition cofibrantly_generated (η : morcls_L_map_structure J) :=
    is_catiso (total_functor (R_map_rlp_morcls_structure η)).

Definition algebraically_free : UU :=
    ∑ η : morcls_L_map_structure J, cofibrantly_generated η.


(* Garner 2008, Proposition 3.12 / Garner 2007, p18 *)
Lemma algebraically_free_nwfs_gives_cofibrantly_generated_wfs :
  algebraically_free -> 
    (nwfs_R_maps_class n)^cl = λ x y f, ∥rlp_morcls_disp J f∥.
Proof.
intro H.
destruct H as [η cofibη].
unfold cofibrantly_generated in cofibη.
set (θ := (_,, cofibη) : catiso _ _).

(* suffices to show R = J□ *)
apply morcls_eq_impl_morcls_cl_eq.
{
  (* J□ is closed under retracts *)
  intros x' y' g' x y g Hg.
  destruct Hg as [Jg Rgg'].
  use (hinhuniv _ Jg).
  clear Jg; intro Jg.

  apply hinhpr.
  intros f Jf.
  simpl in Jg.
  apply (@right_lifting_data_retract J g g').
  - exact Rgg'.
  - exact Jg.
  - exact Jf.
}

apply morphism_class_subset_antisymm; 
  intros x y f Hf;
  use (hinhuniv _ Hf);
  clear Hf; intro Hf;
  apply hinhpr.
- (* R-Map ⊆ J□ *)
  (* θ is a functor that lies over identity *)
  set (θf := θ (mor_to_arrow_ob f,, Hf)).
  assert (Hθf : mor_to_arrow_ob f = pr1 θf).
  {
    reflexivity.
  }
  rewrite Hθf.
  exact (pr2 θf).
- (* J□ ⊆ R-Map *)
  (* the inverse of θ also lies over identity *)
  set (ftot := (mor_to_arrow_ob f,, Hf) : total_category (rlp_morcls_disp J)).
  set (θinvf := (inv_catiso θ) ftot).
  (* set (test := fully_faithful_inv_hom (pr12 θ) ). *)

  assert (Hθinvf : mor_to_arrow_ob f = pr1 θinvf).
  {
    apply isotoid.
    - apply is_univalent_total_category.
      * admit.
      * admit.
    - use make_z_iso.
      * admit.
      * admit.
      * admit.
  }
  rewrite Hθinvf.
  exact (pr2 θinvf).
Admitted.


(* Garner 2007, p19 *)

Section lifting_with_J.
Context (g : arrow C) (CC : Coproducts (morcls_lp J g) C) (POs : Pushouts C).

Definition morcls_lp_dom_coprod :=
  CC (λ (f : morcls_lp J g), arrow_dom (pr11 f)).
Definition morcls_lp_cod_coprod :=
  CC (λ (f : morcls_lp J g), arrow_cod (pr11 f)).

Definition morcls_lp_coprod :=
 (CoproductOfArrows' _ _ 
   morcls_lp_dom_coprod morcls_lp_cod_coprod
   (λ (f : morcls_lp J g), arrow_mor (pr11 f))).

(* the canonical diagram capturing all lifting problems in J *)
Definition morcls_lp_coprod_diagram : morcls_lp_coprod --> g.
Proof.
  use tpair.
  - split.
    * exact (CoproductArrow _ _ (morcls_lp_dom_coprod) (λ j, arrow_mor00 (pr2 j))).
    * exact (CoproductArrow _ _ (morcls_lp_cod_coprod) (λ j, arrow_mor11 (pr2 j))).
  - abstract (
      unfold morcls_lp_coprod;
      simpl;
      rewrite postcompWithCoproductArrow;
      rewrite precompWithCoproductArrow;
      apply maponpaths;
      apply funextsec;
      intro j;
      exact (arrow_mor_comm (pr2 j))
    ).
Defined.

(* It is possible to show this more generally for _any_
   coproduct of maps in J, but this is not really necessary or useful
   for us.
   
   The proof of this lemma is practically the same as that of 
   wfs_closed_coproducts, but we do _not_ need the axiom of choice here,
   since we know the actual lifting data. *)
Lemma lifting_data_impl_lifting_coprod_lp : 
  right_lifting_data J g -> elp (morcls_lp_coprod) g.
Proof.
  intro rldJg.
  intros h k S.

  set (hj := λ (j : morcls_lp J g), (CoproductIn _ _ _ j) · h).
  set (kj := λ (j : morcls_lp J g), (CoproductIn _ _ _ j) · k).

  (* fill-in for each square *)
  assert (∏ (j : morcls_lp J g), ∑ lj, ((pr11 j) · lj = hj j) × (lj · g = kj j)) as jlift.
  { 
    intro j.
    (* use lifting data of j with respect to g *)
    use (rldJg (pr11 j) (pr21 j)).
    unfold hj, kj.
    rewrite <- assoc.
    etrans. apply maponpaths. exact S.
    rewrite assoc, assoc.
    etrans. apply maponpaths_2.
    unfold morcls_lp_coprod.
    exact (CoproductOfArrows'In _ _ _ _ _ j).
    reflexivity.
  }

  set (jlifts := foralltototal _ _ jlift).
  destruct jlifts as [lj hlj].
  set (hl := isCoproduct_Coproduct _ _ (morcls_lp_cod_coprod) _ lj).
  destruct hl as [[l hl] uniqueness].
  
  exists l.
  split; rewrite CoproductArrowEta, (CoproductArrowEta _ _ _ _ _ l).
  - (* factor f as well *)
    unfold morcls_lp_coprod.
    rewrite (precompWithCoproductArrow).

    (* maps are equal if maps through coproduct are equal *)
    apply CoproductArrowUnique.

    (* now we can reason in separate diagrams again *)
    intro j.
    rewrite (CoproductInCommutes _ _ _ (morcls_lp_dom_coprod)).

    (* this is basically exactly the relation we want to prove: *)
    destruct (hlj j) as [hljcomm _].

    (* by definition *)
    change (CoproductIn _ _ _ _ · h) with (hj j).
    rewrite (hl j).
    exact hljcomm.
  - (* factor through coproduct object *)
    apply CoproductArrowUnique.

    (* reason about separate diagrams again *)
    intro j.
    rewrite assoc.
    rewrite (CoproductInCommutes _ _ _ (morcls_lp_cod_coprod)).

    (* the relation we want to prove *)
    destruct (hlj j) as [_ kljcomm].

    (* by definition *)
    change (CoproductIn _ _ _ _ · k) with (kj j).
    rewrite (hl j).
    exact kljcomm.
Qed.

(* we need the actual diagram for the other direction 
   (this does not hold for just any coproduct) *)
Lemma lifting_coprod_lp_impl_lifting_data : 
  filler (arrow_mor_comm (morcls_lp_coprod_diagram)) ->
      right_lifting_data J g.
Proof.
  intro l.
  intros f Jf h k H.

  (* obtain maps in total diagram *)
  destruct l as [ltot [Hl1 Hl2]].
  simpl in Hl1, Hl2, ltot.

  (* The lift we are looking for is formed using the  
     inclusion of arrow_cod f into the coproduct of all domains *)
  set (Jtot := total_category (morcls_disp J)).

    (* f as object of the total category of the morphism class J *)
  set (f' := (f,, Jf) : Jtot).
    (* H as lifting problem J --> g *)
  set (Hlp := (f',, (make_dirprod h k,, H)) : morcls_lp J g).
    (* inclusion of arrow_cod/dom f into coproduct of all domains *)
  set (codf_in := (CoproductIn _ _ (morcls_lp_cod_coprod) Hlp)).
  set (domf_in := (CoproductIn _ _ (morcls_lp_dom_coprod) Hlp)).

  exists (codf_in · ltot).
  split.
  - (* h = (inclusion of arrow_dom f) · (top morphism of canonical diagram) *)
    assert (h = domf_in · (arrow_mor00 (morcls_lp_coprod_diagram))) as Hh.
    {
      unfold domf_in.
      symmetry.
      
      exact (
          CoproductInCommutes _ _ _ 
          (morcls_lp_dom_coprod) 
          _ _ Hlp
      ).
    }
    rewrite Hh.

    (* commutativity of f with inclusions of domain / codomain *)
    assert (f · codf_in = domf_in · (morcls_lp_coprod)) as Hf.
    {
      unfold codf_in, domf_in, morcls_lp_coprod.
      rewrite (CoproductOfArrows'In _ _ (morcls_lp_dom_coprod)).
      reflexivity.
    }
    rewrite assoc.
    etrans. apply maponpaths_2.
            exact Hf.
    rewrite <- assoc.
    now rewrite Hl1.
  - rewrite <- assoc.
    etrans. apply maponpaths.
            exact Hl2.

    apply pathsinv0.

    (* k = codf_in · kj *)
    unfold codf_in.
    symmetry.
    exact (
        CoproductInCommutes _ _ _ 
        (morcls_lp_cod_coprod) 
        _ _ Hlp
    ).
Qed.

Lemma lifting_data_Jg_iff_lifting_coprod_lp : 
    filler (arrow_mor_comm (morcls_lp_coprod_diagram)) <->
      right_lifting_data J g.
Proof.
  split.
  - apply lifting_coprod_lp_impl_lifting_data.
  - intro rldJg.
    apply lifting_data_impl_lifting_coprod_lp.
    exact rldJg.
Qed.

(*
We turn the diagram
          h_x
    ∑A_x ----> C
     |         |
∑f_x |         | g
     v         v
    ∑B_x ----> D
          k_x

into the pushout diagram
         h_x
    ∑A_x ----> C--\ 
     |         |  |
∑f_x |     λ1g |  \
     v         v   |
    ∑B_x ---> E1g  | id · g
      \__       \  |
         \_   ρ1g|
      k_x  \_____ \|
                   D
using the pushout property. Inserting an identity morphism gives a diagram
          h_x
    ∑A_x ----> C ====== C
     |         |        |
∑f_x |         | λ1g    |
     v         v        v
    ∑B_x ---> E1g ----> D  ~~> k_x
                   ρ1g
*)

Definition morcls_lp_coprod_diagram_pushout :
    Pushout (morcls_lp_coprod) (arrow_mor00 morcls_lp_coprod_diagram) :=
  POs _ _ _ (morcls_lp_coprod) (arrow_mor00 morcls_lp_coprod_diagram).

Definition E1 : C :=
  PushoutObject morcls_lp_coprod_diagram_pushout.
Definition λ1 : (arrow_dom g) --> E1 :=
  PushoutIn2 morcls_lp_coprod_diagram_pushout.
Definition ρ1 : E1 --> (arrow_cod g) :=
  PushoutArrow 
    morcls_lp_coprod_diagram_pushout
    _ (arrow_mor11 morcls_lp_coprod_diagram)
    g (pathsinv0 (arrow_mor_comm morcls_lp_coprod_diagram)).

(*
    C ===== C
    |       |
 λ1g|       | g
    v       v
   E1g ---> D
       ρ1g
*)
Definition morcls_lp_coprod_diagram_red : λ1 --> g.
Proof.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact ρ1.
  - abstract (
      rewrite id_left;
      symmetry;
      use PushoutArrow_PushoutIn2
    ).
Defined.

(* Lifting w.r.t. the coproduct diagram of J is the same as lifting
   w.r.t. this reduced diagram (follows from pushout properties) *)
Lemma lifting_coprod_lp_red_impl_lifting_coprod_lp :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)) ->
  filler (arrow_mor_comm (morcls_lp_coprod_diagram)).
Proof.
  intro H.
  destruct H as [l [Hl1 Hl2]].
  simpl in Hl1, Hl2.
  exists ((PushoutIn1 morcls_lp_coprod_diagram_pushout) · l).
  split; simpl.
  - (* ∑fx · (PushoutIn1 · l) = ∑hx *)
    rewrite assoc.
    rewrite (PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout)).
    
    (* ∑hx · λ1g · l = ∑hx *)
    rewrite <- assoc.
    etrans. apply maponpaths. exact Hl1.
    now rewrite id_right.
  - (* (PushoutIn1 · l) · g = ∑kx *)
    rewrite <- assoc.
    etrans. apply maponpaths. exact Hl2.
    
    (* PushoutIn1 · ρ1g = ∑kx *)
    use PushoutArrow_PushoutIn1.
Qed.

Lemma lifting_coprod_lp_impl_lifting_coprod_lp_red :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram)) ->
  filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)).
Proof.
  intro H.
  destruct H as [l [Hl1 Hl2]].
  simpl in Hl1, Hl2.
  
  (* commutativity of f · l = ∑hx · id *)
  assert (H : morcls_lp_coprod · l = 
            arrow_mor00 morcls_lp_coprod_diagram · identity (pr11 g)).
  {
    rewrite id_right.
    exact Hl1.
  }

  (* obtain lift using pushout property on lift *)
  set (lred := PushoutArrow 
                  morcls_lp_coprod_diagram_pushout
                  _ l (identity _) H).
  exists lred.
  split.
  - (* λ1g · lred = identity *)
    apply PushoutArrow_PushoutIn2.
  - (* lred · g = ρ1g *)
    simpl.
    use PushoutArrowUnique; simpl.
    * (* PushoutIn1 · (lred · g) = ∑kx*)
      rewrite assoc.
      etrans. apply maponpaths_2.
      exact (PushoutArrow_PushoutIn1 _ _ _ _ _).
      exact Hl2.
    * (* PushoutIn2 · (lred · g) = g*)
      rewrite assoc.
      etrans. apply maponpaths_2.
      exact (PushoutArrow_PushoutIn2 _ _ _ _ _).
      now rewrite id_left.
Qed.

(* almost proposition 12 in Garner, 2007 *)
Lemma lifting_coprod_lp_iff_lifting_coprod_lp_red :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram)) <->
  filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)).
Proof.
  split.
  - exact lifting_coprod_lp_impl_lifting_coprod_lp_red.
  - exact lifting_coprod_lp_red_impl_lifting_coprod_lp.
Qed.

End lifting_with_J.

Section one_step_monad.

Context (CC : ∏ (g : arrow C), Coproducts (morcls_lp J g) C) (POs : Pushouts C).

(* Garner 2008, section 5.2 (functor K) *)
Definition morcls_coprod_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - (* sending g to ∑_{x ∈ S_g} f_x*)
    intro g.
    exact (morcls_lp_coprod g (CC g)).
  - (* map γ: g --> g' gives map of lifting problems *)
    intros g g' γ.
    use mors_to_arrow_mor.
    * use CoproductOfArrowsInclusion.
      + (* inclusion of lifting problems S_g into S_g' with γ *)
        intro lpJg.
        destruct lpJg as [f S].  
        exists f.
        exact (S · γ).
      + (* map from lifting problem of S_g's left hand domain into that of S_g'
           The lifting problems have the same domain on the left, as f is the
           same. *)
        intro. exact (identity _).
    * use CoproductOfArrowsInclusion.
      + (* the same map here *)
        intro lpJg.
        destruct lpJg as [f S].  
        exists f.
        exact (S · γ).
      + intro. exact (identity _).
    * (* commutativity of coproduct arrow inclusion with
         ∑_{x∈S_g} f_x and ∑_{x∈S_g'} f_x *)
      abstract (
        simpl;
        unfold morcls_lp_coprod;
        simpl;
        etrans; [use CoproductOfArrowsInclusion_comp|];
        apply pathsinv0;
        etrans; [use CoproductOfArrowsInclusion_comp|];
        simpl;
        (* equality of coproduct of arrows *)
        apply maponpaths;
        apply funextsec;
        intro;
        etrans; [apply id_right|];
        apply pathsinv0;
        etrans; [apply id_left|];
        reflexivity
      ).
Defined.

(* todo: not sure this is possible, BUT, we don't really use
   the functorial properties of this map, just its definition. *)
Definition morcls_coprod_functor_is_functor : is_functor morcls_coprod_functor_data.
Proof.
  split.
  - intro g.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; simpl; apply pathsinv0, Coproduct_endo_is_identity; intro.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_dom_coprod g (CC g))).
      simpl.
      etrans. apply id_left.
      assert (H : (pr1 i,, (pr2 i · identity _)) = i).
      {
        rewrite id_right.
        reflexivity.
      }
      rewrite <- (@CoproductIn_idtoiso _ _ _ _ _ _ H).
      apply pathsinv0.
      rewrite <- (id_left _).
      apply cancel_postcomposition.
      (* todo: need univalence requirement here? *)
      admit.
    * etrans.
      apply (CoproductOfArrowsInclusionIn _ (morcls_lp_cod_coprod  g (CC g))).
      simpl.
      etrans. apply id_left.
      (* todo: why does maponpaths not work here? *)
      admit.
  - intros f g h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod; simpl; apply pathsinv0.
    * etrans. use CoproductOfArrowsInclusion_comp.
      simpl.
      etrans. apply maponpaths.
      apply funextsec.
      intro.
      apply id_right.

      apply CoproductArrowUnique.
      intro.
      etrans. use (CoproductOfArrowsInclusionIn _ _ _ _ i).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      (* again up to idtoiso? CoproductIn_idtoiso *)
      (* todo: why does maponpaths not work here? *)
      admit.
    * etrans. use CoproductOfArrowsInclusion_comp.
      simpl.
      etrans. apply maponpaths.
      apply funextsec.
      intro.
      apply id_right.
      (* CopOfArrIncl (... i · S · T) (mlp_cod_cop f) (mlp_cod_cop h) (x -> identity x) =
         CopOfArrIncl (... i · (S · T)) (mlp_cod_cop f) (mlp_cod_cop h) (x -> identity x)
      *)
      (*
      unfold morcls_lp_cod_coprod.
      need version of maponpaths_4 which works with dependent types in arguments.
      *)
      apply CoproductArrowUnique.
      intro.
      etrans. use (CoproductOfArrowsInclusionIn _ _ _ _ i).
      etrans. apply id_left.
      apply pathsinv0.
      etrans. apply id_left.
      (* can't use maponpaths because function is dependent here:
         ∏ (i : morcls_lp J h), <type dependent on i> *)
      admit.
Admitted.

(* K in Garner *)
Definition morcls_coprod_functor : functor (arrow C) (arrow C) :=
    (_,, morcls_coprod_functor_is_functor).

Definition morcls_coprod_nat_trans_data : nat_trans_data morcls_coprod_functor (functor_identity _).
Proof.
  intro g.
  exact (morcls_lp_coprod_diagram g (CC g)).
Defined.

Definition morcls_coprod_nat_trans_is_nat_trans : is_nat_trans _ _ morcls_coprod_nat_trans_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod; simpl.
  - etrans.
    use precompWithCoproductArrowInclusion.
    simpl.
    rewrite postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    etrans. apply id_left.
    reflexivity.
  - etrans.
    use precompWithCoproductArrowInclusion.
    simpl.
    rewrite postcompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro i.
    etrans. apply id_left.
    reflexivity.
Qed.

(* φ in Garner 2007, p23 *)
Definition morcls_coprod_nat_trans : nat_trans morcls_coprod_functor (functor_identity _) :=
    (_,, morcls_coprod_nat_trans_is_nat_trans).

Arguments CoproductObject {_} {_} {_}.
Lemma commuting_cube_construction {g g' : arrow C}
    {aa : CoproductObject (morcls_lp_dom_coprod _ (CC g)) 
          --> CoproductObject (morcls_lp_dom_coprod _ (CC g'))}
    {bb : CoproductObject (morcls_lp_cod_coprod _ (CC g)) 
          --> CoproductObject (morcls_lp_cod_coprod _ (CC g'))}
    {cc : arrow_dom g --> arrow_dom g'}
    (leftface : (morcls_coprod_functor g) · bb = aa · (morcls_coprod_functor g'))
    (topface  : arrow_mor00 (morcls_lp_coprod_diagram g (CC _)) · cc = 
                aa · arrow_mor00 (morcls_lp_coprod_diagram g' (CC _))) :
  E1 g (CC _) POs --> E1 g' (CC _) POs.
Proof.
  (* The map induced by pushouts on the front and back face
     (only the front face is drawn)
          ∑h
      ∑A ------> C
       |\ aa       \  cc
  ∑f=Kg|  \     ∑h'  \
       |    ∑A' -----> C
       v    |
      ∑B    |Kg'       |
        \   |=     PO    λ1g'
      bb  \ v∑f'       v
           ∑B' - - - > E1g'
  *)
  set (CE1g' := cc · (λ1 g' (CC g') POs)).
  set (BE1g' := bb · (PushoutIn1 (morcls_lp_coprod_diagram_pushout g' (CC g') POs))).

  use (PushoutArrow 
       (morcls_lp_coprod_diagram_pushout g (CC g) POs)
       _ BE1g' CE1g').
  
  abstract (
    (* Left to show commutativity of (outer) pushout diagram *)
    (* Kg · (arrow_mor11 Kγ) · (PushoutIn1 g') = (PushoutIn g) · γ00 · λ1g *)
    unfold CE1g', BE1g';
    do 2 rewrite assoc;

    (* first rewrite commutativity of left face *)
    etrans; [apply maponpaths_2; exact leftface|];
    
    (* rewrite commutativity in top face *)
    apply pathsinv0;
    etrans; [apply maponpaths_2; exact topface|];

    (* cancel precomposition with aa: ∑A --> ∑A' arrow *)
    do 2 rewrite <- assoc;
    apply cancel_precomposition;

    (* all that's left is commutativity in the pushout square of g' *)
    apply pathsinv0;
    exact (PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout g' (CC g') POs))
  ).
Defined.


(* one step comonad functor L1 sends g to λ1g *)
Definition one_step_comonad_functor_data : functor_data (arrow C) (arrow C).
Proof.
  use make_functor_data.
  - intro g.
    exact (λ1 g (CC g) POs).
  - intros g g' γ.
    (* The map on morphisms becomes the right face from the cube induced by
          ∑h
      ∑A ------> C
       |\          \  γ00
  ∑f=Kg|  \     ∑h'  \
       |    ∑A' -----> C
       v Kγ |
      ∑B    |Kg'       |
        \   |=     PO    λ1g'
          \ v∑f'       v
           ∑B' - - - > E1g'
    *)
    (* the morphism E1g --> E1g' we will need arises from the pushout
         property with the following maps. *)
    set (Kγ := (#morcls_coprod_functor)%cat γ).
    set (φγ := nat_trans_ax morcls_coprod_nat_trans g g' γ).
    set (φγ00 := dirprod_pr1 (pathsdirprodweq (base_paths _ _ φγ))).

    use mors_to_arrow_mor.
    * exact (arrow_mor00 γ).
    * use commuting_cube_construction.
      + exact (arrow_mor00 Kγ).
      + exact (arrow_mor11 Kγ).
      + exact (arrow_mor00 γ).
      + abstract (exact (pathsinv0 (arrow_mor_comm Kγ))).
      + abstract (exact (pathsinv0 φγ00)).
    * (* commutativity of right face *)
      (* γ00 · λ1g' = λ1g · ccc *)
      (* This follows simply from the properties of a pushout *)
      abstract (
        apply pathsinv0;
        etrans; [use PushoutArrow_PushoutIn2|];
        reflexivity
      ).
Defined.

Definition one_step_comonad_functor_is_functor : is_functor one_step_comonad_functor_data.
Proof.
  split.
  - intro g.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * (* top map is identity simply because it comes from a functor *)
      reflexivity.
    * (* bottom map is identity because the pushout arrow is unique *)
      apply pathsinv0, PushoutArrowUnique.
      + now rewrite id_right, functor_id, id_left.
      + now rewrite id_right, id_left.
  - intros f g h S T.
    apply subtypePath; [intro; apply homset_property|].
    apply pathsdirprod.
    * reflexivity.
    * apply pathsinv0, PushoutArrowUnique.
      (* simplifying gives big ugly terms
         Gotta keep in mind that (# one_step_comonad_functor_data) S 
         is a PushoutArrow and we can then use pushout properties. *)
      + rewrite functor_comp.
        (* PushoutIn1 · (PushoutArrow · PushoutArrow) = arrow_mor11 · PushoutIn *)
        rewrite assoc.
        etrans. apply maponpaths_2.
        use PushoutArrow_PushoutIn1.
        rewrite <- assoc.
        etrans. apply maponpaths.
        use PushoutArrow_PushoutIn1.
        rewrite assoc.
        reflexivity.
      + (* PushoutIn2 (PushoutArrow · PushoutArrow) = arrow_mor00 (S T) · PushoutIn *)
        rewrite assoc.
        etrans. apply maponpaths_2.
        use PushoutArrow_PushoutIn2.
        rewrite <- assoc.
        etrans. apply maponpaths.
        use PushoutArrow_PushoutIn2.
        rewrite assoc.
        reflexivity.
Qed.

Definition one_step_comonad_functor : functor (arrow C) (arrow C) :=
    (_,, one_step_comonad_functor_is_functor).

Definition one_step_comonad_counit_data : nat_trans_data (one_step_comonad_functor) (functor_identity _).
Proof.
  (* Send λ1 g --> g along
      C ====== C
      |        |
  λ1g |        | g
      v        v
    E1g ----> D
          ρ1g
  *)
  intro g.
  use mors_to_arrow_mor.
  - exact (identity _).
  - exact (ρ1 g (CC g) POs).
  - abstract (exact (arrow_mor_comm (morcls_lp_coprod_diagram_red g (CC g) POs))).
Defined.

Definition one_step_comonad_counit_is_nat_trans : is_nat_trans _ _ one_step_comonad_counit_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - simpl.
    now rewrite id_left, id_right.
  - (* PushoutArrow (morcls_lp_coprod_diagram_pushout g (CC g) POs) ...
       · ρ1g' = ρ1g · γ11 *)
    (* We are trying to prove an equality of maps E1g --> arrow_cod g' *)
    use (MorphismsOutofPushoutEqual 
          (isPushout_Pushout (morcls_lp_coprod_diagram_pushout g (CC g) POs))).
    * (* todo: see exactly what's going on here *)
      rewrite assoc.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn1.
      rewrite <- assoc.
      etrans. apply maponpaths.
      use PushoutArrow_PushoutIn1.
      rewrite assoc.
      apply pathsinv0.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn1.
      
      (* simplify left hand side *)
      etrans. { simpl. reflexivity. }
      (* k_x · γ11 = arrow_mor11 (Kγ) · k_x' *) 
      (* this is just the commutativity of the bottom square of the
         commutative cube of φ *)
      set (φax := nat_trans_ax morcls_coprod_nat_trans g g' γ).
      set (bottom_square := dirprod_pr2 (pathsdirprodweq (base_paths _ _ φax))).
      exact (pathsinv0 bottom_square).
    * rewrite assoc.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn2.
      rewrite <- assoc.
      etrans. apply maponpaths.
      use PushoutArrow_PushoutIn2.
      rewrite assoc.
      apply pathsinv0.
      etrans. apply maponpaths_2.
      use PushoutArrow_PushoutIn2.

      simpl.
      exact (pathsinv0 (arrow_mor_comm γ)).
Qed.

Definition one_step_comonad_counit : nat_trans (one_step_comonad_functor) (functor_identity _) :=
    (_,, one_step_comonad_counit_is_nat_trans).

(* ψg in Garner *)
Definition morcls_lp_coprod_L1_inclusion (g : arrow C) :
    morcls_lp J g → morcls_lp J (λ1 g (CC g) POs).
Proof.
  (* The inclusion of lifting problems is induced by
    S_g → S_{L1g} : x ↦ (f_x -- in_x -> Kg = ∑f -- ϵg -> L1g)
    where ϵg is morcls_lp_coprod_diagram_red:
              ∑h
    A ---> ∑A ---> C
    |      |       |
  f |    ∑f|       | λ1g
    v      v       v
    B ---> ∑B ---> E1g
    *)
  intro S.
  exists (pr1 S).
  (* right hand square *)
  set (rhs := PushoutSqrCommutes (morcls_lp_coprod_diagram_pushout g (CC g) POs)).
  set (rhs_mor := mors_to_arrow_mor (morcls_lp_coprod g (CC g)) (λ1 _ (CC g) POs) _ _ (pathsinv0 rhs)).
  use (λ inx, inx · rhs_mor).

  (* left hand square *)
  use mors_to_arrow_mor.
  - exact (CoproductIn _ _ (morcls_lp_dom_coprod g (CC g)) S).
  - exact (CoproductIn _ _ (morcls_lp_cod_coprod g (CC g)) S).
  - abstract (exact (CoproductInCommutes _ _ _ _ _ _ S)).
Defined.

(* δg in Garner *)
Definition morcls_lp_coprod_L1_map (g : arrow C) :
    (morcls_lp_coprod _ (CC g)) --> (morcls_lp_coprod _ (CC (λ1 g (CC g) POs))).
Proof.
  (* the inclusion of the objects are just identity on themselves *)
  use mors_to_arrow_mor;
    try exact (CoproductOfArrowsInclusion 
              (morcls_lp_coprod_L1_inclusion g) _ _ 
              (λ _, (identity _))).
  
  (* commutativity *)
  abstract (
    etrans; [use precompWithCoproductArrowInclusion|];
    simpl;
    apply pathsinv0;
    etrans; [use postcompWithCoproductArrow|];
    simpl;
    apply maponpaths;
    apply funextsec;
    intro S;
    rewrite id_left;
    rewrite <- assoc;
    etrans; [apply maponpaths; exact (CoproductOfArrowsInclusionIn _ _ _ _ S)|];
    etrans; [apply maponpaths; apply id_left|];
    reflexivity
  ).
Defined.

Definition one_step_comonad_mul_data : 
    nat_trans_data
      (one_step_comonad_functor)
      (functor_composite one_step_comonad_functor one_step_comonad_functor).
Proof.
  intro g.
  (* The map on morphisms becomes the right face from the cube induced by
          ∑h
      ∑A ------> C
       |\          =  
  ∑f=Kg|  \     ∑h'  =
       |    ∑A' -----> C
       v δg |
      ∑B    |Kg'       |
        \   |=     PO    λ1g'
          \ v∑f'       v
           ∑B' - - - > E1g'
    *)
  set (δg := morcls_lp_coprod_L1_map g).
  
  use mors_to_arrow_mor.
  - exact (identity _).
  - use commuting_cube_construction.
    * (* aa *) exact (arrow_mor00 δg).
    * (* bb *) exact (arrow_mor11 δg).
    * (* cc *) exact (identity _).
    * (* left face *)
      exact (pathsinv0 (arrow_mor_comm δg)).
    * (* top face *)
      abstract (
        rewrite id_right;
        cbn;
        rewrite precompWithCoproductArrowInclusion;
        apply maponpaths;
        apply funextsec;
        intro S;
        rewrite id_left;
        cbn;
        apply pathsinv0;
        etrans; [exact (CoproductInCommutes _ _ _ _ _ _ S)|];
        reflexivity
      ).
  - (* commutativity in right face *)
    abstract (
      etrans; [apply id_left|];
      (* commuting cube construction is a pushout arrow *)
      apply pathsinv0;
      etrans; [apply PushoutArrow_PushoutIn2|];
      now rewrite id_left
    ).
Defined.

Definition one_step_comonad_mul_is_nat_trans : is_nat_trans _ _ one_step_comonad_mul_data.
Proof.
  intros g g' γ.
  apply subtypePath; [intro; apply homset_property|].
  apply pathsdirprod.
  - (* simpl. *)
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply id_left.
    reflexivity. (* wow... *)
  - simpl.
    (* equality of arrows E1 g --> E1 (λ1g) *)
    use (MorphismsOutofPushoutEqual 
      (isPushout_Pushout (morcls_lp_coprod_diagram_pushout g (CC _) POs))).
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              use PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1. 
      etrans. apply assoc.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc'.
      etrans. apply maponpaths.
              apply PushoutArrow_PushoutIn1.
      etrans. apply assoc.
      
      apply cancel_postcomposition.
      cbn.
      etrans. use CoproductOfArrowsInclusion_comp.
      apply pathsinv0.
      etrans. use CoproductOfArrowsInclusion_comp.
      (* apply maponpaths_1234. *)
      
      admit.
    * etrans. apply assoc.
      etrans. apply maponpaths_2.
              use PushoutArrow_PushoutIn2.
      etrans. rewrite assoc'.
              apply maponpaths.
              apply PushoutArrow_PushoutIn2. 
      etrans. now rewrite assoc, id_right.

      apply pathsinv0.
      etrans. apply assoc.
      etrans. apply maponpaths_2.
              apply PushoutArrow_PushoutIn2.
      etrans. rewrite assoc'.
              apply maponpaths.
              apply PushoutArrow_PushoutIn2.
      etrans. apply id_left.
      apply pathsinv0.
      reflexivity.
Admitted.

Definition one_step_comonad_mul : 
    nat_trans 
      (one_step_comonad_functor)
      (functor_composite one_step_comonad_functor one_step_comonad_functor) :=
  (_,, one_step_comonad_mul_is_nat_trans).

Definition one_step_comonad_functor_with_μ : functor_with_μ (op_cat (arrow C)) :=
    (functor_opp one_step_comonad_functor,, op_nt one_step_comonad_mul).

Definition one_step_comonad_data : Monad_data (op_cat (arrow C)) :=
    ((functor_opp one_step_comonad_functor,,
      op_nt one_step_comonad_mul),,
    op_nt one_step_comonad_counit).

End one_step_monad.

(* Section lifting_with_J_continued.

Lemma lifting_coprod_lp_red_iff_maps :
    filler (arrow_mor_comm (morcls_lp_coprod_diagram_red)) <->
  let Λ1g := mors_to_arrow_mor g ρ1g λ1g (identity _) test in
  ∑ (γ : ρ1g --> g), γ · Λ1g = identity _.

Lemma lifting_with_J_iff_one_step_monad_unit :
    right_lifting_data J g <->

End lifting_with_J_continued. *)