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

Require Import CategoryTheory.DisplayedCats.algebras.

Local Open Scope cat.
Local Open Scope mor_disp.
Local Open Scope Cat.


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
    exact (∏ (f : arrow C) (H : J _ _ (arrow_mor f)) (S : f --> g),
          (filler_map (δ f H _ _ (arrow_mor_comm S))) · (arrow_mor00 mn) = 
           filler_map (δ' f H _ _ (arrow_mor_comm (S · mn)))).
  - (* propositional morphism data *)
    intros.
    do 3 (apply impred; intro).
    apply homset_property.
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

Definition morcls_lp_dom_coprod (J : morphism_class C) (g : arrow C)
    (CC : Coproducts (morcls_lp J g) C) :=
  CC (λ (f : morcls_lp J g), arrow_dom (pr11 f)).
Definition morcls_lp_cod_coprod (J : morphism_class C) (g : arrow C)
    (CC : Coproducts (morcls_lp J g) C) :=
  CC (λ (f : morcls_lp J g), arrow_cod (pr11 f)).

Definition morcls_lp_coprod (J : morphism_class C) (g : arrow C)
    (CC : Coproducts (morcls_lp J g) C) :=
  (
    CoproductOfArrows _ _ 
    (morcls_lp_dom_coprod J g CC) (morcls_lp_cod_coprod J g CC)
    (λ (f : morcls_lp J g), arrow_mor (pr11 f))
  ).

(* the canonical diagram capturing all lifting problems in J *)
Definition morcls_lp_coprod_diagram (J : morphism_class C) (g : arrow C)
    (CC : Coproducts (morcls_lp J g) C) :
  morcls_lp_coprod J g CC --> g.
Proof.
  use tpair.
  - split.
    * exact (CoproductArrow _ _ (morcls_lp_dom_coprod J g CC) (λ j, arrow_mor00 (pr2 j))).
    * exact (CoproductArrow _ _ (morcls_lp_cod_coprod J g CC) (λ j, arrow_mor11 (pr2 j))).
  - unfold morcls_lp_coprod.
    simpl.
    rewrite postcompWithCoproductArrow.
    rewrite precompWithCoproductArrow.
    apply maponpaths.
    apply funextsec.
    intro j.
    exact (arrow_mor_comm (pr2 j)).
Defined.

Context (n : nwfs C).

Definition morcls_L_map_structure (J : morphism_class C) : UU := 
  disp_functor (functor_identity _) (op_disp_cat (morcls_disp J)) (nwfs_L_maps n).

Context {J : morphism_class C}.

(* "this assignation extends to a functor θ: R-Map ⟶ J□", Garner 2007, p18 *)
Definition R_map_rlp_morcls_structure_data (η : morcls_L_map_structure J) : 
    disp_functor_data (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp J).
Proof.
  use tpair.
  - (* map on displayed objects (send arrow to itself, with lifting data) *)
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
  - (* map on displayed objects respects morphism property *)
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
Defined.

Definition R_map_rlp_morcls_structure_axioms (η : morcls_L_map_structure J) :
    disp_functor_axioms (R_map_rlp_morcls_structure_data η).
Proof.
  unfold disp_functor_axioms.
  split; intros.
  - 
    admit.
  - 
    admit.
Admitted.

Definition R_map_rlp_morcls_structure (η : morcls_L_map_structure J) : 
    disp_functor (functor_identity _) (nwfs_R_maps n) (rlp_morcls_disp J) :=
  (_,, R_map_rlp_morcls_structure_axioms η).

(* we say that n := (L, R, Δ) is cofibrantly generated by (J, η) if θ is
   an isomorphism of categories *)
Definition cofibrantly_generated (η : morcls_L_map_structure J) :=
    is_catiso (total_functor (R_map_rlp_morcls_structure η)).

(* It is possible to show this more generally for _any_
   coproduct of maps in J, but this is not really necessary or useful
   for us.
   
   The proof of this lemma is practically the same as that of 
   wfs_closed_coproducts, but we do _not_ need the axiom of choice here,
   since we know the actual lifting data. *)
Lemma lifting_data_impl_lifting_coprod_lp 
    (g : arrow C) (CC : Coproducts (morcls_lp J g) C) : 
  right_lifting_data J g -> elp (morcls_lp_coprod J g CC) g.
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
    exact (CoproductOfArrowsIn _ _ _ _ _ j).
    reflexivity.
  }

  set (jlifts := foralltototal _ _ jlift).
  destruct jlifts as [lj hlj].
  set (hl := isCoproduct_Coproduct _ _ (morcls_lp_cod_coprod J g CC) _ lj).
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
    rewrite (CoproductInCommutes _ _ _ (morcls_lp_dom_coprod J g CC)).

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
    rewrite (CoproductInCommutes _ _ _ (morcls_lp_cod_coprod J g CC)).

    (* the relation we want to prove *)
    destruct (hlj j) as [_ kljcomm].

    (* by definition *)
    change (CoproductIn _ _ _ _ · k) with (kj j).
    rewrite (hl j).
    exact kljcomm.
Qed.

(* we need the actual diagram for the other direction *)
Lemma lifting_coprod_lp_impl_lifting_data 
    (g : arrow C) (CC : Coproducts (morcls_lp J g) C) : 
  filler (arrow_mor_comm (morcls_lp_coprod_diagram J g CC)) ->
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
    (* inclusion of arrow_cod f into coproduct of all domains *)
  set (codf_in := (CoproductIn _ _ (morcls_lp_cod_coprod J g CC) Hlp)).
  set (domf_in := (CoproductIn _ _ (morcls_lp_dom_coprod J g CC) Hlp)).

  exists (codf_in · ltot).
  split.
  - (* h = (inclusion of arrow_dom f) · (top morphism of canonical diagram) *)
    assert (h = domf_in · (arrow_mor00 (morcls_lp_coprod_diagram J g CC))) as Hh.
    {
      unfold domf_in.
      symmetry.
      
      exact (
          CoproductInCommutes _ _ _ 
          (morcls_lp_dom_coprod J g CC) 
          _ _ Hlp
      ).
    }
    rewrite Hh.

    (* commutativity of f with inclusions of domain / codomain *)
    assert (f · codf_in = domf_in · (morcls_lp_coprod J g CC)) as Hf.
    {
      unfold codf_in, domf_in, morcls_lp_coprod.
      rewrite (CoproductOfArrowsIn _ _ (morcls_lp_dom_coprod J g CC)).
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
        (morcls_lp_cod_coprod J g CC) 
        _ _ Hlp
    ).
Qed.

Lemma lifting_data_iff_lifting_coprod_lp 
    (g : arrow C) (CC : Coproducts (morcls_lp J g) C) : 
    filler (arrow_mor_comm (morcls_lp_coprod_diagram J g CC)) <->
      right_lifting_data J g.
Proof.
  split.
  - apply lifting_coprod_lp_impl_lifting_data.
  - intro rldJg.
    apply lifting_data_impl_lifting_coprod_lp.
    exact rldJg.
Qed.