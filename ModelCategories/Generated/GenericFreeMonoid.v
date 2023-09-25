Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import CategoryTheory.Monoidal.Categories.
Require Import CategoryTheory.Monoidal.CategoriesOfMonoids.


Local Open Scope cat.


Section Mon_alg.

Import BifunctorNotations.
Import MonoidalNotations.

Context {C : category} (V : monoidal C).

Definition pointed : UU :=
    ∑ T, I_{V} --> T.

Coercion pointed_obj (T : pointed) : C := pr1 T.
Definition pointed_pt (T : pointed) : I_{V} --> T := pr2 T.

Definition Mon_alg_data (T : pointed) (X : C) : UU :=
    ∑ (x : T ⊗_{V} X --> X), (luinv_{V} _) · ((pointed_pt T) ⊗^{V}_{r} X) · x  = identity _.

Coercion Mon_alg_map {T : pointed} {X : C} (XX : Mon_alg_data T X) := pr1 XX.
Definition Mon_alg_map_comm {T : pointed} {X : C} (XX : Mon_alg_data T X) := pr2 XX.

Definition Mon_alg_mor_axioms 
    {T : pointed}
    {X Y : C}
    (XX : Mon_alg_data T X)
    (YY : Mon_alg_data T Y)
    (f : X --> Y) : UU :=
  XX · f = (T ⊗^{V}_{l} f) · YY.

Lemma isaprop_Mon_alg_mor_axioms 
    {T : pointed}
    {X Y : C}
    (XX : Mon_alg_data T X)
    (YY : Mon_alg_data T Y)
    (f : X --> Y) : 
  isaprop (Mon_alg_mor_axioms XX YY f).
Proof.
  apply homset_property.
Qed.

Definition Mon_alg_disp_ob_mor (T : pointed) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (Mon_alg_data T X).
  - intros X Y XX YY f.
    exact (Mon_alg_mor_axioms XX YY f).
Defined.

Definition Mon_alg_disp_id_comp (T : pointed) : 
    disp_cat_id_comp _ (Mon_alg_disp_ob_mor T).
Proof.
  split.
  - intros X XX.
    (* simpl.
    unfold Mon_alg_mor_axioms. *)
    etrans. apply id_right.
    apply pathsinv0.
    etrans. apply maponpaths_2.
            use (bifunctor_leftid V).
    apply id_left.
  - intros X Y Z f g XX YY ZZ ff gg.
    simpl.
    unfold Mon_alg_mor_axioms.

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            exact ff.
    etrans. apply assoc'.
    etrans. apply cancel_precomposition.
            exact gg.
    
    apply pathsinv0.
    etrans. apply maponpaths_2.
            use (bifunctor_leftcomp V).
    apply assoc'.
(* Qed because morphisms are propositional anyway *)
Qed.  

Definition Mon_alg_disp_data (T : pointed) : 
    disp_cat_data C := (_,, Mon_alg_disp_id_comp T).

Definition Mon_alg_axioms (T : pointed) :
    disp_cat_axioms _ (Mon_alg_disp_data T).
Proof.
  repeat split; intros; try apply homset_property.
  apply isasetaprop.
  apply homset_property.
Defined.

Definition Mon_alg_disp (T : pointed) : 
    disp_cat C := (_,, Mon_alg_axioms T).

Definition Mon_alg (T : pointed) : 
    category := total_category (Mon_alg_disp T).

Lemma Mon_alg_action_alg_map_rel {T : pointed} 
    (X : Mon_alg T) (A : C) :
  luinv^{ V }_{ pr1 X ⊗_{ V} A} · pointed_pt T ⊗^{ V}_{r} (pr1 X ⊗_{ V} A)
  · (αinv^{ V }_{ T, pr1 X, A} · pr12 X ⊗^{ V}_{r} A) =
  identity _.
Proof.
  destruct X as [X [x rel]].
  cbn.
  
  Search (luinv^{ ?V }_{ ?X ⊗_{?V} ?A}).
Admitted.

Lemma Mon_alg_action_mor_rel {T : pointed} (X : Mon_alg T)
    {A B : C} (f : A --> B) :
    Mon_alg_mor_axioms
      (_,, Mon_alg_action_alg_map_rel X A)
      (_,, Mon_alg_action_alg_map_rel X B) (pr1 X ⊗^{ V}_{l} f).   
Proof.
  unfold Mon_alg_mor_axioms.
  destruct X as [X [x rel]].
  cbn.

Admitted.

Definition Mon_alg_right_action_data {T : pointed} (X : Mon_alg T) :
  functor_data C (Mon_alg T).
Proof.
  use make_functor_data.
  - intro A.
    exists ((pr1 X) ⊗_{V} A).
    cbn.
    unfold Mon_alg_data.
    exists ((αinv_{V} T (pr1 X) A) · ((pr12 X) ⊗^{V}_{r} A)).
    apply Mon_alg_action_alg_map_rel.
  - intros A B f.
    simpl.
    exists ((pr1 X) ⊗^{V}_{l} f).
    exact (Mon_alg_action_mor_rel X f).
Defined.

Definition Mon_alg_right_action_axioms {T : pointed} (X : Mon_alg T) :
    is_functor (Mon_alg_right_action_data X).
Proof.
  split.
  - intro x.
    apply subtypePath; [intro; apply isaprop_Mon_alg_mor_axioms|].
    use (bifunctor_leftid V).
  - intros A B D f g.
    apply subtypePath; [intro; apply isaprop_Mon_alg_mor_axioms|].
    use (bifunctor_leftcomp V).
Qed.

Definition Mon_alg_right_action {T : pointed} (X : Mon_alg T) :
    functor C (Mon_alg T) :=
  (_,, Mon_alg_right_action_axioms X).

(* basically want to formalize Garner / Kelly (generalized) stuff about
   T-Alg (/ T-Mod in Garner)
   and how one obtains a monoid from the free T-algebra
   Mon should be a monoidal category (Ff_C) is at least
*)

Lemma Mon_induced_alg_map_rel {T S : pointed} {A : C} (F : T --> S)
    (a : Mon_alg_disp S A) : 
  luinv^{ V }_{ A} · pointed_pt T ⊗^{ V}_{r} A · (F ⊗^{ V}_{r} A · (pr1 a)) =
    identity _.
Proof.

Admitted.

Lemma Mon_induced_alg_map_mor_rel {T S : pointed} {A B : C} (F : T --> S)
    {a : Mon_alg_disp S A} {b : Mon_alg_disp S B} {f : A --> B}
    (ff : Mon_alg_mor_axioms a b f) :
    F ⊗^{ V}_{r} A · (pr1 a) · f = T ⊗^{ V}_{l} f · (F ⊗^{ V}_{r} B · (pr1 b)).
Proof.

Admitted.

Definition Mon_induced_alg_map_data {T S : pointed} (F : T --> S) :
    disp_functor_data (functor_identity _) (Mon_alg_disp S) (Mon_alg_disp T).
Proof.
  use tpair.
  - intros A a.
    exists ((F ⊗^{V}_{r} A) · (Mon_alg_map a)).
    apply Mon_induced_alg_map_rel.
  - 
    (* simpl. *)
    intros A B a b f ff.
    (* unfold Mon_alg_mor_axioms.
    cbn. *)
    apply Mon_induced_alg_map_mor_rel.
    unfold Mon_alg_mor_axioms.
    exact ff.
Defined.

Definition Mon_induced_alg_map_axioms {T S : pointed} (F : T --> S) :
    disp_functor_axioms (Mon_induced_alg_map_data F).
Proof.
  use tpair; simpl; intros; apply isaprop_Mon_alg_mor_axioms.
Qed.

Definition Mon_induced_alg_map {T S : pointed} (F : T --> S) :
    disp_functor (functor_identity _) (Mon_alg_disp S) (Mon_alg_disp T) :=
  (_,, Mon_induced_alg_map_axioms F).

(* define NWFS_alg as disp_cat over Mon_alg with
   "associativity axiom" (Kelly, par 22.1)
   then free monoid as NWFS with equivalence of alg- categories 
   
   I think equivalence should be sufficient, as opposed to
   iso, since we care about the retract closure of the algebras
   in the end anyway?

   if we do not care about cofibrantly generated, we can skip
   this NWFS-alg stuff definition for now, and just show
   that the NWFS exists.
*)

Definition Mon_alg_forgetful_functor (T : pointed) :
    functor (Mon_alg T) C :=
  pr1_category _.

(* todo: show that this holds whenever sequence on I --> X
   converges *)
Definition alg_forgetful_functor_right_action_is_adjoint {T : pointed} (X : Mon_alg T) : UU :=
    are_adjoints (Mon_alg_right_action X) (Mon_alg_forgetful_functor T).  

(* not every object can be pointed in a general monoidal category *)
Definition alg_forgetful_functor_right_action_is_adjoint_induced_mul {T : pointed} (X : Mon_alg T) 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  (pr1 X) ⊗_{V} (pr1 X) --> (pr1 X).
Proof.
  destruct X as [X [x rel]].
  set (m := Monad_from_adjunction Adj).
  set (μ := μ m (I_{V})).

  (* simpl in μ.
  cbn. *)
  exact (X ⊗^{V}_{l} (ruinv_{V} X) ·
         μ ·
         ru_{V} X).
Defined.

Definition alg_forgetful_functor_right_action_is_adjoint_monoid_data
    {T : pointed} {X : Mon_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X) :
  monoid_data V (pr1 X).
Proof.
  exists (alg_forgetful_functor_right_action_is_adjoint_induced_mul X Adj).
  set (η := unit_from_are_adjoints Adj I_{V} · ru_{V} (pr1 X)).
  exact η.
Defined.

Definition alg_forgetful_functor_right_action_is_adjoint_monoid_laws 
    {T : pointed} {X : Mon_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X)  :
  monoid_laws V (alg_forgetful_functor_right_action_is_adjoint_monoid_data Adj).
Proof.
  (* these should just follow from the monad laws of Monad_from_adjunction Adj *)
  set (m := Monad_from_adjunction Adj).
  repeat split.
  - unfold monoid_laws_unit_left.
    cbn.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul.
    cbn.
    set (test := Monad_law1 (T := m)).
    set (testI := test I_{V}).
    cbn in testI.
    etrans. apply maponpaths_2.
            apply (bifunctor_rightcomp V).
    etrans. apply assoc.
    etrans. apply maponpaths_2.
            apply assoc.
            

    show_id_type.
    admit.
  - unfold monoid_laws_unit_right.
    cbn.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul.
    cbn.
    admit.
  - unfold monoid_laws_assoc.
    cbn.
    unfold alg_forgetful_functor_right_action_is_adjoint_induced_mul.
    (* cbn. *)

    etrans. apply cancel_postcomposition.
            apply maponpaths.
            apply (bifunctor_leftcomp V).
    etrans. apply cancel_postcomposition.
            apply maponpaths.
            apply maponpaths_2.
            apply (bifunctor_leftcomp V).

    etrans. apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc.
    etrans. do 3 apply cancel_postcomposition.
            apply assoc.
    etrans. do 2 apply cancel_postcomposition.
            apply assoc'.
    etrans. do 2 apply cancel_postcomposition.
            apply maponpaths.
    {
      exact (pathsinv0 (bifunctor_leftcomp V _ _ _ _ _ _)).
    }
    etrans. do 2 apply cancel_postcomposition.
            do 2 apply maponpaths.
    {
      exact (pr1 (monoidal_rightunitorisolaw V (pr1 X))).
    }
    etrans. do 2 apply cancel_postcomposition.
            apply maponpaths.
            apply (bifunctor_leftid V).
    etrans. do 2 apply cancel_postcomposition.
            apply id_right.

    etrans. do 2 apply cancel_postcomposition.
            apply assoc.
    etrans. apply cancel_postcomposition.
            apply assoc'.
    etrans. apply cancel_postcomposition.
            apply cancel_precomposition.
            exact (Monad_law3 (T := m) I_{V}).
    
    (* cbn. *)
    etrans. apply maponpaths_2.
            apply assoc.
    apply pathsinv0.
    etrans. apply assoc.
    apply cancel_postcomposition.
    etrans. apply assoc.
    apply cancel_postcomposition.
    apply pathsinv0.

    etrans. apply cancel_postcomposition.
            apply (monoidal_associatornatleft V).
    admit.
Admitted.

Definition alg_forgetful_functor_right_action_is_adjoint_monoid 
    {T : pointed} {X : Mon_alg T} 
    (Adj : alg_forgetful_functor_right_action_is_adjoint X)  :
  monoid _ _ := (_,, alg_forgetful_functor_right_action_is_adjoint_monoid_laws Adj).

(* todo: define free monoid *)
(* Lemma alg_free_monad_exists_if_alg_forgetful_functor_right_action_is_adjoint {T : pointed} (X : Mon_alg T) :
    alg_forgetful_functor_right_action_is_adjoint X -> (total_category (NWFS C)).
Proof.
  intro Adj.
  
  exists (pr11 X).
  split; [exact (pr21 X)|].

  exists (alg_forgetful_functor_right_action_is_adjoint_induced_mul Adj).
  exact (alg_forgetful_functor_right_action_is_adjoint_monad_laws Adj).
Defined. *)

End Mon_alg.