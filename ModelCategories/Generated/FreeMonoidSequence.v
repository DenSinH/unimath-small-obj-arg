Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.


Definition poset_precat_ob_mor (P : Poset) : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (carrierofposet P).
  - intros n m.
    exact (posetRelation P n m).
Defined.

Definition poset_precat_data (P : Poset) : precategory_data.
Proof.
  use make_precategory_data.
  - exact (poset_precat_ob_mor P).
  - intro n.
    apply (isrefl_posetRelation P).
  - intros n m l nm ml.
    exact (istrans_posetRelation P _ _ _ nm ml).
Defined.

Definition poset_precat_is_precategory (P : Poset) : is_precategory (poset_precat_data P).
Proof.
  use make_is_precategory_one_assoc; 
      intros; apply propproperty.
Qed.

Definition poset_precategory (P : Poset) : precategory :=
    (_,, poset_precat_is_precategory P).

Definition poset_precat_has_homsets (P : Poset) : has_homsets (poset_precategory P).
Proof.
  intros n m.
  apply isasetaprop.
  apply propproperty.
Qed.

Definition poset_category (P : Poset) : category :=
    (poset_precategory P,, poset_precat_has_homsets P).

Lemma natleh_isPartialOrder : isPartialOrder natleh.
Proof.
  split.
  - split.
    * intros n m l.
      apply istransnatleh.
    * exact isreflnatleh.
  - intros n m.
    apply isantisymmnatleh.
Qed.

Definition natleh_PartialOrder : PartialOrder natset.
Proof.
  use make_PartialOrder.
  - exact natleh.
  - exact natleh_isPartialOrder.
Defined.

Definition nat_poset : Poset := (_,, natleh_PartialOrder).

Definition nat_prod_inf (nn : nat × nat) := pr1 nn.
Definition nat_prod_suc (nn : nat × nat) := pr2 nn.

Definition nat_prod_order (nn mm : nat × nat) : UU :=
    (nat_prod_inf nn < nat_prod_inf mm) ⨿ 
    ((nat_prod_inf nn = nat_prod_inf mm) × (nat_prod_suc nn <= nat_prod_suc mm)).

Lemma isaprop_nat_prod_order (nn mm : nat × nat) :
    isaprop (nat_prod_order nn mm).
Proof.
  apply isapropcoprod.
  - apply isasetbool.
  - apply isapropdirprod.
    * apply isasetnat.
    * apply isasetbool.
  - intros P Q.
    destruct Q as [Q _].
    apply (nat_neq_to_nopath (natlthtoneq _ _ P)).
    exact Q.
Qed.

Definition nat_prod_hrel : hrel (nat × nat).
Proof.
  intros nn mm.
  use make_hProp.
  - exact (nat_prod_order nn mm).
  - apply isaprop_nat_prod_order.
Defined.

Lemma isrefl_nat_prod_hrel : isrefl nat_prod_hrel.
Proof.
  intro nn.
  right.
  split.
  - reflexivity.
  - apply isreflnatleh.
Qed.

Lemma istrans_nat_prod_hrel : istrans nat_prod_hrel.
Proof.
  intros nn mm ll nm ml.
  destruct nm as [nm|nm]; destruct ml as [ml|ml].
  - left.
    exact (istransnatlth _ _ _ nm ml).
  - left.
    rewrite <- (pr1 ml).
    exact nm.
  - left.
    rewrite (pr1 nm).
    exact (ml).
  - right.
    rewrite (pr1 nm), (pr1 ml).
    split; [reflexivity|].
    exact (istransnatleh (pr2 nm) (pr2 ml)).
Qed.

Lemma isantisymm_nat_prod_hrel : isantisymm nat_prod_hrel.
Proof.
  intros nn mm nm mn.
  destruct nm as [nm|nm].
  - destruct mn as [mn|mn].
    * apply fromempty.
      exact (isasymmnatlth _ _ nm mn).
    * apply fromempty.
      destruct mn as [mn _].
      set (nmneq := natlthtoneq _ _ nm).
      apply (nat_neq_to_nopath nmneq).
      exact (pathsinv0 mn).
  - destruct mn as [mn|mn].
    * apply fromempty.
      destruct nm as [nm _].
      set (mnneq := natlthtoneq _ _ mn).
      apply (nat_neq_to_nopath mnneq).
      exact (pathsinv0 nm).
    * apply pathsdirprod.
      + exact (pr1 nm).
      + destruct nm as [_ nm].
        destruct mn as [_ mn].
        apply isantisymmnatleh; assumption.
Qed.

Lemma nat_prod_order_isPartialOrder : isPartialOrder nat_prod_hrel.
Proof.
  split.
  - split.
    * exact istrans_nat_prod_hrel.
    * exact isrefl_nat_prod_hrel.
  - intros n m.
    apply isantisymm_nat_prod_hrel.
Qed.

Definition nat_prod_order_PartialOrder : PartialOrder (setdirprod natset natset).
Proof.
  use make_PartialOrder.
  - exact (nat_prod_hrel).
  - exact (nat_prod_order_isPartialOrder).
Defined.

Definition nat_prod_poset : Poset :=
    (_,, nat_prod_order_PartialOrder).

Definition nat_prod : category := poset_category nat_prod_poset.

Local Open Scope Cat.
(*
  todo: define the sequence on nat, then we can define it on
  any copy of nat inductively by setting 0 to the colimit
*)
(* todo: figure out how to do this generically? *)
Definition nat_functor_from_generators_data 
    (C : category)
    (F0 : C)
    (FS : C -> C) :
  functor_data (poset_category nat_poset) C.
Proof.
  use make_functor_data.
  - intro n.
    induction n as [|? prev].
    * exact F0.
    * exact (FS prev).
  - intros n m nm.
    cbn.
    induction (n - m).
    * cbn.
Defined.

Definition nat_prod_colim_functor_from_generators_data 
    (C : category)
    (F0 : C)
    (FS : C -> C) :
    functor_data nat_prod C.
Proof.
  use make_functor_data.
  - intro nn.
    destruct nn as [inf suc].
    induction inf as [|? Hinf].
    * (* inf 0: first copy of ℕ *)
      induction suc as [|? prev].
      + exact F0.
      + exact (FS prev).
    * (* inf n + 1, first term is colimit of previous infinity sequence *)

Defined.
