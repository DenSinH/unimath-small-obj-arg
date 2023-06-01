Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.WellFoundedRelations.

(* https://arxiv.org/pdf/2301.10696.pdf *)


Section definition.

(* Definition of accessibility is mostly used in defining 
   well foundedness. Lemma 2 shows that this is equivalent to 
   transfinite induction.
   
   This corresponds exactly with the statement of strongly_well_founded
   in UniMath.Combinatorics.WellFoundedRelations *)

Definition extensional {X : UU} (lt : hrel X) := 
    ∏ x y, (∏ z, (lt z x <-> lt z y)) -> x = y.

Lemma isaprop_extensional {X : UU} (lt : hrel X) (H : isaset X) : isaprop (extensional lt).
Proof.
  do 2 (apply impred; intro).
  apply isapropimpl.
  apply H.
Qed.

Definition lt_extended {X : UU} (lt : hrel X) : hrel X.
Proof.
  intros x y.
  use make_hProp.
  - exact (∏ (z : X), lt z x -> lt z y).
  - abstract (
      do 2 (apply impred; intro);
      apply propproperty
    ).
Defined.

Definition lt_extended_refl {X : UU} (lt : hrel X) : isrefl (lt_extended lt).
Proof.
  intros x y.
  trivial.
Qed.

Definition lt_extended_trans {X : UU} (lt : hrel X) : istrans (lt_extended lt).
Proof.
  intros x y z ltxy ltyz.
  intros u ltux.
  use ltyz.
  use ltxy.
  exact ltux.
Qed.

Definition extensional' {X : UU} (lt : hrel X) :=
    ∏ x y, (lt_extended lt x y) -> (lt_extended lt y x) -> x = y.

(* https://www.cs.bham.ac.uk/~mhe/TypeTopology/Ordinals.Notions.html#6117 *)
Lemma extensional_impl_extensional' {X : UU} (lt : hrel X) : 
    extensional lt -> extensional' lt.
Proof.
  intros ext x y ltxy ltyx.
  apply (ext x y).
  intro z.
  split; intro ltz.
  - exact (ltxy z ltz).
  - exact (ltyx z ltz).
Qed.

Lemma extensional'_impl_extensional {X : UU} (lt : hrel X) : 
    extensional' lt -> extensional lt.
Proof.
  intros ext' x y extz.
  apply (ext' x y); intros z ltz.
  - apply (pr1 (extz z)). assumption.
  - apply (pr2 (extz z)). assumption.
Qed.

(* prop-valued is baked into hrel *)
Definition is_ordinal {X : UU} (lt : hrel X) :=
    strongly_well_founded lt × extensional lt × istrans lt.

Definition ordinal (X : UU) := ∑ (lt : hrel X), is_ordinal lt.

Definition ordinal_rel {X : UU} (ord : ordinal X) := pr1 ord.
Coercion ordinal_rel : ordinal >-> hrel.
Definition ordinal_wf {X : UU} (ord : ordinal X) := pr12 ord.
Definition ordinal_ext {X : UU} (ord : ordinal X) := pr122 ord.
Definition ordinal_trans {X : UU} (ord : ordinal X) := pr222 ord.

End definition.

Local Definition f {X : UU} (x y : X) {rel : hrel X} (e : extensional rel) : x = y -> x = y.
Proof.
  intro p.
  set (e' := extensional_impl_extensional' _ e).

  apply (e' x y).
  - exact (transportf (λ z, lt_extended rel x z) p (lt_extended_refl rel _)).
  - exact (transportf (λ z, lt_extended rel z x) p (lt_extended_refl rel _)).
Defined.

Local Definition ec {X : UU} (ord : ordinal X) :
    let ext' := extensional_impl_extensional' _ (ordinal_ext ord) in
    ∏ (x x' : X) (l l' : lt_extended ord x x') (m m' : lt_extended ord x' x), ext' _ _ l m = ext' _ _ l' m'.
Proof.
  intros.
  apply (maponpaths_12 (ext' x x')); apply propproperty.
Defined.

Local Definition wconstant {X Y : UU} (f : X -> Y) :=
    ∏ x y, f x = f y.

Local Lemma f_wconstant {X : UU} {x y : X} {rel : hrel X} (e : extensional rel) :
    wconstant (f x y e).
Proof.
  intros p q.
  unfold f.
  apply maponpaths_12; apply propproperty.
Qed.

Local Lemma id_collapsible_is_set {X : UU} :
    (∏ (x y : X), ∑ (f : x = y -> x = y), wconstant f) -> isaset X.
Proof.
  (* uses "local Hedberg" theorem 
     https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Subsingletons.html#4946 *)
  intros pc x y.
  intros p q.
  destruct (pc x y) as [f fwc].

  unfold wconstant in fwc.
  set (test := fwc p q).

  use tpair.
  - induction p.

Admitted.

Lemma extensional_carrier_isaset {X : UU} {rel : hrel X} (ext : extensional rel) : isaset X.
Proof.
  apply id_collapsible_is_set.
  intros x y.
  exists (f _ _ ext).
  apply f_wconstant.
Qed.

Definition sup {X : UU} (ord : ordinal X) (A : hsubtype X) :=
    ∑ (x : X), (∏ (a : X), A a -> ord a x) ×
               (∏ (b : X), ord b x -> ∑ (a : X), ord b a × A a).
