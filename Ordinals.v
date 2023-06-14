Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.WellFoundedRelations.

Require Import CategoryTheory.Cardinals.

Local Open Scope type_scope.


(* https://arxiv.org/pdf/2301.10696.pdf *)
#[local] Unset Universe Checking.
Section definition.

(* Definition of accessibility is mostly used in defining 
   well foundedness. Lemma 2 shows that this is equivalent to 
   transfinite induction.
   
   This corresponds exactly with the statement of weakly_well_founded
   in UniMath.Combinatorics.WellFoundedRelations *)
Lemma isaprop_weakly_well_founded {X} {lt : X -> X -> Type} : isaprop (weakly_well_founded lt).
Proof.
  do 3 (apply impred; intro).
  apply propproperty.
Qed.

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
    weakly_well_founded lt × extensional lt × istrans lt.
    
Definition ordinal := ∑ (X : UU) (lt : hrel X), is_ordinal lt.

Definition ordinal_carrier (ord : ordinal) := pr1 ord.
Definition ordinal_rel (ord : ordinal) := pr12 ord.
Coercion ordinal_rel : ordinal >-> hrel.
Definition ordinal_wf (ord : ordinal) := pr1 (pr22 ord).
Definition ordinal_ext (ord : ordinal) := pr12 (pr22 ord).
Definition ordinal_trans (ord : ordinal) := pr22 (pr22 ord).

End definition.

Local Definition f {X : UU} (x y : X) {rel : hrel X} (e : extensional rel) : x = y -> x = y.
Proof.
  intro p.
  set (e' := extensional_impl_extensional' _ e).

  apply (e' x y).
  - exact (transportf (λ z, lt_extended rel x z) p (lt_extended_refl rel _)).
  - exact (transportf (λ z, lt_extended rel z x) p (lt_extended_refl rel _)).
Defined.

Local Definition ec (ord : ordinal) :
    let ext' := extensional_impl_extensional' _ (ordinal_ext ord) in
    ∏ (x x' : ordinal_carrier ord) (l l' : lt_extended ord x x') (m m' : lt_extended ord x' x), ext' _ _ l m = ext' _ _ l' m'.
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

Lemma isaprop_is_ordinal {X : UU} {lt : hrel X} (isord : is_ordinal lt) : isaprop (is_ordinal lt).
Proof.
  repeat apply isapropdirprod.
  - apply isaprop_weakly_well_founded.
  - apply isaprop_extensional.
    apply (extensional_carrier_isaset (pr12 isord)).
  - apply (@isaprop_istrans (make_hSet X (extensional_carrier_isaset (pr12 isord))) _).
Qed.

Coercion ordinal_carrier_hset (ord : ordinal) : hSet :=
    make_hSet _ (extensional_carrier_isaset (ordinal_ext ord)).

Lemma nat_is_ordinal : is_ordinal (λ (x y : nat), x < y).
Proof.
  repeat split.
  - intros P H x.
    induction x.
    * apply H.
      intros y Hy.
      apply fromempty.
      exact (negnatlthn0 y Hy).
    * admit. 
  - intros x y H.
    induction x.
    * induction y; [reflexivity|].
      apply fromempty.
      apply (negnatlthn0 y).
      apply (H y).
      apply natlthnsn.
    * induction y.
      + admit.
      + admit. 
  - use istransnatlth.
Admitted.

(* todo: restriction on sup? (<= ord, hsubset hsubset <= hsubset)... *)
Definition ordinal_with_sup : UU := 
    ∑ (ord : ordinal), hsubtype ord -> ordinal.
Coercion ordinal_with_sup_ordinal (ord : ordinal_with_sup) : ordinal
    := pr1 ord.
Definition ordinal_sup (ord : ordinal_with_sup) := pr2 ord.

Definition initial_segment {ord : ordinal} (a : ord) :=
    ∑ (x : ord), ord x a.

Definition initial_segment_lt {ord : ordinal} (a : ord) : hrel (initial_segment a).
Proof.
  intros x y.
  exact (ord (pr1 x) (pr1 y)).
Defined.

(* https://tdejong.com/agda-html/st-tt-ordinals/Ordinals.OrdinalOfOrdinals.html#13335 *)
Lemma initial_segment_is_ordinal {ord : ordinal} (a : ord) : is_ordinal (initial_segment_lt a).
Proof.
  repeat split.
  - intros P H x.
    apply H.
    intros y yx.
    destruct x as [x segx].
    destruct y as [y segy].
    set (wford := ordinal_wf ord).

    (* extend family P to whole ordinal *)
    set (Pext := λ (x : ord), ∀ (xa : ord x a), P (x,, xa)).

    (* prove hereditariness (accessibility) of family Pext *)
    assert (HPext : hereditary (ordinal_rel ord) Pext).
    {
      intros X HY Xa.
      apply H.
      intros Y XY.
      exact (HY (pr1 Y) XY (pr2 Y)).
    }
    exact ((wford Pext HPext) y segy).
  - intros x y ext.
    apply subtypePath; [intro; apply propproperty|].
    apply ordinal_ext.
    intro z.
    split.
    * destruct x as [x segx].
      intro zx.
      simpl in zx.
      set (segz := (z,, ordinal_trans ord _ _ _ zx segx) : initial_segment a).
      apply (ext segz).
      exact zx.
    * destruct y as [y segy].
      intro zy.
      simpl in zy.
      set (segz := (z,, ordinal_trans ord _ _ _ zy segy) : initial_segment a).
      apply (ext segz).
      exact zy.
  - intros x y z xy yz.
    unfold initial_segment_lt in *.
    exact (ordinal_trans ord _ _ _ xy yz).
Qed.

Definition initial_segment_ordinal {ord : ordinal} (a : ord) : ordinal :=
    (initial_segment a,, (initial_segment_lt a,, initial_segment_is_ordinal a)).

Notation "ord ↓ a" := (@initial_segment_ordinal ord a) (at level 60).

(* todo: equality here? *)
(* Remark 6: In Definition 5 above, we could have defined a
bounded simulation using an identification α = β ↓ b, but opted
for an equivalence α ' β ↓ b instead. These two expressions are
equivalent by univalence. However, the latter has the advantage
of begin small, i.e., living in the same universe as α and β,
while the former lives in the next universe. 

In Agda code: still uses equality *)

Definition bounded_simulation (α β : ordinal) :=
    ∑ (b : β), (α = β ↓ b).

Definition ordinal_lt : hrel ordinal :=
    λ α β, ∥bounded_simulation α β∥.

Lemma bounded_simulation_trans {α β γ : ordinal} :
    bounded_simulation α β -> bounded_simulation β γ -> bounded_simulation α γ.
Proof.
  intros αβ βγ.
  destruct αβ as [b αeq].
  destruct βγ as [c βeq].

  (* b : β = γ ↓ c, need to get bounded simulation corresponding
     to b *)
  (* set (test := pr1 βeq).
  set (test := eqweqmap βeq). *)
  exists c.
  rewrite αeq.
  (* cant use subtypePath, Σ type in ordinal is problem *)
  
Admitted.

Lemma ordinal_lt_trans : istrans ordinal_lt.
Proof.
  intros α β γ αβ βγ.
  use (hinhuniv _ αβ).
  clear αβ; intro αβ.
  use (hinhuniv _ βγ).
  clear βγ; intro βγ.
  
  apply hinhpr.
  use (bounded_simulation_trans αβ βγ).
Qed.

(*
Lemma ordinal_ordinal_is_ordinal : is_ordinal (ordinal_ordinal_lt).
Proof.
  repeat split.
  - admit.
  - admit.
  - intros α β γ αβ βγ.
    use (hinhuniv _ αβ).
    clear αβ; intro αβ.
    destruct αβ as [a aeq].
    use (hinhuniv _ βγ).
    clear βγ; intro βγ.
    destruct βγ as [b beq].


    (* todo: initial segment of initial segment *)
    apply hinhpr.
    unfold bounded_simulation.
    exists b.
    rewrite <- beq.

Qed. *)

Definition filtered_ordinal (α : cardinal) :=
    ∑ (ord : ordinal_with_sup), 
      ∏ (A : hsubtype ord), 
        (cardinal_leq (cardinalpr (carrier_subset A)) α) -> 
          (ordinal_lt (ordinal_sup ord A) ord).