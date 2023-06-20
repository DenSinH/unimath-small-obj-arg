Require Import UniMath.MoreFoundations.All.


Definition path_eqrel
           (X : UU)
  : eqrel X.
Proof.
  use make_eqrel.
  - exact (λ x₁ x₂, ∥ x₁ = x₂ ∥).
  - repeat split.
    + intros x₁ x₂ x₃.
      use factor_through_squash.
      {
        apply impred ; intro.
        apply propproperty.
      }
      intro p.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro q.
      apply hinhpr.
      exact (p @ q).
    + intros x.
      exact (hinhpr (idpath _)).
    + intros x₁ x₂.
      use factor_through_squash.
      {
        apply propproperty.
      }
      intro p.
      apply hinhpr.
      exact (!p).
Defined.

Definition settrunc
           (X : UU)
  : hSet
  := setquotinset (path_eqrel X).

Definition settruncin
           (X : UU)
  : X -> settrunc X
  := setquotpr (path_eqrel X).

Definition settrunc_rec
           (X : UU)
           {Y : hSet}
           (i : X → Y)
  : settrunc X → Y.
Proof.
  use setquotuniv.
  - exact i.
  - intros x₁ x₂.
    use factor_through_squash.
    {
      apply setproperty.
    }
    intro p.
    exact (maponpaths i p).
Defined.

Definition settrunc_rec_eq
           (X : UU)
           {Y : hSet}
           (i : X → Y)
           (x : X)
  : settrunc_rec X i (settruncin X x) = i x.
Proof.
  apply idpath.
Qed.

Definition settrunc_rec_unique
           (X : UU)
           {Y : hSet}
           (i : X → Y)
           (f g : settrunc X → Y)
           (p : ∏ (x : X), f (settruncin X x) = g (settruncin X x))
  : f = g.
Proof.
  use funextsec.
  use setquotunivprop'.
  {
    intro.
    apply setproperty.
  }
  intro x.
  cbn.
  exact (p x).
Qed.

Section SetTruncPropInd.
  Context {X : UU}
          {Y : settrunc X -> UU}
          (Yisaprop : ∏ (x : settrunc X), isaprop (Y x))
          (iY : ∏ (x : X), Y (settruncin X x)).

  Definition total_space
    : hSet
    := (∑ (x : settrunc X), make_hSet (Y x) (isasetaprop (Yisaprop x)))%set.

  Definition map_to_total_space
    : settrunc X -> total_space.
  Proof.
    use settrunc_rec.
    exact (λ x, settruncin X x ,, iY x).
  Defined.

  Definition map_to_total_space_commute
             (x : settrunc X)
    : pr1 (map_to_total_space x) = x.
  Proof.
    use (eqtohomot
           (@settrunc_rec_unique
              X
              (settrunc X)
              (settruncin X)
              (λ x, pr1 (map_to_total_space x))
              (λ x, x)
              _)
           x).
    clear x.
    intro x.
    cbn.
    apply idpath.
  Qed.

  Definition settrunc_prop_ind
             (x : settrunc X)
    : Y x
    := transportf Y (map_to_total_space_commute x) (pr2 (map_to_total_space x)).
End SetTruncPropInd.

Section SetTruncInd.
  Context {X : UU}
          {Y : settrunc X -> UU}
          (Yisaset : ∏ (x : settrunc X), isaset (Y x))
          (iY : ∏ (x : X), Y (settruncin X x)).

  Definition total_space_set
    : hSet
    := (∑ (x : settrunc X), make_hSet (Y x) (Yisaset x))%set.

  Definition map_to_total_space_set
    : settrunc X -> total_space_set.
  Proof.
    use settrunc_rec.
    exact (λ x, settruncin X x ,, iY x).
  Defined.

  Definition map_to_total_space_set_commute
             (x : settrunc X)
    : pr1 (map_to_total_space_set x) = x.
  Proof.
    use (eqtohomot
           (@settrunc_rec_unique
              X
              (settrunc X)
              (settruncin X)
              (λ x, pr1 (map_to_total_space_set x))
              (λ x, x)
              _)
           x).
    clear x.
    intro x.
    cbn.
    apply idpath.
  Qed.

  Definition settrunc_ind
             (x : settrunc X)
    : Y x
    := transportf Y (map_to_total_space_set_commute x) (pr2 (map_to_total_space_set x)).
End SetTruncInd.

Notation "∥ A ∥_0" := (settrunc A) (at level 20) : type_scope.

Definition settruncpr {X : UU} : X -> ∥ X ∥_0 := setquotpr _.

Definition settruncfun {X Y : UU} (f : X -> Y) : ∥ X ∥_0 -> ∥ Y ∥_0.
Proof.
  intro x0.
  use (setquotfun _ _ f _ x0).
  intros x y R.

  change (∥f x = f y∥).
  use (hinhuniv _ R).
  clear R; intro R.
  apply hinhpr.
  apply maponpaths.
  exact R.
Defined.

Definition settruncuniv {X : UU} {S : hSet} (f : X -> S) (wit : ∥ X ∥_0) : S.
Proof.
  use (@settrunc_ind X (λ _, S) (λ _, setproperty S) (λ x, f x) wit).
Defined.

Definition settruncpropuniv {X : UU} {P : hProp} (f : X -> P) (wit : ∥ X ∥_0) : P.
Proof.
  use (@settrunc_prop_ind X (λ _, P) (λ _, propproperty P) (λ x, f x) wit).
Defined.

(* Proposition settrunc_unique
    {X : UU}
    {Y : hSet}
    (i : X → Y)
    (f g : settrunc X → Y)
    (p : ∏ (x : X), f (settruncpr x) = g (settruncpr x))
  : f = g.
Proof.
  apply funextsec.
  intro x.
  
Qed. *)


Declare Scope cardinal_scope.
Local Open Scope cardinal_scope.
Local Open Scope type_scope.

Definition cardinal : hSet := ∥hSet∥_0.
Definition cardinalpr (A : hSet) : cardinal := settruncpr A.

Definition cardinal_add (A B : cardinal) : cardinal.
Proof.
  use (settruncuniv _ A).
  clear A; intro A.
  use (settruncuniv _ B).
  clear B; intro B.
  apply settruncpr.

  use make_hSet.
  - exact (A ⨿ B).
  - apply isasetcoprod; apply setproperty.
Defined.

Definition cardinal_mul (A B : cardinal) : cardinal.
Proof.
  use (settruncuniv _ A).
  clear A; intro A.
  use (settruncuniv _ B).
  clear B; intro B.
  apply settruncpr.
  
  use make_hSet.
  - exact (A × B).
  - apply isaset_dirprod; apply setproperty.
Defined.

(* two cardinals are equal if any set is of cardinality A
   if and only if it is of cardinality B *)
Lemma cardinal_eq (A B : cardinal) :
    (∏ (x : hSet), pr1 A x <-> pr1 B x) -> A = B.
Proof.
  intro H.
  apply subtypePath; [intro; apply isapropiseqclass|].
  apply funextsec.
  intro.
  apply hPropUnivalence; apply H.
Qed.

Notation "A + B" := (cardinal_add A B) : cardinal_scope.
Notation "A * B" := (cardinal_mul A B) : cardinal_scope.

(* Lemma cardinal_add_assoc (A B C : cardinal) : 
    (A + B) + C = A + (B + C).
Proof.
  use cardinal_eq.
  
Qed. *)

Definition cardinal_leq : hrel cardinal.
Proof.
  intros A B.
  change (make_hSet _ isasethProp).
  (* use (settrunc_ind _ _ A); intro a; [apply isasethProp|].
  simpl.
  use (settrunc_ind _ _ B); intro b; [apply isasethProp|].
  simpl.
  exact (∃ f : a -> b, isInjective f). *)

  use (settruncuniv _ A).
  clear A; intro A.
  use (settruncuniv _ B).
  clear B; intro B.
  exact (∃ f : A -> B, isInjective f).
Defined.

Notation "A ≤ B" := (cardinal_leq A B) : cardinal_scope.


Lemma cardinal_leq_refl : isrefl cardinal_leq.
Proof.
  intro.
  unfold cardinal_leq.
  unfold cardinal in x.
  unfold settruncuniv.
  simpl.
Admitted.

Lemma cardinal_leq_trans : istrans cardinal_leq.
Proof.
  
Admitted.