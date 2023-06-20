Require Import UniMath.MoreFoundations.All.

Require Import CategoryTheory.FoundationsSets.

Declare Scope cardinal_scope.
Local Open Scope cardinal_scope.
Local Open Scope type_scope.

(* We just view cardinals as hSets, that way it is easier to work with
   The only time we really need the set trunctation is when regarding
   the equality of cardinals. For this we can *)
Definition cardinal : UU := hSet.
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

Lemma cardinal_eq (A B : cardinal) :
    pr1 A = pr1 B -> A = B.
Proof.
  intro H.
  apply subtypePath; [intro; apply isapropiseqclass|].
  exact H.
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

Admitted.

Lemma cardinal_leq_trans : istrans cardinal_leq.
Proof.
  
Admitted.