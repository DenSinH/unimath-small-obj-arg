
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

From Model Require Import morphism_class retract.


Section wfs.

Local Open Scope cat.
Local Open Scope subtype.
(* Local Open Scope set. *)

Variables M : category.

(* todo: figure out how to import the notation and everything *)
(* todo: rlp/llp arguments *)
(* todo: morphism class arguments *)
Notation "S ⊆ T" := (morphism_class_containedIn M S T) (at level 70).

(* in a category, we know that homs are sets, so equality must be a prop *)
(* Lean: lp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L14 *)
(* Normal ∑-type is not a proposition, we need it to be to use it to create morphism classes *)
Definition lp {a b x y : M} (f : a --> b) (g : x --> y) : UU := 
    ∏ (h : a --> x) (k : b --> y), 
        g ∘ h = k ∘ f -> ∃ l : b --> x, (l ∘ f = h) × (g ∘ l = k).

Definition isaprop_lp {a b x y : M} (f : a --> b) (g : x --> y) : isaprop (lp f g).
Proof.
  apply impred_isaprop.
  intro.
  apply impred_isaprop.
  intro.
  apply impred_isaprop.
  intro.
  apply propproperty.
Defined.

Definition lp_hProp {a b x y : M} (f : a --> b) (g : x --> y) : hProp :=
    make_hProp (lp f g) (isaprop_lp f g).

(* Lean: llp @ https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L18 *)
(* 
       g
    A ---> E
    |     /|
  i |  λ/  | p
    v /    v
    X ---> B
       f 
*)
(* Messing with hProps gets a bit annoying at times *)
Definition llp (R : morphism_class M) : (morphism_class M) :=
    λ {a x : M} (i : a --> x), ∀ (e b : M) (p : e --> b), ((R _ _) p ⇒ lp_hProp i p)%logic.

Definition rlp (L : morphism_class M) : (morphism_class M) :=
    λ {e b : M} (p : e --> b), ∀ (a x : M) (i : a --> x), ((L _ _) i ⇒ lp_hProp i p)%logic.

(* There is stuff in 
  https://unimath.github.io/doc/UniMath/4dd5c17/UniMath.MoreFoundations.Subtypes.html
to do this, but I don't know if we want to use this or not...
I figured I'd define my own, it should be mostly compatible
*)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L24 *)
Lemma llp_anti {R R' : morphism_class M} (h : R ⊆ R') : llp R' ⊆ llp R.
Proof.
  unfold "⊆" in *.
  intros a x i H.
  intros e b p K.
  (* LLP for i in R' *)
  apply (H e b p).
  (* R ⊆ R' *)
  apply (h e b p).
  (* i in R *)
  exact K.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L27 *)
(* todo: in lean this is also a Prop? *)
Record is_wfs (L R : morphism_class M) (* : Prop *) := {
  wfs_llp  : L = llp R;
  wfs_rlp  : R = rlp L;
  (* Any map can be factored through maps in L and R *)
  wfs_fact : ∀ x y (f : x --> y), ∃ z (g : x --> z) (h : z --> y),
             (L _ _) g × (R _ _) h × h ∘ g = f
}.

Arguments wfs_llp {_ _}.
Arguments wfs_rlp {_ _}.
Arguments wfs_fact {_ _}.

(* Can't do dot notation like in lean (is_wfs.lp)*)
(* any two maps in a wfs have the lifting property with respect to each other *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L33 *)
Lemma is_wfs'lp {L R : morphism_class M} (w : is_wfs L R)
  {a b x y} {f : a --> b} {g : x --> y} (hf : (L _ _) f) (hg : (R _ _) g) : lp_hProp f g.
Proof.
  rewrite w.(wfs_llp) in hf.
  exact (hf _ _ _ hg). 
Defined.

(* if f' is a retract of f and f is in L for some WFS, then so is f'  *)
(* proposition 14.1.13 in More Concise AT *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L40 *)
Lemma is_wfs'retract {L R : morphism_class M} (w : is_wfs L R)
  {a b a' b'} {f : a --> b} {f' : a' --> b'} (r : retract M f f') (hf : (L _ _) f) : (L _ _) f'.
Proof.
  rewrite w.(wfs_llp).
  intros x y g hg h k s.
  (* existence of lift in part of diagram *)
  specialize (is_wfs'lp w hf hg (h ∘ r.(ra _ _ _)) (k ∘ r.(rb _ _ _))) as ehl.
  
  unshelve epose proof (ehl _) as ehl.
  {
    rewrite <- assoc, s, assoc, assoc, (r.(hr _ _ _)).
    reflexivity.
  }
  
  (* extract lift and turn proof into normal ∑-type *)
  unshelve eapply (hinhuniv _ ehl).
  intro hl.
  apply hinhpr.
  destruct hl as [l [hlh hlk]].
  (* composition in diagram *)
  exists (l ∘ r.(ib _ _ _)).
  (* diagram chasing *)
  split.
  * rewrite assoc, <- (r.(hi _ _ _)), <- assoc, hlh, assoc, r.(ha _ _ _), id_left.
    reflexivity.
  * rewrite <- assoc, hlk, assoc, r.(hb _ _ _), id_left.
    reflexivity.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L52 *)
(* Lemma 14.1.9 in MCAT *)
Lemma llp_rlp_self (L : morphism_class M) : L ⊆ llp (rlp L).
Proof.
  intros a b f hf x y g hg.
  apply (hg _ _ _).
  exact hf.
Defined.

(* no counterpart *)
Lemma rlp_llp_self (L : morphism_class M) : L ⊆ rlp (llp L).
Proof.
  intros a b f hf x y g hg.
  apply (hg _ _ _).
  exact hf.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L55 *)
(* No counterpart in MCAT, (□(I□), I□) is a WFS *)
Lemma wfs_of_factorization (I : morphism_class M) 
  (h : ∀ {x y} (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (llp (rlp I) _ _ g) × (rlp I _ _ h) × (h ∘ g = f)) :
  is_wfs (llp (rlp I)) (rlp I).
Proof.
  constructor.
  - reflexivity.
  - apply morphism_class_equal_cond.
    split; intros x y g hg.
    * exact (rlp_llp_self _ _ _ _ hg).
    * intros a b f hf.
      apply (hg _ _ _).
      exact (llp_rlp_self _ _ _ _ hf).
  - exact h.
Defined.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L67 *)
(* same name as Lemma 14.1.12 in MCAT, but a different phrasing 
In MCAT, the statement is in reference of a single morphism, not a whole class
*)
Lemma retract_argument {L R L' : morphism_class M} (w : is_wfs L R)
  (H : ∀ {x y} (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (L' _ _) g × (R _ _) h × h ∘ g = f) :
  ∏ {a b} (f : a --> b), (L _ _) f -> ∃ {x' y'} (f' : x' --> y') (r : retract _ f' f), (L' _ _) f'.
Proof.
  intros a b f hf.

  (* rcases H f with ⟨z, g, h, hg, hh, hgh⟩, *)
  (* Get factorization for f from H *)
  specialize (H _ _ f) as eHf.
  simpl in eHf.
  unshelve eapply (hinhuniv _ eHf).
  intro Hf.
  destruct Hf as [z [g [h [hg [hh hgh]]]]].

  (* rcases w.lp hf hh g (𝟙 _) (by rw hgh; simp) with ⟨l, hl₁, hl₂⟩, *)
  (* Use lifting property to get map in diagram *)
  specialize (is_wfs'lp w hf hh g (identity _)) as ehl.
  unshelve epose proof (ehl _) as ehl.
  {
    rewrite hgh, id_right.
    reflexivity.
  }
  unshelve eapply (hinhuniv _ ehl).
  intro hl.
  destruct hl as [l [hl1 hl2]].

  (* convert goal to normal ∑-type *)
  apply hinhpr.

  (* Show that g is a retract of f *)
  assert (r : retract _ g f).
  {
    split with (identity a) (identity a) l h.
    - now rewrite id_left.
    - exact hl2.
    - rewrite id_left.
      now symmetry.
    - rewrite id_left.
      now symmetry.
  }

  (* finish proof *)
  exists a, z, g, r.
  exact hg.
Defined.

Lemma lp_isos_univ {a b x y} (f : a --> b) (g : x --> y) : 
  (morphism_class_isos M _ _) f -> lp f g.
Proof.
  intro H.
  intros h k s.
  simpl in H.
  remember (make_iso _ H) as fiso.
  replace f with (morphism_from_iso fiso) in *.
  - (* todo: this in happly tactic? *)
    apply hinhpr.
    exists (h ∘ (inv_from_iso fiso)).
    split.
    * rewrite assoc, iso_inv_after_iso, id_left.
      reflexivity.
    * rewrite <- assoc, s, assoc.
      rewrite iso_after_iso_inv, id_left.
      reflexivity.
  - (* todo: by clause in replace? *)
    rewrite Heqfiso.
    trivial.
Defined.

Lemma llp_univ : llp (morphism_class_univ M) = morphism_class_isos M.
Proof.
  apply morphism_class_equal_cond.
  split; intros a b f H.
  - specialize ((H _ _ f) tt).
    specialize (H (identity _) (identity _)).
    unshelve epose proof (H _) as H.
    {
      rewrite id_left, id_right.
      reflexivity.
    }
    (* todo: turn this unshelve eapply / destruct into an Ltac *)
    unshelve eapply (hinhuniv _ H).
    intro hl.
    destruct hl as [l [hfl hlf]].
    unfold morphism_class_isos.
    
    assert (is_z_isomorphism f) as f_z_iso.
    {
      exists l.
      split; assumption.
    }
    apply is_iso_from_is_z_iso.
    exact f_z_iso.
  - intros x y g _.
    exact (lp_isos_univ f g H).
Defined.

Lemma rlp_isos : rlp (morphism_class_isos M) = morphism_class_univ M.
Proof.
  (* This proof is slightly different *)
  apply morphism_class_equal_cond.
  split.
  - intros x y g H.
    unfold morphism_class_univ.
    exact tt.
  - rewrite <- llp_univ.
    exact (rlp_llp_self _).
Defined.

Lemma wfs_isos_univ : is_wfs (morphism_class_isos M) (morphism_class_univ M).
Proof.
  constructor; try symmetry.
  - exact llp_univ.
  - exact rlp_isos.
  - intros x y f.
    apply hinhpr.
    exists x, (identity x), f.
    split; repeat try split.  (* todo: somehow, this solves the second subgoal? *)
    * exact (identity_is_iso M x).
    * rewrite id_left.
      reflexivity.
Defined.



End wfs.