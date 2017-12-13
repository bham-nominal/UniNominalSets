
Require Import UniMath.Ktheory.GroupAction.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartC.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.Algebra.Monoids_and_Groups.

(* Actually this is an equivalence *)
Lemma weq_eq {A B} (f g : A≃B) : pr1weq f = pr1weq g -> f = g.
  intro h.
  apply subtypeEquality'.
  - exact h.
  - apply isapropisweq.
Defined.

(* Group of permutation of a set *)
Section Permutations.

  Variable (A : hSet).

  Definition symmetries_hset : hSet :=
    (weq A A ,, isasetweqfromset _ _ (setproperty A)).

  Definition symmetries_binop : binop (weq A A) := weqcomp.

  Definition symmetries_is_group : isgrop symmetries_binop.
    use mk_isgrop.
    - use mk_ismonoidop.
      + intros f g h.
        now apply weq_eq.
      + exists (idweq A).
        now split; intro x; apply weq_eq.
    - exists invweq.
      split.
      + intro x.
        apply weqcompinvl.
      + intro x.
        apply weqcompinvr.
  Defined.

  Definition symmetries_group : gr := (symmetries_hset ,, symmetries_binop) ,, symmetries_is_group.
End Permutations.

Definition is_minimum (Q : nat -> UU) (n : nat) := Q n × (∏ p, Q p -> n <= p).
Definition isaprop_is_minimum (Q : nat -> UU) (n : nat) : isaprop (Q n) -> isaprop (is_minimum Q n).
 intro h.
 apply isapropdirprod.
 + exact h.
 + apply impred_isaprop.
   intro t.
   apply impred_isaprop.
   intro h'.
   apply isasetbool.
Defined.

Definition minsigma (Q  : nat -> UU) := ∑ (n : nat),is_minimum Q n.
Lemma minsigma_isaprop (Q : nat -> UU) (isPQ : forall n, isaprop (Q n)) : isaprop (minsigma Q).
Proof.
  use (isapropsubtype (fun Z => hProppair (is_minimum Q Z) _)).
  (*
forall n m,
*)
  - apply isaprop_is_minimum.
    apply isPQ.
  - cbn.
    intros p q hp hq.
    apply isantisymmnatleh.
    + apply (pr2 hp).
      now destruct hq.
    + apply (pr2 hq).
      now destruct hp.
Qed.



Section NominalSet.
Variable (X : hSet).
Variable (act : ActionStructure (symmetries_group natset) X).
(* Definition is_stn_strictly_increasing {m} (f : ⟦m⟧→nat) := ∏ (i j:⟦m⟧), i < j → f i < f j. *)
(* stn *)
Require Import UniMath.Combinatorics.StandardFiniteSets.
Open Scope stn.
Local Notation "g * x" := (act_mult act g x) : action_scope.
Open Scope action_scope.


Definition is_support_fun {m : nat} (f : ⟦m⟧→nat) :
  (∏ (s : weq nat nat),( ∏ y, s (f y) = y) -> s * x = x).

Definition is_support_of_size (x : X) (m : nat) (f : ⟦m⟧→nat)
           := (is_stn_strictly_increasing f) × (∏ (s : weq nat nat),( ∏ y, s (f y) = y) -> s * x = x).

(* Should be defined in the relevant file of UniMath *)
Lemma isaprop_is_stn_strictly_increasing {m} (f : ⟦m⟧→nat) : isaprop (is_stn_strictly_increasing f).
Proof.
  repeat (apply impred_isaprop; intros ?).
  apply isasetbool.
Qed.
Lemma isaprop_is_support_of_size x m f : isaprop (is_support_of_size x m f).
  apply isapropdirprod.
  - apply isaprop_is_stn_strictly_increasing.
  - repeat (apply impred_isaprop; intros ?).
    apply setproperty.
Qed.

Definition has_support_of_size (x : X) (m:nat) : UU :=
  ∑  (f : ⟦m⟧→nat), is_support_of_size x m f.

Definition has_finite_support (x : X) :=
  minsigma (has_support_of_size x).

Lemma isaprop_has_finite_support (x : X) : isaprop (has_finite_support x).
  apply minsigma_isaprop.
Lemma isaprop_support_of_size (x : X) (m : nat) : isaprop (has_support_of_size x m).
  use (isapropsubtype (fun Z => hProppair (is_support_of_size x m Z) _)).
  - apply isaprop_is_support_of_size.
  - cbn.
    intros f g hf hg.
  apply
