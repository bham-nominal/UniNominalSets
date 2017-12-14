Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.Monoids_and_Groups.


Section ListFacts.
  Context (A : hSet).

  Fact list_preserve_hset : isaset (list A).
  Proof.
    unfold list.
    eapply (@isofhleveltotal2 2).
    - pose isasetnat.
      exact i.
    - intros.
      induction x.
      + apply (isasetunit).
      + apply isofhleveldirprod.
        * exact (setproperty A).
        * exact IHx.
  Qed.

  Definition setlist : hSet.
    use hSetpair.
    - exact (list A).
    - apply list_preserve_hset.
  Defined.


  Definition reverse {X : UU} : list X -> list X.
  Proof.
    use list_ind.
    - apply nil.
    - intros x ? rev.
      exact (concatenate rev (cons x nil)).
  Defined.

  Definition reverse_cons {X : UU} (x : X) (l : list X)
    : reverse (cons x l) = concatenate (reverse l) (cons x nil).
  Proof.
    reflexivity.
  Defined.

  Definition concatenate_nil_runit (l : list A) : concatenate l nil = l.
    use (list_ind (λ l, concatenate l nil = l)).
    - reflexivity.
    - intros.
      simpl.
      simpl in X.
      rewrite (concatenateStep).
      rewrite X.
      reflexivity.
  Defined.


  Definition concatenate_nil_lunit {X : UU} : forall (l : list X), concatenate nil l = l.
  Proof.
    reflexivity.
  Defined.


  Definition concatenate_assoc (l1 l2 l3 : list A) :
    concatenate (concatenate l1 l2) l3 = concatenate l1 (concatenate l2 l3).
  Admitted.

End ListFacts.

Arguments reverse {_} _.
