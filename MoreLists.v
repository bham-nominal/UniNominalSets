Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.Monoids_and_Groups.


Section ListFacts.
  Context (A : hSet).

  Fact list_preserve_hset : isofhlevel 2 (list A).
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

  Definition rev l :=
    foldr (fun x acc => @cons A x acc) nil l.

  Definition concatenate_nil_lunit (l : list A) : concatenate l nil = l.
    use (list_ind (λ l, concatenate l nil = l)).
    - reflexivity.
    - intros.
      simpl.
      simpl in X.
      rewrite (concatenateStep).
      rewrite X.
      reflexivity.
  Defined.

  Definition concatenate_assoc (l1 l2 l3 : list A) :
    concatenate (concatenate l1 l2) l3 = concatenate l1 (concatenate l2 l3).
  Admitted.

End ListFacts.
