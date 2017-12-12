Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Ktheory.GroupAction.
Require Import UniMath.Foundations.Sets.

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


Section Perm.

  Context (A : hSet).

  Definition supp : hSet := @setlist (setdirprod A A).

  Definition unit : supp := nil.
  Definition mult : supp -> supp -> supp := concatenate.
  Definition inv  : supp -> supp := rev (setdirprod A A).

  Definition assoc : isassoc mult := concatenate_assoc (setdirprod A A).

  Definition unital : isunital mult.
    use isunitalpair.
    - exact unit.
    - split.
      + unfold islunit.
        reflexivity.
      + unfold isrunit.
        intros.
        apply concatenate_nil_lunit.
  Defined.

  Definition monoidop : ismonoidop mult.
  apply mk_ismonoidop.
  - exact assoc.
  - exact unital.
  Defined.

  Definition invstruct : invstruct mult monoidop.
  use mk_invstruct.
  - exact inv.
  - unfold unel_is. simpl.
    apply mk_isinv.
    + unfold islinv.
      intros.

    + unfold isrinv.
      intros.
      admit.
  Admitted.

  Definition grop : isgrop mult.
  use mk_isgrop.
  - exact monoidop.
  - exact invstruct.
  Defined.


  Definition Perm : gr.
    use grconstr.
    - use setwithbinoppair.
      + exact supp.
      + exact mult.
    - simpl. exact grop.
  Defined.


End Perm.



Section Nom.
  Context (AtomSet : hSet).
  Context (PermASet : UU).
  Context (finitelySupported : ∀ {X : PermASet}, X -> UU).

  Definition isNominalSet (X : PermASet) :=
    ∀ x : X, finitelySupported x.

End Nom.