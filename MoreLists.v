Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Algebra.Monoids_and_Groups.


Infix "::" := cons (at level 60, right associativity) : lists_scope.
Delimit Scope lists_scope with lists.
Bind Scope lists_scope with list.

Infix "++" := concatenate (right associativity, at level 60) : lists_scope.

Local Open Scope lists_scope.

Module ListsNotations.
Notation " [ ] " := nil (format "[ ]") : lists_scope.
Notation " [ x ] " := (cons x nil) : lists_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : lists_scope.
End ListsNotations.

Import ListsNotations.
Open Scope lists_scope.

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





  Definition concatenate_nil_runit (l : list A) : concatenate l [ ] = l.
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
  Proof.
    revert l1.
    use list_ind.
    - simpl.
      rewrite !concatenate_nil_lunit.
      reflexivity.
    - simpl ; intros x xs IH.
      rewrite !concatenateStep.
      rewrite IH.
      reflexivity.
  Defined.


  Definition reverse {X : UU} : list X -> list X.
  Proof.
    use list_ind.
    - apply nil.
    - intros x ? rev.
      exact (rev ++ (cons x nil)).
  Defined.

  Definition reverse_cons {X : UU} (x : X) (l : list X)
    : reverse (x :: l) = (reverse l) ++ [x].
  Proof.
    reflexivity.
  Defined.


  Definition list_ind_on (xs : list A) :
    ∏ (P : list A → UU), P nil → (∏ (x : A) (xs : list A), P xs → P (x :: xs)) → P xs.
    intros P X X0.
    exact (list_ind P X X0 xs).
  Defined.

  Lemma reverse_concatenate_distr : forall x y:list A, reverse (x ++ y) = reverse y ++ reverse x.
  Proof.
    intros x.
    apply (list_ind_on x).
    - simpl. intros y.
      apply (list_ind_on y).
      + apply idpath.
      + intros x0 xs X.
        now rewrite concatenate_nil_runit.
    - intros x0 xs IHl.
      simpl in *.
      intros y.
      clear x. rename x0 into a. rename xs into l.
      simpl.
      replace ((a :: l) ++ y) with (a :: (l ++ y)) by reflexivity.
      repeat rewrite reverse_cons.
      rewrite (IHl y).
      rewrite concatenate_assoc.
      apply idpath.
  Defined.

  Definition reverse_involutive (l : list A) : reverse (reverse l) = l.
  Proof.
    revert l.
    apply list_ind.
    - cbn. reflexivity.
    - intros x xs IH.
      replace (reverse (x :: xs)) with (reverse xs ++ [x]) by easy.
      rewrite (reverse_concatenate_distr (reverse xs) [x]).
      now rewrite IH.
  Defined.

End ListFacts.

Arguments reverse {_} _.
Arguments concatenate_assoc {_} _ _ _.
