Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.

Require Import MoreLists.
Require Import PermLists.


Definition weq_compose
           {A B C : Type}
           (f : A ≃ B)
           (g : B ≃ C)
  : A ≃ C.
Proof.
  now apply (weqcomp f).
  (* induction f as [f wef]. *)
  (* induction g as [g weg]. *)
  (* exists (g ∘ f). *)
  (* apply twooutof3c ; assumption. *)
Defined.

Section PermutationGroup.
  Variable (A : UU)
           (isasetA : isaset A).

  Definition perm_op : setwithbinop.
  Proof.
    unfold setwithbinop.
    use tpair.
    - use tpair.
      + exact (weq A A).
      + simpl.
        apply isasetweqtoset.
        exact isasetA.
    - simpl.
      intros g f.
      apply (weq_compose f g).
  Defined.

  Definition perm_group : gr.
  Proof.
    unfold gr.
    exists perm_op.
    use tpair.
    - unfold ismonoidop.
      use tpair.
      + intros f g h.
        use pair_path_in2.
        apply isapropisweq.
      + simpl.
        unfold isunital, isunit, islunit, isrunit.
        exists (idweq A).
        use tpair.
        * simpl.
          intros f.
          induction f as [f wef].
          use pair_path_in2.
          apply isapropisweq.
        * simpl.
          intros f.
          induction f as [f wef].
          use pair_path_in2.
          apply isapropisweq.
    - use tpair.
      + simpl.
        apply invweq.
      + use tpair.
        * intros f.
          unfold unel_is.
          simpl.
          use total2_paths2_f.
          -- apply funextfun.
             intros z.
             apply homotinvweqweq.
          -- apply isapropisweq.
        * intros f.
          unfold unel_is.
          simpl.
          use total2_paths2_f.
          -- apply funextfun.
             intros z.
             apply homotweqinvweq.
          -- apply isapropisweq.
  Defined.
End PermutationGroup.

Section FinitePermutations.
  Context  {A : hSet}
           (dec_A : isdeceq A).

  Definition isasetA : isaset A.
  Proof.
    use isasetifdeceq.
    assumption.
  Defined.

  Definition finite_perms : hsubtype (perm_group A isasetA).
  Proof.
    intros w.
    use hexists.
    - apply (@swap_list A).
    - intros s.
      exact (w = swap_list_to_weq dec_A s).
  Defined.

  Definition is_sub_gr_finite_perms : issubgr finite_perms.
  Proof.
    use tpair.
    - use tpair.
      + intros f1 f2.
        induction f1 as [w1 l1'].
        induction f2 as [w2 l2'].
        unfold finite_perms in *.
        apply (Propositions.squash_to_hProp l1').
        intro l1.
        apply (Propositions.squash_to_hProp l2').
        intro l2.
        apply total2tohexists ; cbn.
        clear l1' l2'.
        induction l1 as [l1 p1].
        induction l2 as [l2 p2].
        rewrite p1, p2. clear p1. clear p2.
        use tpair.
        * exact (concatenate l1 l2).
        * cbn.
          apply swap_list_to_weq_concat.
      + cbn.
        apply total2tohexists.
        use tpair.
        * exact nil.
        * reflexivity.
    - intros w.
      induction w as [w we].
      intros l'.
      unfold finite_perms in *.
      apply (Propositions.squash_to_hProp l').
      intro l. clear l'.
      induction l as [l p].
      rewrite p. clear p.
      apply total2tohexists ; cbn.
      now apply weq_inverse_list.
  Defined.

End FinitePermutations.
