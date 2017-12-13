Add LoadPath "~/Documents/UniMath".
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.

Require Import PermLists.

Definition weq_compose
           {A B C : Type}
           (f : A ≃ B)
           (g : B ≃ C)
  : A ≃ C.
Proof.
  induction f as [f wef].
  induction g as [g weg].
  exists (g ∘ f).
  apply twooutof3c ; assumption.
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
  Variable (A : hSet)
           (dec_A : isdeceq A).


  Definition finite_perms : hsubtype (perm_group A isasetA).
  Proof.
    intros w.
    use hexists.
    - apply swap_list.
    - intros s.
      unfold perm_group in w.
      simpl in w.
      exact (w = swap_list_to_weq A dec_A s).
  Defined.

  Definition is_sub_gr_finite_perms : issubgr finite_perms.
  Proof.
    use tpair.
    - use tpair.
      + unfold issubsetwithbinop ; cbn.
        intros f1 f2.
        induction f1 as [w1 l1].
        induction f2 as [w2 l2].
        cbn.
        admit.
      + cbn.
        admit.
    - cbn.
      intros f.
      induction f as [w l].
      intros H.
      admit.
  Admitted.

End FinitePermutations.