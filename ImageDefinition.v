Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Ktheory.GroupAction.

Require Import MoreLists.
Require Import PermLists.

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
      apply (weqcomp f g).
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

(*
Section GroupAction.
  Definition action (A : UU) (G : gr) : UU.
  Proof.
    use (∑ (f : G -> A -> A), _ × _).
    - exact (forall (a : A), f (unel G) a = a).
    - exact (forall (g1 g2 : G) (a : A), f (op g1 g2) a = f g1 (f g2 a)).
  Defined.

  Definition mult_action (G : gr) : action G G.
  Proof.
    exists op.
    split ; [ apply lunax | apply assocax ].
  Defined.
End GroupAction.
*)

Definition finite_perm_gr : gr.
Proof.
  use carrierofasubgr.
  apply (perm_group nat isasetnat).
  unfold subgr.
  exists (@finite_perms natset isdeceqnat).
  exact (@is_sub_gr_finite_perms natset isdeceqnat).
Defined.

Definition app_action : ActionStructure finite_perm_gr natset.
Proof.
  use make.
  - intros f n.
    apply (pr1 (pr1 f) n).
  - simpl.
    apply idpath.
  - intros f1 f2 n.
    induction f1 as [f1 p1].
    induction f2 as [f2 p2].
    simpl.
    apply idpath.
Defined.

Definition member {A : UU} (deceqA : isdeceq A) : A -> list A -> bool.
Proof.
  intros a.
  use list_ind.
  - apply false.
  - simpl ; intros x xs IH.
    induction (deceqA a x).
    + apply true.
    + apply IH.
Defined.

Definition nominal_set : UU.
Proof.
  use (∑ (X : hSet) (f : ActionStructure finite_perm_gr X), ∀ (x : X),
          hexists (fun l : list nat => _)).
  induction f as [f p].
  use (∀ (π : finite_perm_gr), _).
  use himpl.
  - use (∀ (n : nat), _).
    use himpl.
    + use eqset.
      * exact boolset.
      * exact (member isdeceqnat n l).
      * exact true.
    + unfold finite_perm_gr in π.
      use eqset.
      * exact natset.
      * exact (pr1 (pr1 π) n).
      * exact n.
  - use eqset ; [ apply X | apply (f π x) | apply x].
Defined.

Definition nat_nominal_set : nominal_set.
Proof.
  unfold nominal_set.
  exists natset.
  use tpair.
  - apply app_action.
  - simpl.
    intros n.
    apply total2tohexists.
    exists (cons n nil).
    intros x H.
    apply (H n).
    cbn.
    destruct (isdeceqnat n n).
    + simpl.
      reflexivity.
    + use fromempty.
      apply n0.
      apply idpath.
Defined.
