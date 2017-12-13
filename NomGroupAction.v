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
  Context (dec : isdeceq A).

  Definition carrier : hSet := @setlist (setdirprod A A).

  Definition swap (a₁ a₂ : A) (a : A) : A.
    apply (@coprod_rect (a₁ = a) (a₁ != a)).
    - intros eq. exact a₂.
    - intros neq.
      apply (@coprod_rect (a₂ = a) (a₂ != a)).
      + intros eq. exact a₁.
      + intros neq_a_a₂. exact a.
      + exact (dec a₂ a).
    - exact (dec a₁ a).
  Defined.

  Definition actA : carrier -> A -> A.
    intros l a.
    apply (@list_ind (setdirprod A A)).
    - exact a.
    - intros x xs a'.
      (* actA xs a = a' *)
      exact (swap (pr1 x) (pr2 x) a').
    - exact l.
  Defined.

  Definition hrel_gr : hrel carrier.
    unfold hrel.
    intros l₁ l₂.
    use hProppair.
    - exact (actA l₁ = actA l₂).
    - assert (isaset (A -> A)).
      + apply isaset_forall_hSet.
      + apply X.
  Defined.

  Definition equiv_gr : eqrel carrier.
    use eqrelconstr.
    - exact hrel_gr.
    - intros l₁ l₂ l₃.
      intros H₁ H₂.
      unfold hrel_gr in *.
      simpl in *.
      rewrite H₁. exact H₂.
    - intros l. simpl. reflexivity.
    - intros l₁ l₂ H. simpl in *. symmetry. exact H.
  Defined.

  Definition carrier_q : hSet := setquotinset equiv_gr.

  Definition unit : carrier_q.
    use setquotpair.
    - exact (setquotpr equiv_gr nil).
    - use iseqclassconstr.
      + apply hinhpr.
        simpl.
        use (carrierpair).
        * exact nil.
        * simpl.
          reflexivity.
      + intros.
        simpl in *.
        rewrite X0. exact X.
      + intros. simpl in *.
        rewrite <- X.
        exact X0.
  Defined.

  Definition concatenate_q (l₁ l₂ : carrier) : carrier_q.
    use setquotpair.
    - exact (setquotpr equiv_gr (concatenate l₁ l₂)).
    - use iseqclassconstr.
      + apply hinhpr.
        use carrierpair.
        * exact (concatenate l₁ l₂).
        * simpl. reflexivity.
      + intros. simpl in *.
        rewrite X in X0.
        exact X0.
      + intros. simpl in *.
        rewrite X in X0. exact X0.
  Defined.

  Fact compat_concat : iscomprelfun2 equiv_gr concatenate_q.
    intros x ? y y' R_x_x' R_y_y'.
    simpl in R_x_x', R_y_y'.
    Check concatenate_q x y.
    (* use iseqclass *)
    pose (iseqclass equiv_gr).
    unfold iseqclass in u.
    pose (concatenate_q x y).
    pose (pr1 p).
    pose (pr2 p). cbn beta in i.

    unfold p in h. hnf in h.
    use total2_paths_f.
    - simpl.
      remember (fun x1 : list (dirprod (pr1hSet A) (pr1hSet A)) =>
                  hrel_gr (@concatenate (dirprod (pr1hSet A) (pr1hSet A)) x y) x1) as lhs.
      remember (fun x1 : list (dirprod (pr1hSet A) (pr1hSet A)) =>
                  hrel_gr (@concatenate (dirprod (pr1hSet A) (pr1hSet A)) x' y') x1) as rhs.

      pose @funextfun. unfold funextfunStatement in f.
      pose @impred_prop.
      pose (i0 carrier lhs).

    (* Because x and x' induce the same action, they should be in the same
       equivalence class.

       We want to show that the equivalence classes of x@x0 and x'@x0' are the
       same, i.e. [x@x0] = [x'@x0']. 

     *)

    unfold concatenate_q.
    unfold setquotpair. simpl.

  Definition mult : carrier_q -> carrier_q -> carrier_q.
    intros g₁ g₂.
    exact (setquotuniv2 equiv_gr carrier_q concatenate_q compat_concat g₁ g₂).
  Defined.

  Definition inv  : carrier_q -> carrier_q := rev (setdirprod A A).

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
      + exact carrier.
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