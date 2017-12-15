Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Ktheory.GroupAction.
Require Import UniMath.Foundations.Sets.

Require Import MoreLists.
Require Import PermLists.

Section Perm.

  Local Open Scope lists_scope.

  Context {A : hSet}.
  Context (dec_A : isdeceq A).

  Definition carrier : hSet := @swap_list A.

  Definition actA_f : carrier -> A -> A.
    intros l a.
    apply (@list_ind (setdirprod A A)).
    - exact a.
    - intros x xs a'.
      (* actA xs a = a' *)
      exact (swap_map dec_A x a').
    - exact l.
  Defined.

  Fact act_cons_swap : forall x xs, actA_f (x :: xs) = swap_map dec_A x ∘ actA_f xs.
  Proof.
    intros.
    unfold actA_f.
    apply funextfun.
    intros a.
    simpl.
    rewrite list_ind_compute_2.
    unfold funcomp.
    reflexivity.
  Defined.

  Lemma act_concat_comp : forall l1 l2, actA_f (concatenate l1 l2) = (actA_f l1) ∘ (actA_f l2).
  Proof.
    intros l1 l2.
    apply (@list_ind (setdirprod A A)
                     (λ l1, actA_f (concatenate l1 l2) = actA_f l1 ∘ actA_f l2)).
    - apply idpath.
    - intros.
      rewrite concatenateStep.
      idtac.
      pose (act_cons_swap x (xs ++ l2)).
      rewrite X in p.
      rewrite funcomp_assoc in p.
      rewrite <- (act_cons_swap x xs) in p.
      exact p.
  Defined.

  Lemma act_reverse_inverse (l : carrier) :
    ∏ x : A, actA_f (reverse l) (actA_f l x) = x.
  Proof.
    intro a.
    apply (@list_ind (setdirprod A A) (fun l => actA_f (reverse l) (actA_f l a) = a)).
    - cbn. apply idpath.
    - intros x xs h.
      rewrite reverse_cons. rewrite act_concat_comp.
      rewrite 2 act_cons_swap.
      unfold funcomp. cbn.
      rewrite swap_auto_inv. exact h.
  Defined.

  Definition actA : carrier -> A ≃ A.
    intros l.
    use weqgradth.
    - exact (actA_f l).
    - exact (actA_f (reverse l)).
    - apply act_reverse_inverse.
    - pose (act_reverse_inverse (reverse l)).
      rewrite reverse_involutive in p. apply p.
  Defined.

  Definition hrel_gr : hrel carrier.
    unfold hrel.
    intros l₁ l₂.
    use hProppair.
    - exact (actA_f l₁ = actA_f l₂).
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
    apply subtypeEquality'.
    - simpl. change (fun x => ?h x) with h.
      pose @funextfun. unfold funextfunStatement in f.
      apply f. intro l.
      apply subtypeEquality'.
      + simpl. rewrite 2 act_concat_comp.
        now rewrite R_x_x', R_y_y'.
      + apply isapropisaprop.
    - apply isapropiseqclass.
  Defined.

  Definition mult : carrier_q -> carrier_q -> carrier_q.
    intros g₁ g₂.
    exact (setquotuniv2 equiv_gr carrier_q concatenate_q compat_concat g₁ g₂).
  Defined.

  Definition inv_q (l : carrier) : carrier_q.
    use setquotpair.
    - exact (setquotpr equiv_gr (reverse l)).
    - use iseqclassconstr.
      + apply hinhpr.
        use carrierpair.
        * exact (reverse l).
        * simpl. apply idpath.
      + intros l1 l2 R_l1_l2 Rl1. simpl in *.
        rewrite Rl1. assumption.
      + intros l1 l2 h h'. simpl in *.
        rewrite <- h. exact h'.
  Defined.

  Lemma act_rev : forall l, actA_f (reverse l) = invmap (actA l).
  Proof.
    intro l.
    pose (h := act_reverse_inverse l).
    change (∏ x : A, actA_f (reverse l) (actA_f l x) = x)
    with (((actA_f (reverse l)) ∘ (actA_f l)) ~ idfun A) in h.
    pose (h' := funhomot (invmap (actA l)) h).
    assert (eq : actA_f l ∘ invmap (actA l) = idfun A).
    { apply funextfun. intro x. unfold idfun, funcomp.
      change (actA_f l (invmap (actA l) x) = x)
      with (actA l (invmap (actA l) x) = x).
      apply homotweqinvweq.
    }
    rewrite <- funcomp_assoc in h'.
    rewrite eq in h'.
    assert (obv1 : actA_f (reverse l) ∘ idfun A = actA_f (reverse l)).
    { apply funextfun. intro x. unfold funcomp, idfun. apply idpath. }
    assert (obv2 : idfun A ∘ invmap (actA l) = invmap (actA l)).
    { apply funextfun. intro x. unfold funcomp, idfun. apply idpath. }
    rewrite obv1, obv2 in h'.
    apply funextfun. apply h'.
  Defined.

  Fact compat_inv : iscomprelfun equiv_gr inv_q.
  Proof.
    intros l1 l2 R_l1_l2. simpl in *.
    apply subtypeEquality'.
    - simpl. change (fun x => ?h x) with h.
      pose @funextfun. unfold funextfunStatement in f.
      apply f. intro l.
      apply subtypeEquality'.
      + simpl. rewrite 2 act_rev.
        assert (h : actA l1 = actA l2).
        { apply subtypeEquality'.
          - simpl. assumption.
          - apply isapropisweq.
        }
        rewrite h. apply idpath.
      + apply isapropisaprop.
    - apply isapropiseqclass.
  Defined.

  Definition inv : carrier_q -> carrier_q.
    intros g.
    exact (setquotuniv equiv_gr carrier_q inv_q compat_inv g).
  Defined.

  Definition unital : isunital mult.
    use isunitalpair.
    - exact unit.
    - use isunitpair.
      + assert (h : forall l, isaprop (mult unit l = l)).
        { intro l'. apply (setproperty carrier_q). }
        pose (goal := fun l => ((mult unit l = l),, h l)).
        assert (forall l, pr1 (goal l)).
        { use setquotunivprop.
          intro x. cbn.
          apply subtypeEquality'.
          - cbn. apply idpath.
          - apply isapropiseqclass.
        }
        unfold islunit. apply X.
      + unfold isrunit.
        assert (h : forall l, isaprop (mult l unit = l)).
        { intro l'. apply (setproperty carrier_q). }
        pose (goal := fun l => ((mult l unit = l),, h l)).
        assert (forall l, pr1 (goal l)).
        { use setquotunivprop.
          intro x. cbn.
          apply subtypeEquality'.
          - unfold concatenate_q. cbn.
            apply funextfun. intro l.
            (* unfold carrier, swap_list, swap in x. *)
            simpl in x.
            pose (p := concatenate_nil_runit swap x).
            simpl in p. rewrite p. apply idpath.
          - apply isapropiseqclass.
        }
        apply X.
  Defined.

  Definition assoc : isassoc mult.
    unfold isassoc.
    assert (prop : forall x y z, isaprop (mult (mult x y) z = mult x (mult y z))).
    { intros x y z. apply (setproperty carrier_q). }
    pose (goal :=
      fun x y z => ((mult (mult x y) z = mult x (mult y z)),, prop x y z)
    ).
    assert (cut : forall x y z, pr1 (goal x y z)).
    { simple refine (setquotuniv3prop _ goal _).
      intros x y z. unfold goal. simpl.
      apply subtypeEquality'.
      - simpl.
        pose (p := concatenate_assoc x y z).
        simpl in p. rewrite p. apply idpath.
      - apply isapropiseqclass.
    }
    apply cut.
  Defined.

  Definition monoidop : ismonoidop mult.
    apply mk_ismonoidop.
    - exact assoc.
    - exact unital.
  Defined.

  Definition invstruct : invstruct mult monoidop.
    use mk_invstruct.
    - exact inv.
    - use tpair.
      + unfold islinv. cbn.
        assert (prop : forall x, isaprop (mult (inv x) x = unit)).
        { intro x. apply (setproperty carrier_q). }
        pose (goal := fun x => (mult (inv x) x = unit),, prop x).
        assert (cut : forall x, pr1 (goal x)).
        { use setquotunivprop.
          intro x. simpl.
          apply subtypeEquality'.
          - simpl.
            apply funextfun. intro l.
            apply subtypeEquality'.
            + cbn. rewrite act_concat_comp.
              assert (h : actA_f (reverse x) ∘ actA_f x = actA_f nil).
              { apply funextfun.
                unfold funcomp. intro y. rewrite act_reverse_inverse.
                apply idpath.
              }
              simpl in h. rewrite <- h.
              apply idpath.
            + apply isapropisaprop.
          - apply isapropiseqclass.
        }
        apply cut.
      + cbn. unfold isrinv.
        assert (prop : forall x, isaprop (mult x (inv x) = unit)).
        { intro x. apply (setproperty carrier_q). }
        pose (goal := fun x => (mult x (inv x) = unit),, prop x).
        assert (cut : forall x, pr1 (goal x)).
        { use setquotunivprop.
          intro x. simpl.
          apply subtypeEquality'.
          - simpl.
            apply funextfun. intro l.
            apply subtypeEquality'.
            + cbn. rewrite act_concat_comp.
              assert (h : actA_f x ∘ actA_f (reverse x) = actA_f nil).
              { apply funextfun.
                unfold funcomp. intro y.
                pose (act_reverse_inverse (reverse x)).
                rewrite reverse_involutive in p.
                rewrite p.
                apply idpath.
              }
              simpl in h. rewrite <- h.
              apply idpath.
            + apply isapropisaprop.
          - apply isapropiseqclass.
        }
        apply cut.
  Defined.

  Definition grop : isgrop mult.
    use mk_isgrop.
    - exact monoidop.
    - exact invstruct.
  Defined.

  Definition Perm : gr.
    use grconstr.
    - use setwithbinoppair.
      + exact carrier_q.
      + exact mult.
    - simpl. exact grop.
  Defined.

End Perm.

Section Nom.
  Context (AtomSet : hSet).
  Context (PermASet : UU).
  (* Context (finitelySupported : ∀ {X : PermASet}, X -> UU). *)

  (* Definition isNominalSet (X : PermASet) := *)
  (*   ∀ x : X, finitelySupported x. *)

End Nom.
