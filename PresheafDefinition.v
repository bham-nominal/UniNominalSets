Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartC.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Local Open Scope cat.

Lemma incl_eq A B (f g : incl A B) :  pr1incl _ _ f = pr1incl _ _ g -> f = g.
  intro e.
  apply subtypeEquality'.
  - exact e.
  - apply isapropisincl.
Defined.
Lemma isincl_idfun (A : UU) : isincl (idfun A).
Proof.
  intros a e e'.
  apply hlevelntosn.
  apply iscontrcoconustot.
Defined.
Definition names_ob : UU := nat.

Definition names_mor (p q : names_ob) := incl (stn p) (stn q).


Definition names_mor_ob_mor : precategory_ob_mor := (names_ob,,names_mor).


Definition id_mor_precat (c : names_mor_ob_mor) : c --> c :=
  (idfun _ ,, isincl_idfun _).

Definition names_precat_data : precategory_data :=
  precategory_data_pair _ id_mor_precat (fun a b c => inclcomp).


Lemma is_precategory_names_data  :
  is_precategory names_precat_data.
Proof.
  (repeat split);  now simpl; intros; apply incl_eq.
Qed.

Definition names_precat  : precategory :=
  (_,,is_precategory_names_data).

Lemma has_homsets_names_precat : has_homsets names_precat.
Proof.
  intros a b.
  apply isaset_total2.

  - apply impred_isaset.
    intros _.
    apply isasetstn.
  - intros.
    apply hlevelntosn.
    apply isapropisincl.
Qed.

Definition names_cat : category := (names_precat ,, has_homsets_names_precat).

Definition nominal_set_cat := [ names_cat, hset_category].

Section nameabstraction.
  Variable (X : nominal_set_cat).
