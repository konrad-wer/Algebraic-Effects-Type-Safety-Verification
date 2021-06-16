From Coq Require Import Strings.String.
From AlgEffects Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Sets.Uniset.
From AlgEffects Require Import Calculus.

Import Calculus.

Lemma canonical_forms_bool : forall E v,
  E \ empty |- v \in BoolType ->
  v = VTrue \/ v = VFalse.
Proof with auto.
  intros.
  inversion H. subst.
  - inversion H0.
  - left...
  - right...
Qed.

Lemma canonical_forms_fun : forall E v T1 T2,
  E \ empty |- v \in (FunType T1 T2) ->
  exists x c, v = VFun x T1 c.
Proof with eauto.
  intros.
  inversion H; subst...
  - inversion H0.
Qed.

Lemma canonical_forms_handler : forall E v T1 T2,
  E \ empty |- v \in (HandlerType T1 T2) ->
  exists xr cr opCase, v = VHandler xr cr opCase.
Proof with eauto.
  intros.
  inversion H; subst...
  - inversion H0.
Qed.

Ltac solve_by_invertion :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      subst; try discriminate; eauto]
  end end.

Ltac solve_by_invertion_with t :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      subst; try discriminate; eauto using t ]
  end end.

Theorem progress : forall E c T,
  E \ empty ||- c \in T ->
  (exists v, c = CReturn v) \/
  (exists op v y c', c = COp op v y c') \/
  exists c', (E \ c --> c').
Proof with eauto.
  intros E C T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; try solve_by_invertion...
  - inversion H0; subst; try discriminate; right; left...
  - destruct IHHt1; subst; try reflexivity; right; right.
    + destruct H as [v H]. subst...
    + destruct H.
      * destruct H as (op & v & y & c' & H). subst...
      * destruct H as [c' H]...
 - destruct IHHt; try reflexivity; right; right; inversion H; subst; try discriminate.
  + destruct H0 as [v H0]. subst...
  + destruct H0.
    * destruct H0 as (op' & v & y & c' & H0); inversion H7; subst.
      destruct (eqb_stringP op op'); subst...
    * destruct H0 as [c' H0]...
Qed.

Lemma weakening : forall v E Gamma Gamma' T,
  inclusion Gamma Gamma' ->
  E \ Gamma  |- v \in T  ->
  E \ Gamma' |- v \in T.
Proof with eauto.
  apply (value_mut (fun c => forall E Gamma Gamma' T,
      inclusion Gamma Gamma' ->
      E \ Gamma  ||- c \in T  ->
      E \ Gamma' ||- c \in T)
    (fun v => forall E Gamma Gamma' T,
      inclusion Gamma Gamma' ->
      E \ Gamma  |- v \in T  ->
      E \ Gamma' |- v \in T)
    (fun opCase => forall E Gamma Gamma' op T,
      inclusion Gamma Gamma' ->
      has_type_opCase E Gamma op opCase T ->
      has_type_opCase E Gamma' op opCase T)); 
 
    intros; solve_by_invertion_with inclusion_update.
Qed.

Lemma weakening_empty : forall E Gamma v T,
     E \ empty |- v \in T  ->
     E \ Gamma |- v \in T.
Proof.
  intros E Gamma c T.
  eapply weakening.
  discriminate.
Qed.

Lemma weakening_computation : forall c E Gamma Gamma' T,
  inclusion Gamma Gamma' ->
  E \ Gamma  ||- c \in T  ->
  E \ Gamma' ||- c \in T.
Proof with eauto using weakening, inclusion_update.
  intros c E Gamma Gamma' T Hi Ht.
  generalize dependent Gamma'.
  induction Ht; intros; subst...
Qed.

Lemma substitution_preserves_typing : forall c E Gamma x U v T,
  E \ x |-> U ; Gamma ||- c \in T ->
  E \ empty |- v \in U   ->
  E \ Gamma ||- subst x v c \in T.
Proof with eauto using weakening_empty.
   apply (computation_mut (fun c => forall E Gamma x U v T,
      E \ x |-> U ; Gamma ||- c \in T ->
      E \ empty |- v \in U   ->
      E \ Gamma ||- subst x v c \in T)
    (fun v => forall E Gamma x U v' T,
      E \ x |-> U ; Gamma |- v \in T ->
      E \ empty |- v' \in U   ->
      E \ Gamma |- subst_in_value x v' v \in T)
    (fun opCase => forall E Gamma x U v op T,
      has_type_opCase E (x |-> U ; Gamma) op opCase T ->
      E \ empty |- v \in U   ->
      has_type_opCase E Gamma op (subst_in_opCase x v opCase) T)); 

  intros; subst; simpl; try solve_by_invertion.
  - inversion H1. subst. destruct (eqb_stringP x0 x)...
    + eapply T_Op... subst. rewrite update_shadow in H13...
    + eapply T_Op... rewrite update_permute in H13...
  - inversion H1. destruct (eqb_stringP x0 x); subst... 
    + eapply T_Do. eapply H in H9... rewrite update_shadow in H10...
    + eapply T_Do... rewrite update_permute in H10...
  - inversion H. destruct (eqb_stringP x0 x); subst...
    + apply weakening_empty. rewrite update_eq in H4. 
      injection H4 as H4. subst...
    + rewrite update_neq in H4...
  - inversion H0. destruct (eqb_stringP x0 x); subst...
    + rewrite update_shadow in H8...
    + rewrite update_permute in H8...
  - inversion H1. destruct (eqb_stringP x0 x); subst...
    + rewrite update_shadow in H8...
    + rewrite update_permute in H8...
  - inversion H0. destruct (eqb_stringP x0 x); subst; simpl.
    + econstructor...
      rewrite update_permute in H12...
      rewrite update_shadow in H12...
      rewrite update_permute in H12...
    + destruct (eqb_stringP x0 k); subst.
      * econstructor... rewrite update_shadow in H12...
      * econstructor... eapply H...
        rewrite update_permute... 
        rewrite update_permute with (x1 := x0)...
Qed.

Lemma inclusion_empty_in_any : forall (A : Type) (m : partial_map A), inclusion empty m.
Proof.
  unfold inclusion.
  intros. inversion H.
Qed.

Lemma set_remove_neq_incl : forall x y Delta Delta',
  x <> y ->
  In Delta x ->
  incl (set_remove y Delta) Delta' ->
  In Delta' x.
Proof with eauto.
  intros.
  unfold In in *. unfold incl in H1.
  unfold set_remove in H1. simpl in H1. specialize H1 with x.
  destruct (eqb_stringP y x).
  - unfold not in H. exfalso...
  - rewrite -> H0 in H1. inversion H1...
Qed.

Theorem preservation : forall E c c' T,
  E \ empty ||- c \in T  ->
  E \ c --> c'  ->
  E \ empty ||- c' \in T.
Proof with eauto using inclusion_empty_in_any.
  intros E c c' T HT.
  remember empty as Gamma.
  generalize dependent c'.
  induction HT; intros; subst; 
  try solve_by_invertion_with inclusion_empty_in_any.
  - inversion H1. subst. inversion H. subst. 
    eapply substitution_preserves_typing ...
  - inversion H; subst...
    + inversion HT1. eapply substitution_preserves_typing ...
    + inversion HT1. subst. eapply T_Op; subst... eapply T_Do ...
      destruct (eqb_stringP x y); subst.
      * rewrite update_shadow...
      * apply weakening_computation with (Gamma := (x |-> T1))...
        unfold inclusion. intros. destruct (eqb_stringP x x0); subst.
        -- rewrite update_eq in H0. rewrite update_eq...
        -- rewrite update_neq in H0... inversion H0.
  - inversion H0; subst...
    + inversion H. subst. eapply substitution_preserves_typing...
      inversion HT...
    + inversion H. inversion HT. inversion H9. subst.
      eapply substitution_preserves_typing...
      * eapply substitution_preserves_typing...
        rewrite H17 in H30. injection H30 as H30. subst...
      * rewrite H30. rewrite H17 in H30. injection H30 as H30. simpl. 
        subst. constructor. econstructor...
        injection H18 as H18. subst. apply weakening with (Gamma := empty)...
   + inversion H. subst. inversion HT. subst. inversion H10. subst. 
      econstructor...
     * eapply set_remove_neq_incl...
     * econstructor... apply weakening with (Gamma := empty)...
Qed.

Corollary safety : forall E c T Delta,
  E \ empty ||- c \in ComputationType T Delta ->
  (exists v, c = CReturn v /\ E \ empty |- v \in T) \/
  (exists op v y c', c = COp op v y c' /\ In Delta op) \/
  (exists c', E \ c --> c' /\ E \ empty ||- c' \in ComputationType T Delta).
Proof with eauto 7.
  intros. apply progress in H as H'. destruct H' as [[v H1] | H23]; 
  try destruct H23 as [H2 | H3].
  - left. exists v. subst. inversion H. subst...
  - right. left. destruct H2 as (op & v & y & c' & H2). subst. inversion H. 
    subst...
  - right. right. destruct H3 as [c' H3]. exists c'. split...
    eapply preservation...
Qed.

Corollary safety_pure : forall E c T,
  E \ empty ||- c \in ComputationType T (Emptyset string) ->
  (exists v, c = CReturn v /\ E \ empty |- v \in T) \/
  (exists c', E \ c --> c' /\ E \ empty ||- c' \in ComputationType T (Emptyset string)).
Proof with eauto 7.
  intros. apply safety in H. destruct H.
  - left ...
  - destruct H.
    + destruct H as (op & _ & _ & _ & _ & H). inversion H.
    + right ...
Qed.
