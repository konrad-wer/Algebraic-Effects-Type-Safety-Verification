From Coq Require Import Strings.String.
From AlgEffects Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Sets.Uniset.
From AlgEffects Require Import Calculus.

Import Calculus.

Lemma canonical_forms_bool : forall E v,
  E \ empty |- v \in BoolType ->
  value v ->
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
  value v ->
  exists x c, v = VFun x T1 c.
Proof.
  intros.
  inversion H. subst.
  - inversion H0.
  - subst. eexists. eexists. reflexivity.
Qed.

Lemma canonical_forms_handler : forall E v T1 T2,
  E \ empty |- v \in (HandlerType T1 T2) ->
  value v ->
  exists xr cr opCase, v = VHandler xr cr opCase.
Proof.
  intros.
  inversion H. subst.
  - inversion H0.
  - subst. eexists. eexists. eexists. reflexivity.
Qed.

Theorem progress : forall E c T,
  E \ empty ||- c \in T ->
  (exists v, c = (CReturn) v /\ value v) \/
  (exists op v y c', c = COp op v y c' /\ value v) \/
  exists c', (E \ c --> c').
Proof.
  intros E C T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  - inversion H; subst.
    + discriminate.
    + inversion H0; subst; try discriminate; right; right; eexists; constructor; constructor.
  - inversion H; subst; try discriminate; right; right; eexists; constructor.
  - inversion H; subst; try discriminate; left; eexists; 
    split; try reflexivity; constructor.
  - inversion H0; subst; try discriminate; right; left;
    eexists; eexists; eexists; eexists; split; try reflexivity; constructor.
  - destruct IHHt1; subst; try reflexivity; right; right.
    + destruct H as (v & H1 & H2). subst. eexists. apply ST_DoReturn. auto.
    + destruct H.
      * destruct H as (op & v & y & c' & H1 & H2). subst. eexists. apply ST_DoOp. auto.
      * destruct H as [c' H]. eexists. apply ST_Do1. apply H.
 - destruct IHHt; try reflexivity; right; right; inversion H; subst; try discriminate.
  + destruct H0 as (v & H1 & H2). subst. eexists. apply ST_HandleReturn. auto.
  + destruct H0.
    * destruct H0 as (op' & v & y & c' & H1 & H2); inversion H7; subst.
      destruct (eqb_stringP op op'); subst.
      -- eexists. subst. apply ST_HandleOpEqual. auto.
      -- eexists. apply ST_HandleOpNotEqual; auto.
    * destruct H0 as [c' H0]. eexists. apply ST_Handle1. eauto.
Qed.

Search "inclusion_update".

Lemma weakening : forall v E Gamma Gamma' T,
  inclusion Gamma Gamma' ->
  E \ Gamma  |- v \in T  ->
  E \ Gamma' |- v \in T.
Proof.
  apply (valueExpr_mut (fun c => forall E Gamma Gamma' T,
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
      has_type_opCase E Gamma' op opCase T)); intros; subst.
  - inversion H1. subst. constructor. apply H with (Gamma := Gamma); assumption.
  - inversion H2. subst. apply T_Op with (T1 := T1) (T2 := T2) (Delta := Delta);
    try eapply H; eauto.
    + eapply H0.
      * apply inclusion_update. apply H1.
      * auto.
  - inversion H2. subst. eapply T_Do.
    + eapply H.
      * apply H1.
      * apply H9.
    + eapply H0.
      * apply inclusion_update. apply H1.
      * apply H10.
  - inversion H3. subst. apply T_If.
    + eapply H. apply H2. apply H9.
    + eapply H0. apply H2. apply H11.
    + eapply H1. apply H2. apply H12.
  - inversion H2. subst. eapply T_App.
    + eapply H. apply H1. apply H7.
    + eapply H0. apply H1. apply H9.
  - inversion H2. subst. eapply T_Handle.
    + eapply H. apply H1. apply H7.
    + eapply H0. apply H1. auto.
  - inversion H0. subst. apply T_Var. auto.
  - inversion H0. constructor.
  - inversion H0. constructor.
  - inversion H1. subst. apply T_Fun. eapply H. 
    + apply inclusion_update. apply H0.
    + auto.
  - inversion H2. subst. eapply T_Handler.
    + eapply H. 
      * apply inclusion_update. apply H1.
      * auto.
    + eapply H0. apply H1. apply H10.
    + auto.
  - inversion H1. subst. eapply T_OpCase. 
    + apply H10.
    + auto.
    + eapply H.
      * repeat (apply inclusion_update). apply H0.
      * auto.
Qed.

Lemma weakening_empty : forall E Gamma v T,
     E \ empty |- v \in T  ->
     E \ Gamma |- v \in T.
Proof.
  intros E Gamma c T.
  eapply weakening.
  discriminate.
Qed. 

Lemma substitution_preserves_typing : forall c E Gamma x U v T,
  E \ x |-> U ; Gamma ||- c \in T ->
  E \ empty |- v \in U   ->
  E \ Gamma ||- subst x v c \in T.
Proof.
   apply (computation_mut (fun c => forall E Gamma x U v T,
      E \ x |-> U ; Gamma ||- c \in T ->
      E \ empty |- v \in U   ->
      E \ Gamma ||- subst x v c \in T)
    (fun v => forall E Gamma x U v' T,
      E \ x |-> U ; Gamma |- v \in T ->
      E \ empty |- v' \in U   ->
      E \ Gamma |- subst_in_valueExpr x v' v \in T)
    (fun opCase => forall E Gamma x U v op T,
      has_type_opCase E (x |-> U ; Gamma) op opCase T ->
      E \ empty |- v \in U   ->
      has_type_opCase E Gamma op (subst_in_opCase x v opCase) T)); intros; subst; simpl.
  - inversion H0. subst. eapply H in H5. 
    + eapply T_Return in H5. apply H5.
    + auto.
  - inversion H1. subst. destruct (eqb_stringP x0 x); eapply H in H2 as H2'.
    + eapply T_Op. apply H9. apply H2'. apply H12. 
      subst. rewrite update_shadow in H13. auto.
    + auto.
    + eapply T_Op. apply H9. apply H2'. apply H12. subst.
      rewrite update_permute in H13; auto. eapply H0 in H13.
      apply H13. assumption.
    + auto.
  - inversion H1. destruct (eqb_stringP x0 x); subst; eapply H in H2 as H2'.
    + eapply T_Do. eapply H in H9.
      apply H9. auto. rewrite update_shadow in H10. auto.
    + apply H9.
    + eapply T_Do. apply H2'. rewrite update_permute in H10; auto.
      eapply H0. apply H10. apply H2.
    + apply H9.
  - inversion H2. subst. constructor.
    + eapply H. apply H9. apply H3.
    + eapply H0. apply H11. apply H3.
    + eapply H1. apply H12. apply H3.
  - inversion H1. subst. eapply T_App.
    + eapply H. apply H7. auto.
    + eapply H0. apply H9. auto.
  - inversion H1. subst. econstructor.
    + eapply H. apply H7. auto.
    + eapply H0. apply H9. auto.
  - inversion H. destruct (eqb_stringP x0 x); subst.
    + apply weakening_empty. rewrite update_eq in H4. 
      injection H4 as H4. subst. auto.
    + rewrite update_neq in H4. constructor. auto. auto.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor.
  - inversion H0. destruct (eqb_stringP x0 x); subst; constructor.
    + rewrite update_shadow in H8. auto.
    + eapply H. rewrite update_permute in H8. apply H8. auto. auto.
  - inversion H1. destruct (eqb_stringP x0 x); subst.
    + econstructor. 
      * rewrite update_shadow in H8. auto.
      * eapply H0. apply H10. apply H2.
      * auto.
    + econstructor. 
      * rewrite update_permute in H8. eapply H in H8. apply H8. auto. auto.
      * eapply H0. apply H10. auto.
      * auto.
  - inversion H0. destruct (eqb_stringP x0 x); subst; simpl.
    + econstructor. apply H10. auto. 
      rewrite update_permute in H12.
      rewrite update_shadow in H12.
      rewrite update_permute in H12. auto. auto. auto.
    + destruct (eqb_stringP x0 k); subst.
      * econstructor. apply H10. auto. 
        rewrite update_shadow in H12. auto.
      * econstructor. apply H10. auto. eapply H.
        rewrite update_permute. rewrite update_permute with (x1 := x0). apply H12.
        auto. auto. auto. 
Qed.
