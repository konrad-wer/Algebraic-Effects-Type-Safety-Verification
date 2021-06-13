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
Proof with eauto.
  intros.
  inversion H; subst...
  - inversion H0.
Qed.

Lemma canonical_forms_handler : forall E v T1 T2,
  E \ empty |- v \in (HandlerType T1 T2) ->
  value v ->
  exists xr cr opCase, v = VHandler xr cr opCase.
Proof with eauto.
  intros.
  inversion H; subst...
  - inversion H0.
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

Lemma weakening : forall v E Gamma Gamma' T,
  inclusion Gamma Gamma' ->
  E \ Gamma  |- v \in T  ->
  E \ Gamma' |- v \in T.
Proof with eauto.
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

  - inversion H1. subst. constructor. apply H with (Gamma := Gamma)...
  - inversion H2. subst. apply T_Op with (T1 := T1) (T2 := T2) (Delta := Delta);
    try eapply H...
    + eapply H0...
      * apply inclusion_update...
  - inversion H2. subst. eapply T_Do...
    + eapply H0...
      * apply inclusion_update...
  - inversion H3. subst. apply T_If...
  - inversion H2. subst. eapply T_App...
  - inversion H2. subst. eapply T_Handle; eauto.
  - inversion H0. subst. apply T_Var...
  - inversion H0. constructor.
  - inversion H0. constructor.
  - inversion H1. subst. apply T_Fun. eapply H. 
    + apply inclusion_update...
    + auto.
  - inversion H2. subst. eapply T_Handler...
    + eapply H...
      * apply inclusion_update...
  - inversion H1. subst. eapply T_OpCase; eauto. 
    + eapply H; eauto.
      * repeat (apply inclusion_update)...
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
Proof with eauto using weakening.
  intros c E Gamma Gamma' T Hi Ht.
  generalize dependent Gamma'.
  induction Ht; intros; subst.
  - eapply T_App...
  - eapply T_If...
  - eapply T_Return...
  - eapply T_Op... apply IHHt... apply inclusion_update...
  - eapply T_Do... apply IHHt2... apply inclusion_update...
  - eapply T_Handle...
Qed.

Lemma substitution_preserves_typing : forall c E Gamma x U v T,
  E \ x |-> U ; Gamma ||- c \in T ->
  E \ empty |- v \in U   ->
  E \ Gamma ||- subst x v c \in T.
Proof with eauto.
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
  - inversion H0. subst. eapply H in H5...
    + eapply T_Return in H5...
  - inversion H1. subst. destruct (eqb_stringP x0 x); eapply H in H2 as H2'...
    + eapply T_Op... subst. rewrite update_shadow in H13...
    + eapply T_Op...
      rewrite update_permute in H13...
  - inversion H1. destruct (eqb_stringP x0 x); subst; eapply H in H2 as H2'...
    + eapply T_Do. eapply H in H9... rewrite update_shadow in H10...
    + eapply T_Do... rewrite update_permute in H10...
  - inversion H2. subst. constructor...
  - inversion H1. subst. eapply T_App...
  - inversion H1. subst. econstructor...
  - inversion H. destruct (eqb_stringP x0 x); subst.
    + apply weakening_empty. rewrite update_eq in H4. 
      injection H4 as H4. subst...
    + rewrite update_neq in H4... constructor...
  - inversion H. subst. constructor.
  - inversion H. subst. constructor.
  - inversion H0. destruct (eqb_stringP x0 x); subst; constructor.
    + rewrite update_shadow in H8. auto.
    + eapply H... rewrite update_permute in H8...
  - inversion H1. destruct (eqb_stringP x0 x); subst.
    + econstructor... rewrite update_shadow in H8...
    + econstructor...
      * rewrite update_permute in H8...
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

Search inclusion.

Lemma inclusion_empty_in_any : forall (A : Type) (m : partial_map A), inclusion empty m.
Proof.
  unfold inclusion.
  intros. inversion H. 
Qed.

Theorem preservation : forall E c c' T,
  E \ empty ||- c \in T  ->
  E \ c --> c'  ->
  E \ empty ||- c' \in T.
Proof with eauto using inclusion_empty_in_any.
  intros E c c' T HT.
  remember empty as Gamma.
  generalize dependent c'.
  induction HT; intros; subst.
  - inversion H1. subst. inversion H. subst. 
    eapply substitution_preserves_typing ...
  - inversion H0; subst ...
  - inversion H0.
  - inversion H2.
  - inversion H; subst.
    + eapply T_Do ...
    + inversion HT1. eapply substitution_preserves_typing ...
    + inversion HT1. subst. eapply T_Op; subst ...
      eapply T_Do ...
      destruct (eqb_stringP x y); subst.
      * rewrite update_shadow...
      * apply weakening_computation with (Gamma := (x |-> T1))...
        unfold inclusion. intros. destruct (eqb_stringP x x0); subst.
        -- rewrite update_eq in H0. rewrite update_eq...
        -- rewrite update_neq in H0... inversion H0.
  - inversion H0; subst.
    + econstructor...
    + inversion H. subst. eapply substitution_preserves_typing...
      inversion HT...
    + inversion H. inversion HT. inversion H10. subst.
      eapply substitution_preserves_typing...
      * eapply substitution_preserves_typing... 
        rewrite H18 in H31. injection H31 as H31. subst...
      * rewrite H31. rewrite H18 in H31. injection H31 as H31. simpl. 
        subst. constructor. econstructor.
        -- apply H22.
        -- apply weakening with (Gamma := empty)...
   + inversion H. inversion HT. subst. econstructor...
     econstructor... apply weakening with (Gamma := empty)...
Qed.

