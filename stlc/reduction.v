Require Export stlc.
From stdpp Require Import relations.

Inductive value {n : nat} : tm n -> Prop :=
  | v_abs τ e : value (tmabs τ e)
  | v_true : value tmtrue
  | v_false : value tmfalse.

Hint Constructors value : core.

Inductive step {n : nat} : tm n -> tm n -> Prop :=
  | S_β a b A :
    value b ->
    step (tmapp (tmabs A a) b) (subst_tm (b..) a)
  | ST_App1 e1 e1' e2 :
    step e1 e1' ->
    step (tmapp e1 e2) (tmapp e1' e2)
  | ST_App2 v e2 e2' :
    value v ->
    step e2 e2' ->
    step (tmapp v e2) (tmapp v e2')
  | ST_IfTrue e1 e2 :
    step (tmif tmtrue e1 e2) e1
  | ST_IfFalse e1 e2 :
    step (tmif tmfalse e1 e2) e2
  | ST_If e1 e1' e2 e3 :
    step e1 e1' ->
    step (tmif e1 e2 e3) (tmif e1' e2 e3).

Hint Constructors step : core.

Definition multistep {n : nat} := rtc (@step n).

Hint Unfold multistep : core.
Hint Constructors rtc : core.

Definition steps {n : nat} (e : tm n) : Prop := exists e', value e' /\ multistep e e'.

Lemma value_no_step {n} : forall (v : tm n),
    value v ->
    ~ (exists v', step v v').
Proof.
  intros. inversion H; unfold not; intros [v' Hv']; inversion Hv'.
Qed.

Ltac val_step :=
  match goal with
    H1: value ?e,
    H2: step ?e ?e'
    |- _ => apply value_no_step in H1; exfalso; apply H1; exists e'; apply H2
  end.

Lemma determinism {n} : forall (e e1 e2 : tm n),
    step e e1 ->
    step e e2 ->
    e1 = e2.
Proof.
  induction e; intros.
  - inversion H.
  - inversion H; inversion H0; subst; try val_step.
    + inversion H5. reflexivity.
    + inversion H8.
    + inversion H4.
    + apply IHe1 with (e2 := e1') in H8; subst; auto.
    + apply IHe2 with (e1 := e2') in H10; subst; auto.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + inversion H0; subst.
      * reflexivity.
      * inversion H5.
    + inversion H0; subst.
      * reflexivity.
      * inversion H5.
    + inversion H0; subst.
      * inversion H5.
      * inversion H5.
      * apply IHe1 with (e2 := e1') in H6; subst; auto.
Qed.

Lemma multi_if_cong {n : nat} : forall (e1 e2 e3 e1' : tm n),
    multistep e1 e1' -> multistep (tmif e1 e2 e3) (tmif e1' e2 e3).
Proof.
  intros. induction H; eauto.
Qed.

Hint Resolve multi_if_cong : core.

Lemma multi_app_cong1 {n : nat} : forall (e1 e1' e2 : tm n),
    multistep e1 e1' ->
    multistep (tmapp e1 e2) (tmapp e1' e2).
Proof.
  intros. induction H; eauto.
Qed.

Hint Resolve multi_app_cong1 : core.

Lemma multi_app_cong2 {n : nat} : forall (e1 e2 e2' : tm n),
    value e1 ->
    multistep e2 e2' ->
    multistep (tmapp e1 e2) (tmapp e1 e2').
Proof.
  intros. induction H0; eauto.
Qed.

Hint Resolve multi_app_cong2 : core.
