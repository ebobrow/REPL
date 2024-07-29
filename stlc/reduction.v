Require Export stlc.
From stdpp Require Import relations.

Inductive value {n : nat} : tm n -> Prop :=
  | v_abs τ e : value (tmabs τ e)
  | v_true : value tmtrue
  | v_false : value tmfalse.

Inductive step {n : nat} : tm n -> tm n -> Prop :=
  | S_β a b A :
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

Definition multistep {n : nat} := rtc (@step n).

Definition steps {n : nat} (e : tm n) : Prop := exists e', value e' /\ multistep e e'.
