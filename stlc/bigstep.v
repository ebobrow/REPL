Require Export stlc.

Inductive value {n : nat} : tm n -> Prop :=
  | v_abs τ e : value (tmabs τ e)
  | v_true : value tmtrue
  | v_false : value tmfalse.

Inductive big_step : tm 0 -> tm 0 -> Prop :=
  | ST_Lam τ e : big_step (tmabs τ e) (tmabs τ e)
  | ST_β e1 e2 τ e' v v' :
    big_step e1 (tmabs τ e') ->
    big_step e2 v ->
    big_step (subst_tm v.. e') v' ->
    big_step (tmapp e1 e2) v'
  | ST_True : big_step tmtrue tmtrue
  | ST_False : big_step tmfalse tmfalse
  | ST_IfTrue e1 e2 e3 v :
    big_step e1 tmtrue ->
    big_step e2 v ->
    big_step (tmif e1 e2 e3) v
  | ST_IfFalse e1 e2 e3 v :
    big_step e1 tmfalse ->
    big_step e3 v ->
    big_step (tmif e1 e2 e3) v.
Hint Constructors big_step : core.

Lemma big_step_val : forall e e',
    big_step e e' -> value e'.
Proof.
  intros. induction H; try constructor; assumption.
Qed.

Lemma val_step : forall v v',
    value v ->
    big_step v v' ->
    v = v'.
Proof.
  intros. inversion H; subst; inversion H0; reflexivity.
Qed.

Definition store n := fin n -> tm n.
Definition empty_store : store 0 := fun x => match x with end.

Inductive big_step' {n} : store n -> tm n -> (store n * tm n) -> Prop :=
  | ST_Lam' ρ τ e : big_step' ρ (tmabs τ e) (ρ, (tmabs τ e))
  | ST_β' ρ ρ' e1 e2 τ e v w' :
    big_step' ρ e1 (ρ', tmabs τ e) ->
    big_step' ρ e2 (empty_store, v) ->
    big_step' (v .: ρ') e w' ->
    big_step' ρ (tmapp e1 e2) w'.
