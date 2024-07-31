Require Export typing.
Require Export reduction.
Require Export stlc.

From stdpp Require Import relations.

Inductive V : ty -> tm 0 -> Prop :=
  | V_True : V tybool tmtrue
  | V_False : V tybool tmfalse
  | V_Arr e τ1 τ2 : (forall v, V τ1 v -> E τ2 (subst_tm v.. e)) ->
                    V (tyarr τ1 τ2) (tmabs τ1 e)
with E : ty -> tm 0 -> Prop :=
  | E_St e τ : (forall e', (multistep e e' /\ ~ exists e'', step e' e'') -> V τ e') ->
               E τ e.

Hint Constructors V : core.
Hint Constructors E : core.

Definition γ_ok {n} (γ : fin n -> tm 0) (Γ : context n) : Prop :=
  forall x, V (Γ x) (γ x).

(* Lemma V_backpreservation : forall τ e e', *)
(*     step e e' -> V τ e' -> V τ e. *)
(* Proof. *)
(*   induction τ; intros. *)
(*   - (* -> *) inversion H0. inversion H6. subst. *)

Lemma V_val : forall τ v,
    V τ v -> value v.
Proof.
  induction τ; intros; inversion H; constructor.
Qed.


Lemma V_no_step : forall τ e,
    V τ e -> ~ exists e', step e e'.
Proof.
  induction τ; unfold not; intros.
  - (* -> *) inversion H. subst. destruct H0. inversion H0.
  - (* bool *) destruct H0. inversion H; subst; inversion H0.
Qed.

Lemma V_impl_E : forall τ e,
    V τ e -> E τ e.
Proof.
  intros. apply E_St with (e' := e).
  - split; eauto using V_no_step.
  - assumption.
Qed.

Lemma fundamental_lemma : forall (e : tm 0) τ γ Γ,
    has_type Γ e τ ->
    γ_ok γ Γ ->
    E τ (subst_tm γ e).
Proof.
  intros e τ γ Γ Hty Hγ. induction Hty.
  - (* var *) simpl. subst. apply V_impl_E. apply Hγ.
  - (* abs *) simpl. admit.
  - (* app *) simpl. remember Hγ. clear Heqγ0. apply IHHty1 in γ0.
    remember Hγ. clear Heqγ1. apply IHHty2 in γ1.
    inversion γ0. inversion γ1. inversion H0. subst.
    destruct H as [Hste1 Hirre1]. destruct H3 as [Hste2 Hirre2].
    econstructor.
    + split.
      * apply rtc_transitive with (y := tmapp (tmabs τ1 e3) e'0).
        -- apply rtc_transitive with (y := tmapp (tmabs τ1 e3) (subst_tm γ e2)).
           ++ apply multi_app_cong1. assumption.
           ++ apply multi_app_cong2; auto.
        -- apply rtc_transitive with (y := subst_tm e'0.. e3).
           ++ econstructor.
              ** constructor. eapply V_val. eassumption.
              ** constructor.
           ++ inversion H11. destruct H as [Hst _]. apply Hst.
    apply E_St with (e' := subst_tm e'0.. e3).
    + destruct H as [Hste1 Hirre1]. destruct H3 as [Hste2 Hirre2]. split.
      * apply rtc_transitive with (y := tmapp (tmabs τ1 e3) e'0).
        -- apply rtc_transitive with (y := tmapp (tmabs τ1 e3) (subst_tm γ e2)).
           ++ apply multi_app_cong1. assumption.
           ++ apply multi_app_cong2; auto.
        -- econstructor.
           ++ constructor. eapply V_val. eassumption.
           ++ constructor.
      *
  - (* if *) simpl. remember Hγ. clear Heqγ0.
    apply IHHty1 in γ0. inversion γ0.
    + constructor.
