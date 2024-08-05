Require Export stlc.
Require Export typing.
Require Export bigstep.

Fixpoint N (τ : ty) (e : tm 0) : Prop :=
  match τ with
    | tybool => big_step e tmtrue \/ big_step e tmfalse
    | tyarr τ1 τ2 => forall e', N τ1 e' -> N τ2 (tmapp e e')
  end.

Definition γ_ok {n : nat} (γ : fin n -> tm 0) (Γ : context n) :=
  forall i, N (Γ i) (γ i).

Lemma γ_ok_cons {n} {γ : fin n -> tm 0} {Γ a A} :
  N A a ->
  γ_ok γ Γ ->
  γ_ok (a .: γ) (A .: Γ).
Proof.
  unfold γ_ok.
  intros h hγ [i|]; simpl; eauto.
Qed.

(* Lemma N_backpreservation : forall τ (e e' : tm 0), *)
(*     big_step e e' -> *)
(*     N τ e' -> N τ e. *)
(* Proof. *)
(*   induction τ. *)
(*   - (* -> *) simpl. intros. apply H0 in H1. induction τ2. *)
(*   - (* bool *) simpl. intros. destruct H0; inversion H0; try (rewrite <- H1 in H; auto); *)
(*                  try (subst; apply big_step_val in H; inversion H). *)

Lemma fundamental_lemma : forall Γ γ (e : tm 0) τ,
    has_type Γ e τ ->
    γ_ok γ Γ ->
    N τ (subst_tm γ e).
Proof.
  intros Γ γ e τ Hty Hγ. induction Hty; simpl.
  - (* var *) subst. apply Hγ.
  - (* app *) intros.
