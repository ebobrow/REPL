Require Export typing.
Require Export reduction.
Require Export stlc.

From stdpp Require Import relations.

Fixpoint N' (τ : ty) (e : tm 0) : Prop :=
  has_type empty_ctxt e τ /\ steps e /\
    match τ with
      | tybool => True
      | tyarr τ1 τ2 => forall e', N' τ1 e' -> N' τ2 (tmapp e e')
    end.

Lemma canonical_forms_bool : forall v,
    value v ->
    has_type empty_ctxt v tybool ->
    v = tmtrue \/ v = tmfalse.
Proof.
  intros. inversion H; auto.
  subst. inversion H0.
Qed.

(* don't check domain equality bc both total functions over fin n *)
Definition γ_ok' {n : nat} (γ : fin n -> tm 0) (Γ : context n) :=
  forall i, N' (Γ i) (γ i).

Lemma γ_ok'_cons {n} {γ : fin n -> tm 0} {Γ a A} :
  N' A a ->
  γ_ok' γ Γ ->
  γ_ok' (a .: γ) (A .: Γ).
Proof.
  unfold γ_ok'.
  intros h hγ [i|]; simpl; eauto.
Qed.

Lemma N'_implies_norm : forall τ (e : tm 0),
    N' τ e -> steps e.
Proof. induction τ; simpl; intros e [_ [Hst _]]; apply Hst. Qed.

Lemma N'_implies_typed : forall τ (e : tm 0),
    N' τ e -> has_type empty_ctxt e τ.
Proof. induction τ; simpl; intros e [Hty _]; apply Hty. Qed.

Lemma preservation {n : nat} : forall Γ (e e' : tm n) τ,
    has_type Γ e τ ->
    step e e' ->
    has_type Γ e' τ.
Admitted.

Lemma multi_preservation {n : nat} : forall Γ (e e' : tm n) τ,
    has_type Γ e τ ->
    multistep e e' ->
    has_type Γ e' τ.
Proof.
  intros. induction H0; eauto using preservation.
Qed.

Lemma N'_preservation : forall τ (e e' : tm 0),
    step e e' ->
    N' τ e -> N' τ e'.
Proof.
  induction τ.
  - intros. destruct H0. destruct H1. repeat split.
Admitted.

Lemma N'_multi_preservation : forall τ (e e' : tm 0),
    multistep e e' ->
    N' τ e -> N' τ e'.
Proof.
  intros. induction H.
  - assumption.
  - apply IHrtc. eapply N'_preservation; eassumption.
Qed.

Lemma N'_backpreservation : forall τ (e e' : tm 0),
    has_type empty_ctxt e τ ->
    step e e' ->
    N' τ e' -> N' τ e.
Proof.
  induction τ; simpl; intros e e' Hty Hstep [Nty [Nstep Nelim]]; repeat split; eauto;
  try (destruct Nstep as [v [Hval Hstv]]; exists v; split; try assumption;
    econstructor; eassumption).
  intros. specialize Nelim with e'0. remember H. clear Heqn. apply Nelim in H.
  assert (step (tmapp e e'0) (tmapp e' e'0)). { constructor. assumption. }
  apply IHτ2 with (e' := tmapp e' e'0); try assumption.
  econstructor.
    * apply Hty.
    * apply N'_implies_typed. assumption.
Qed.

Lemma N'_multi_backpreservation : forall τ (e e' : tm 0),
    has_type empty_ctxt e τ ->
    multistep e e' ->
    N' τ e' -> N' τ e.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHrtc in H1.
    + eapply N'_backpreservation; eassumption.
    + eapply preservation; eassumption.
Qed.

Lemma multi_if_cong {n : nat} : forall (e1 e2 e3 e1' : tm n),
    multistep e1 e1' -> multistep (tmif e1 e2 e3) (tmif e1' e2 e3).
Proof.
  intros. induction H.
  - constructor.
  - econstructor.
    + constructor. eassumption.
    + assumption.
Qed.

Lemma multi_app_cong2 {n : nat} : forall (e1 e2 e2' : tm n),
    value e1 ->
    multistep e2 e2' ->
    multistep (tmapp e1 e2) (tmapp e1 e2').
Proof.
  intros. induction H0.
  - constructor.
  - econstructor.
    + apply ST_App2; eassumption.
    + assumption.
Qed.

Lemma γ_ok'_impl_good_subst {n : nat} : forall γ (Γ : context n),
    γ_ok' γ Γ ->
    good_subst γ Γ empty_ctxt.
Proof.
  intros. unfold γ_ok' in H. unfold good_subst. intros. specialize H with i.
  apply N'_implies_typed. assumption.
Qed.

Lemma fundamental_lemma' : forall Γ γ (e : tm 0) τ,
    has_type Γ e τ ->
    γ_ok' γ Γ ->
    N' τ (subst_tm γ e).
Proof.
  intros Γ γ e τ Hty. induction Hty; subst; intros Hγ.
  - (* var *) simpl. unfold γ_ok' in Hγ. specialize Hγ with i. apply Hγ.
  - (* abs *) repeat split.
    + eapply morphing.
      * constructor. eassumption.
      * apply γ_ok'_impl_good_subst. assumption.
    + exists (subst_tm γ (tmabs τ1 e)). split; constructor.
    + intros. simpl. remember H. clear Heqn0. apply N'_implies_norm in H. destruct H as [v [Hval Hstepv]].
      eapply N'_multi_backpreservation.
      * econstructor.
        -- constructor. eapply morphing.
           ++ eassumption.
           ++ apply γ_ok'_impl_good_subst in Hγ. apply good_subst_ext. assumption.
        -- apply N'_implies_typed in n0. apply n0.
      * eapply rtc_r.
        -- apply multi_app_cong2.
           ++ constructor.
           ++ eassumption.
        -- apply S_β.
      * asimpl. apply IHHty. apply γ_ok'_cons.
        -- eapply N'_multi_preservation; eassumption.
        -- assumption.
  - (* app *) asimpl. specialize IHHty1 with γ. remember Hγ. clear Heqγ0. apply IHHty1 in Hγ.
    destruct Hγ as [_ [_ Helim]]. auto.
  - (* true *) repeat (split; try exists tmtrue); constructor.
  - (* false *) repeat (split; try exists tmfalse); constructor.
  - (* if *) asimpl. assert (multistep (tmif (subst_tm γ e1) (subst_tm γ e2) (subst_tm γ e3))
                               (subst_tm γ e2) \/
                     multistep (tmif (subst_tm γ e1) (subst_tm γ e2) (subst_tm γ e3))
                               (subst_tm γ e3)).
    { apply IHHty1 in Hγ. destruct Hγ as [Hty [[v [Hval Hstepv]] _]].
      remember Hstepv. clear Heqm.
      eapply multi_preservation in Hstepv; [| eassumption].
      apply canonical_forms_bool in Hstepv; [| assumption].
      destruct Hstepv.
      - left. eapply rtc_r.
        + apply multi_if_cong. eassumption.
        + subst. constructor.
      - right. eapply rtc_r.
        + apply multi_if_cong. eassumption.
        + subst. constructor.
    }
    destruct H; eapply N'_multi_backpreservation; eauto;
      constructor; eapply morphing; try eassumption; apply γ_ok'_impl_good_subst; assumption.
Qed.

Fixpoint N (τ : ty) (e : tm 0) : Prop :=
  match τ with
    | tybool => (multistep e tmtrue \/ multistep e tmfalse)
    | tyarr τ1 τ2 => forall e', N τ1 e' -> N τ2 (tmapp e e')
  end.

(* Lemma app_step2 {n} : forall (e1 e2 : tm n), *)
(*     steps (tmapp e1 e2) -> steps e1. *)
(* Proof. *)
(*   intros. destruct H as [v [Hval Hstep]]. *)
(*   inversion Hstep; subst. *)
(*   - inversion Hval. *)
(*   - inversion H; subst. *)
(*     + exists (tmabs A a). split; constructor. *)
(*     +  *)
(*     + exists e1. split. *)
(*       * assumption. *)
(*       * constructor. *)

Lemma N_implies_norm : forall τ e,
    N τ e -> steps e.
Proof.
  induction τ.
  - (* -> *) intros. simpl in H. eapply IHτ2 in H.
    + admit.
    + admit.
  - (* bool *) intros. simpl in H. destruct H.
    + exists tmtrue. split.
      * constructor.
      * assumption.
    + exists tmfalse. split.
      * constructor.
      * assumption.
