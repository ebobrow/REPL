Require Export stlc.
From Coq Require Import Lists.List.

Definition context n := fin n -> ty.

Definition empty_ctxt : context 0 :=
  fun x => match x with end.

Inductive has_type { n : nat } (Γ : context n) : tm n -> ty -> Prop :=
  | T_Var i τ :
    Γ i = τ ->
    has_type Γ (var_tm i) τ
  | T_Lam e τ1 τ2 :
    has_type (τ1 .: Γ) e τ2 ->
    has_type Γ (tmabs τ1 e) (tyarr τ1 τ2)
  | T_App e1 e2 τ1 τ2 :
    has_type Γ e1 (tyarr τ1 τ2) ->
    has_type Γ e2 τ1 ->
    has_type Γ (tmapp e1 e2) τ2
  | T_True : has_type Γ tmtrue tybool
  | T_False : has_type Γ tmfalse tybool
  | T_If e1 e2 e3 τ :
    has_type Γ e1 tybool ->
    has_type Γ e2 τ ->
    has_type Γ e3 τ ->
    has_type Γ (tmif e1 e2 e3) τ.

Hint Constructors has_type : core.

Definition good_renaming {n m}
  (ρ : ren n m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, Γ i = Δ (ρ i).

Definition good_subst {n m}
  (σ : fin n -> tm m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, has_type Δ (σ i) (Γ i).

Lemma good_renaming_ext {n m}
  (ρ : fin n -> fin m)
  Γ Δ
  (h : good_renaming ρ Γ Δ)
  (A : ty) :
  good_renaming (upRen_tm_tm ρ) (A .: Γ) (A .: Δ).
Proof.
  unfold good_renaming in *.
  destruct i as [i|]; simpl; auto.
Qed.

Lemma renaming {n : nat} : forall {m} e τ Γ Δ (ρ : ren n m),
    has_type Γ e τ ->
    good_renaming ρ Γ Δ ->
    has_type Δ (ren_tm ρ e) τ.
Proof.
  intros m e τ Γ Δ ρ Hty. generalize dependent Δ. generalize dependent ρ. generalize dependent m.
  induction Hty; intros m ρ Δ Hρ; asimpl; econstructor; auto.
  - rewrite <- Hρ. assumption.
  - apply good_renaming_ext with (A := τ1) in Hρ.
    apply IHHty with (Δ := τ1 .: Δ) in Hρ. apply Hρ.
Qed.

Lemma weakening {n : nat} : forall (e : tm n) τ1 τ2 Γ,
    has_type Γ e τ1 ->
    has_type (τ2 .: Γ) (ren_tm ↑ e) τ1.
Proof.
  intros. apply renaming with (ρ := ↑) (Δ := τ2 .: Γ) in H.
  - assumption.
  - constructor.
Qed.

Lemma good_subst_ext {n m} (σ : fin n -> tm m) Γ Δ :
  forall t, good_subst σ Γ Δ -> good_subst (up_tm_tm σ) (t .: Γ) (t .: Δ).
Proof.
  unfold good_subst in *.
  destruct i as [i|]; simpl; asimpl.
  - apply weakening. auto.
  - constructor. reflexivity.
Qed.

(* substitution lemma in named syntax *)
Lemma morphing : forall n e m (Γ : context n) (Δ : context m) σ τ,
    has_type Γ e τ ->
    good_subst σ Γ Δ ->
    has_type Δ (subst_tm σ e) τ.
Proof.
  induction e; intros m Γ Δ σ τ Hty Hσ; simpl; inversion Hty; subst;
    try apply Hσ;
    econstructor; eauto using good_subst_ext.
Qed.
