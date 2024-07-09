Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import AutosubstSsr ARS Context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definitions
Inductive type : Type :=
| TyVar (x : var)
| Arr (A B : type)
| All (A : {bind type}).

Inductive term :=
| TeVar (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term)
| TAbs (s : {bind type in term})
| TApp (s : term) (A : type).

Substitution Lemmas
Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.

Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Instance HSubst_term : HSubst type term. derive. Defined.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

One-Step Reduction
Inductive step : term -> term -> Prop :=
| step_beta (A : type) (s t : term) :
    step (App (Abs A s) t) s.[t/]
| step_inst (A : type) (s : term) :
    step (TApp (TAbs s) A) s.|[A/]
| step_appL s1 s2 t :
    step s1 s2 -> step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
    step t1 t2 -> step (App s t1) (App s t2)
| step_abs A s1 s2 :
    step s1 s2 -> step (Abs A s1) (Abs A s2)
| step_tapp A s1 s2 :
    step s1 s2 -> step (TApp s1 A) (TApp s2 A)
| step_tabs s1 s2 :
    step s1 s2 -> step (TAbs s1) (TAbs s2).

Lemma step_ebeta A s t u : u = s.[t/] -> step (App (Abs A s) t) u.

Lemma step_einst A s t : t = s.|[A/] -> step (TApp (TAbs s) A) t.

Lemma step_substf theta sigma s t :
  step s t -> step s.|[theta].[sigma] t.|[theta].[sigma].





Lemma step_subst sigma s t : step s t -> step s.[sigma] t.[sigma].

Lemma step_hsubst theta s t : step s t -> step s.|[theta] t.|[theta].

Many-Step Reduction
Definition red := star step.

Definition sred sigma tau :=
  forall x : var, red (sigma x) (tau x).

Lemma red_app s1 s2 t1 t2 :
  red s1 s2 -> red t1 t2 -> red (App s1 t1) (App s2 t2).





Lemma red_abs A s1 s2 : red s1 s2 -> red (Abs A s1) (Abs A s2).

Lemma red_tapp A s1 s2 : red s1 s2 -> red (TApp s1 A) (TApp s2 A).

Lemma red_tabs s1 s2 : red s1 s2 -> red (TAbs s1) (TAbs s2).

Lemma red_subst sigma s t : red s t -> red s.[sigma] t.[sigma].

Lemma red_hsubst theta s t : red s t -> red s.|[theta] t.|[theta].

Lemma sred_up sigma tau : sred sigma tau -> sred (up sigma) (up tau).

Lemma sred_hup sigma tau theta :
  sred sigma tau -> sred (sigma >>| theta) (tau >>| theta).

Hint Resolve red_app red_abs red_tapp red_tabs sred_up sred_hup : red_congr.

Lemma red_compat sigma tau s :
  sred sigma tau -> red s.[sigma] s.[tau].



Lemma red_beta s t1 t2 : step t1 t2 -> red s.[t1/] s.[t2/].

Syntactic typing
Definition ctx := seq type.
Local Notation "Gamma `_ i" := (get Gamma i).

Inductive has_type (Gamma : ctx) : term -> type -> Prop :=
| ty_var (x : var) :
    x < size Gamma -> has_type Gamma (TeVar x) Gamma`_x
| ty_abs (A B : type) (s : term) :
    has_type (A :: Gamma) s B ->
    has_type Gamma (Abs A s) (Arr A B)
| ty_app (A B : type) (s t : term) :
    has_type Gamma s (Arr A B) ->
    has_type Gamma t A ->
    has_type Gamma (App s t) B
| ty_tabs (A : type) (s : term) :
    has_type Gamma..[ren (+1)] s A ->
    has_type Gamma (TAbs s) (All A)
| ty_tapp (A B : type) (s : term) :
    has_type Gamma s (All A) ->
    has_type Gamma (TApp s B) A.[B/].

(* Strong Normalization *)

Notation sn := (sn step).

Lemma sn_closed t s : sn (App s t) -> sn s.

Lemma sn_tclosed A s : sn (TApp s A) -> sn s.

Lemma sn_subst sigma s : sn s.[sigma] -> sn s.

Lemma sn_hsubst theta s : sn s.|[theta] -> sn s.

(* The Reducibility Candidates/Logical Predicate*)

Definition cand := term -> Prop.

Definition neutral (s : term) : bool :=
  match s with
    | Abs _ _ | TAbs _ => false
    | _ => true
  end.

Record reducible (P : cand) : Prop := {
  p_sn : forall s, P s -> sn s;
  p_cl : forall s t, P s -> step s t -> P t;
  p_nc : forall s, neutral s -> (forall t, step s t -> P t) -> P s
}.

Fixpoint L (T : type) (rho : nat -> cand) : cand :=
  match T with
    | TyVar x => rho x
    | Arr A B => fun s => forall t, L A rho t -> L B rho (App s t)
    | All A => fun s => forall P B, reducible P -> L A (P .: rho) (TApp s B)
  end.

Definition EL E (rho : nat -> cand) (sigma : var -> term) : Prop :=
  forall x, x < size E -> L E`_x rho (sigma x).

Definition admissible (rho : nat -> cand) :=
  forall x, reducible (rho x).

(* Facts about reducible sets. *)

Lemma reducible_sn : reducible sn.

Hint Resolve reducible_sn.

Lemma reducible_var P x : reducible P -> P (TeVar x).

Lemma ad_cons P rho :
  reducible P -> admissible rho -> admissible (P .: rho).

Lemma L_reducible T rho :
  admissible rho -> reducible (L T rho).

















Corollary L_sn A rho s : admissible rho -> L A rho s -> sn s.

Corollary L_cl T rho s t : admissible rho -> L T rho s -> step s t -> L T rho t.

Corollary L_nc T rho s :
  admissible rho -> neutral s -> (forall t, step s t -> L T rho t) -> L T rho s.

Corollary L_var T rho x : admissible rho -> L T rho (TeVar x).

Corollary L_cl_star T rho s t :
  admissible rho -> L T rho s -> red s t -> L T rho t.

(* Closure under beta expansion. *)

Lemma beta_expansion A B rho s t :
  admissible rho -> sn t -> L A rho s.[t/] ->
  L A rho (App (Abs B s) t).







Lemma inst_expansion A B rho s :
  admissible rho -> L A rho s.|[B/] -> L A rho (TApp (TAbs s) B).





(* The type substitution lemma. *)

Lemma extend_ext (rho tau : nat -> cand) :
  (forall i s, rho i s <-> tau i s) ->
  (forall P i s, (P .: rho) i s <-> (P .: tau) i s).

Lemma L_ext T rho tau :
  (forall i s, rho i s <-> tau i s) -> (forall s, L T rho s <-> L T tau s).









Lemma L_ren A rho xi s :
  L A.[ren xi] rho s <-> L A (xi >>> rho) s.







Lemma L_weaken A P rho s : L A.[ren (+1)] (P .: rho) s <-> L A rho s.

Lemma L_subst A rho sigma s :
  L A.[sigma] rho s <-> L A (fun i => L (sigma i) rho) s.







(* The fundamental theorem. *)

Theorem soundness Gamma s A :
  has_type Gamma s A -> forall rho theta sigma,
    admissible rho -> EL Gamma rho sigma -> L A rho s.|[theta].[sigma].









Lemma rho_id : admissible (fun _ => sn).

Corollary type_L E s T rho : has_type E s T -> admissible rho -> L T rho s.




Corollary strong_normalization E s T : has_type E s T -> sn s.
