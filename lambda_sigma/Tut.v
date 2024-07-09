Require Import Autosubst.Autosubst.

Inductive term :=
| Var (x : var)
| App (s t : term)
| Lam (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Eval simpl in fun sigma x => (Var x).[sigma].
(* simplifies to sigma x*)

Eval simpl in fun sigma s t => (App s t).[sigma].
(* simplifies to App s.[sigma] t.[sigma]*)

Eval simpl in fun sigma s => (Lam s).[sigma].
(* simplifies to Lam s.[up sigma]*)

Goal forall sigma,
  (Lam (App (Var 0) (Var 3))).[sigma] = Lam (App (Var 0) (sigma 2).[ren(+1)]).
intros. asimpl. reflexivity. Qed.

Inductive step : term -> term -> Prop :=
| Step_beta (s1 s2 t : term) :
    s1.[t/] = s2 -> step (App (Lam s1) t) s2
| Step_appL (s1 s2 t : term) :
    step s1 s2 -> step (App s1 t) (App s2 t)
| Step_appR (s t1 t2 : term) :
    step t1 t2 -> step (App s t1) (App s t2)
| Step_lam (s1 s2 : term) :
    step s1 s2 -> step (Lam s1) (Lam s2).

Lemma substitutivity s1 s2 :
  step s1 s2 -> forall sigma, step s1.[sigma] s2.[sigma].
Proof.
  induction 1; intros; simpl; eauto using step; subst.
  constructor. asimpl. reflexivity.
Qed.
