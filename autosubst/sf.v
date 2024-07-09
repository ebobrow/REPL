Require Import stlc core unscoped.

From Coq Require Import Init.Datatypes.
From Coq Require Import Init.Nat.

Definition context := list ty.

Reserved Notation "Gamma '|--' t '∈' T" (at level 40).

Fixpoint nth {A : Type} (l : list A) (n : nat) : option A :=
  match l with
    | nil => None
    | cons h t => if eqb n 0 then Some h else nth t (n - 1)
  end.

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma n T1,
      nth Gamma n = Some T1 ->
      Gamma |-- var_tm n ∈ T1
  | T_Abs : forall Gamma T1 T2 t1,
      cons T2 Gamma |-- t1 ∈ T1 ->
      Gamma |-- (lam T2 t1) ∈ (Fun T2 T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 ∈ (Fun T2 T1) ->
      Gamma |-- t2 ∈ T2 ->
      Gamma |-- (Core.app t1 t2) ∈ T1

where "Gamma '|--' t '∈' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Example typing_example_1 :
  nil |-- lam Base (var_tm 0) ∈ (Fun Base Base).
Proof. eauto. Qed.

Example typing_example_2 :
  nil |--
    lam Base (lam (Fun Base Base) (Core.app (var_tm 0) (Core.app (var_tm 0) (var_tm 1))))
    ∈ (Fun Base (Fun (Fun Base Base) Base)).
Proof. repeat constructor. apply T_App with (T2 := Base).
       - repeat constructor.
       - apply T_App with (T2 := Base); repeat constructor.
Qed.

Inductive value : tm -> Prop :=
  | V_Abs : forall t T,
      value (lam T t)
  | V_Var : forall n,
      value (var_tm n).

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T2 t1 v2,
         value v2 ->
         (Core.app (abs T2 t1) v2) --> t1 [v2/]
  | ST_App1 : ∀ t1 t1' t2,
         t1 --> t1' →
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : ∀ v1 t2 t2',
         value v1 →
         t2 --> t2' →
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : ∀ t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : ∀ t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : ∀ t1 t1' t2 t3,
      t1 --> t1' →
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').
Hint Constructors step : core.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Theorem progress : forall t T,
    nil |-- t ∈ T ->
    value t \/ exists t',
