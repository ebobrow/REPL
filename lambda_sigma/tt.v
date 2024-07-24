From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value (tm_abs x T2 t1)
  | v_true :
    value tm_true
  | v_false :
    value tm_false.
Hint Constructors value : db.

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
    | tm_var y =>
        if String.eqb x y then s else t
    | tm_abs y T t1 =>
        if String.eqb x y then t else tm_abs y T (subst x s t1)
    | tm_app t1 t2 =>
        tm_app (subst x s t1) (subst x s t2)
    | tm_true => tm_true
    | tm_false => tm_false
    | tm_if t1 t2 t3 =>
        tm_if (subst x s t1) (subst x s t2) (subst x s t3)
  end.

(** Reduction *)
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
      value v2 ->
      step (tm_app (tm_abs x T2 t1) v2) (subst x v2 t1)
  | ST_App1 : forall t1 t1' t2,
      step t1 t1' ->
      step (tm_app t1 t2) (tm_app t1' t2)
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      step t2 t2' ->
      step (tm_app v1 t2) (tm_app v1 t2')
  | ST_IfTrue : forall t1 t2,
      step (tm_if tm_true t1 t2) t1
  | ST_IfFalse : forall t1 t2,
      step (tm_if tm_false t1 t2) t2
  | ST_If : forall t1 t1' t2 t3,
      step t1 t1' ->
      step (tm_if t1 t2 t3) (tm_if t1' t2 t3).
Hint Constructors step : db.

Inductive multistep : tm -> tm -> Prop :=
  | multi_refl : forall t, multistep t t
  | multi_step : forall x y z,
      step x y ->
      multistep y z ->
      multistep x z.
Hint Constructors multistep : db.

Definition steps (e : tm) : Prop := exists e', value e' /\ multistep e e'.
Hint Unfold steps : db.

Lemma multistep_mid : forall x y z,
    multistep x y -> multistep y z -> multistep x z.
Proof.
  intros x y z Hxy Hyz. induction Hxy.
  - assumption.
  - induction Hyz; eauto with db.
Qed.

Lemma multi_if_cong : forall e1 e2 e3 e1',
    multistep e1 e1' -> multistep (tm_if e1 e2 e3) (tm_if e1' e2 e3).
Proof.
  intros. induction H.
  - constructor.
  - econstructor.
    + constructor. eassumption.
    + assumption.
Qed.

Lemma multi_app_cong2 : forall e1 e2 e2',
    value e1 ->
    multistep e2 e2' ->
    multistep (tm_app e1 e2) (tm_app e1 e2').
Proof.
  intros. induction H0.
  - constructor.
  - econstructor.
    + apply ST_App2; eassumption.
    + assumption.
Qed.

(** Typing *)
Notation env := (list (string * ty)).
Fixpoint get { A : Type } (s : string) (E : list (string * A)) : option A :=
  match E with
    | nil => None
    | (x, t) :: E' => if String.eqb x s then Some t else get s E'
  end.

Inductive has_type : env -> tm -> ty -> Prop :=
  | T_Var : forall G x T1,
      get x G = Some T1 ->
      has_type G (tm_var x) T1
  | T_Abs : forall G x T1 T2 t1,
      has_type (cons (x, T2) G) t1 T1 ->
      has_type G (tm_abs x T2 t1) (Ty_Arrow T2 T1)
  | T_App : forall T1 T2 G t1 t2,
      has_type G t1 (Ty_Arrow T2 T1) ->
      has_type G t2 T2 ->
      has_type G (tm_app t1 t2) T1
  | T_True : forall G,
      has_type G tm_true Ty_Bool
  | T_False : forall G,
      has_type G tm_false Ty_Bool
  | T_If : forall t1 t2 t3 T1 G,
      has_type G t1 Ty_Bool ->
      has_type G t2 T1 ->
      has_type G t3 T1 ->
      has_type G (tm_if t1 t2 t3) T1.
Hint Constructors has_type : db.

(** Closed terms *)
Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x, appears_free_in x (tm_var x)
  | afi_app1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs : forall x y T t, x <> y -> appears_free_in x t -> appears_free_in x (tm_abs y T t)
  | afi_if1 : forall x t1 t2 t3, appears_free_in x t1 -> appears_free_in x (tm_if t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3, appears_free_in x t2 -> appears_free_in x (tm_if t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3, appears_free_in x t3 -> appears_free_in x (tm_if t1 t2 t3).

Definition closed (t : tm) := forall x, ~ (appears_free_in x t).

Lemma ctxt_contains_free_vars : forall G x t T1,
    appears_free_in x t ->
    has_type G t T1 ->
    exists T2, get x G = Some T2.
Proof.
  intros G x t T1 Hfree Hty. generalize dependent x. induction Hty; intros; inversion Hfree; subst.
  - (* var *) exists T1. assumption.
  - (* abs *) apply IHHty in H4.
    destruct H4. inversion H.
    apply String.eqb_neq in H2. rewrite String.eqb_sym in H2. rewrite H2 in H1.
    exists x1. assumption.
  - (* app1 *) apply IHHty1 in H1. destruct H1. exists x0. assumption.
  - (* app2 *) apply IHHty2 in H1. destruct H1. exists x0. assumption.
  - (* if1 *) apply IHHty1 in H1. destruct H1. exists x0. assumption.
  - (* if2 *) apply IHHty2 in H1. destruct H1. exists x0. assumption.
  - (* if3 *) apply IHHty3 in H1. destruct H1. exists x0. assumption.
Qed.

Lemma nil_ctxt_implies_closed : forall x T,
    has_type nil x T -> closed x.
Proof.
  unfold closed. induction x; intros T Hty.
  - inversion Hty. inversion H1.
  - inversion Hty. subst.
    unfold not. intros. inversion H; subst.
    + eapply IHx1 in H2. apply H2. apply H3.
    + eapply IHx2 in H4. apply H4. apply H3.
  - inversion Hty. subst.
    unfold not. intros. destruct (eqb_spec x0 s).
    + inversion H. contradiction.
    + inversion H. subst. remember ((s, t) :: nil) as G.
      assert (~ exists T, get x0 G = Some T). { unfold not. intros. destruct H0. subst. simpl in H0.
                                           apply String.eqb_neq in n. rewrite String.eqb_sym in n.
                                           rewrite n in H0. discriminate H0. }
      apply H0. eapply ctxt_contains_free_vars; eassumption.
  - unfold not. intros. inversion H.
  - unfold not. intros. inversion H.
  - inversion Hty. subst. unfold not. intros. inversion H; subst.
    + eapply IHx1; eassumption.
    + eapply IHx2; eassumption.
    + eapply IHx3; eassumption.
Qed.

(** Normalization *)
Fixpoint N (T : ty) (t : tm) : Prop :=
  has_type nil t T /\ steps t /\
    (match T with
       | Ty_Bool => True
       | Ty_Arrow T1 T2 => forall t', N T1 t' -> N T2 (tm_app t t')
    end).

Lemma N_implies_typed : forall t T,
    N T t -> has_type nil t T.
Proof. intros. destruct T; simpl; destruct H as [Hty _]; apply Hty. Qed.

Lemma N_implies_norm : forall t T,
    N T t -> steps t.
Proof. intros. induction T; unfold N in H; destruct H as [_ [Hstep _]]; apply Hstep. Qed.

Lemma get1 {A: Type} : forall G1 G2 x (T : A),
    get x G1 = Some T ->
    get x (G1 ++ G2) = Some T.
Proof.
  intros. induction G1.
  - inversion H.
  - destruct a. simpl in H. simpl. destruct (String.eqb s x).
    + assumption.
    + apply IHG1 in H. apply H.
Qed.

Lemma get2 {A: Type} : forall G1 G2 x (T : A),
    get x (G1 ++ G2) = Some T ->
    get x G1 = None ->
    get x G2 = Some T.
Proof.
  induction G1.
  - intros. simpl in H. apply H.
  - intros. destruct a. simpl in H. simpl in H0. destruct (String.eqb_spec s x).
    + discriminate H0.
    + apply IHG1 in H; assumption.
Qed.

Lemma get3 {A : Type} : forall G1 G2 x (T : A),
    get x G1 = None ->
    get x G2 = Some T ->
    get x (G1 ++ G2) = Some T.
Proof.
  induction G1.
  - intros. simpl. assumption.
  - intros. destruct a. simpl. simpl in H. destruct (String.eqb_spec s x).
    + inversion H.
    + apply IHG1; assumption.
Qed.

Lemma get4 {A : Type} : forall G1 G2 x,
    get x G1 = None ->
    get x G2 = None ->
    @get A x (G1 ++ G2) = None.
Proof.
  induction G1.
  - intros. simpl. apply H0.
  - intros. destruct a. simpl. simpl in H. destruct (String.eqb_spec s x).
    + inversion H.
    + apply IHG1; assumption.
Qed.

Lemma weakening : forall G1 G2 t T,
    (forall x U, get x G1 = Some U -> get x G2 = Some U) ->
    has_type G1 t T ->
    has_type G2 t T.
Proof.
  intros. generalize dependent G2.
  induction H0; intros; econstructor; eauto.
  eapply IHhas_type. intros. simpl. simpl in H1. destruct (String.eqb_spec x x0); auto.
Qed.

Lemma weakening' : forall G t T,
    has_type nil t T ->
    has_type G t T.
Proof.
  intros. eapply weakening with (G1 := nil).
  - intros. inversion H0.
  - assumption.
Qed.

Lemma ctxt_overwrite : forall t x T1 T2 G E U,
    has_type (E ++ (x, T1) :: (x, T2) :: G) t U ->
    has_type (E ++ (x, T1) :: G) t U.
Proof.
  induction t; intros; inversion H; subst; econstructor; eauto.
  - induction E.
    + simpl. simpl in H2. destruct (String.eqb_spec x s); assumption.
    + destruct a. simpl in *. destruct (String.eqb_spec s0 s); auto using T_Var.
  - eapply IHt with (E := (s, t) :: E). eassumption.
Qed.

Lemma ctxt_commute : forall t x1 x2 T1 T2 G E U,
    x1 <> x2 ->
    has_type (E ++ (x1, T1) :: (x2, T2) :: G) t U ->
    has_type (E ++ (x2, T2) :: (x1, T1) :: G) t U.
Proof.
  induction t; intros; inversion H0; subst; econstructor; eauto.
  - induction E.
    + simpl in *. destruct (String.eqb_spec x1 s).
      * subst. destruct (String.eqb_spec x2 s).
        -- subst. contradiction.
        -- assumption.
      * destruct (String.eqb_spec x2 s); assumption.
    + destruct a. simpl in *. destruct (String.eqb_spec s0 s); auto using T_Var.
  - apply IHt with (E := (s, t) :: E); assumption.
Qed.

Lemma subst_preserves_typing : forall G x U t v T,
    has_type ((x, U) :: G) t T ->
    has_type nil v U ->
    has_type G (subst x v t) T.
Proof.
  intros G x U t v T Ht Hv.
  generalize dependent G. generalize dependent T.
  induction t; intros T G H; inversion H; subst; simpl; eauto with db.
  - (* var *) destruct (eqb_spec x s).
    + subst. inversion H2. assert (String.eqb s s = true) by apply String.eqb_refl.
      rewrite H0 in H1. inversion H1. subst. eapply weakening' in Hv. apply Hv.
    + apply String.eqb_neq in n. unfold get in H2. rewrite n in H2. fold (@get ty) in H2.
      constructor. assumption.
  - (* abs *) destruct (eqb_spec x s).
    + subst. constructor. eapply ctxt_overwrite with (E := nil). simpl. eassumption.
    + constructor. apply IHt. apply ctxt_commute with (E := nil).
      * symmetry. assumption.
      * assumption.
Qed.

Lemma preservation : forall T t t',
    has_type nil t T ->
    step t t' ->
    has_type nil t' T.
Admitted.
Hint Resolve preservation : db.

Lemma multi_preservation : forall T t t',
    has_type nil t T ->
    multistep t t' ->
    has_type nil t' T.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmultistep. eapply preservation; eassumption.
Qed.

Lemma progress : forall t T,
    has_type nil t T ->
    steps t.
Admitted.
Hint Resolve progress : db.

Lemma canonical_form_bool : forall v,
    value v ->
    has_type nil v Ty_Bool ->
    v = tm_true \/ v = tm_false.
Proof.
  intros. inversion H.
  - subst. inversion H0.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Lemma step_preserves_R : forall T t t', step t t' -> N T t -> N T t'. *)
(* Proof with eauto with db. *)
(*   induction T; simpl; intros t t' Hstep HN; destruct HN as [Hty [Rstep Relim]]; repeat split... *)
(* Qed. *)

(* Lemma multistep_preserves_R : forall T t t', multistep t t' -> N T t -> N T t'. *)
(* Proof. *)
(*   intros T t t' Hstep. induction Hstep. *)
(*   - auto. *)
(*   - intros. apply IHHstep. eapply step_preserves_R; eassumption. *)
(* Qed. *)

Lemma step_preserves_R' : forall T t t',
    has_type nil t T -> step t t' -> N T t' -> N T t.
Proof with eauto with db.
  induction T; simpl; intros t t' Hty Hstep HN; destruct HN as [Rty [Rstep Relim]]; repeat split...
  - (* -> elim *) intros.
    eapply IHT2; eauto using ST_App1.
    eapply T_App.
    + eassumption.
    + apply N_implies_typed. assumption.
Qed.

Lemma multistep_preserves_R' : forall T t t',
    has_type nil t T -> multistep t t' -> N T t' -> N T t.
Proof.
  intros T t t' Hty Hstep. induction Hstep.
  - auto.
  - intros. eapply step_preserves_R'; try eassumption.
    apply preservation with (t' := y) in Hty.
    + apply IHHstep in Hty; assumption.
    + assumption.
Qed.

(** Multisubst *)

Definition multisubst := list (string * tm).

Fixpoint do_multisubst (sub : multisubst) (t : tm) :=
  match sub with
    | nil => t
    | (x, v) :: sub' => do_multisubst sub' (subst x v t)
  end.

(* Inductive instantiation : multisubst -> env -> Prop := *)
(*   | V_nil : *)
(*     instantiation nil nil *)
(*   | V_cons : forall x T v g G, *)
(*       value v -> N T v -> *)
(*       instantiation g G -> *)
(*       instantiation ((x,v)::g) ((x,T)::G). *)

Inductive no_dups : multisubst -> Prop :=
  | nd_nil : no_dups nil
  | nd_cons (s : string) (v : tm) (g' : multisubst) :
      no_dups g' -> get s g' = None -> no_dups ((s, v) :: g').

Definition instantiation (g : multisubst) (G : env) : Prop :=
  (* no_dups g /\ forall x T, (get x G = Some T -> N T (do_multisubst g (tm_var x))). *)
  (* no_dups g /\ forall x T, (get x G = Some T -> (exists v, get x g = Some v /\ N T v)). *)
  (* no_dups g /\ (forall x T, get x G = Some T <-> (exists v, get x g = Some v /\ N T v)). *)
  no_dups g /\ (forall x, (exists T, get x G = Some T) <-> (exists v, get x g = Some v)) /\
    (forall x T, get x G = Some T -> exists v, get x g = Some v /\ N T v).

Lemma inst_impl_nd_step : forall g G s v,
    instantiation ((s, v) :: g) G ->
    no_dups g.
Proof.
  intros. unfold instantiation in H. destruct H. inversion H. assumption.
Qed.

Fixpoint drop {X:Set} (n:string) (nxs:list (string * X))
            : list (string * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') =>
        if String.eqb n' n then drop n nxs'
        else (n',x)::(drop n nxs')
  end.

Lemma get_drop_neq {A : Set} : forall (G : list (string * A)) s1 s2,
    s1 <> s2 ->
    get s1 G = get s1 (drop s2 G).
Proof.
  induction G.
  - intros. reflexivity.
  - intros. destruct a. simpl. destruct (String.eqb_spec s s1).
    + assert (String.eqb s s2 = false).
      { subst. apply String.eqb_neq. assumption. }
      rewrite H0. simpl. apply String.eqb_eq in e. rewrite e. reflexivity.
    + destruct (String.eqb_spec s s2).
      * auto.
      * simpl. apply String.eqb_neq in n. rewrite n. auto.
Qed.

Lemma get_drop_eq {A : Set} : forall (G : list (string * A)) s,
    get s (drop s G) = None.
Proof.
  induction G.
  - intros. reflexivity.
  - intros. destruct a. simpl. destruct (String.eqb_spec s0 s).
    + apply IHG.
    + simpl. apply String.eqb_neq in n. rewrite n. apply IHG.
Qed.

Lemma instantiation_drop : forall g G s v,
    instantiation ((s, v) :: g) G ->
    instantiation g (drop s G).
Proof.
  intros. split.
  - eapply inst_impl_nd_step. eassumption.
  - intros. split.
    + intros. split.
      * intros. destruct H as [_ [Hdom _]]. specialize Hdom with x. simpl in *.
        destruct H0 as [T HT].
        destruct (String.eqb_spec s x).
        -- subst. rewrite get_drop_eq in HT. discriminate HT.
        -- apply Hdom. exists T. rewrite <- get_drop_neq in HT; [| symmetry]; assumption.
      * intros. destruct H0 as [v' Hv]. destruct H as [Hnd [Hdom _]].
        specialize Hdom with x. simpl in *. destruct (String.eqb_spec s x).
        -- inversion Hnd. subst. rewrite Hv in H3. discriminate H3.
        -- rewrite <- get_drop_neq; [| symmetry; assumption]. apply Hdom.
           exists v'. assumption.
    + intros. destruct H as [_ [Hdom HN]]. specialize Hdom with x. specialize HN with x T.
      simpl in *. destruct (String.eqb_spec s x).
      * subst. rewrite get_drop_eq in H0. discriminate H0.
      * rewrite <- get_drop_neq in H0; [| symmetry; assumption]. apply HN in H0. apply H0.
Qed.

Lemma drop_notin {A : Set} : forall g x,
    get x g = None ->
    @drop A x g = g.
Proof.
  induction g.
  - intros. reflexivity.
  - intros. destruct a. simpl in *. destruct (String.eqb_spec s x).
    + discriminate H.
    + rewrite IHg; auto.
Qed.

Lemma nd_drop : forall g x,
    no_dups g -> no_dups (drop x g).
Proof.
  induction g.
  - intros. simpl. assumption.
  - intros. destruct a. simpl. destruct (String.eqb_spec s x).
    + inversion H. subst. rewrite drop_notin; assumption.
    + inversion H. subst. constructor.
      * apply IHg. assumption.
      * erewrite get_drop_neq in H4; eassumption.
Qed.

Lemma nd_drop' : forall g x v,
    no_dups g -> no_dups ((x, v) :: drop x g).
Proof.
  intros. induction g.
  - intros. simpl. constructor; auto.
  - intros. inversion H. subst. simpl. destruct (String.eqb_spec s x).
    + subst. constructor; rewrite drop_notin; assumption.
    + constructor.
      * constructor.
        -- apply IHg in H2. inversion H2. subst. assumption.
        -- rewrite <- get_drop_neq; assumption.
      * simpl. apply String.eqb_neq in n. rewrite n.
        apply get_drop_eq.
Qed.

Lemma instantiation_drop' : forall g G x v T,
    instantiation g G ->
    instantiation ((x, v) :: drop x g) ((x, T) :: G).
Proof.
  unfold instantiation. intros g G x v T [Hnd HN]. split.
  - eapply nd_drop' in Hnd. eassumption.
Admitted.

Lemma instantiation_drop'' : forall g G s,
    instantiation g G ->
    instantiation (drop s g) (drop s G).
Admitted.

Lemma multisubst_app : forall g e1 e2,
    do_multisubst g (tm_app e1 e2) = tm_app (do_multisubst g e1) (do_multisubst g e2).
Proof.
  induction g; intros.
  - reflexivity.
  - destruct a. simpl. apply IHg.
Qed.

Lemma multisubst_if : forall g e1 e2 e3,
    do_multisubst g (tm_if e1 e2 e3) = tm_if (do_multisubst g e1) (do_multisubst g e2) (do_multisubst g e3).
Proof.
  induction g; intros.
  - reflexivity.
  - destruct a. simpl. apply IHg.
Qed.

Lemma multisubst_true : forall g,
    do_multisubst g tm_true = tm_true.
Proof.
  intros. induction g.
  - reflexivity.
  - destruct a. simpl. assumption.
Qed.

Lemma multisubst_false : forall g,
    do_multisubst g tm_false = tm_false.
Proof.
  intros. induction g.
  - reflexivity.
  - destruct a. simpl. assumption.
Qed.

Lemma multisubst_abs : forall g x T t,
    do_multisubst g (tm_abs x T t) = tm_abs x T (do_multisubst (drop x g) t).
Proof.
  induction g; intros.
  - reflexivity.
  - destruct a. simpl. destruct (String.eqb_spec s x); apply IHg.
Qed.

Lemma N_implies_closed : forall t T,
    N T t -> closed t.
Proof.
  intros. apply N_implies_typed in H. eapply nil_ctxt_implies_closed. eassumption.
Qed.

Lemma subst_closed : forall s x t,
    ~ appears_free_in x t ->
    subst x s t = t.
Proof.
  induction t; intros.
  - simpl. destruct (String.eqb_spec x s0).
    + subst. assert (appears_free_in s0 (tm_var s0)) by constructor.
      apply H in H0. inversion H0.
    + reflexivity.
  - simpl. assert (~ appears_free_in x t1). {
      unfold not. intros. apply H. constructor. assumption.
    }
    apply IHt1 in H0. rewrite H0.
    assert (~ appears_free_in x t2). {
      unfold not. intros. apply H. apply afi_app2. assumption.
    }
    apply IHt2 in H1. rewrite H1. reflexivity.
  - simpl. destruct (String.eqb_spec x s0).
    + reflexivity.
    + assert (~ appears_free_in x t0). {
        unfold not. intros. apply H. constructor; assumption.
      }
      apply IHt in H0. rewrite H0. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. assert (~ appears_free_in x t1). { unfold not. intros. apply H. constructor. assumption. }
    assert (~ appears_free_in x t2). { unfold not. intros. apply H. apply afi_if2. assumption. }
    assert (~ appears_free_in x t3). { unfold not. intros. apply H. apply afi_if3. assumption. }
    apply IHt1 in H0. rewrite H0. apply IHt2 in H1. rewrite H1. apply IHt3 in H2. rewrite H2.
    reflexivity.
Qed.

Lemma multisubst_closed : forall g t,
    closed t ->
    do_multisubst g t = t.
Proof.
  induction g.
  - intros. reflexivity.
  - intros. destruct a. simpl. rewrite subst_closed.
    + apply IHg. assumption.
    + unfold closed in H. specialize H with s. apply H.
Qed.

Lemma subst_commute : forall x1 v1 x2 v2 t,
    closed v1 -> closed v2 ->
    x1 <> x2 ->
    subst x1 v1 (subst x2 v2 t) = subst x2 v2 (subst x1 v1 t).
Proof.
  intros. induction t.
  - simpl. destruct (String.eqb_spec x2 s).
    + subst. assert (String.eqb x1 s = false). { apply String.eqb_neq. assumption. }
      rewrite H2. simpl. rewrite String.eqb_refl.
      assert (~ appears_free_in x1 v2) by eapply H0.
      apply subst_closed. assumption.
    + simpl. destruct (String.eqb_spec x1 s).
      * assert (~ appears_free_in x2 v1) by eapply H.
        rewrite subst_closed; auto.
      * simpl. apply String.eqb_neq in n. rewrite n. reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
  - simpl. destruct (String.eqb_spec x2 s).
    + subst. simpl. assert (String.eqb x1 s = false). { apply String.eqb_neq. assumption. }
      rewrite H2. simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. destruct (String.eqb_spec x1 s).
      * subst. simpl. assert (String.eqb x2 s = false). { apply String.eqb_neq. assumption. }
        rewrite H2. reflexivity.
      * simpl. apply String.eqb_neq in n. rewrite n. rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. rewrite IHt3. reflexivity.
Qed.

Lemma instantiation_commute : forall g G x1 v1 x2 v2,
    x1 <> x2 ->
    instantiation ((x1, v1) :: (x2, v2) :: g) G ->
    instantiation ((x2, v2) :: (x1, v1) :: g) G.
Proof.
  Admitted.
  (* induction g. *)
  (* - intros. split. *)
  (*   + repeat constructor. *)
  (*     simpl. apply String.eqb_neq in H. rewrite H. reflexivity. *)
  (*   + intros. destruct H0 as [_ HN]. apply HN in H1. simpl. simpl in H1. *)
  (*     destruct (String.eqb_spec x1 x). *)
  (*     * subst. assert (String.eqb x2 x = false). { apply String.eqb_neq. symmetry. apply H. } *)
  (*       rewrite H0. simpl. rewrite String.eqb_refl. admit. *)
  (*     * simpl in H1. destruct (String.eqb_spec x2 x). *)
  (*       -- admit. *)
  (*       -- simpl. apply String.eqb_neq in n. rewrite n. assumption. *)
  (* - intros. admit. *)
  (*   Admitted. *)

Lemma instantiation_impl_closed : forall g G x v T,
    get x G = Some T ->
    instantiation ((x, v) :: g) G ->
    closed v.
Proof.
  induction g.
  - intros. destruct H0 as [_ [_ HN]]. specialize HN with x T.
    apply HN in H. destruct H as [v0 [Hgetv HNv]].
    inversion Hgetv. rewrite String.eqb_refl in H0. inversion H0. subst.
    apply N_implies_closed in HNv. apply HNv.
  - intros. destruct a. assert (x <> s).
    { destruct H0 as [Hnd _]. inversion Hnd. subst. inversion H4. destruct (String.eqb_spec s x).
      - discriminate H1.
      - symmetry. assumption.
    }
    assert (get x (drop s G) = Some T).
    { erewrite get_drop_neq in H; eassumption. }
    eapply IHg.
    + eapply H2.
    + eapply instantiation_drop. apply instantiation_commute; eassumption.
Qed.

Lemma subst_multisubst : forall g G x v t,
    instantiation g G ->
    closed v ->
    subst x v (do_multisubst (drop x g) t) = do_multisubst (drop x g) (subst x v t).
Proof.
  induction g.
  - reflexivity.
  - intros. destruct a. simpl. assert (instantiation g (drop s G)).
    { eapply instantiation_drop. eassumption. }
    (* inversion H. subst. *)
    destruct (String.eqb_spec s x).
    + eapply IHg; eassumption.
    + simpl. rewrite subst_commute. eapply IHg; try eassumption.
      * eapply instantiation_impl_closed.
        -- admit.
        -- eassumption.
      * assumption.
      * assumption.
Admitted.

Lemma step_closed : forall t t',
    closed t ->
    step t t' ->
    closed t'.
Proof.
  induction t; intros t' Hclos Hstep; inversion Hstep; subst.
Admitted.

Lemma multistep_closed : forall t t',
    closed t ->
    multistep t t' ->
    closed t'.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmultistep. eapply step_closed; eassumption.
Qed.

Lemma multisubst_var : forall g G x T v,
    has_type G (tm_var x) T ->
    instantiation g G ->
    get x g = Some v ->
    do_multisubst g (tm_var x) = v.
Proof.
  induction g.
  - intros. inversion H1.
  - intros. destruct a. remember H0 as Hins. clear HeqHins.
    destruct H0 as [_ HN]. inversion H. apply HN in H3.
    destruct H3 as [v' [Hgetv HNv]]. subst.
    simpl in *. destruct (String.eqb_spec s x).
    + inversion H1. inversion Hgetv. subst. apply N_implies_closed in HNv.
      apply multisubst_closed. assumption.
    + eapply IHg with (G := drop s G).
      * constructor. inversion H. rewrite <- get_drop_neq.
        -- eassumption.
        -- symmetry. assumption.
      * eapply instantiation_drop. eassumption.
      * assumption.
Qed.

Lemma multisubst_var' : forall g x,
    get x g = None ->
    do_multisubst g (tm_var x) = tm_var x.
Proof.
  induction g.
  - intros. reflexivity.
  - intros. destruct a. simpl in *. destruct (String.eqb_spec s x).
    + discriminate H.
    + apply IHg. assumption.
Qed.

Lemma notsome_impl_none {A : Type} : forall g x,
    ~ (exists v, get x g = Some v) ->
    @get A x g = None.
Proof.
  induction g.
  - intros. reflexivity.
  - intros. destruct a. simpl in *. destruct (String.eqb s x).
    + exfalso. apply H. exists a. reflexivity.
    + apply IHg. apply H.
Qed.

Lemma get5 {A : Type} : forall G1 G2 G3 x T,
    get x (G1 ++ G2 ++ G3) = Some T ->
    get x G2 = None ->
    @get A x (G1 ++ G3) = Some T.
Proof.
  intros. destruct (get x G1) eqn:E1.
  - remember E1. clear Heqe. eapply get1 in E1. rewrite H in E1. rewrite <- E1 in e.
    apply get1. assumption.
  - apply get2 in H; [| assumption]. apply get2 in H; [| assumption].
    apply get3; assumption.
Qed.

Lemma annoying_get_lemma : forall e G1 G2 G3 s T U,
    has_type ((s, U) :: G1 ++ G2 ++ G3) e T ->
    has_type ((s, U) :: G1 ++ (drop s G2) ++ G3) e T.
Proof.
  induction e; intros; inversion H; econstructor; eauto.
  - simpl in *. destruct (String.eqb_spec s0 s).
    + assumption.
    + destruct (get s G1) eqn:E.
      * remember E. clear Heqe. eapply get1 in E. rewrite H2 in E. rewrite E.
        apply get1. assumption.
      * apply get3 with (G2 := drop s0 G2 ++ G3) (T := T) in E.
        -- assumption.
        -- apply get2 in H2.
           ++ destruct (get s G2) eqn:E2.
              ** remember E2. clear Heqe. eapply get1 in E2. rewrite H2 in E2. rewrite E2.
                 apply get1. rewrite <- get_drop_neq; [|symmetry]; assumption.
              ** apply get2 in H2.
                 --- rewrite get_drop_neq with (s2 := s0) in E2. apply get3; assumption.
                     symmetry. assumption.
                 --- assumption.
           ++ assumption.
   - subst. admit.
Admitted.

Lemma multisubst_preserves_types' : forall e G1 G2 G3 g T,
    (forall x U, get x G2 = Some U -> get x G1 = None) ->
    has_type (G1 ++ G2 ++ G3) e T ->
    instantiation g G2 ->
    has_type (G1 ++ G3) (do_multisubst g e) T.
Proof.
  induction e; intros G1 G2 G3 g T Hdisj Hty Hins.
  - remember Hins. clear Heqi.
    destruct Hins as [Hnd [Hdom HN]]. specialize HN with s T.
    inversion Hty. subst. destruct (get s G2) eqn:Es.
    + assert (Some t = Some T).
      { remember Es. clear Heqe. apply Hdisj in Es. erewrite get3 in H1.
        - eapply H1.
        - assumption.
        - apply get1. assumption. }
      apply HN in H. destruct H as [v [Hgetv HNv]].
      apply N_implies_typed in HNv. erewrite multisubst_var with (G := G2); eauto using T_Var.
      apply weakening'. eassumption.
    + specialize Hdom with s. destruct Hdom as [Hdomf Hdomb].
      assert (~ exists (T : ty), None = Some T). { unfold not. intros. destruct H as [T' HT']. discriminate HT'. }
      rewrite <- Es in H. assert (~ exists v, get s g = Some v).
      { unfold not. intros. apply H. apply Hdomb. apply H0. }
      rewrite multisubst_var'.
      * constructor. eapply get5; eassumption.
      * apply notsome_impl_none. assumption.
  - inversion Hty. subst. rewrite multisubst_app. eapply T_App; eauto.
  - inversion Hty. subst. rewrite multisubst_abs. eapply T_Abs.
    eapply IHe with (G1 := (s, t) :: G1) (G2 := drop s G2).
    + intros. simpl. destruct (String.eqb_spec s x).
      * subst. rewrite get_drop_eq in H. discriminate H.
      * rewrite <- get_drop_neq in H.
        -- apply Hdisj in H. apply H.
        -- symmetry. assumption.
    + apply annoying_get_lemma. assumption.
    + apply instantiation_drop''. assumption.
  - inversion Hty. rewrite multisubst_true. constructor.
  - inversion Hty. rewrite multisubst_false. constructor.
  - inversion Hty. subst. rewrite multisubst_if. constructor; eauto.
Qed.

Lemma multisubst_preserves_types : forall e G g T,
    has_type G e T ->
    instantiation g G ->
    has_type nil (do_multisubst g e) T.
Proof.
  intros. apply multisubst_preserves_types' with (G1 := nil) (G2 := G).
  - intros. reflexivity.
  - rewrite app_nil_r. simpl. assumption.
  - assumption.
Qed.

Lemma fundamental_lemma : forall G g e T,
    has_type G e T ->
    instantiation g G ->
    N T (do_multisubst g e).
Proof.
  intros G g e T Hty Hsub.
  generalize dependent g.
  induction Hty; intros.
  - (* var *) remember Hsub. clear Heqi.
    destruct Hsub as [_ [Hdom HN]]. specialize HN with x T1.
    apply HN in H. destruct H as [v [Hgetv HNv]].
    specialize Hdom with x. destruct Hdom as [_ Hdomb].
    assert (exists v, get x g = Some v). { exists v. apply Hgetv. }
    apply Hdomb in H. destruct H as [T HT].
    erewrite multisubst_var with (v := v); try eassumption.
    constructor. apply HT.
  - (* abs *) subst. simpl. split.
    + eapply multisubst_preserves_types; eauto with db.
    + split.
      * eapply progress. eapply multisubst_preserves_types; eauto with db.
      * intros.
        remember H as HN. clear HeqHN.
        apply N_implies_norm in H. destruct H as [v [Hval Hst]].
        apply multistep_preserves_R' with (t' := subst x v (do_multisubst (drop x g) t1)).
        -- eapply T_App.
           ++ apply multisubst_preserves_types with (G := G).
              ** constructor. assumption.
              ** assumption.
           ++ apply N_implies_typed. assumption.
        -- rewrite multisubst_abs.
           apply multistep_mid with (y := tm_app (tm_abs x T2 (do_multisubst (drop x g) t1)) v).
           ++ apply multi_app_cong2.
              ** constructor.
              ** apply Hst.
           ++ apply multi_step with (y := subst x v (do_multisubst (drop x g) t1)).
              ** constructor. apply Hval.
              ** constructor.
        -- assert (subst x v (do_multisubst (drop x g) t1) = do_multisubst ((x, v) :: drop x g) t1).
           { simpl. eapply subst_multisubst.
             - eassumption.
             - apply multistep_closed with (t := t').
               + eapply N_implies_closed; eassumption.
               + apply Hst.
           }
           rewrite H. apply IHHty. apply instantiation_drop'. assumption.
  - (* app *) rewrite multisubst_app. remember Hsub. clear Heqi.
    apply IHHty1 in Hsub. destruct Hsub as [_ [_ Helim]].
    specialize Helim with (do_multisubst g t2).
    apply IHHty2 in i. apply Helim in i. apply i.
  - (* true *) simpl. rewrite multisubst_true. split; eauto with db.
  - (* false *) simpl. rewrite multisubst_false. split; eauto with db.
  - (* if *) rewrite multisubst_if.
    assert (multistep (do_multisubst g t1) tm_true \/ multistep (do_multisubst g t1) tm_false).
    + apply IHHty1 in Hsub. destruct Hsub as [Nty [Nstep _]].
      destruct Nstep. destruct H. apply canonical_form_bool in H.
      * destruct H; subst; [left|right]; apply H0.
      * eapply multi_preservation; eassumption.
    + assert (multistep (tm_if (do_multisubst g t1) (do_multisubst g t2) (do_multisubst g t3))
                        (do_multisubst g t2) \/
              multistep (tm_if (do_multisubst g t1) (do_multisubst g t2) (do_multisubst g t3))
                        (do_multisubst g t3)).
      * destruct H.
        -- left. eapply multistep_mid.
           ++ apply multi_if_cong. eassumption.
           ++ eauto with db.
        -- right. eapply multistep_mid.
           ++ eapply multi_if_cong. eassumption.
           ++ eauto with db.
      * destruct H0.
        -- eapply multistep_preserves_R'.
           ++ constructor.
              ** apply IHHty1. assumption.
              ** apply N_implies_typed. apply IHHty2. assumption.
              ** apply N_implies_typed. apply IHHty3. assumption.
           ++ apply H0.
           ++ apply IHHty2. assumption.
        -- eapply multistep_preserves_R'.
           ++ constructor.
              ** apply IHHty1. assumption.
              ** apply N_implies_typed. apply IHHty2. assumption.
              ** apply N_implies_typed. apply IHHty3. assumption.
           ++ apply H0.
           ++ apply IHHty3. assumption.
Qed.
