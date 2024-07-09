From Coq Require Import Lia.

Inductive exp : Type :=
    | var : exp
    | lam : exp -> exp
    | app : exp -> exp -> exp
    | es  : exp -> sub -> exp       (*  e [ s ] *)
with sub : Type :=
   | id : sub
   | shift : sub
   | cons : exp -> sub -> sub
   | comp : sub -> sub -> sub.     (* s1 ○ s2 *)

Scheme exp_ind' := Induction for exp Sort Prop
                             with sub_ind' := Induction for sub Sort Prop.
Combined Scheme exp_sub_ind from exp_ind', sub_ind'.

Notation "'LET' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint interp_exp (n : nat) (e : exp) : option exp :=
  match n with
    | O => None
    | S n' =>
        match e with
        | var => Some var
        | lam e' => LET x <== interp_exp n' e' IN Some (lam x)
        | app e1 e2 => LET x1 <== interp_exp n' e1 IN
                       LET x2 <== interp_exp n' e2 IN Some (app x1 x2)
        | es e' s => LET e'' <== interp_exp n' e' IN
                     LET s' <== interp_sub n' s IN
            match e'', s' with
            | a, id          => Some a                                                       (* a[id] -> a *)
            | var, cons a _  => Some a                                                       (* 1[a . s] -> a *)
            | app a b, s'    => LET x1 <== interp_exp n' (es a s') IN
                                LET x2 <== interp_exp n' (es b s')
                                IN Some (app x1 x2) (* (ab)[s] -> (a[s])(b[s]) *)
            | lam var, _     => Some (lam var)                                                 (* (\1)[s] -> \1 *)
            | lam a, s'      => LET x <== interp_exp n' (es a (cons var (comp s' shift))) IN
                                   Some (lam x) (* (\a)[s] -> \(a[1 . (s o shift)]) *)
            (* in normal form, so it must be 1[shift^n] *)
            | es a s', t     => interp_exp n' (es a (comp s' t))                        (* a[s][t] -> a[s o t] *)
            | var, shift     => Some (es var shift)
            | var, comp s1 s2 => Some (es var (comp shift (comp s1 s2))) (* comp must be shift^n *)
            end
        end
  end
with interp_sub (n : nat) (s : sub) : option sub :=
  match n with
    | O => None
    | S n' =>
        match s with
        | id => Some id
        | shift => Some shift
        | cons a s' => LET x1 <== interp_exp n' a IN
                       LET x2 <== interp_sub n' s' IN Some (cons x1 x2)
        | comp s1 s2 => LET s1' <== interp_sub n' s1 IN
                        LET s2' <== interp_sub n' s2 IN
            match s1', s2' with
            | id, s'           => Some s'                                        (* id o s -> s *)
            | s', id           => Some s'                                     (* ↑ o id -> ↑ *)
            | shift, cons a s' => Some s'                                        (* ↑ o (a ⋅ s) -> s *)
            | cons a s', t     => LET x1 <== interp_exp n' (es a t) IN
                                  LET x2 <== interp_sub n' (comp s' t) IN
                                  Some (cons x1 x2) (* (a ⋅ s) o t -> a[t] ⋅ (s o t) *)
            | comp s1 s2, s3   => interp_sub n' (comp s1 (comp s2 s3))      (* (s1 o s2) o s3 -> s1 o (s2 o s3) *)
            | s1, s2           => Some (comp s1 s2)
            end
        end
  end.

Definition is_some { A : Type } (o : option A) : Prop :=
  match o with
    | Some _ => True
    | None => False
  end.

Inductive is_some' {A : Type} : option A -> Prop :=
  | some_is_some (a : A) : is_some' (Some a).

Lemma step_more : forall e i1 i2,
    i2 >= i1 ->
    exists e', interp_exp i1 e = Some e' ->
    interp_exp i2 e = Some e'.
Proof.
  induction i1.
  - intros i2 Hge. eexists. intros Heval.
    simpl in Heval. discriminate.
  - intros i2 Hge. destruct i2. inversion Hge.
    assert (i1 <= i2) by lia.
    destruct e.
    + (* var *)
      simpl. exists var. reflexivity.
    + (* lam *)
      apply IHi1 in H. destruct H as [e' He'].
      exists e'. simpl.
      Admitted.

Lemma step_more' : forall e i1 i2,
    i2 >= i1 ->
    is_some' (interp_exp i1 e) ->
    is_some' (interp_exp i2 e).
Proof.
  induction i1; intros i2 Hge Heval.
  - simpl in Heval. inversion Heval.
  - destruct i2. inversion Hge.
    assert (i2 >= i1) by lia.
    destruct e.
    + (* var *)
      simpl. constructor.
    + (* lam *)
      apply IHi1 in H.
      * simpl. simpl in Heval. inversion Heval.
        Admitted.

Theorem termination :
  (forall e, exists i, is_some' (interp_exp i e)) /\ (forall s, exists i, is_some' (interp_sub i s)).
Proof.
  apply exp_sub_ind.
  - (* var *)
    exists 1. simpl. constructor.
  - (* lam *)
    intros e IHe.
    destruct IHe as [i H]. exists (S i).
    inversion H. simpl. rewrite <- H1. constructor.
  - (* app *)
    intros e1 IHe1 e2 IHe2.
    destruct IHe1 as [i1 Hi1]. destruct IHe2 as [i2 Hi2].
    exists (S (i1 + i2)). apply step_more' with (i2 := i1 + i2) in Hi1.
    apply step_more' with (i2 := i1 + i2) in Hi2.
    inversion Hi1. inversion Hi2. simpl. rewrite <- H0. rewrite <- H1. constructor.
    lia. lia.
  - (* es *)
    intros e IHe s IHs. destruct IHe as [i_e IHe]. inversion IHe.
    destruct IHs as [i_s IHs]. inversion IHs.
    induction a.
    + (* var *) exists (S (i_e + i_s)). simpl. symmetry in H0.
      assert (i_e + i_s >= i_e) by lia.
      apply step_more with (e := e) in H. Admitted.
      (* eapply H in H0. *)
      (* apply step_more with (i2 := i_e + i_s) in H0. *)

Fixpoint interp_exp' (n : nat) (e : exp) : exp :=
  match n with
    | O => e
    | S n' =>
        match e with
        | var => var
        | lam e' => lam (interp_exp' n' e')
        | app e1 e2 => app (interp_exp' n' e1) (interp_exp' n' e2)
        | es e' s =>
            match interp_exp' n' e', interp_sub' n' s with
            (* a[id] -> a *)
            | a, id          => a
            (* 1[a . s] -> a *)
            | var, cons a _  => a
            (* (ab)[s] -> (a[s])(b[s]) *)
            | app a b, s'    => app (interp_exp' n' (es a s')) (interp_exp' n' (es b s'))
            (* (\1)[s] -> \1 *)
            | lam var, _     => lam var
            (* (\a)[s] -> \(a[1 . (s o shift)]) *)
            | lam a, s'      => lam (interp_exp' n' (es a (cons var (comp s' shift))))

            (* in normal form, so it must be 1[shift^n] *)
            (* a[s][t] -> a[s o t] *)
            | es a s', t     => interp_exp' n' (es a (comp s' t))
            | e, s           => es e s
            (* (* 1[shift] *) *)
            (* | var, shift     => es var shift *)
            (* (* 1[shift o (shift...)] *) *)
            (* | var, comp s1 s2 => es var (comp shift (comp s1 s2)) (* comp must be shift^n *) *)
            end
        end
  end
with interp_sub' (n : nat) (s : sub) : sub :=
  match n with
    | O => s
    | S n' =>
        match s with
        | id => id
        | shift => shift
        | cons a s' => cons (interp_exp' n' a) (interp_sub' n' s')
        | comp s1 s2 =>
            match interp_sub' n' s1, interp_sub' n' s2 with
            (* id o s -> s *)
            | id, s'           => s'
            (* ↑ o id -> ↑ *)
            | s', id           => s'
            (* ↑ o (a ⋅ s) -> s *)
            | shift, cons a s' => s'
            (* (a ⋅ s) o t -> a[t] ⋅ (s o t) *)
            | cons a s', t     => cons (interp_exp' n' (es a t)) (interp_sub' n' (comp s' t))
            (* (s1 o s2) o s3 -> s1 o (s2 o s3) *)
            | comp s1 s2, s3   => interp_sub' n' (comp s1 (comp s2 s3))
            | s1, s2           => comp s1 s2
            end
        end
  end.

Inductive only_shifts : sub -> Prop :=
  | shift_only_shifts : only_shifts shift
  | comp_only_shifts (s : sub) (H : only_shifts s) : only_shifts (comp shift s).

Inductive norm_exp : exp -> Prop :=
  | norm_var : norm_exp var
  | norm_lam (e : exp) (H : norm_exp e) : norm_exp (lam e)
  | norm_app (e1 e2 : exp) (H1 : norm_exp e1) (H2 : norm_exp e2) : norm_exp (app e1 e2)
  | norm_shift_var (s : sub) (H : only_shifts s) : norm_exp (es var s).

Inductive norm_sub : sub -> Prop :=
  | norm_shifts (s : sub) (H : only_shifts s) : norm_sub s
  | norm_id : norm_sub id
  | norm_cons (a : exp) (s : sub) (H1 : norm_exp a) (H2 : norm_sub s) : norm_sub (cons a s).

Lemma more :
  (forall e i1 i2, i1 <= i2 -> norm_exp (interp_exp' i1 e) -> norm_exp (interp_exp' i2 e))
    /\ (forall s i1 i2, i1 <= i2 -> norm_sub (interp_sub' i1 s) -> norm_sub (interp_sub' i2 s)).
Proof.
  apply exp_sub_ind.
  Admitted.

Lemma more' :
  (forall e i1 i2, i1 <= i2 -> norm_exp (interp_exp' i1 e) -> interp_exp' i1 e = interp_exp' i2 e)
    /\ (forall s i1 i2, i1 <= i2 -> norm_sub (interp_sub' i1 s) -> interp_sub' i1 s = interp_sub' i2 s).
Proof.
  apply exp_sub_ind.
  - (* var *) intros. destruct i1; destruct i2; reflexivity.
  - (* lam *) intros e IH i1 i2 Hge Hnorm.
    apply IH in Hge. destruct i1.
    + destruct i2.
      * reflexivity.
      * simpl.
        Admitted.

Theorem termination' :
  (forall e, exists i, norm_exp (interp_exp' i e)) /\ (forall s, exists i, norm_sub (interp_sub' i s)).
Proof.
  apply exp_sub_ind.
  - (* var *)
    exists 1. constructor.
  - (* lam *)
    intros e [i IHe]. exists (S i). simpl. apply norm_lam. assumption.
  - (* app *)
    intros e1 [i1 IHe1] e2 [i2 IHe2]. exists (S (i1 + i2)). simpl.
    destruct more as [moree _]. apply moree with (i2 := i1 + i2) in IHe1.
    apply moree with (i2 := i1 + i2) in IHe2. apply norm_app; assumption.
    lia. lia.
  - (* es *)
    intros e [i_e IHe] s [i_s IHs].
    (* inversion IHs. *)
    (* + induction (interp_exp' i_e e) eqn:E. *)
    (*   * exists (S (i_e + i_s)). *)
    (*     assert (norm_exp (interp_exp' i_e e)). { rewrite E. constructor. } *)
    (*     destruct more' as [moree mores]. apply moree with (i2 := i_e + i_s) in H1. *)
    (*     rewrite E in H1. simpl. rewrite <- H1. inversion H. *)
    induction (interp_sub' i_s s) eqn:Es.
    + exists (S (i_e + i_s)). simpl. destruct (interp_exp' i_e e) eqn:Ee;
      assert (norm_exp (interp_exp' i_e e)). { rewrite Ee. constructor. }
      * destruct more' as [moree mores]. apply moree with (i2 := i_e + i_s) in H.
        rewrite Ee in H. rewrite <- H.
        assert (norm_sub (interp_sub' i_s s)). { rewrite Es. apply norm_id. }
        apply mores with (i2 := i_e + i_s) in H0. rewrite Es in H0. rewrite <- H0. constructor.
        lia. lia.
      * rewrite Ee. assumption.
      * destruct more' as [moree mores]. apply moree with (i2 := i_e + i_s) in H.
        rewrite Ee in H. rewrite <- H.
        assert (norm_sub (interp_sub' i_s s)). { rewrite Es. apply norm_id. }
        apply mores with (i2 := i_e + i_s) in H0. rewrite Es in H0. rewrite <- H0.
        destruct e0; assumption. lia. lia.
      * rewrite Ee. assumption.
      * destruct more' as [moree mores]. apply moree with (i2 := i_e + i_s) in H.
        rewrite Ee in H. rewrite <- H.
        assert (norm_sub (interp_sub' i_s s)). { rewrite Es. apply norm_id. }
        apply mores with (i2 := i_e + i_s) in H0. rewrite Es in H0. rewrite <- H0. constructor.
        inversion IHe. assumption. inversion IHe. assumption. lia. lia.
      * rewrite Ee. assumption.
      * destruct more' as [moree mores]. apply moree with (i2 := i_e + i_s) in H.
        rewrite Ee in H. rewrite <- H.
        assert (norm_sub (interp_sub' i_s s)). { rewrite Es. apply norm_id. }
        apply mores with (i2 := i_e + i_s) in H0. rewrite Es in H0. rewrite <- H0. assumption.
        lia. lia.
    + destruct (interp_exp' i_e e) eqn:Ee.
      * destruct more' as [moree mores].
        rewrite <- Ee in IHe. apply moree with (i2 := i_e + i_s) in IHe.
        rewrite <- Es in IHs. apply mores with (i2 := i_e + i_s) in IHs.
        exists (S (i_e + i_s)). simpl. rewrite Ee in IHe. rewrite <- IHe.
        rewrite Es in IHs. rewrite <- IHs. constructor. constructor. lia. lia.
      * inversion IHe. induction e0; subst.
        -- exists (S (i_e + i_s)). destruct more' as [moree mores].
           assert (norm_exp (interp_exp' i_e e)). { rewrite Ee. assumption. }
           apply moree with (i2 := i_e + i_s) in H. rewrite Ee in H.
           assert (norm_sub (interp_sub' i_s s)). { rewrite Es. assumption. }
           apply mores with (i2 := i_e + i_s) in H1. rewrite Es in H1.
           simpl. rewrite <- H. rewrite <- H1. repeat constructor. lia. lia.
        -- admit.
        -- eexists. destruct more' as [moree mores].
           assert (norm_exp (interp_exp' i_e e)). { rewrite Ee. assumption. }
           apply moree with (i2 := ?i) in H.
           assert (norm_sub (interp_sub' i_s s)). { rewrite Es. assumption. }
           apply mores with (i2 := ?i) in H1.
