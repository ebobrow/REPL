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

Fixpoint interp_exp (n : nat) (e : exp) : exp :=
  match n with
    | O => e
    | S n' =>
        match e with
        | var => var
        | lam e' => lam (interp_exp n' e')
        | app e1 e2 => app (interp_exp n' e1) (interp_exp n' e2)
        | es e' s =>
            match interp_exp n' e', interp_sub n' s with
            (* a[id] -> a *)
            | a, id          => a
            (* 1[a . s] -> a *)
            | var, cons a _  => a
            (* (ab)[s] -> (a[s])(b[s]) *)
            | app a b, s'    => app (interp_exp n' (es a s')) (interp_exp n' (es b s'))
            (* (\1)[s] -> \1 *)
            | lam var, _     => lam var
            (* (\a)[s] -> \(a[1 . (s o shift)]) *)
            | lam a, s'      => lam (interp_exp n' (es a (cons var (comp s' shift))))

            (* in normal form, so it must be 1[shift^n] *)
            (* a[s][t] -> a[s o t] *)
            | es a s', t     => interp_exp n' (es a (comp s' t))
            | e, s           => es e s
            end
        end
  end
with interp_sub (n : nat) (s : sub) : sub :=
  match n with
    | O => s
    | S n' =>
        match s with
        | id => id
        | shift => shift
        | cons a s' => cons (interp_exp n' a) (interp_sub n' s')
        | comp s1 s2 =>
            match interp_sub n' s1, interp_sub n' s2 with
            (* id o s -> s *)
            | id, s'           => s'
            (* ↑ o id -> ↑ *)
            | s', id           => s'
            (* ↑ o (a ⋅ s) -> s *)
            | shift, cons a s' => s'
            (* (a ⋅ s) o t -> a[t] ⋅ (s o t) *)
            | cons a s', t     => cons (interp_exp n' (es a t)) (interp_sub n' (comp s' t))
            (* (s1 o s2) o s3 -> s1 o (s2 o s3) *)
            | comp s1 s2, s3   => interp_sub n' (comp s1 (comp s2 s3))
            | s1, s2           => comp s1 s2
            end
        end
  end.

Inductive reduce_exp :  exp -> exp -> Prop :=
  | var_refl : reduce_exp var var
  | step_var_id :
    (* 1[id] = 1 *)
    reduce_exp (es var id) var
  | step_var_cons (e : exp) (s : sub) :
    (*  1 [ a . s ]  = a  *)
    reduce_exp (es var (cons e s)) e
  | step_app (a b : exp) (s : sub) :
    (* (ab)[s] = (a[s])(b[s])  *)
    reduce_exp (es (app a b) s)  (app (es a s) (es b s))
  | step_abs (a : exp) (s : sub) :
    (* (\a)[s] = \(a[1 . s o shift]) *)
    reduce_exp (es (lam a) s) (lam (es a (cons var (comp s shift))))
  | step_clos (e : exp) (s1 s2 : sub) :
    reduce_exp (es (es e s1) s2) (es e (comp s1 s2))
  | reduce_subs (e1 e2 : exp) (s1 s2 : sub) (H1 : reduce_exp e1 e2) (H2 : reduce_sub s1 s2) :
    reduce_exp (es e1 s1) (es e2 s2)
  | reduce_lam (e1 e2 : exp) (H : reduce_exp e1 e2) :
    reduce_exp (lam e1) (lam e2)
  | reduce_app (e1 e2 e1' e2' : exp) (H1 : reduce_exp e1 e1') (H2 : reduce_exp e2 e2') :
    reduce_exp (app e1 e2) (app e1' e2')
with reduce_sub : sub -> sub -> Prop :=
  | id_refl : reduce_sub id id
  | shift_refl : reduce_sub shift shift
  | step_id_l (s : sub) :
    (* id o s = s *)
    reduce_sub (comp id s) s
  | step_shift_id :
    (* shift o id = shift *)
    reduce_sub (comp shift id) shift
  | step_shift_cons (a : exp) (s : sub) :
    (* shift o (a . s) = s *)
    reduce_sub (comp shift (cons a s)) s
  | step_map (a : exp) (s t : sub) :
    (* (a . s) o t = a[t] . (s o t) *)
    reduce_sub (comp (cons a s) t) (cons (es a t) (comp s t))
  | step_ass (s1 s2 s3 : sub) :
    (* (s1 o s2) o s3 = s1 o (s2 o s3) *)
    reduce_sub (comp (comp s1 s2) s3) (comp s1 (comp s2 s3))
  | step_cons (e1 e2 : exp) (s1 s2 : sub) (H1 : reduce_exp e1 e2) (H2 : reduce_sub s1 s2) :
    reduce_sub (cons e1 s1) (cons e2 s2)
  | step_comp (s1 s2 s1' s2' : sub) (H1 : reduce_sub s1 s1') (H2 : reduce_sub s2 s2') :
    reduce_sub (comp s1 s2) (comp s1' s2').

Scheme reduce_exp_ind' := Induction for reduce_exp Sort Prop
                               with reduce_sub_ind' := Induction for reduce_sub Sort Prop.

Combined Scheme reduce_ind from reduce_exp_ind', reduce_sub_ind'.

Lemma reduce_refl : (forall e, reduce_exp e e) /\ (forall s, reduce_sub s s).
Proof.
  apply exp_sub_ind; intros; try constructor; repeat assumption.
Qed.

Lemma reduce_exp_refl : forall e, reduce_exp e e.
Proof. apply reduce_refl. Qed.

Lemma reduce_sub_refl : forall s, reduce_sub s s.
Proof. apply reduce_refl. Qed.

Inductive reduce_exp_star : exp -> exp -> Prop :=
  | ert_refl x : reduce_exp_star x x
  | ert_step x y z
             (Hxy : reduce_exp_star x y)
             (Hyz : reduce_exp y z) :
    reduce_exp_star x z
with reduce_sub_star : sub -> sub -> Prop :=
  | srt_refl x : reduce_sub_star x x
  | srt_step x y z
             (Hxy : reduce_sub_star x y)
             (Hyz : reduce_sub y z) :
    reduce_sub_star x z.

Scheme reduce_exp_star_ind' := Induction for reduce_exp_star Sort Prop
                               with reduce_sub_star_ind' := Induction for reduce_sub_star Sort Prop.

Combined Scheme reduce_star_ind from reduce_exp_star_ind', reduce_sub_star_ind'.

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

Hint Constructors reduce_exp : db.
Hint Constructors reduce_sub : db.
Hint Resolve reduce_exp_refl : db.
Hint Resolve reduce_sub_refl : db.
Hint Constructors reduce_exp_star : db.
Hint Constructors reduce_sub_star : db.

Lemma estep_star_first : forall x y z,
    reduce_exp x y -> reduce_exp_star y z -> reduce_exp_star x z.
Proof. intros x y z Hxy Hyz. induction Hyz; eauto with db. Qed.
Hint Resolve estep_star_first : db.

Lemma estep_star_mid : forall x y z,
    reduce_exp_star x y -> reduce_exp_star y z -> reduce_exp_star x z.
Proof.
  intros x y z Hxy Hyz. induction Hxy.
  - assumption.
  - induction Hyz; eauto with db.
Qed.
Hint Resolve estep_star_mid : db.

Lemma sstep_star_first : forall x y z,
    reduce_sub x y -> reduce_sub_star y z -> reduce_sub_star x z.
Proof. intros x y z Hxy Hyz. induction Hyz; eauto with db. Qed.
Hint Resolve sstep_star_first : db.

Lemma sstep_star_mid : forall x y z,
    reduce_sub_star x y -> reduce_sub_star y z -> reduce_sub_star x z.
Proof.
  intros x y z Hxy Hyz. induction Hxy.
  - assumption.
  - induction Hyz; eauto with db.
Qed.
Hint Resolve sstep_star_mid : db.

Lemma lam_cong_star : forall e e',
    reduce_exp_star e e' ->
    reduce_exp_star (lam e) (lam e').
Proof. intros e e' He. induction He; eauto with db. Qed.
Hint Resolve lam_cong_star : db.

Lemma app_cong_star : forall a a' b b',
    reduce_exp_star a a' ->
    reduce_exp_star b b' ->
    reduce_exp_star (app a b) (app a' b').
Proof. intros e e' s s' He Hs. induction He; induction Hs; eauto with db. Qed.
Hint Resolve app_cong_star : db.

Lemma es_cong_star : forall e e' s s',
    reduce_exp_star e e' ->
    reduce_sub_star s s' ->
    reduce_exp_star (es e s) (es e' s').
Proof. intros e e' s s' He Hs. induction He; induction Hs; eauto with db. Qed.
Hint Resolve es_cong_star : db.

Lemma cons_cong_star : forall e e' s s',
    reduce_exp_star e e' ->
    reduce_sub_star s s' ->
    reduce_sub_star (cons e s) (cons e' s').
Proof. intros e e' s s' He Hs. induction He; induction Hs; eauto with db. Qed.
Hint Resolve cons_cong_star : db.

Lemma comp_cong_star : forall s s' t t',
    reduce_sub_star s s' ->
    reduce_sub_star t t' ->
    reduce_sub_star (comp s t) (comp s' t').
Proof. intros s s' t t' Hs Ht. induction Hs; induction Ht; eauto with db. Qed.
Hint Resolve comp_cong_star : db.

Fixpoint construct_n_shifts (n : nat) : sub :=
  match n with
    | O => shift
    | S n' => comp shift (construct_n_shifts n')
  end.

Fixpoint construct_binding_form_h (s : sub) (lvl : nat) (i : nat) : sub :=
  let e := match lvl-i with
          | O => var
          | S _ => es var (construct_n_shifts (pred (lvl-i)))
          end
  in match i with
       | O => cons e (comp s (construct_n_shifts lvl))
       | S i' => cons e (construct_binding_form_h s lvl i')
     end.

(* s results from repeated application of Abs: *)
(* 1 . (s o ↑) *)
(* 1 . (1[↑] . ... . (1[↑^n] . (s o ↑^n+1))) *)
Definition construct_binding_form (s : sub) (lvl : nat) : sub :=
  construct_binding_form_h s lvl lvl.

Compute construct_binding_form id 0.
Compute construct_binding_form id 2.

Lemma lam_helper : forall e i,
    reduce_exp_star (es e (construct_binding_form id i)) e.
Proof.
  induction e.
  - induction i.
    + unfold construct_binding_form. unfold construct_binding_form_h.
      eauto with db.
    + unfold construct_binding_form. unfold construct_binding_form_h.
      assert (S i - S i = 0) by lia. rewrite H. fold construct_binding_form_h.
      eauto with db.
  - induction i.
    + unfold construct_binding_form. unfold construct_binding_form_h.
      simpl. apply estep_star_mid with (y := lam (es e (construct_binding_form id 1))).
      { unfold construct_binding_form. unfold construct_binding_form_h.
        simpl.
        (* have to do this manually because it takes eauto too long :( *)
        apply estep_star_mid with (y := lam (es e (cons var (comp (cons var (comp id shift)) shift)))).
        { eauto with db. }
        apply estep_star_mid with (y := lam (es e (cons var (cons (es var shift) (comp (comp id shift) shift))))).
        { eauto with db. }
        apply ert_step with (y := (lam (es e (cons var (cons (es var shift) (comp id (comp shift shift))))))).
        { eauto 10 with db. }
        eauto with db.
      }
      auto with db.
    + unfold construct_binding_form. unfold construct_binding_form_h.
      assert (S i - S i = 0) by lia. rewrite H. fold construct_binding_form_h.
      admit.
  - eauto with db.
  - induction i.
    + unfold construct_binding_form. unfold construct_binding_form_h. simpl.
      induction s.
      *
        (* apply estep_star_mid with (y := es e (comp id (cons var (comp id shift)))). *)
        (* { eauto with db. } *)
        apply estep_star_mid with (y := es e (construct_binding_form id 0)).
        { eauto with db. }
        admit.
      * apply estep_star_mid with (y := es e (comp id shift)).
        { eauto with db. }
        eauto with db.
      * admit.
      * admit.
    + unfold construct_binding_form. unfold construct_binding_form_h.
      assert (S i - S i = 0) by lia. rewrite H. fold construct_binding_form_h.
      admit.
Admitted.

Lemma reduce_star_id : forall e,
    reduce_exp_star (es e id) e.
Proof.
  induction e; eauto with db.
  - (* lam *) apply estep_star_mid with (y := lam (es e (cons var (comp id shift)))).
    + eauto with db.
    + assert (es e (cons var (comp id shift)) = es e (construct_binding_form id 0)) by reflexivity.
      rewrite H. apply lam_cong_star.
      apply lam_helper.
  - (* es *) apply estep_star_mid with (y := es e (comp s id)).
    + eauto with db.
    + induction s; eauto with db.
      * admit.
      * apply estep_star_mid with (y := es e (comp s1 (comp s2 id))); eauto with db.
        apply es_cong_star; try constructor. admit.
  (* - (* es *) destruct step_star_first as [estep _]. *)
  (*   assert (reduce_exp (es (es e s) id) (es e (comp s id))) by constructor. *)
  (*   eapply estep in H. *)
  (*   + eauto with db. *)
  (*   + apply es_cong_star. *)
  (*     * constructor. *)
  (*     * admit. *)
Admitted.

Lemma interp_sound :
  (forall e i, reduce_exp_star e (interp_exp i e)) /\ (forall s i, reduce_sub_star s (interp_sub i s)).
Proof.
  apply exp_sub_ind; intros; destruct i; try constructor.
  - (* lam *) simpl. specialize H with i. induction H; eauto with db.
  - (* app *) simpl. specialize H with i. specialize H0 with i. apply app_cong_star; assumption.
  - (* es *) simpl. specialize H with i. specialize H0 with i.
    induction (interp_exp i e); induction (interp_sub i s); eauto with db.
    + (* es lam id *) apply estep_star_mid with (y := es (lam e0) id).
      * eauto with db.
      * destruct e0; apply reduce_star_id.
    + (* es lam shift *) generalize dependent e. induction e0.
      * eauto with db.
      * intros. admit.
      * admit.
      * admit.
    + (* es lam cons *) generalize dependent e. induction e0.
      * eauto with db.
      * admit.
      * admit.
      * admit.
    + (* es lam comp *) generalize dependent e. induction e0.
      * eauto with db.
      * admit.
      * admit.
      * admit.
    + (* es app id *) apply estep_star_mid with (y := es (app e0_1 e0_2) id); eauto with db.
      apply reduce_star_id.
    + (* es app shift *) admit.
    + (* es app cons *) admit.
    + (* es app comp *) admit.
    + (* es es id *) apply estep_star_mid with (y := es (es e0 s0) id); eauto with db.
      apply reduce_star_id.
    + (* es es shift *) admit.
    + (* es es cons *) admit.
    + (* es es comp *) admit.
  - (* cons *) simpl. specialize H with i. specialize H0 with i. apply cons_cong_star; assumption.
  - (* comp *) admit.
