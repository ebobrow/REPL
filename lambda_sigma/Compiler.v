Require Import Coq.Logic.FunctionalExtensionality.

Module Meta.

Inductive exp : Type :=
    | var : nat -> exp
    | lam : exp -> exp
    | app : exp -> exp -> exp.

Definition renaming := nat -> nat.
Definition sub      := nat -> exp.

Definition ids : sub := fun x => var x.
Definition cons { A : Type } : A -> (nat -> A) -> (nat -> A) :=
  fun s f => fun x => match x with
                    | O => s
                    | S x' => f x'
                  end.

Fixpoint apply_renaming (e : exp) (r : renaming) : exp :=
  match e with
    | var x => var (r x)
    | app e1 e2 => app (apply_renaming e1 r) (apply_renaming e2 r)
    | lam e1 => lam (apply_renaming e1 (cons 0 (fun x => S (r x))))
  end.

Definition id : sub := fun x => var x.
(* Definition cons : exp → sub → sub := …. *)
(* Definition cons : sub -> sub -> sub := *)
(*   fun s1 s2 => fun x => match x with *)
(*                     | O => s1 x *)
(*                     | S x' => s2 x' *)
(*                   end. *)
(* Definition shift : sub := fun x => var (S x). *)

Fixpoint apply_subst (e : exp) (s : sub) : exp :=
  match e with
    | var x => s x
    | app e1 e2 => app (apply_subst e1 s) (apply_subst e2 s)
    | lam e1 => lam (apply_subst e1 (cons (var 0) (fun x => apply_renaming (s x) (fun x => S x))))
end.

Compute (apply_subst (var 0) (fun x => var (S x))).
Compute (apply_subst (app (var 1) (var 0)) (cons (var 42) ids)).

Inductive reduction :  exp -> exp -> Prop :=
   | beta_red (e1 e2 : exp) : reduction (app (lam e1) e2) (apply_subst e1 (cons e2 id))
   | app_cong : forall e1 e1' e2 e2',
       reduction e1 e1'  -> reduction e2 e2' -> reduction (app e1 e2) (app e1' e2')
   | lam_cong (e1 e2 : exp) : reduction e1 e2 -> reduction (lam e1) (lam e2)
   | refl (e : exp) : reduction e e
   (* | symmetric (e1 ) *)
.

Lemma renaming_subst_equiv:
  forall e r s, (forall n, var (r n) = s n) ->
  apply_renaming e r = apply_subst e s.
Proof.
  induction e.
  - intros r s H. apply H.
  - simpl. intros r s H. f_equal.
    assert (H1 : forall n, var ((fun x : nat => match x with
                                      | 0 => 0
                                      | S x' => S (r x')
                                      end) n) =
           (fun x : nat => match x with
                        | 0 => var 0
                        | S x' => apply_renaming (s x') (fun x0 : nat => S x0)
                       end) n).
    { induction n.
      * reflexivity.
      * rewrite <- H. reflexivity. }
    apply IHe in H1. apply H1.
  - intros r s H. simpl. f_equal.
    + apply IHe1 in H. apply H.
    + apply IHe2 in H. apply H.
Qed.

Lemma renaming_comp e : forall r1 r2,
    (apply_renaming (apply_renaming e r1) r2) = (apply_renaming e (fun x => r2 (r1 x))).
Proof. induction e.
       - reflexivity.
       - intros. simpl. unfold cons. f_equal.
         assert (H : (fun x : nat => match x with
                                | 0 => 0
                                | S x' => S (r2 (r1 x'))
                                end) =
                       (fun x => (fun x : nat => match x with
                                         | 0 => 0
                                         | S x' => S (r2 x')
                                         end) ((fun x : nat => match x with
                                                          | 0 => 0
                                                          | S x' => S (r1 x')
                                                          end) x))).
         { apply functional_extensionality. destruct x; reflexivity. }
         rewrite H. apply IHe.
       - intros. simpl. f_equal. apply IHe1. apply IHe2.
Qed.

Lemma rename_then_sub e : forall r s,
    (apply_subst (apply_renaming e r) s) = (apply_subst e (fun x => s (r x))).
Proof. induction e.
       - reflexivity.
       - intros. simpl. f_equal. unfold cons.
         assert (H : (fun x : nat => match x with
                                | 0 => var 0
                                | S x' => apply_renaming (s (r x')) (fun x0 : nat => S x0)
                                end) =
                       (fun x => (fun x : nat => match x with
                                         | 0 => var 0
                                         | S x' => apply_renaming (s x') (fun x0 : nat => S x0)
                                         end) ( (fun x : nat => match x with
                                                           | 0 => 0
                                                           | S x' => S (r x')
                                                           end) x))).
         { apply functional_extensionality. destruct x; reflexivity. }
         rewrite H. apply IHe.
       - intros. simpl. f_equal. apply IHe1. apply IHe2.
Qed.

Lemma sub_then_rename e : forall r s,
    (apply_renaming (apply_subst e s) r) = (apply_subst e (fun x => apply_renaming (s x) r)).
  Proof. induction e.
         - reflexivity.
         - intros r s. simpl. f_equal. unfold cons.
           assert (H : (fun x : nat => match x with
                    | 0 => var 0
                    | S x' => apply_renaming (apply_renaming (s x') r) (fun x0 : nat => S x0)
                    end) =
                  (fun x => apply_renaming ((fun x : nat => match x with
                                   | 0 => var 0
                                   | S x' => apply_renaming (s x') (fun x0 : nat => S x0)
                                   end) x) (fun x : nat => match x with
                                                         | 0 => 0
                                                         | S x' => S (r x')
                                                         end))).
           { apply functional_extensionality. destruct x.
           - reflexivity.
           - rewrite renaming_comp. rewrite renaming_comp. reflexivity. }
           rewrite H. apply IHe.
         - intros. simpl. f_equal. apply IHe1. apply IHe2.
Qed.

Lemma subst_comp e : forall s t,
    (apply_subst (apply_subst e s) t) = (apply_subst e (fun x =>
apply_subst (s x) t)).
  Proof.
    induction e.
    - reflexivity.
    - intros s t. simpl. f_equal. unfold cons.
      assert (H : (fun x : nat => match x with
                             | 0 => var 0
                             | S x' => apply_renaming (apply_subst (s x') t) (fun x0 : nat => S x0)
                             end) =
                    (fun x : nat => apply_subst ((fun x : nat => match x with
                                                       | 0 => var 0
                                                       | S x' => apply_renaming (s x') (fun x0 : nat => S x0)
                                                       end) x) (fun x : nat => match x with
                                                                          | 0 => var 0
                                                                          | S x' => apply_renaming (t x') (fun x0 : nat => S x0)
                                                                          end))).
      { apply functional_extensionality. destruct x.
      - reflexivity.
      - rewrite sub_then_rename. rewrite rename_then_sub. reflexivity. }
      rewrite H. apply IHe.
    - intros. simpl. f_equal. apply IHe1. apply IHe2.
Qed.

(* Lemma raise_rename_eq : forall r e, *)
(*     equal (apply_renaming e r) (apply_subst e (fun x => var (r x))). *)
(* Proof. intros r e. induction e. *)
(*        - apply refl. *)
(*        - Admitted. *)


Example beta_r : forall e : exp,
    (* (λ x. y x) e  =   y e *)
    reduction (app (lam (app (var 1) (var 0))) e) (app (var 0) e).
Proof. apply beta_red. Qed.

End Meta.

(* Object-version (λ σ-calculus) *)

Module Object.

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

(* "λ x. x"              (lam var)  *)
(* "λ x . λ y. x"       (lam (lam (es (var)↑))) *)

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
            | var, id        => var                                                     (* 1[id] -> 1 *)
            | var, cons a s' => a                                                       (* 1[a . s] -> a *)
            | app a b, s'    => app (interp_exp n' (es a s')) (interp_exp n' (es b s')) (* (ab)[s] -> (a[s])(b[s]) *)
            | lam var, s'    => lam var
            | lam a, s'      => lam (interp_exp n' (es a (cons var (comp s' shift))))   (* (\a)[s] -> \(a[1 . (s o shift)]) *)
            (* in normal form, so it must be 1[shift^n] *)
            | es a s', t     => interp_exp n' (es a (comp s' t))                        (* a[s][t] -> a[s o t] *)
            | var, shift     => es var shift
            | var, comp s1 s2 => es var (comp shift (comp s1 s2)) (* comp must be shift^n *)
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
            | id, s'           => s'                                        (* id o s -> s *)
            | shift, id        => shift                                     (* ↑ o id -> ↑ *)
            | shift, cons a s' => s'                                        (* ↑ o (a ⋅ s) -> s *)
            | cons a s', t     => cons (interp_exp n' (es a t)) (interp_sub n' (comp s' t)) (* (a ⋅ s) o t -> a[t] ⋅ (s o t) *)
            | comp s1 s2, s3   => interp_sub n' (comp s1 (comp s2 s3))      (* (s1 o s2) o s3 -> s1 o (s2 o s3) *)
            | s1, s2           => comp s1 s2
            end
        end
  end.

Inductive exp' : Type :=
    | var' : exp'
    | lam' : exp' -> exp'
    | app' : exp' -> exp' -> exp'
    | es'  : exp' -> sub' -> exp'       (*  e [ s ] *)
with sub' : Type :=
   | id'    : sub'
   | shift' : nat -> sub'           (* shift^n+1 *)
   | cons'  : exp' -> sub' -> sub'
   | comp'  : sub' -> sub' -> sub'.     (* s1 ○ s2 *)

(* Fixpoint interp_exp' (fuel : nat) (e : exp') : exp' := *)
(*   match fuel with *)
(*     | O => e *)
(*     | S fuel' => *)
(*         match e with *)
(*         | var' => var' *)
(*         | lam' e' => lam' (interp_exp' fuel' e') *)
(*         | app' a b => app' (interp_exp' fuel' a) (interp_exp' fuel' b) *)
(*         | es' a s => match interp_exp' fuel' a, interp_sub' fuel' s with *)
(*                       | var', shift' n => es' var' (shift' n) *)
(*                       | e', id' => e' (* e[id] => e *) *)
(*                       | var', cons' a' s' => a' (* 1[a . s] => a *) *)
(*                       | app' a' b', s' => app' (interp_exp' fuel' (es' a' s')) (interp_exp' fuel' (es' b' s')) (* (ab)[s] => (a[s])(b[s]) *) *)
(*                       | lam' var', s' => lam' var' (* (\1)[s] => \1 *) (* note--more efficient to not step s *) *)
(*                       | lam' a', s' => lam' (interp_exp' fuel' (es' a' (cons' var' (comp' s' (shift' 1))))) *)
(*                       | es' var' (shift' n), shift' m => es' var' (shift' (n + m)) *)
(*                       | es' var' (shift' 0), cons' a' s' => es' var' s' *)
(*                       | es' var' (shift' (S n')), cons' a' s' => (interp_exp' fuel' (es' var' (comp' (shift' n') s'))) *)
(*                       | es' var' s', t' => es' var' (interp_sub' fuel' (comp' s' t')) *)

(*                       (* unreachable (not in normal form) *) *)
(*                       | var', comp' _ _ => var' *)
(*                       | es' (lam' _) _, _ => var' *)
(*                       | es' (app' _ _) _, _ => var' *)
(*                       | es' (es' _ _) _, _ => var' *)
(*                     end *)
(*         end *)
(*   end *)
(* with interp_sub' (fuel : nat) (s : sub') : sub' := *)
(*   match fuel with *)
(*     | O => s *)
(*     | S fuel' => *)
(*         match s with *)
(*         | id' => id' *)
(*         | shift' n => shift' n *)
(*         | cons' a s' => cons' (interp_exp' fuel' a) (interp_sub' fuel' s') *)
(*         | comp' s1 s2 => match interp_sub' fuel' s1, interp_sub' fuel' s2 with *)
(*                           | id', s => s *)
(*                           | s, id' => s *)
(*                           | shift' n, shift' m => shift' (S (n + m)) *)
(*                           | shift' 0, cons' a t => t *)
(*                           | shift' (S n'), cons' a t => interp_sub' fuel' (comp' (shift' n') t) *)
(*                           | cons' a s, t => cons' (interp_exp' fuel' (es' a t)) (interp_sub' fuel' (comp' s t)) *)
(*                           (* | comp' s1' s2', s3' => interp_sub' fuel' (comp' s1' (comp' s2' s3')) *) *)

(*                           (* unreachable (not in normal form) *) *)
(*                           | comp' _ _, _ => id' *)
(*                           | _, comp' _ _ => id' *)
(*                         end *)
(*         end *)
(*   end. *)

Fixpoint interp_exp' (e : exp') : exp' :=
  match e with
  | var' => var'
  | lam' e' => lam' (interp_exp' e')
  | app' a b => app' (interp_exp' a) (interp_exp' b)
  | es' a s => match interp_exp' fuel' a, interp_sub' fuel' s with
              | var', shift' n => es' var' (shift' n)
              | e', id' => e' (* e[id] => e *)
              | var', cons' a' s' => a' (* 1[a . s] => a *)
              | app' a' b', s' => app' (interp_exp' fuel' (es' a' s')) (interp_exp' fuel' (es' b' s')) (* (ab)[s] => (a[s])(b[s]) *)
              | lam' var', s' => lam' var' (* (\1)[s] => \1 *) (* note--more efficient to not step s *)
              | lam' a', s' => lam' (interp_exp' fuel' (es' a' (cons' var' (comp' s' (shift' 1)))))
              | es' var' (shift' n), shift' m => es' var' (shift' (n + m))
              | es' var' (shift' 0), cons' a' s' => es' var' s'
              | es' var' (shift' (S n')), cons' a' s' => (interp_exp' fuel' (es' var' (comp' (shift' n') s')))
              | es' var' s', t' => es' var' (interp_sub' fuel' (comp' s' t'))

              (* unreachable (not in normal form) *)
              | var', comp' _ _ => var'
              | es' (lam' _) _, _ => var'
              | es' (app' _ _) _, _ => var'
              | es' (es' _ _) _, _ => var'
              end
  end
with interp_es' (e : exp') (s : sub') : exp' :=
  match e, s with
  | var', shift' n => es' var' (shift' n)
  | e', id' => e' (* e[id] => e *)
  | var', cons' a' s' => a' (* 1[a . s] => a *)
  | app' a' b', s' => app' (interp_es' a' s') (interp_es' b' s') (* (ab)[s] => (a[s])(b[s]) *)
  | lam' var', s' => lam' var' (* (\1)[s] => \1 *) (* note--more efficient to not step s *)
  | lam' a', s' => lam' (interp_exp' fuel' (es' a' (cons' var' (comp' s' (shift' 1)))))
  | es' var' (shift' n), shift' m => es' var' (shift' (n + m))
  | es' var' (shift' 0), cons' a' s' => es' var' s'
  | es' var' (shift' (S n')), cons' a' s' => (interp_exp' fuel' (es' var' (comp' (shift' n') s')))
  | es' var' s', t' => es' var' (interp_sub' fuel' (comp' s' t'))

  (* unreachable (not in normal form) *)
  | var', comp' _ _ => var'
  | es' (lam' _) _, _ => var'
  | es' (app' _ _) _, _ => var'
  | es' (es' _ _) _, _ => var'
  end
with interp_sub' (fuel : nat) (s : sub') : sub' :=
  match fuel with
    | O => s
    | S fuel' =>
        match s with
        | id' => id'
        | shift' n => shift' n
        | cons' a s' => cons' (interp_exp' fuel' a) (interp_sub' fuel' s')
        | comp' s1 s2 => match interp_sub' fuel' s1, interp_sub' fuel' s2 with
                          | id', s => s
                          | s, id' => s
                          | shift' n, shift' m => shift' (S (n + m))
                          | shift' 0, cons' a t => t
                          | shift' (S n'), cons' a t => interp_sub' fuel' (comp' (shift' n') t)
                          | cons' a s, t => cons' (interp_exp' fuel' (es' a t)) (interp_sub' fuel' (comp' s t))
                          (* | comp' s1' s2', s3' => interp_sub' fuel' (comp' s1' (comp' s2' s3')) *)

                          (* unreachable (not in normal form) *)
                          | comp' _ _, _ => id'
                          | _, comp' _ _ => id'
                        end
        end
  end.

Fixpoint fuel_exp' (e : exp') : nat :=
  match e with
    | var' => 0
    | lam' e' => S (fuel_exp' e')
    | app' a b => S (Nat.max (fuel_exp' a) (fuel_exp' b))
    | es' a s => fuel_es' a s
  end
with fuel_es' (e : exp') (s : sub') : nat :=
  match e, s with
    | _, id' => 1
    | var', shift' _ => 0
    | lam' var', _ => 1
    | app' a b, s' => S (Nat.max (fuel_es' a s') (fuel_es' b s'))
    | lam' e', s' => 1000
    | es' var' (shift' n), shift' m => 1
    | es' var' (shift' 0), cons' e' s' => 1
    | es' var' (shift' (S n)), cons' e' s' => 1000 (* fuel_es' var' (comp' (shift' n) s') *)
    | es' var' s', t' => 1000 (* fuel_sub' (comp' s' t') *)

    | var', cons' e' s' => 1000 (* S (Nat.max (fuel_exp' e') (fuel_sub' s')) *)
    | var', comp' s1 s2 => 1000 (* S (Nat.max (fuel_sub' s1) (fuel_sub' s2)) *)
    | es' (lam' e') s', t' => 1000
    | es' (app' a b) s', t' => 1000
    | es' (es' e' e1) s2, s3 => 1000
  end
with fuel_sub' (s : sub') : nat :=
  match s with
    | id' | shift' _ => 0
    | cons' a s' => S (Nat.max (fuel_exp' a) (fuel_sub' s'))
    | comp' s1 s2 => S (Nat.max (fuel_sub' s1) (fuel_sub' s2))
  end.

Compute fuel_exp' (es' (app' (lam' var') var') id').
Compute interp_exp' 1 (es' (app' (lam' var') var') id').

Compute fuel_exp' (es' (lam' (es' var' (shift' 0))) (shift' 0)).
Compute interp_exp' 4 (es' (lam' (es' var' (shift' 0))) (shift' 0)).
Compute interp_exp' 5 (es' (lam' (es' var' (comp' (shift' 0) (shift' 0)))) (shift' 0)).

Fixpoint normal_exp' (e : exp') : bool :=
  match e with
    | var' => true
    | app' a b => andb (normal_exp' a) (normal_exp' b)
    | lam' a => normal_exp' a
    | es' var' s => normal_sub' s
    | es' a s => false
  end
with normal_sub' (s : sub') : bool :=
  match s with
    | id' | shift' _ => true
    | cons' a s' => andb (normal_exp' a) (normal_sub' s')
    | _ => false
  end.

Fixpoint only_shifts (s : sub) : bool :=
  match s with
    | shift => true
    | comp shift s => only_shifts s
    | _ => false
  end.

Fixpoint normal_exp (e : exp) : bool :=
  match e with
    | var => true
    | app a b => andb (normal_exp a) (normal_exp b)
    | lam a => normal_exp a
    | es var s => normal_sub s
    | es a s => false
  end
with normal_sub (s : sub) : bool :=
  match s with
    | id | shift => true
    | comp shift s' => only_shifts s'
    | cons a s' => andb (normal_exp a) (normal_sub s')
    | _ => false
  end.

Fixpoint naive_height_exp (e : exp) : nat :=
  match e with
    | var => 0
    | lam e' => 1 + naive_height_exp e'
    | app a b => 1 + (Nat.max (naive_height_exp a) (naive_height_exp b))
    | es e' s => 1 + (Nat.max (naive_height_exp e') (naive_height_sub s))
  end
with naive_height_sub (s : sub) : nat :=
  match s with
    | id | shift => 0
    | cons a s' => 1 + (Nat.max (naive_height_exp a) (naive_height_sub s'))
    | comp s1 s2 => 1 + (Nat.max (naive_height_sub s1) (naive_height_sub s2))
  end.

Compute naive_height_exp (es (app (lam var) var) id). (* = 3 *)
Compute interp_exp 3 (es (app (lam var) var) id).

Compute naive_height_exp (es (lam (es var shift)) shift). (* = 3 *)
Compute naive_height_exp (lam (es (es var shift) (cons var (comp shift shift)))). (* = 4 *)
Compute naive_height_exp (lam (es var (comp shift (cons var (comp shift shift))))). (* = 5 *)
Compute naive_height_exp (lam (es var (comp shift shift))). (* = 3 *)
Compute interp_exp 4 (es (lam (es var shift)) shift).

Compute naive_height_exp (es (lam (es var (comp shift shift))) shift). (* = 4 *)
Compute interp_exp 100 (es (lam (es var (comp shift shift))) shift).

Fixpoint fuel_es (e : exp) (s : sub) : nat :=
  match e, s with
    | var, id => 1
    | var, cons (a s) =>

Fixpoint fuel_exp (e : exp) : nat :=
  if normal_exp e then 0 else
    match e with
    | var => 0
    | es var shift => 0
    (* | es var (comp s1 s2) => S (fuel_sub (comp s1 s2)) *)
    | lam e' => S (fuel_exp e')
    | app a b => S (max (fuel_exp a) (fuel_exp b))
    | es var id => 1
    | es var (cons a s) => S (fuel_exp a)
    | es (app a b) s => 100 (* S (max (fuel_exp (es a s)) (fuel_exp (es b s))) *)
    | es (lam a) s => 100
    | es (es a s) t => 100
    | es var s => S (fuel_sub s)
    end
with fuel_sub (s : sub) : nat :=
  if normal_sub s then 0 else
    match s with
      | id | shift | comp shift shift => 0
      | comp id s' => S (fuel_sub s')
      | comp shift id => 1
      | comp shift (cons a s') => S (fuel_sub s')
      | comp (cons a s') t => 100
      | comp (comp s1 s2) s3 => 100
      | comp shift (comp s1 s2) => 100 (* S (fuel_sub (comp s1 s2)) *)
      | cons a s' => S (max (fuel_exp a) (fuel_sub s'))
    end.

Compute fuel_exp (es (app (lam var) var) id).

Inductive reduce_exp :  exp -> exp -> Prop :=
  | var_refl : reduce_exp var var
  (* | step_beta (a1 b1 a2 b2 : exp) (H1 : reduce_exp a1 a2) (H2 : reduce_exp b1 b2) : *)
  (*   (* (\a)b = a[b . id] *) *)
  (*   reduce_exp (app (lam a1) b1)   (es a2 (cons b2 id)) *)
  | step_var_id :
    (* 1[id] = 1 *)
    reduce_exp (es var id) var
  | step_var_cons (e : exp) (s1 s2 : sub) (H1 : reduce_sub s1 (cons e s2)) :
    (*  1 [ a . s ]  = a  *)
    reduce_exp (es var s1) e
  | step_app (a1 b1 a2 b2 : exp) (s1 s2 : sub)
      (H1 : reduce_exp a1 a2) (H2 : reduce_exp b1 b2) (H3 : reduce_sub s1 s2) :
    (* (ab)[s] = (a[s])(b[s])  *)
    reduce_exp (es (app a1 b1) s1)  (app (es a2 s2) (es b2 s2))
  | step_abs (a1 a2 : exp) (s1 s2 : sub)
      (H1 : reduce_exp a1 a2) (H2 : reduce_sub s1 s2) :
    (* (\a)[s] = \(a[1 . s o shift]) *)
    reduce_exp (es (lam a1) s1) (lam (es a2 (cons var (comp s2 shift))))
  (* | step_clos (a1 a2 : exp) (s1 t1 s2 t2 : sub) *)
  (*     (H1 : reduce_exp a1 a2) (H2 : reduce_sub s1 s2) (H3 : reduce_sub t1 t2) : *)
  (*   (* a[s][t] = a[s o t] *) *)
    (* reduce_exp (es (es a1 s1) t1) (es a2 (comp s2 t2)) *)
  | step_clos (s1 s2 t1 t2 : sub)
               (H2 : reduce_sub s1 s2) (H3 : reduce_sub t1 t2) :
    reduce_exp (es (es var s1) t2) (es var (comp s2 t2))
  | reduce_subs (e1 e2 : exp) (s1 s2 : sub) (H1 : reduce_exp e1 e2) (H2 : reduce_sub s1 s2) :
    reduce_exp (es e1 s1) (es e2 s2)
  | reduce_lam (e1 e2 : exp) (H : reduce_exp e1 e2) :
    reduce_exp (lam e1) (lam e2)
  | reduce_app (e1 e2 e1' e2' : exp) (H1 : reduce_exp e1 e1') (H2 : reduce_exp e2 e2') :
    reduce_exp (app e1 e2) (app e1' e2')
with reduce_sub : sub -> sub -> Prop :=
  | id_refl : reduce_sub id id
  | shift_refl : reduce_sub shift shift
  | step_id_l (s1 s2 : sub) (H1 : reduce_sub s1 s2) :
    (* id o s = s *)
    reduce_sub (comp id s1) s2
  | step_shift_id :
    (* shift o id = shift *)
    reduce_sub (comp shift id) shift
  | step_shift_cons (a : exp) (s1 s2 : sub) (H1 : reduce_sub s1 s2) :
    (* shift o (a . s) = s *)
    reduce_sub (comp shift (cons a s1)) s2
  | step_map (a1 a2 : exp) (s1 t1 s2 t2 : sub)
      (H1 : reduce_exp a1 a2) (H2 : reduce_sub s1 s2) (H3 : reduce_sub t1 t2) :
    (* (a . s) o t = a[t] . (s o t) *)
    reduce_sub (comp (cons a1 s1) t1) (cons (es a2 t2) (comp s2 t2))
  | step_ass (s1 s2 s3 s1' s2' s3' : sub)
      (H1 : reduce_sub s1 s1') (H2 : reduce_sub s2 s2') (H3 : reduce_sub s3 s3') :
    (* (s1 o s2) o s3 = s1 o (s2 o s3) *)
    reduce_sub (comp (comp s1 s2) s3) (comp s1' (comp s2' s3'))

  | step_cons (e1 e2 : exp) (s1 s2 : sub) (H1 : reduce_exp e1 e2) (H2 : reduce_sub s1 s2) :
    reduce_sub (cons e1 s1) (cons e2 s2)
  | step_comp (s1 s2 s1' s2' : sub) (H1 : reduce_sub s1 s1') (H2 : reduce_sub s2 s2') :
    reduce_sub (comp s1 s2) (comp s1' s2')
.

Scheme reduce_exp_ind' := Induction for reduce_exp Sort Prop
                               with reduce_sub_ind' := Induction for reduce_sub Sort Prop.

Combined Scheme reduce_ind from reduce_exp_ind', reduce_sub_ind'.

Scheme exp_ind' := Induction for exp Sort Prop
                             with sub_ind' := Induction for sub Sort Prop.
Combined Scheme exp_sub_ind from exp_ind', sub_ind'.

Lemma reduce_refl : (forall e, reduce_exp e e) /\ (forall s, reduce_sub s s).
Proof.
  apply exp_sub_ind; intros; try constructor; repeat assumption.
Qed.

Inductive reduce_exp_star : exp -> exp -> Prop :=
  | ert_refl x : reduce_exp_star x x
  | ert_step x y (H : reduce_exp x y) : reduce_exp_star x y
  | ert_trans x y z
        (Hxy : reduce_exp_star x y)
        (Hyz : reduce_exp_star y z) :
        reduce_exp_star x z
with reduce_sub_star : sub -> sub -> Prop :=
  | srt_refl x : reduce_sub_star x x
  | srt_step x y (H : reduce_sub x y) : reduce_sub_star x y
  | srt_trans x y z
        (Hxy : reduce_sub_star x y)
        (Hyz : reduce_sub_star y z) :
        reduce_sub_star x z.

Scheme reduce_exp_star_ind' := Induction for reduce_exp_star Sort Prop
                               with reduce_sub_star_ind' := Induction for reduce_sub_star Sort Prop.

Combined Scheme reduce_star_ind from reduce_exp_star_ind', reduce_sub_star_ind'.

End Object.

Fixpoint compile (e : Object.exp) : Meta.exp :=
  match e with
    | Object.var => Meta.var 0
    | Object.lam e1 => Meta.lam (compile e1)
    | Object.app e1 e2 => Meta.app (compile e1) (compile e2)
    | Object.es e1 s => Meta.apply_subst (compile e1) (compile_subst s)
  end
  with compile_subst (s : Object.sub) : Meta.sub :=
         match s with
           | Object.id => Meta.ids
           | Object.shift => fun x => Meta.var (S x)
           | Object.cons s f => Meta.cons (compile s) (compile_subst f)
           | Object.comp f g => fun e => Meta.apply_subst ((compile_subst f) e) (compile_subst g)
          end.

Lemma preserves_equality : forall e1 e2,
    Object.reduce_exp e1 e2 -> Meta.reduction (compile e1) (compile e2).
Proof. intros e1 e2 H. destruct H.
       (* - apply Meta.refl. *)
       (* - apply Meta.beta_red. *)
       (* - apply Meta.refl. *)
       (* - apply Meta.refl. *)
       (* - apply Meta.refl. *)
       (* - simpl. apply Meta.lam_cong. unfold Meta.cons. *)
       (*   assert (H1 : (fun x : nat => match x with *)
       (*                            | 0 => Meta.var 0 *)
       (*                            | S x' => Meta.apply_renaming (compile_subst s x') (fun x0 : nat => S x0) *)
       (*                            end) = *)
       (*          (fun x : nat => match x with *)
       (*                      | 0 => Meta.var 0 *)
       (*                      | S x' => Meta.apply_subst (compile_subst s x') (fun x0 : nat => Meta.var (S x0)) *)
       (*                      end)). *)
       (*   { apply functional_extensionality. induction x. *)
       (*     - reflexivity. *)
       (*     - apply Meta.renaming_subst_equiv. reflexivity.} *)
       (*   rewrite H1. apply Meta.refl. *)
       (* - simpl. generalize dependent s. generalize dependent t. induction a. *)
       (*   + intros. apply Meta.refl. *)
       (*   + intros. simpl. apply Meta.lam_cong. unfold Meta.cons. rewrite Meta.subst_comp. *)
       (*     assert (H: (fun x : nat => *)
       (*                   Meta.apply_subst *)
       (*                     match x with *)
       (*                     | 0 => Meta.var 0 *)
       (*                     | S x' => Meta.apply_renaming (compile_subst s x') (fun x0 : nat => S x0) *)
       (*                     end *)
       (*                     (fun x0 : nat => *)
       (*                        match x0 with *)
       (*                        | 0 => Meta.var 0 *)
       (*                        | S x' => Meta.apply_renaming (compile_subst t x') (fun x1 : nat => S x1) *)
       (*                        end)) =  (fun x : nat => *)
       (*                                    match x with *)
       (*                                    | 0 => Meta.var 0 *)
       (*                                    | S x' => Meta.apply_renaming (Meta.apply_subst (compile_subst s x') (compile_subst t)) (fun x0 : nat => S x0) *)
       (*                                    end)). *)
       (*     { apply functional_extensionality. destruct x. *)
       (*     - reflexivity. *)
       (*     - rewrite Meta.sub_then_rename. rewrite Meta.rename_then_sub. reflexivity. } *)
       (*     rewrite H. apply Meta.refl. *)
       (*   + intros. simpl. apply Meta.app_cong. apply IHa1. apply IHa2. *)
       (*   + intros. simpl. rewrite Meta.subst_comp. apply Meta.refl. *)
           Admitted.

(* Theorem confluence : (forall e1 e2 : Object.exp, *)
(*     Object.reduce_exp e1 e2 -> forall e3, Object.reduce_exp e1 e3 -> *)
(*     exists e4, Object.reduce_exp e2 e4 /\ Object.reduce_exp e3 e4) /\ *)
(*                        (forall s1 s2 : Object.sub, *)
(*                        Object.reduce_sub s1 s2 -> forall s3, Object.reduce_sub s1 s3 -> *)
(*                        exists s4, Object.reduce_sub s2 s4 /\ Object.reduce_sub s3 s4). *)
(* Proof. apply Object.reduce_ind. *)
(*        - (* var -> var *) intros. inversion H. exists Object.var. split; constructor. *)
(*        - (* 1[id] -> 1 *) intros. inversion H; try (exists Object.var; split; constructor). *)
(*          inversion H0. inversion H4. subst. inversion H0. subst. exists Object.var; split; constructor. *)
(*        - (* 1 [a . s] -> a *) intros. inversion H0. *)
(*          + subst. inversion H1. *)
(*          + subst. inversion H0. *)
(*            * subst. inversion H3. *)
(*            * subst. apply H in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx1. inversion Hx2. subst. inversion H11. subst. *)
(*              exists e2. split; assumption. *)
(*            * subst. inversion H5. subst. admit. *)
(*          + admit. *)
(*        - (* (ab)[s] -> (a[s])(b[s]) *) intros. inversion H5. *)
(*          + subst. apply H in H9. apply H0 in H11. apply H4 in H12. *)
(*            destruct H9 as [a [Ha1 Ha2]]. destruct H11 as [b [Hb1 Hb2]]. destruct H12 as [s [Hs1 Hs2]]. *)
(*            exists (Object.app (Object.es a s) (Object.es b s)). split; repeat constructor; assumption. *)
(*          + subst. inversion H5. subst. inversion H8. subst. *)
(*            apply H in H9. apply H0 in H14. apply H4 in H13. *)
(*            destruct H9 as [a [Ha1 Ha2]]. destruct H14 as [b [Hb1 Hb2]]. destruct H13 as [s [Hs1 Hs2]]. *)
(*            exists (Object.app (Object.es a s) (Object.es b s)). split; repeat constructor; assumption. *)
(*        - (* (\a)[s] -> \(a[a . s o shift]) *) intros. inversion H3. *)
(*          + subst. apply H in H6. apply H0 in H8. destruct H6 as [a [Ha1 Ha2]]. destruct H8 as [s [Hs1 Hs2]]. *)
(*            exists (Object.lam (Object.es a (Object.cons Object.var (Object.comp s Object.shift)))). *)
(*            split; repeat constructor; assumption. *)
(*          + subst. inversion H6. subst. apply H in H5. apply H0 in H8. *)
(*            destruct H5 as [a [Ha1 Ha2]]. destruct H8 as [s [Hs1 Hs2]]. *)
(*            exists (Object.lam (Object.es a (Object.cons Object.var (Object.comp s Object.shift)))). *)
(*            split; repeat constructor; assumption. *)
(*        - (* 1[s][t] -> 1[s o t] *) intros s1 s2 t1 t2 IRs IHs IRt IHt e IHe. inversion IHe. *)
(*          * subst. apply IHs in H3. destruct H3 as [s' [Hs1 Hs2]]. *)
(*            exists (Object.es Object.var (Object.comp s' t2)). split; repeat constructor; try assumption; try apply Object.reduce_refl. *)
(*          * subst. inversion H3. *)
(*            -- subst. inversion IRs. subst. *)
(*               exists (Object.es Object.var s3). split; repeat constructor. assumption. apply Object.reduce_refl. *)
(*            -- subst. inversion IRs. subst. assert (Object.reduce_sub (Object.cons a1 s) (Object.cons e2 s)). *)
(*               { constructor. assumption. apply Object.reduce_refl. } *)
(*               apply IHs in H. destruct H as [x [Hx1 Hx2]]. inversion Hx1. inversion Hx2. subst. inversion H12. subst. *)
(*               exists (Object.es e3 s3). split. *)
(*               ++ (* need stronger assumption *) admit. *)
(*               ++ constructor. assumption. apply Object.reduce_refl. *)
(*            -- subst. inversion H5. subst. apply IHs in H6. destruct H6 as [s' [Hs1 Hs2]]. *)
(*               exists (Object.es Object.var (Object.comp s' s3)). split. *)
(*               ++ repeat constructor; assumption. *)
(*               ++ apply Object.step_clos with (t1 := s3). assumption. apply Object.reduce_refl. *)
(*        - (* e1 -> e2, s1 -> s2 |- e1[s1] -> e2[s2] *) intros. inversion H3. *)
(*          + subst. inversion H1. inversion H2. subst. exists Object.var. split; constructor. *)
(*          + subst. inversion H1. inversion H2. subst. *)
(*            assert (Object.reduce_sub (Object.cons a1 s) (Object.cons e3 s0)). { repeat constructor; assumption. } *)
(*            apply H0 in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx1. inversion Hx2. subst. inversion H15. subst. *)
(*            exists e2. split; try constructor; assumption. *)
(*          + subst. inversion H1. subst. apply H0 in H9. destruct H9 as [s [Hs1 Hs2]]. *)
(*            assert (Object.reduce_exp (Object.app a1 b1) (Object.app a2 b2)). { constructor; assumption. } *)
(*            apply H in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx1. inversion Hx2. subst. inversion H16. subst. *)
(*            exists (Object.app (Object.es e1'0 s) (Object.es e2'0 s)). split; repeat constructor; assumption. *)
(*          + subst. inversion H1. subst. *)
(*            assert (Object.reduce_exp (Object.lam a1) (Object.lam a2)). { constructor; assumption. } *)
(*            apply H in H4. destruct H4 as [e [He1 He2]]. inversion He1. inversion He2. subst. inversion H12. subst. *)
(*            apply H0 in H8. destruct H8 as [s [Hs1 Hs2]]. *)
(*            exists (Object.lam (Object.es e2 (Object.cons Object.var (Object.comp s Object.shift)))). *)
(*            split; repeat constructor; assumption. *)
(*          + subst. inversion H1. *)
(*            * subst. inversion H6. subst. *)
(*              exists (Object.es Object.var s2). split; repeat constructor; try apply Object.reduce_refl. assumption. *)
(*            * subst. inversion H6. subst. *)
(*              assert (Object.reduce_exp (Object.es Object.var (Object.cons a1 s)) e0). { constructor; assumption. } *)
(*              apply H in H4. destruct H4 as [e [He1 He2]]. *)
(*              exists (Object.es e s2). split. *)
(*                -- constructor. assumption. apply Object.reduce_refl. *)
(*                -- (* stronger assumption *) admit. *)
(*            * subst. inversion H7. subst. *)
(*              assert (Object.reduce_exp (Object.es Object.var s0) (Object.es Object.var s3)). { constructor; assumption. } *)
(*              apply H in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx2. *)
(*              -- subst. inversion H6. *)
(*                 ++ subst. inversion H10. subst. exists (Object.es Object.var s2). split; repeat constructor. apply Object.reduce_refl. *)
(*                    assumption. *)
(*                 ++ subst. inversion H4; exists (Object.es Object.var s2); split; repeat constructor; try assumption; *)
(*                           apply Object.reduce_refl. *)
(*                 ++ subst. exists (Object.es Object.var s2). split; repeat constructor; try assumption; apply Object.reduce_refl. *)
(*              -- subst. (* more general rule *) admit. *)
(*              -- subst. inversion H9. subst. exists (Object.es Object.var (Object.comp s6 s2)). split. *)
(*                 ** (* more general? *) admit. *)
(*                 ** repeat constructor; assumption. *)
(*          + subst. apply H in H6. destruct H6 as [e [He1 He2]]. apply H0 in H8. destruct H8 as [s [Hs1 Hs2]]. *)
(*            exists (Object.es e s). split; constructor; assumption. *)
(*        - (* e1 -> e2 |- \e1 -> \e2 *) intros. inversion H1. subst. apply H0 in H3. destruct H3 as [e [He1 He2]]. *)
(*          exists (Object.lam e). split; constructor; assumption. *)
(*        - (* e1 -> e1', e2 -> e2' |- e1 e2 -> e1' e2' *) intros. inversion H3. subst. *)
(*          apply H in H6. apply H0 in H8. destruct H6 as [a [Ha1 Ha2]]. destruct H8 as [b [Hb1 Hb2]]. *)
(*          exists (Object.app a b). split; constructor; assumption. *)
(*        - (* id -> id *) intros. inversion H. exists Object.id. split; constructor. *)
(*        - (* split -> split *) intros. inversion H. exists Object.shift. split; constructor. *)
(*        - (* id o s -> s *) intros. inversion H0. *)
(*          + subst. apply H in H3. destruct H3 as [s [Hs1 Hs2]]. exists s. split; assumption. *)
(*          + subst. inversion H4. subst. apply H in H6. destruct H6 as [s [Hs1 Hs2]]. *)
(*            exists s. split; try constructor; assumption. *)
(*        - (* shift o id -> shift *) intros. inversion H. *)
(*          + subst. exists Object.shift. split; constructor. *)
(*          + subst. inversion H0. inversion H4. subst. exists Object.shift. split; constructor. *)
(*        - (* shift o (a . s) -> s *) intros. inversion H0. *)
(*          + subst. apply H in H5. destruct H5. exists x. assumption. *)
(*          + subst. inversion H4. inversion H6. subst. apply H in H9. destruct H9 as [s [Hs1 Hs2]]. *)
(*            exists s. split; try constructor; assumption. *)
(*        - (* (a . s) o t -> a[t] . (s o t) *) intros. inversion H5. *)
(*          + subst. apply H in H9. apply H0 in H11. apply H4 in H12. *)
(*            destruct H9 as [a [Ha1 Ha2]]. destruct H11 as [s [Hs1 Hs2]]. destruct H12 as [t [Ht1 Ht2]]. *)
(*            exists (Object.cons (Object.es a t) (Object.comp s t)). split; repeat constructor; assumption. *)
(*          + subst. inversion H8. subst. *)
(*            apply H in H9. apply H0 in H12. apply H4 in H10. *)
(*            destruct H9 as [a [Ha1 Ha2]]. destruct H12 as [s [Hs1 Hs2]]. destruct H10 as [t [Ht1 Ht2]]. *)
(*            exists (Object.cons (Object.es a t) (Object.comp s t)). split; repeat constructor; assumption. *)
(*        - (* (s1 o s2) o s3 -> s1 o (s2 o s3) *) intros. inversion H5. *)
(*          + subst. apply H in H9. apply H0 in H11. apply H4 in H12. *)
(*            destruct H9 as [a [Ha1 Ha2]]. destruct H11 as [b [Hb1 Hb2]]. destruct H12 as [c [Hc1 Hc2]]. *)
(*            exists (Object.comp a (Object.comp b c)). split; repeat constructor; assumption. *)
(*          + subst. inversion H8. *)
(*            * subst. inversion H1. subst. apply H0 in H11. apply H4 in H10. *)
(*              destruct H11 as [t1 [Ht1 Ht1']]. destruct H10 as [t2 [Ht2 Ht2']]. *)
(*              exists (Object.comp t1 t2). split; repeat constructor; assumption. *)
(*            * subst. inversion H1. inversion H5. *)
(*              -- subst. apply H4 in H16. destruct H16 as [s [Hs1 Hs2]]. inversion H2. inversion H15. subst. *)
(*                 exists (Object.comp Object.shift s). split; repeat constructor; assumption. *)
(*              -- subst. inversion H2. subst. apply H4 in H14. destruct H14 as [s [Hs1 Hs2]]. *)
(*                 exists (Object.comp Object.shift s). split; repeat constructor; assumption. *)
(*            * subst. inversion H1. subst. inversion H2. subst. (* stronger assumption *) admit. *)
(*            * subst. inversion H1. subst. apply H0 in H13. apply H4 in H10. *)
(*              apply H in H1. destruct H1 as [x [Hx1 Hx2]]. inversion Hx1. subst. *)
(*              destruct H13 as [s [Hs1 Hs2]]. destruct H10 as [t [Ht1 Ht2]]. *)
(*              assert (Object.reduce_sub (Object.cons a1 s0) (Object.cons a2 s4)). { constructor; assumption. } *)
(*              apply H in H1. destruct H1 as [y [Hy1 Hy2]]. inversion Hy1. inversion Hy2. subst. inversion H20. subst. *)
(*              exists (Object.cons (Object.es e3 (Object.comp s t)) (Object.comp s7 (Object.comp s t))). split. *)
(*              -- repeat constructor; assumption. *)
(*              -- (* stronger assumption *) admit. *)
(*            * subst. inversion H1. *)
(*              -- subst. inversion H9. subst. apply H0 in H13. destruct H13 as [s [Hs1 Hs2]]. *)
(*                 apply H4 in H10. destruct H10 as [t [Ht1 Ht2]]. *)
(*                 assert (Object.reduce_sub (Object.comp Object.id s4) s2'1). { constructor. assumption. } *)
(*                 apply H in H6. destruct H6 as [x [Hx1 Hx2]]. *)
(*                 exists (Object.comp x (Object.comp s t)). split. *)
(*                 ++ repeat constructor; assumption. *)
(*                 ++ (* stronger assumption? *) admit. *)
(*              -- subst. inversion H9. inversion H11. subst. apply H0 in H13. destruct H13 as [s [Hs1 Hs2]]. *)
(*                 apply H4 in H10. destruct H10 as [t [Ht1 Ht2]]. *)
(*                 exists (Object.comp Object.shift (Object.comp s t)). split; repeat constructor; assumption. *)
(*              -- subst. inversion H11. inversion H9. subst. apply H0 in H13. destruct H13 as [s [Hs1 Hs2]]. *)
(*                 apply H4 in H10. destruct H10 as [t [Ht1 Ht2]]. *)
(*                 assert (Object.reduce_sub (Object.comp Object.shift (Object.cons a s1)) s4). { constructor; assumption. } *)
(*                 apply H in H6. destruct H6 as [x [Hx1 Hx2]]. *)
(*                 exists (Object.comp x (Object.comp s t)). split. *)
(*                 ++ repeat constructor; assumption. *)
(*                 ++ (* stronger assumption *) admit. *)
(*              -- subst. inversion H9. subst. admit. *)
(*              -- admit. *)
(*              -- admit. *)
(*            * subst. apply H in H9. apply H0 in H12. apply H4 in H10. *)
(*              destruct H9 as [a [Ha1 Ha2]]. destruct H12 as [b [Hb1 Hb2]]. destruct H10 as [c [Hc1 Hc2]]. *)
(*              exists (Object.comp a (Object.comp b c)). split; repeat constructor; assumption. *)
(*        - (* e1 -> e2, s1 -> s2 |- e1 . s1 -> e2 . s2 *) intros. inversion H3. subst. *)
(*          apply H in H6. apply H0 in H8. destruct H6 as [e [He1 He2]]. destruct H8 as [s [Hs1 Hs2]]. *)
(*          exists (Object.cons e s). split; repeat constructor; assumption. *)
(*        - (* s1 -> s1', s2 -> s2' |- s1 o s2 -> s1' o s2' *) intros. inversion H3. *)
(*          + subst. inversion H1. subst. apply H0 in H7. destruct H7 as [s [Hs1 Hs2]]. *)
(*            exists s. split; repeat constructor; assumption. *)
(*          + subst. inversion H1. inversion H2. subst. exists Object.shift. split; constructor. *)
(*          + subst. inversion H1. subst. inversion H2. subst. *)
(*            assert (Object.reduce_sub (Object.cons a s0) (Object.cons a s3)). *)
(*            { constructor. apply Object.reduce_refl. assumption. } *)
(*            apply H0 in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx1. inversion Hx2. subst. inversion H15. subst. *)
(*            exists s4. split; repeat constructor; assumption. *)
(*          + subst. inversion H1. subst. apply H0 in H9. destruct H9 as [s [Hs1 Hs2]]. *)
(*            assert (Object.reduce_sub (Object.cons a1 s0) (Object.cons a2 s4)). { constructor; assumption. } *)
(*            apply H in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx1. inversion Hx2. subst. inversion H16. subst. *)
(*            exists (Object.cons (Object.es e0 s) (Object.comp s5 s)). split; repeat constructor; assumption. *)
(*          + subst. inversion H1. *)
(*            * subst. inversion H6. subst. *)
(*              assert (Object.reduce_sub (Object.comp Object.id s4) (Object.comp Object.id s2'0)). { constructor; assumption. } *)
(*              apply H in H4. destruct H4 as [s [Hs1 Hs2]]. inversion Hs2. *)
(*              -- subst. apply H0 in H9. destruct H9 as [t [Ht1 Ht2]]. *)
(*                 exists (Object.comp s t). split; repeat constructor; assumption. *)
(*              -- subst. apply H0 in H9. destruct H9 as [t [Ht1 Ht2]]. inversion H8. subst. *)
(*                 exists (Object.comp s2'1 t). split; repeat constructor; try assumption. *)
(*                 (* needs stronger assumption *) admit. *)
(*            * subst. inversion H6. inversion H7. subst. apply H0 in H9. destruct H9 as [s [Hs1 Hs2]]. *)
(*              exists (Object.comp Object.shift s). split; repeat constructor; assumption. *)
(*            * subst. inversion H6. inversion H7. subst. apply H0 in H9. destruct H9 as [s [Hs1 Hs2]]. *)
(*              assert (Object.reduce_sub (Object.comp Object.shift (Object.cons a s1)) s3). { constructor. assumption. } *)
(*              apply H in H4. destruct H4 as [t [Ht1 Ht2]]. *)
(*              exists (Object.comp t s). split. *)
(*              -- constructor; assumption. *)
(*              -- (* needs stronger assumption *) admit. *)
(*                (* assert (Object.reduce_sub (Object.comp (Object.cons e2 s3) s3') *) *)
(*                (*                            (Object.cons (Object.es e2 s3') (Object.comp s3 s3'))). *) *)
(*                (*  { constructor; apply Object.reduce_refl. } *) *)
(*                 (* assert (Object.reduce_sub (Object.comp Object.shift (Object.comp (Object.cons e2 s3) s3')) *) *)
(*                 (*           (Object.comp Object.shift (Object.cons (Object.es e2 s3') (Object.comp s3 s3')))). *) *)
(*                 (* { repeat constructor; apply Object.reduce_refl. } *) *)
(*                 (* assert (Object.reduce_sub (Object.comp Object.shift (Object.comp (Object.cons e2 s3) s3')) *) *)
(*                 (*           (Object.comp s3 s3')). admit. admit. *) *)
(*            * subst. inversion H6. subst. admit. (* looks familiar but I can't remember from where *) *)
(*            * subst. admit. (* inversion H6.*) *)
(*              (* -- subst. inversion H8. subst. apply H0 in H9. destruct H9 as [s [Hs1 Hs2]]. *) *)
(*              (*    assert (Object.reduce_sub (Object.comp (Object.comp Object.id s3) s4) (Object.comp s1'0 s2'0)). *) *)
(*              (*    { repeat constructor; assumption. } *) *)
(*              (*    apply H in H4. destruct H4 as [x [Hx1 Hx2]]. inversion Hx2; subst. *) *)
(*              (*    ++ exists (Object.comp x s). split. *) *)
(*              (*       ** constructor; assumption. *) *)
(*              (*       ** repeat constructor; assumption. *) *)
(*              (*    ++  *) *)
(*            * subst. assert (Object.reduce_sub (Object.comp s0 s4) (Object.comp s1'0 s2'0)). { constructor; assumption. } *)
(*              apply H in H4. destruct H4 as [x [Hx1 Hx2]]. apply H0 in H9. destruct H9 as [s [Hs1 Hs2]]. *)
(*              admit. *)
(*          + subst. apply H in H6. destruct H6 as [s [Hs1 Hs2]]. apply H0 in H8. destruct H8 as [t [Ht1 Ht2]]. *)
(*            exists (Object.comp s t). split; constructor; assumption. *)
(*            Admitted. *)

(* Theorem local_confluence : *)
(*   (forall e1 e2 : Object.exp, Object.reduce_exp e1 e2 -> forall e3, Object.reduce_exp e1 e3 -> *)
(*                     exists e4, Object.reduce_exp_star e2 e4 /\ Object.reduce_exp_star e3 e4) /\ *)
(*   (forall s1 s2 : Object.sub, Object.reduce_sub s1 s2 -> forall s3, Object.reduce_sub s1 s3 -> *)
(*                     exists s4, Object.reduce_sub_star s2 s4 /\ Object.reduce_sub_star s3 s4). *)
(* Proof. apply Object.reduce_ind. *)
(*        - (* beta reduction *) intros. inversion H. *)
(*          exists (Object.es a (Object.cons b Object.id)). split; repeat constructor. *)
(*        - (* 1[id] = 1 *) intros. inversion H. *)
(*          + exists e3. split; subst; constructor. *)
(*          + subst. inversion H0. *)
(*        - (*  1 [ a . s ]  = a  *) intros. inversion H. *)
(*          + exists e3. split; constructor. *)
(*          + inversion H0. *)
(*        - (* (ab)[s] = (a[s])(b[s])  *) intros. inversion H. *)
(*          + exists e3. subst. split; constructor. *)
(*          + subst. inversion H0. subst. exists (Object.es a0 (Object.cons (Object.es b s2) s2)). split. *)
(*            * admit. *)
(*            * apply Object.ert_trans with (y := Object.es a0 (Object.comp (Object.cons b Object.id) s2)). *)
(*              -- repeat constructor. *)
(*              --  *)
(*        - (* (\a)[s] = \(a[1 . s o shift]) *) intros. inversion H. *)
(*          + exists e3. subst. split; constructor. *)
(*          + subst. inversion H0. *)
(*        - (* a[s][t] = a[s o t] *) intros. inversion H. *)
(*          + subst. exists (Object.es a (Object.comp s t)). split; constructor. *)
(*          + subst. admit. *)
(*        - intros. admit. *)
(*        - (* id o s = s *) intros. inversion H. exists s3. split; constructor. *)
(*        - (* shift o id = shift *) intros. inversion H. exists s3. subst. split; constructor. *)
(*        - (* shift o (a . s) = s *) intros. inversion H. exists s3. split; constructor. *)
(*        - (* (a . s) o t = a[t] . (s o t) *) intros. inversion H. exists s3. subst. split; constructor. *)
(*        - (* (s1 o s2) o s3 = s1 o (s2 o s3) *) intros. inversion H. exists s0. subst. split; constructor. *)
(*        - intros. inversion H3. subst. apply H0 in H8. apply H in H6. destruct H6 as [e [E1 E2]]. destruct H8 as [s [S1 S2]]. *)
(*          exists (Object.cons e s). split. *)
(*          * admit. *)
