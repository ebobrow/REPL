Inductive ren : Type :=
  | id : ren
  | shift : ren
  | cons : nat -> ren -> ren
  | comp : ren -> ren -> ren.

Inductive exp : Type :=
  | var : nat -> exp
  | lam : exp -> exp
  | app : exp -> exp -> exp
  | er  : exp -> ren -> exp.

Fixpoint interp_ren (r : ren) : ren :=
  match r with
    | id => id
    | shift => shift
    | cons n r => cons n (interp_ren r)
    | comp r1 r2 => match interp_ren r1, interp_ren r2 with
                     | id, r2' => r2'
                     | r1', id => r1'
                     | shift, cons n r => r
                     | cons n r1, r2 =>

Fixpoint interp_exp (e : exp) : exp :=
  match e with
    | var n => var n
    | lam e' => lam (interp_exp e')
    | app e1 e2 => app (interp_exp e1) (interp_exp e2)
    | er e r => match interp_exp e, interp_ren r with
                 | e, id => e
                 | var n, shift => var (S n)
                 | var 0, cons n _ => var n
