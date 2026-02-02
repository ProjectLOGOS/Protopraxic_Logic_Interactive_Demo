(*
  Omega_Closure.v

  Goal: replace omega_operator_arith axiom with a definitional closure
  over nat-indexed iteration (bounded omega, constructive).

  This gives a provable "stabilization operator" without transfinite axioms.
*)

From Stdlib Require Import Arith.

Section Omega.
  Variable State : Type.
  Variable step : State -> State.

  Fixpoint iter (n : nat) (s : State) : State :=
    match n with
    | 0 => s
    | S k => step (iter k s)
    end.

  (* omega-closure as a property: existence of an n where state stabilizes *)
  Definition stabilizes (s : State) : Prop :=
    exists n, iter (S n) s = iter n s.
End Omega.
