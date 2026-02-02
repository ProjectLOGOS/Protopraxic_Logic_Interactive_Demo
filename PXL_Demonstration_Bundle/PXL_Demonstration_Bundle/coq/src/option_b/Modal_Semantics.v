(*
  Modal_Semantics.v

  Kripke semantics for the restricted modal syntax.
  We keep R abstract; for S5 work we will later require it to be an equivalence.
*)

From PXL Require Import PXLv3_SemanticModal.
From PXL.option_b Require Import Modal_Syntax.

Section Semantics.
  Variable W : Type.
  Variable R : W -> W -> Prop.

  (* Valuation: which atoms are true at a world *)
  Variable V : nat -> W -> Prop.

  Fixpoint holds (w : W) (phi : MForm) : Prop :=
    match phi with
    | Atom n   => V n w
    | Bot      => False
    | And a b  => holds w a /\ holds w b
    | Or a b   => holds w a \/ holds w b
    | Imp a b  => holds w a -> holds w b
    | Not a    => ~ holds w a
    | Box a    => forall u, R w u -> holds u a
    | Dia a    => exists u, R w u /\ holds u a
    end.

  Definition valid (phi : MForm) : Prop :=
    forall w : W, holds w phi.
End Semantics.
