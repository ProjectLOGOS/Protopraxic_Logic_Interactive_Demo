(************************************************************************)
(*  PXL_Imp_Nothing.v                                                   *)
(*  Impossibility of Nothing (ION) / Necessary Being foundation         *)
(************************************************************************)

From Stdlib Require Import Unicode.Utf8.
From PXL Require Import PXL_Definitions PXL_Modal_Axioms_Semantic PXL_Kernel_Axioms.

Module PXL_Imp_Nothing.

  (*** Canonical foundations (PXL-native) ***)
  Definition Adm (x : Obj) : Prop := x ⧟ x.
  Definition Nec (x : Obj) : Prop := □ (Adm x).
  Definition Cont (x : Obj) : Prop :=
    ◇ (Adm x) /\
    ◇ (~ Adm x).
  Definition Expl (y x : Obj) : Prop := grounded_in (Adm x) y.
  Definition UG (x : Obj) : Prop := forall y : Obj, Cont y -> Expl x y.

  (*** ION-layer primitives for substrate attribution ***)
  Parameter S : Obj -> Prop.
  Parameter God : Obj.

  (*** ION-layer axioms (explicitly accepted) ***)
  Axiom ION_P4 : exists x : Obj, Cont x.
  Axiom ION_P5 : forall x : Obj, Cont x -> exists y : Obj, Expl y x.
  Axiom ION_P6 : forall x : Obj, Cont x -> exists y : Obj, Nec y /\ Expl y x.
  Axiom ION_P7a : forall x : Obj, (Nec x /\ UG x) -> S x.
  Axiom ION_P8 : forall x : Obj, S x <-> (x ⧟ God).

End PXL_Imp_Nothing.
