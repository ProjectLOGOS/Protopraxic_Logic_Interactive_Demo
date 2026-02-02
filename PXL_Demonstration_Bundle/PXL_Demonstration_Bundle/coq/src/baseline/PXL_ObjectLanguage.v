(** PXL_ObjectLanguage.v
    Object-language formulas + stratified truth to prevent liar-family self-reference.

    This file does NOT add axioms to PXL. It defines a typed syntax layer
    that can be interpreted into Prop using the existing modal operators Box/Dia
    from PXLv3 (or any other semantics you provide).
*)

Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

From Stdlib Require Import Arith.PeanoNat.

(* Import the baseline kernel operators (Box, Dia) and notations. *)
From PXL Require Import PXLv3.

(* A small, explicit level type (use nat for simplicity). *)
Definition Lvl := nat.

(* Atomics for the object language: keep abstract. *)
Parameter Atom : Type.

(* Object-language formulas indexed by level.
   Key design choice: Truth is only permitted "one level up":
     FTruth : Form level -> Form (S level)
   This makes "this sentence is false" untypable, since it would require FTruth
   at the same level as the sentence.
*)
Inductive Form : Lvl -> Type :=
| FAtom  : forall level, Atom -> Form level
| FTop   : forall level, Form level
| FBot   : forall level, Form level
| FNot   : forall level, Form level -> Form level
| FAnd   : forall level, Form level -> Form level -> Form level
| FOr    : forall level, Form level -> Form level -> Form level
| FImp   : forall level, Form level -> Form level -> Form level
| FBox   : forall level, Form level -> Form level
| FDia   : forall level, Form level -> Form level
| FTruth : forall level, Form level -> Form (S level).

Arguments FAtom {level} _.
Arguments FTop {level}.
Arguments FBot {level}.
Arguments FNot {level} _.
Arguments FAnd {level} _ _.
Arguments FOr {level} _ _.
Arguments FImp {level} _ _.
Arguments FBox {level} _.
Arguments FDia {level} _.
Arguments FTruth {level} _.

(* A semantic interpretation into Prop.
   - We interpret atomics via a valuation.
   - We interpret FBox/FDia using the kernel's Box/Dia on Prop.
   - We interpret FTruth as "the denotation of the lower-level formula" (reflection),
     but stratification prevents circular truth talk at the same level.
*)
Section Semantics.

  Variable val : Atom -> Prop.

  Fixpoint denote {level : Lvl} (phi : Form level) : Prop :=
    match phi with
    | FAtom a     => val a
    | FTop        => True
    | FBot        => False
    | FNot p      => ~ denote p
    | FAnd p q    => denote p /\ denote q
    | FOr p q     => denote p \/ denote q
    | FImp p q    => denote p -> denote q
    | FBox p      => Box (denote p)
    | FDia p      => Dia (denote p)
    | FTruth p    => denote p
    end.

End Semantics.
