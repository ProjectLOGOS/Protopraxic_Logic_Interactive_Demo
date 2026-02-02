(*
  Modal_Syntax.v

  Restricted propositional modal syntax:
    - atoms are indexed by nat
    - connectives: bottom, and, or, imp, not
    - modalities: box, diamond
  Deliberately small so decidability for S5 is tractable.
*)

Inductive MForm : Type :=
| Atom : nat -> MForm
| Bot  : MForm
| And  : MForm -> MForm -> MForm
| Or   : MForm -> MForm -> MForm
| Imp  : MForm -> MForm -> MForm
| Not  : MForm -> MForm
| Box  : MForm -> MForm
| Dia  : MForm -> MForm.
