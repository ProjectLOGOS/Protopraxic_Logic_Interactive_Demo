From PXL Require PXLv3_SemanticModal.
From PXL Require Import PXLv3 PXL_Foundations PXL_Bridge_Proofs PXL_Privative PXL_Goodness_Existence.

Parameter add : Obj -> Obj -> Obj.
Infix " ⊕ " := add (at level 50, left associativity).

Parameter obj_exp : Obj -> nat -> Obj.
Notation "x ^ n" := (obj_exp x n) (at level 30, right associativity).

Parameter void : Obj.

Definition triune_plus_one_cascade : Obj :=
  obj_exp (add void 𝕀₁) 3.

(* Trinitarian plus-one principle: three successive I₁ lifts of void
   recover the necessary triune root 𝕆. *)
Axiom triune_plus_one_encodes_O :
  triune_plus_one_cascade ⧟ 𝕆.

Definition NonEquivProp (P : Prop) : Prop :=
  exists x y : Obj, P <-> x ⇎ y.

Definition PrivativeProp (P : Prop) : Prop :=
  exists x y : Obj, P <-> ~ (Dia (x ⧟ y)).

Lemma non_equiv_prop_equiv :
  forall P : Prop, NonEquivProp P <-> PrivativeProp P.
Proof.
  intros P; split.
  - intros [x [y H]].
    destruct H as [HPto Hback].
    exists x, y; split.
    + intro HP.
      apply (proj1 (non_equiv_privative_equiv x y)).
      apply HPto; exact HP.
    + intro Hno.
      apply Hback.
      apply (proj2 (non_equiv_privative_equiv x y)); exact Hno.
  - intros [x [y H]].
    destruct H as [HPto Hback].
    exists x, y; split.
    + intro HP.
      apply (proj2 (non_equiv_privative_equiv x y)).
      apply HPto; exact HP.
    + intro Hneq.
      apply Hback.
      apply (proj1 (non_equiv_privative_equiv x y)); exact Hneq.
Qed.

Theorem trinitarian_optimization :
  forall P : Prop,
    NonEquivProp P \/ Truth P \/ Goodness P ->
    PrivativeProp P \/ Coherence P \/ Existence P.
Proof.
  intros P [Hn | [Ht | Hg]].
  - left.
    apply (proj1 (non_equiv_prop_equiv P)); exact Hn.
  - right; left.
    apply truth_entails_coherence; exact Ht.
  - right; right.
    apply goodness_entails_existence; exact Hg.
Qed.
