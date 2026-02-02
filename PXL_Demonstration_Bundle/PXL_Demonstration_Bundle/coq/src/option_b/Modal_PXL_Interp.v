(*
  Modal_PXL_Interp.v

  Purpose:
  Provide a formal bridge between:
    - syntactic modal formulas (MForm)
    - semantic modal kernel operators (PXLv3_SemanticModal.Box/Dia)

  This is restricted (propositional fragment with nat-indexed atoms).
  It is EXPERIMENTAL and non-invasive: baseline does not import it.
*)

From PXL Require Import PXLv3_SemanticModal.
From PXL.modal Require Import PXL_Modal_Semantic_Kripke.
From PXL.option_b Require Import Modal_Syntax Modal_Semantics.

Module SM := PXLv3_SemanticModal.

Section PXLInterp.

  (* Atom assignment into Prop-level meanings *)
  Variable A : nat -> Prop.

  (*
    Connect to Kripke holds semantics when atoms are interpreted
    as constant propositions across worlds: Vc n w := A n.

    We use the semantic modal kernel for Box/Dia (PXL_Box/PXL_Dia),
    with the same frame parameters. Reflexivity is needed to witness
    local Box/Dia cases at an arbitrary world; symmetry/transitivity
    are carried as assumptions to match the kernel parameters.
  *)
  Section KripkeContext.
    Variable W : Type.
    Variable R : W -> W -> Prop.
    Variable w0 : W.

    Hypothesis R_refl  : forall x : W, R x x.
    Hypothesis R_symm  : forall x y : W, R x y -> R y x.
    Hypothesis R_trans : forall x y z : W, R x y -> R y z -> R x z.

    Definition kBox (p : Prop) : Prop := @PXL_Box W R p.

    Definition kDia (p : Prop) : Prop := @PXL_Dia W R p.

    Definition k_ax_Nec : forall p, p -> kBox p.
    Proof.
      intros p Hp.
      refine (@PXL_ax_Nec_sem W R p _).
      exact Hp.
    Defined.

    Definition k_ax_T : forall p, kBox p -> p.
    Proof.
      intros p Hp.
      refine (@PXL_ax_T_sem W R R_refl w0 p _).
      exact Hp.
    Defined.

    Fixpoint interp (phi : MForm) : Prop :=
      match phi with
      | Atom n   => A n
      | Bot      => False
      | And p q  => interp p /\ interp q
      | Or  p q  => interp p \/ interp q
      | Imp p q  => interp p -> interp q
      | Not p    => ~ interp p
      | Box p    => kBox (interp p)
      | Dia p    => kDia (interp p)
      end.

    (* Constant valuation across worlds *)
    Definition Vc (n : nat) (_ : W) : Prop := A n.

    Lemma holds_interp_const : forall w phi, holds W R Vc w phi <-> interp phi.
    Proof.
      intros w phi; revert w.
      induction phi; intros w; simpl.
      - reflexivity.
      - tauto.
      - specialize (IHphi1 w). specialize (IHphi2 w). tauto.
      - specialize (IHphi1 w). specialize (IHphi2 w). tauto.
      - specialize (IHphi1 w). specialize (IHphi2 w). tauto.
      - specialize (IHphi w). tauto.
      - (* Box *)
        split.
        + intro Hbox.
          (* Get interp phi at the current world, then lift via necessitation. *)
          specialize (Hbox w (R_refl w)).
          apply (proj1 (IHphi w)) in Hbox.
          apply k_ax_Nec. exact Hbox.
        + intro Hbox.
          (* Unpack Box (interp phi) back to local holds at any reachable world. *)
          intros u Hru.
          apply (proj2 (IHphi u)).
          apply k_ax_T in Hbox. exact Hbox.
      - (* Dia *)
        split.
        + intro Hdia.
          destruct Hdia as [u [Hru Hu]].
          apply (proj1 (IHphi u)) in Hu.
          exists w. exists u. exact (conj Hru Hu).
        + intro Hdia.
          destruct Hdia as [w' [u' [Hru' Hiphi]]].
          exists w. split.
          * apply R_refl.
          * apply (proj2 (IHphi w)). exact Hiphi.
    Qed.

  End KripkeContext.

End PXLInterp.
