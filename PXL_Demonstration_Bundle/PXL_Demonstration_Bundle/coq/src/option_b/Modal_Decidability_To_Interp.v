(*
  Modal_Decidability_To_Interp.v

  Purpose:
  Tie together:
    - finite-model decision procedure (valid_over_dec_cex)
    - interp bridge into semantic modal kernel
  so we can produce audit-friendly witnesses when a formula fails.
*)

From Stdlib Require Import List.
Import ListNotations.

From PXL Require Import PXLv3_SemanticModal.
From PXL.option_b Require Import Modal_Syntax Modal_Semantics Modal_Decidability_Skeleton Modal_PXL_Interp.

Section Glue.

  Variable W : Type.
  Variable worlds : list W.
  Variable R : W -> W -> Prop.
  Variable w0 : W.

  Hypothesis R_dec    : forall (x y : W), {R x y} + {~ R x y}.
  Hypothesis worlds_cover : forall w : W, In w worlds.
  Hypothesis R_refl : forall w : W, R w w.
  Hypothesis R_symm : forall x y : W, R x y -> R y x.
  Hypothesis R_trans : forall x y z : W, R x y -> R y z -> R x z.

  (* Constant valuation determined by A *)
  Variable A : nat -> Prop.
  Hypothesis A_dec : forall n : nat, {A n} + {~ A n}.
  Definition Vc (n : nat) (_ : W) : Prop := A n.
  Definition V_dec (n : nat) (w : W) : {Vc n w} + {~ Vc n w} :=
    match A_dec n with
    | left Ha => left Ha
    | right Hna => right Hna
    end.

  Definition interpP (phi : MForm) : Prop := interp A W R phi.

  (* Bridge the decision procedure to kernel-level interp evidence or counterexample. *)
  Theorem valid_over_dec_interp_cex :
    forall phi,
      {forall w, In w worlds -> interpP phi} + {exists w, In w worlds /\ ~ interpP phi}.
  Proof.
    intro phi.
    destruct (valid_over_dec_cex W worlds R Vc R_dec V_dec worlds_cover phi) as [Hvalid|Hcex].
    - left. intros w Hin.
      specialize (Hvalid w Hin).
      (* holds <-> interp from the bridge lemma *)
      pose proof (holds_interp_const A W R w0 R_refl w phi) as Hiff.
      apply (proj1 Hiff). exact Hvalid.
    - right.
      destruct Hcex as [w [Hin Hn]].
      pose proof (holds_interp_const A W R w0 R_refl w phi) as Hiff.
      exists w. split; [exact Hin|].
      intro Hinterp.
      apply Hn.
      apply (proj2 Hiff). exact Hinterp.
  Qed.

End Glue.
