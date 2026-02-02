From PXL Require Import PXLv3 PXL_Foundations PXL_Bridge_Proofs PXL_Privative
                        PXL_Goodness_Existence PXL_Internal_LEM PXL_Trinitarian_Optimization
                        PXL_S2_Axioms PXL_Arithmetic Trinitarian_Identity_Closure.

Set Implicit Arguments.
Set Universe Polymorphism.

Module Import InternalLEM := PXL_Internal_LEM.

Theorem LOGOS_ETGC_Summary :
  (forall P : Prop, Goodness P <-> Existence P) /\
  (forall P : Prop, Truth P <-> Coherence P) /\
  (forall P : Prop, coherence (truth_obj P) <-> Truth P) /\
  (forall P : Prop, P \/ ~ P) /\
  (forall X : Obj, coherence X -> ~ (pxl_equation X ⧟ void)) /\
  (forall X : Obj, (X × void) ⧟ void -> ~ (coherence (void /ι))).
Proof.
  split.
  - intro P.
    split; intro H.
    + apply goodness_entails_existence; exact H.
    + apply existence_entails_goodness; exact H.
  - split.
    + intro P.
      apply truth_coherence_equiv.
    + split.
      * apply satisfies_I2.
      * split.
        { intro P.
          apply pxl_excluded_middle. }
        { split.
          - intros X HX.
            exact (@pxl_equation_encodes_structure_arith X HX).
          - intros X Hcollapse.
            exact (@imaginary_boundary_arith X Hcollapse). }
Qed.
