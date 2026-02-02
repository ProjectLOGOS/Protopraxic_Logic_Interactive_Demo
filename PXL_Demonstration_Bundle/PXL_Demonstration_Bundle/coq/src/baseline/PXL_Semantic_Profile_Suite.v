(*
  PXL_Semantic_Profile_Suite.v

  Purpose:
  Single entrypoint proving the semantic modal kernel profile (17-axiom kernel)
  compiles alongside the semantic ports of key baseline modules.

  This is the file you point auditors/investors to when you say:
  "The semantic modal profile compiles end-to-end."
*)

From PXL Require Import PXLv3_SemanticModal.

(* Semantic modal theorems (parallel proof layer, assumption-free) *)
From PXL.modal Require Import PXL_Modal_Semantic_Kripke.

(* Semantic ports (lane) *)
From PXL Require Import PXL_Sanity_SemanticPort.
From PXL Require Import PXL_Foundations_SemanticPort.
From PXL Require Import PXL_Bridge_Proofs_SemanticPort.
From PXL Require Import PXL_Internal_LEM_SemanticPort.
From PXL Require Import PXL_Trinitarian_Optimization_SemanticPort.

Import PXL_Internal_LEM.

(* Smoke checks *)
Check ax_K.
Check ax_T.
Check ax_Nec.
Check pxl_excluded_middle.
