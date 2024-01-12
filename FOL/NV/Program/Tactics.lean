import Std


set_option autoImplicit false


inductive Term : Type
  | var_ : String → Term
  | meta_ : Nat → Term
  deriving Inhabited, DecidableEq

open Term


inductive Formula : Type
  | pred_ : String → List Term → Formula
  | eq_ : Term → Term → Formula
  | true_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : String → Formula → Formula
  | meta_ : Nat → Formula
  deriving Inhabited, DecidableEq

open Formula


inductive Proof : Type
  | struct_1_ : List Formula → Formula → Formula → Proof → Proof
  | struct_2_ : List Formula → Formula → Formula → Proof → Proof
  | struct_3_ : List Formula → List Formula → Formula → Formula → Formula → Proof → Proof
  | assume_ : Formula → Proof
  | prop_0_ : Proof
  | prop_1_ : Formula → Formula → Proof
  | prop_2_ : Formula → Formula → Formula → Proof
  | prop_3_ : Formula → Formula → Proof
  | mp_ : List Formula → Formula → Formula → Proof → Proof → Proof
  | dt_ : List Formula → Formula → Formula → Proof → Proof
  | pred_1_ : String → Formula → Formula → Proof
  | pred_2_ : String → Term → Formula → Proof
  | pred_3_ : String → Formula → Proof
  | gen_ : String → Formula → Proof → Proof
  | eq_1_ : Term → Proof
  | eq_2_eq_ : Term → Term → Term → Term → Proof
  | eq_2_pred_ : String → List Term → List Term → Proof
  | sub_ : List Formula → Formula → List (String × (List Term) × Formula) → Proof → Proof
  | thm_ : String → Proof
  | meta_ : Nat → Proof
  deriving Inhabited, DecidableEq

open Proof


structure Sequent : Type :=
  (hypothesis_list : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq


structure State : Type :=
  (proof_meta_to_sequent_map : Std.HashMap Nat Sequent)
  (proof_meta_to_proof_map : Std.HashMap Nat Proof)
  (remaining_goal_list : List Nat)
