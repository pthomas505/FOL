import Std
import Mathlib.Util.CompileInductive


set_option autoImplicit false


inductive Formula : Type
  | atom_ : String → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | meta_ : Nat → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula


structure Sequent : Type :=
  (hypotheses : List Formula)
  (conclusion : Formula)
  deriving Inhabited, DecidableEq


inductive Proof : Type
  | prop_1_ : Formula → Formula → Proof
  | prop_2_ : Formula → Formula → Formula → Proof
  | prop_3_ : Formula → Formula → Proof
  | mp_ : Proof → Proof → Proof
  | meta_ : Nat → Proof


structure State : Type :=
  (meta_to_sequent_map : Std.HashMap Nat Sequent)
  (meta_to_proof_map : Std.HashMap Nat Proof)
  (remaining_goal_list : List Nat)


def init (goal : Sequent) : State := {
  meta_to_sequent_map := Std.HashMap.empty.insert 0 goal
  meta_to_proof_map := Std.HashMap.empty
  remaining_goal_list := [0]
}

def exact_prop_1 (phi psi : Formula) (state : State) : Option State := do
  let i ← state.remaining_goal_list.head?
  let goal ← state.meta_to_sequent_map.find? i
  if goal = {
    hypotheses := []
    conclusion := phi.imp_ (psi.imp_ phi)
  }
  then Option.some {
    meta_to_sequent_map := state.meta_to_sequent_map
    meta_to_proof_map := state.meta_to_proof_map.insert i (Proof.prop_1_ phi psi)
    remaining_goal_list := state.remaining_goal_list.drop 1
  }
  else Option.none
