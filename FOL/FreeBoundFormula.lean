import Mathlib.Util.CompileInductive


inductive Var : Type
  | F : String → Var
  | B : String → Var
  deriving Inhabited, DecidableEq

open Var

inductive Formula : Type
  | pred_ : String → List Var → Formula
  | true_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : String → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula


def freeToBoundVar (v : String) : Var → Var
  | F x => if x = v then B x else F x
  | B x => B x

def replaceFreeVarFun (σ : String → String) : Var → Var
  | F x => F (σ x)
  | B x => B x

def sub (σ : String → String) : Formula → Formula
  | pred_ X xs => pred_ X (xs.map (replaceFreeVarFun σ))
  | true_ => true_
  | not_ phi => not_ (sub σ phi)
  | imp_ phi psi => imp_ (sub σ phi) (sub σ psi)
  | forall_ x phi => forall_ x (sub σ phi)

def freeToBound (v : String) : Formula → Formula
  | pred_ X xs => pred_ X (xs.map (freeToBoundVar v))
  | true_ => true_
  | not_ phi => not_ (freeToBound v phi)
  | imp_ phi psi => imp_ (freeToBound v phi) (freeToBound v psi)
  | forall_ x phi => forall_ x (freeToBound v phi)
