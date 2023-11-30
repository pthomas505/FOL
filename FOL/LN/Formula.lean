import Mathlib.Tactic

set_option autoImplicit false


namespace NV

/--
  The type of named variable formulas.
-/
inductive Formula : Type
  | pred_ : String → List String → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : String → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of named variable formulas.
-/
def Formula.toString : Formula → String
  | pred_ X xs => s! "({X} {xs})"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | forall_ x phi => s! "(∀ {x}. {phi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }


end NV

--------------------------------------------------

namespace LN

-- If a bound variable has a de Bruijn index of 0 then it is bound by the first binder to its left that it is in the scope of.


/--
  The type of locally nameless variables.
-/
inductive Var
| free_ : String → Var
| bound_ : ℕ → Var -- de Bruijn index
  deriving Inhabited, DecidableEq

compile_inductive% Var

open Var

/--
  The string representation of locally nameless variables.
-/
def Var.toString : Var → String
  | free_ x => x
  | bound_ i => s! "{i}"

instance : ToString Var :=
  { toString := fun v => v.toString }


/--
  The type of locally nameless formulas.

  The string in the forall_ constructor is only used as a hint for translating to the named variable representation.
-/
inductive Formula : Type
  | pred_ : String → List Var → Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : String → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of locally nameless formulas.
-/
def Formula.toString : Formula → String
  | pred_ X vs => s! "({X} {vs})"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | forall_ _ phi => s! "(∀ {phi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }


#lint
