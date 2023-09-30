import Std.Tactic.Lint.Frontend
import Std.Data.HashMap.Basic

import Mathlib.Data.String.Lemmas
import Mathlib.Util.CompileInductive
import FOL.Tactics

set_option autoImplicit false


namespace NV

/--
  The type of formulas.
-/
inductive Formula : Type
  | pred_const_ : String → List String → Formula
  | pred_var_ : String → List String → Formula
  | true_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : String → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | pred_const_ X xs => s! "({X} {xs})"
  | pred_var_ X xs => s! "({X} {xs})"
  | true_ => "T"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | forall_ x phi => s! "(∀ {x}. {phi.toString})"

instance : ToString Formula :=
  { toString := fun F => F.toString }

end NV


namespace LN

/--
  The type of variables.
-/
inductive Var
| F : String → Var
| B : ℕ → Var
  deriving Inhabited, DecidableEq

compile_inductive% Var

open Var

/--
  The string representation of variables.
-/
def Var.toString : Var → String
  | F x => x
  | B n => s! "{n}"

instance : ToString Var :=
  { toString := fun x => x.toString }


/--
  The type of formulas.
-/
inductive Formula : Type
  | pred_const_ : String → List Var → Formula
  | pred_var_ : String → List Var → Formula
  | true_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : String → Formula → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | pred_const_ X xs => s! "({X} {xs})"
  | pred_var_ X xs => s! "({X} {xs})"
  | true_ => "T"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | forall_ x phi => s! "(∀ {x}. {phi.toString})"


instance : ToString Formula :=
  { toString := fun F => F.toString }


def Var.freeVarSet : Var → Finset String
  | F x => {x}
  | B _ => {}


/--
  Formula.freeVarSet F := The set of all of the variables that have a free occurrence in the formula F.
-/
def Formula.freeVarSet : Formula → Finset String
  | pred_const_ _ xs => xs.toFinset.biUnion Var.freeVarSet
  | pred_var_ _ xs => xs.toFinset.biUnion Var.freeVarSet
  | true_ => {}
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ _ phi => phi.freeVarSet


end LN

/--
  The conversion of named variables to locally nameless variables.
-/
def NVVarToLNVar
  (context : Std.HashMap String ℕ)
  (x : String) :
  LN.Var :=
  let opt := context.find? x
  if h : Option.isSome opt
  then
    let i := Option.get opt h
    LN.Var.B i
  else LN.Var.F x


/--
  Helper function for NVToLN.
-/
def NVToLNAux
  (context : Std.HashMap String Nat) :
  NV.Formula → LN.Formula
| NV.Formula.pred_const_ X xs => LN.Formula.pred_const_ X (xs.map (NVVarToLNVar context))
| NV.Formula.pred_var_ X xs => LN.Formula.pred_var_ X (xs.map (NVVarToLNVar context))
| NV.Formula.true_ => LN.Formula.true_
| NV.Formula.not_ phi => LN.Formula.not_ (NVToLNAux context phi)
| NV.Formula.imp_ phi psi => LN.Formula.imp_ (NVToLNAux context phi) (NVToLNAux context psi)
| NV.Formula.forall_ x phi =>
    let context' := (Std.HashMap.mapVal (fun _ val => val + 1) context).insert x 0
    LN.Formula.forall_ x (NVToLNAux context' phi)

/--
  The conversion of named variable formulas to locally nameless formulas.
-/
def NVToLN (F : NV.Formula) : LN.Formula :=
  NVToLNAux {} F


#eval NVToLN (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "y"]))


def finset_string_max_len :
  Finset String → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 String.length


lemma finset_string_max_len_mem
  (x : String)
  (xs : Finset String)
  (h1 : x ∈ xs) :
  x.length <= finset_string_max_len xs :=
  by
  induction xs using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1

    cases h1
    case inl c1 =>
      subst c1
      unfold finset_string_max_len
      simp
    case inr c1 =>
      unfold finset_string_max_len at ih

      unfold finset_string_max_len
      simp
      right
      exact ih c1


def variant
  (x : String)
  (c : Char)
  (xs : Finset String) :
  String :=
  if h : x ∈ xs
  then
  have : finset_string_max_len xs - String.length x < finset_string_max_len xs + 1 - String.length x :=
    by
    obtain s1 := finset_string_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s1]
    simp
  variant (x ++ c.toString) c xs
  else x
  termination_by variant x _ xs => finset_string_max_len xs + 1 - x.length


lemma variant_not_mem
  (x : String)
  (c : Char)
  (xs : Finset String) :
  variant x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_string_max_len xs - String.length x < finset_string_max_len xs + 1 - String.length x :=
    by
    obtain s1 := finset_string_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s1]
    simp
  by
    unfold variant
    simp
    simp only [if_pos h]
    apply variant_not_mem
  else by
    unfold variant
    simp
    simp [if_neg h]
    exact h
  termination_by variant_not_mem x _ xs => finset_string_max_len xs + 1 - x.length


def LNVarToNVVar
  (outer : ℕ) 
  (context : Std.HashMap ℕ String) :
  LN.Var → Option String
  | LN.Var.F x => Option.some x
  | LN.Var.B n => context.find? (outer - n - 1)


def LNToNVAux
  (c : Char)
  (outer : ℕ) 
  (context : Std.HashMap ℕ String) :
  LN.Formula → Option NV.Formula
  | LN.Formula.pred_const_ X xs => do
      let xs' ← xs.mapM (LNVarToNVVar outer context)
      Option.some (NV.Formula.pred_const_ X xs')
  | LN.Formula.pred_var_ X xs => do
      let xs' ← xs.mapM (LNVarToNVVar outer context)
      Option.some (NV.Formula.pred_var_ X xs')
  | LN.Formula.true_ => Option.some NV.Formula.true_
  | LN.Formula.not_ phi => do
      let phi' ← LNToNVAux c outer context phi
      Option.some (NV.Formula.not_ phi')
  | LN.Formula.imp_ phi psi => do
      let phi' ← LNToNVAux c outer context phi
      let psi' ← LNToNVAux c outer context psi
      Option.some (NV.Formula.imp_ phi' psi')
  | LN.Formula.forall_ x phi => do
      let x' := variant x c phi.freeVarSet
      let phi' ← LNToNVAux c (outer + 1) (context.insert outer x') phi
      Option.some (NV.Formula.forall_ x' phi')


def LNToNV
  (c : Char)
  (F : LN.Formula) :
  Option NV.Formula :=
  LNToNVAux c 0 {} F

#eval (NVToLN (NV.Formula.forall_ "z" (NV.Formula.forall_ "y" (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "y", "z"])))))

#eval LNToNV '+' (NVToLN (NV.Formula.forall_ "z" (NV.Formula.forall_ "x" (NV.Formula.forall_ "y" (NV.Formula.pred_var_ "X" ["x", "y", "z"])))))

#eval LNToNV '+' (LN.Formula.forall_ "z" (LN.Formula.forall_ "x" (LN.Formula.forall_ "y" (LN.Formula.pred_var_ "X" [(LN.Var.F "z"), (LN.Var.B 0), (LN.Var.F "y")]))))
