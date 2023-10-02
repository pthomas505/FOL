import Std.Tactic.Lint.Frontend
import Std.Data.HashMap.Basic

import Mathlib.Data.String.Lemmas
import Mathlib.Util.CompileInductive

import FOL.List
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
  The type of locally nameless variables.
-/
inductive Var
| F : String → Var
| B : ℕ → Var
  deriving Inhabited, DecidableEq

compile_inductive% Var

open Var

/--
  The string representation of locally nameless variables.
-/
def Var.toString : Var → String
  | F x => x
  | B n => s! "{n}"

instance : ToString Var :=
  { toString := fun x => x.toString }


/--
  The type of locally nameless formulas.
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
  The string representation of locally nameless formulas.
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
  | B _ => ∅


/--
  Formula.freeVarSet F := The set of all of the variables that have a free occurrence in the formula F.
-/
def Formula.freeVarSet : Formula → Finset String
  | pred_const_ _ xs => xs.toFinset.biUnion Var.freeVarSet
  | pred_var_ _ xs => xs.toFinset.biUnion Var.freeVarSet
  | true_ => ∅
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ _ phi => phi.freeVarSet


def openVar
  (k : ℕ)
  (v : String) :
  Var → Var
  | F x => F x
  | B n => if k = n then F v else B n

def openFormulaAux
  (k : ℕ)
  (v : String) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map (openVar k v))
  | pred_var_ X xs => pred_var_ X (xs.map (openVar k v))
  | true_ => true_
  | not_ phi => not_ (openFormulaAux k v phi)
  | imp_ phi psi => imp_ (openFormulaAux k v phi) (openFormulaAux k v psi)
  | forall_ x phi => forall_ x (openFormulaAux (k + 1) v phi)

def openFormula
  (v : String)
  (F : Formula) :
  Formula :=
  openFormulaAux 0 v F


def closeVar
  (k : ℕ)
  (v : String) :
  Var → Var
  | F x => if v = x then B k else F x
  | B n => B n

def closeFormulaAux
  (k : ℕ)
  (v : String) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map (closeVar k v))
  | pred_var_ X xs => pred_var_ X (xs.map (closeVar k v))
  | true_ => true_
  | not_ phi => not_ (closeFormulaAux k v phi)
  | imp_ phi psi => imp_ (closeFormulaAux k v phi) (closeFormulaAux k v psi)
  | forall_ x phi => forall_ x (closeFormulaAux (k + 1) v phi)

def closeFormula
  (v : String)
  (F : Formula) :
  Formula :=
  closeFormulaAux 0 v F


lemma CloseVarOpenVarComp
  (x : Var)
  (v : String)
  (k : ℕ)
  (h1 : v ∉ Var.freeVarSet x) :
  (closeVar k v ∘ openVar k v) x = x :=
  by
  cases x
  case F x =>
    simp only [Var.freeVarSet] at h1
    simp at h1

    simp
    simp only [openVar]
    simp only [closeVar]
    simp only [if_neg h1]
  case B n =>
    simp
    simp only [openVar]
    split_ifs
    case _ c1 =>
      simp only [closeVar]
      simp
      exact c1
    case _ c1 =>
      simp only [closeVar]

example
  (F : Formula)
  (k : ℕ)
  (v : String)
  (h1 : v ∉ F.freeVarSet) :
  closeFormulaAux k v (openFormulaAux k v F) = F :=
  by
  induction F generalizing k
  case pred_const_ X xs | pred_var_ X xs =>
    unfold Formula.freeVarSet at h1
    simp at h1

    unfold openFormulaAux
    unfold closeFormulaAux
    simp
    simp only [List.map_eq_self_iff]
    intro x a1
    apply CloseVarOpenVarComp
    exact h1 x a1
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold Formula.freeVarSet at h1

    unfold openFormulaAux
    unfold closeFormulaAux
    simp only [phi_ih k h1]
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.freeVarSet at h1
    simp at h1
    push_neg at h1

    unfold openFormulaAux
    unfold closeFormulaAux
    cases h1
    case _ h1_left h1_right =>
      simp only [phi_ih k h1_left]
      simp only [psi_ih k h1_right]
  case forall_ x phi phi_ih =>
    unfold Formula.freeVarSet at h1

    unfold openFormulaAux
    unfold closeFormulaAux
    simp only [phi_ih (k + 1) h1]


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
  (context : Std.HashMap String ℕ) :
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


def NVVarToLNVar'
  (outer : ℕ)
  (context : Std.HashMap String ℕ)
  (x : String) :
  LN.Var :=
  let opt := context.find? x
  if h : Option.isSome opt
  then
    let n := Option.get opt h
    LN.Var.B (outer - n)
  else LN.Var.F x

def NVToLNAux'
  (outer : ℕ)
  (context : Std.HashMap String ℕ) :
  NV.Formula → LN.Formula
| NV.Formula.pred_const_ X xs => LN.Formula.pred_const_ X (xs.map (NVVarToLNVar' outer context))
| NV.Formula.pred_var_ X xs => LN.Formula.pred_var_ X (xs.map (NVVarToLNVar' outer context))
| NV.Formula.true_ => LN.Formula.true_
| NV.Formula.not_ phi => LN.Formula.not_ (NVToLNAux' outer context phi)
| NV.Formula.imp_ phi psi => LN.Formula.imp_ (NVToLNAux' outer context phi) (NVToLNAux' outer context psi)
| NV.Formula.forall_ x phi =>
    let context' := context.insert x (outer + 1)
    LN.Formula.forall_ x (NVToLNAux' (outer + 1) context' phi)

def NVToLN' (F : NV.Formula) : LN.Formula :=
  NVToLNAux' 0 ∅ F

#eval NVToLN' (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "y"]))

#eval (NVToLN' (NV.Formula.forall_ "z" (NV.Formula.forall_ "y" (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "y", "z"])))))


#eval LN.openFormula "z" (NVToLN' (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "z"])))

#eval LN.closeFormula "z" (NVToLN' (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "z"])))

#eval LN.closeFormula "z" (NVToLN' (NV.Formula.pred_var_ "X" ["x", "z"]))

#eval LN.closeFormula "z" (LN.openFormula "z" (NVToLN' (NV.Formula.pred_var_ "X" ["x", "z"])))


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


def fresh
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
  fresh (x ++ c.toString) c xs
  else x
  termination_by fresh x _ xs => finset_string_max_len xs + 1 - x.length


lemma fresh_not_mem
  (x : String)
  (c : Char)
  (xs : Finset String) :
  fresh x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_string_max_len xs - String.length x < finset_string_max_len xs + 1 - String.length x :=
    by
    obtain s1 := finset_string_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s1]
    simp
  by
    unfold fresh
    simp
    simp only [if_pos h]
    apply fresh_not_mem
  else by
    unfold fresh
    simp
    simp [if_neg h]
    exact h
  termination_by fresh_not_mem x _ xs => finset_string_max_len xs + 1 - x.length


def LNVarToNVVar
  (outer : ℕ)
  (context : Std.HashMap ℤ String) :
  LN.Var → Option String
  | LN.Var.F x => Option.some x
  | LN.Var.B n => context.find? (outer - n)


def LNToNVAux
  (c : Char)
  (outer : ℕ)
  (context : Std.HashMap ℤ String) :
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
      let x' := fresh x c phi.freeVarSet
      let phi' ← LNToNVAux c (outer + 1) (context.insert (outer + 1) x') phi
      Option.some (NV.Formula.forall_ x' phi')


def LNToNV
  (c : Char)
  (F : LN.Formula) :
  Option NV.Formula :=
  LNToNVAux c 0 ∅ F

#eval (NVToLN (NV.Formula.forall_ "z" (NV.Formula.forall_ "y" (NV.Formula.forall_ "x" (NV.Formula.pred_var_ "X" ["x", "y", "z"])))))

#eval (LNToNV '+' (NVToLN' (NV.Formula.forall_ "x" (NV.Formula.forall_ "y" (NV.Formula.forall_ "z" (NV.Formula.pred_var_ "X" ["x", "y", "z"]))))))

#eval LNToNV '+' (NVToLN (NV.Formula.forall_ "z" (NV.Formula.forall_ "x" (NV.Formula.forall_ "y" (NV.Formula.pred_var_ "X" ["x", "y", "z"])))))

#eval LNToNV '+' (LN.Formula.forall_ "z" (LN.Formula.forall_ "x" (LN.Formula.forall_ "y" (LN.Formula.pred_var_ "X" [(LN.Var.F "z"), (LN.Var.B 0), (LN.Var.F "y")]))))

#eval LNToNV '+' (LN.Formula.forall_ "y" (LN.Formula.forall_ "x" (LN.Formula.forall_ "y++" (LN.Formula.pred_var_ "X" [(LN.Var.B 2), (LN.Var.B 0), (LN.Var.F "y")]))))

#eval LNToNV '+' (LN.Formula.forall_ "x" (LN.Formula.pred_var_ "X" [(LN.Var.B 5)]))

example
  (F : NV.Formula)
  (outer_1 : ℕ)
  (outer_2 : ℕ)
  (context_1 : Std.HashMap String ℕ)
  (context_2 : Std.HashMap ℤ String)
  (c : Char) :
  LNToNVAux c outer_2 context_2 (NVToLNAux' outer_1 context_1 F) = Option.some F :=
  by sorry
