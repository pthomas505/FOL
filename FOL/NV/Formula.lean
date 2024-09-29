import Batteries.Tactic.Lint.Frontend
import Mathlib.Util.CompileInductive
import Lean.Data.Json.Basic


set_option autoImplicit false


namespace FOL.NV


/--
  The type of variable names.
-/
structure VarName extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString VarName :=
  { toString := fun (x : VarName) => x.toString }

/-
instance : Repr VarName :=
  { reprPrec := fun (x : VarName) _ => x.toString.toFormat }
-/

instance : Lean.ToJson VarName :=
  { toJson := fun (x : VarName) => Lean.toJson x.toString }

instance : Lean.FromJson VarName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (VarName.mk str) }


/--
  The type of predicate names.
-/
structure PredName extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString PredName :=
  { toString := fun (X : PredName) => X.toString }

/-
instance : Repr PredName :=
  { reprPrec := fun (X : PredName) _ => X.toString.toFormat }
-/

instance : Lean.ToJson PredName :=
  { toJson := fun (X : PredName) => Lean.toJson X.toString }

instance : Lean.FromJson PredName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (PredName.mk str) }


/--
  The type of definition names.
-/
structure DefName extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString DefName :=
  { toString := fun (X : DefName) => X.toString }

/-
instance : Repr DefName :=
  { reprPrec := fun (X : DefName) _ => X.toString.toFormat }
-/

instance : Lean.ToJson DefName :=
  { toJson := fun (X : DefName) => Lean.toJson X.toString }

instance : Lean.FromJson DefName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (DefName.mk str) }


/--
  The type of formulas.
-/
inductive Formula : Type
  | pred_const_ : PredName → List VarName → Formula
  | pred_var_ : PredName → List VarName → Formula
  | eq_ : VarName → VarName → Formula
  | true_ : Formula
  | false_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | and_ : Formula → Formula → Formula
  | or_ : Formula → Formula → Formula
  | iff_ : Formula → Formula → Formula
  | forall_ : VarName → Formula → Formula
  | exists_ : VarName → Formula → Formula
  | def_ : DefName → List VarName → Formula
  deriving Inhabited, DecidableEq, Lean.ToJson, Lean.FromJson, Repr

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | pred_const_ X xs =>
    if xs.isEmpty
    then s! "{X}"
    else s! "({X} {xs})"
  | pred_var_ X xs =>
    if xs.isEmpty
    then s! "{X}"
    else s! "({X} {xs})"
  | eq_ x y => s! "({x} = {y})"
  | true_ => "T"
  | false_ => "F"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"
  | forall_ x phi => s! "(∀ {x}. {phi.toString})"
  | exists_ x phi => s! "(∃ {x}. {phi.toString})"
  | def_ X xs => s! "def ({X} {xs})"


instance : ToString Formula :=
  { toString := fun (F : Formula) => F.toString }

/-
instance : Repr Formula :=
  { reprPrec := fun (F : Formula) _ => F.toString.toFormat }
-/


/--
  And_ [] := T

  And_ [phi] := phi ∧ T

  And_ [phi_0 ... phi_n] := phi_0 ∧ ... ∧ phi_n ∧ T
-/
def Formula.And_ (l : List Formula) : Formula :=
  List.foldr Formula.and_ true_ l

#eval Formula.And_ [pred_var_ (PredName.mk "X") [], pred_var_ (PredName.mk "Y") []]


/--
  Or_ [] := F

  Or_ [phi] := phi ∨ F

  Or_ [phi_0 ... phi_n] := phi_0 ∨ ... ∨ phi_n ∨ F
-/
def Formula.Or_ (l : List Formula) : Formula :=
  List.foldr Formula.or_ Formula.false_ l

#eval Formula.Or_ [pred_var_ (PredName.mk "X") [], pred_var_ (PredName.mk "Y") []]


/--
  Forall_ [x_0 ... x_n] phi := ∀ x_0 ... ∀ x_n phi
-/
def Formula.Forall_ (xs : List VarName) (phi : Formula) : Formula :=
  List.foldr Formula.forall_ phi xs

#eval Formula.Forall_ [VarName.mk "x", VarName.mk "y"] (Formula.pred_var_ (PredName.mk "phi") [])


/--
  Exists_ [x_0 ... x_n] phi := ∃ x_0 ... ∃ x_n phi
-/
def Formula.Exists_ (xs : List VarName) (phi : Formula) : Formula :=
  List.foldr Formula.exists_ phi xs

#eval Formula.Exists_ [VarName.mk "x", VarName.mk "y"] (Formula.pred_var_ (PredName.mk "phi") [])


#lint
