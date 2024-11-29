import Batteries.Tactic.Lint.Frontend
import Mathlib.Util.CompileInductive
import Lean.Data.Json.Basic


set_option autoImplicit false


/--
  The type of variable names.
-/
structure VarName_ extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString VarName_ :=
  { toString := VarName_.toString }


instance : Lean.ToJson VarName_ :=
  { toJson := fun (x : VarName_) => Lean.toJson x.toString }

instance : Lean.FromJson VarName_ :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (VarName_.mk str) }

#eval Lean.toJson (VarName_.mk "x")
#eval ((Lean.fromJson? "x") : Except String VarName_)


/--
  The type of predicate names.
-/
structure PredName_ extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString PredName_ :=
  { toString := PredName_.toString }


instance : Lean.ToJson PredName_ :=
  { toJson := fun (X : PredName_) => Lean.toJson X.toString }

instance : Lean.FromJson PredName_ :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (PredName_.mk str) }

#eval Lean.toJson (PredName_.mk "X")
#eval ((Lean.fromJson? "X") : Except String PredName_)


/--
  The type of definition names.
-/
structure DefName extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString DefName :=
  { toString := DefName.toString }


instance : Lean.ToJson DefName :=
  { toJson := fun (X : DefName) => Lean.toJson X.toString }

instance : Lean.FromJson DefName :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (DefName.mk str) }

#eval Lean.toJson (DefName.mk "X")
#eval ((Lean.fromJson? "X") : Except String DefName)


/--
  The type of formulas.
-/
inductive Formula : Type
  | pred_const_ : PredName_ → List VarName_ → Formula
  | pred_var_ : PredName_ → List VarName_ → Formula
  | eq_ : VarName_ → VarName_ → Formula
  | true_ : Formula
  | false_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | and_ : Formula → Formula → Formula
  | or_ : Formula → Formula → Formula
  | iff_ : Formula → Formula → Formula
  | forall_ : VarName_ → Formula → Formula
  | exists_ : VarName_ → Formula → Formula
  | def_ : DefName → List VarName_ → Formula
  deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

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
  | def_ X xs =>
    if xs.isEmpty
    then s! "def {X}"
    else s! "def ({X} {xs})"

instance : ToString Formula :=
  { toString := Formula.toString }


#eval Lean.toJson (pred_const_ (PredName_.mk "X") [])
#eval Lean.toJson (forall_ (VarName_.mk "x") (pred_const_ (PredName_.mk "X") []))

/--
  Parses a JSON formatted string into a `Formula`.
-/
def json_string_to_formula
  (str : String) :
  Except String Formula :=
  match Lean.Json.parse str with
  | Except.ok json => ((Lean.fromJson? json) : Except String Formula)
  | Except.error e => Except.error e

#eval json_string_to_formula "{\"pred_const_\": [\"X\", []]}"
#eval json_string_to_formula "{\"forall_\": [\"x\", {\"pred_const_\": [\"X\", []]}]}"


/--
  And_ [] := T

  And_ [phi] := phi ∧ T

  And_ [phi_0 ... phi_n] := phi_0 ∧ ... ∧ phi_n ∧ T
-/
def Formula.And_ (l : List Formula) : Formula :=
  List.foldr and_ true_ l

#eval (And_ []).toString

#eval (And_ [pred_var_ (PredName_.mk "X") []]).toString

#eval (And_ [pred_var_ (PredName_.mk "X") [], pred_var_ (PredName_.mk "Y") []]).toString


/--
  Or_ [] := F

  Or_ [phi] := phi ∨ F

  Or_ [phi_0 ... phi_n] := phi_0 ∨ ... ∨ phi_n ∨ F
-/
def Formula.Or_ (l : List Formula) : Formula :=
  List.foldr or_ false_ l

#eval (Or_ []).toString

#eval (Or_ [pred_var_ (PredName_.mk "X") []]).toString

#eval (Or_ [pred_var_ (PredName_.mk "X") [], pred_var_ (PredName_.mk "Y") []]).toString


/--
  Forall_ [x_0 ... x_n] phi := ∀ x_0 ... ∀ x_n phi
-/
def Formula.Forall_ (xs : List VarName_) (phi : Formula) : Formula :=
  List.foldr forall_ phi xs

#eval (Forall_ [] (pred_var_ (PredName_.mk "phi") [])).toString

#eval (Forall_ [VarName_.mk "x"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x"])).toString

#eval (Forall_ [VarName_.mk "x", VarName_.mk "y"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x", VarName_.mk "y"])).toString


/--
  Exists_ [x_0 ... x_n] phi := ∃ x_0 ... ∃ x_n phi
-/
def Formula.Exists_ (xs : List VarName_) (phi : Formula) : Formula :=
  List.foldr exists_ phi xs

#eval (Exists_ [] (pred_var_ (PredName_.mk "phi") [])).toString

#eval (Exists_ [VarName_.mk "x"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x"])).toString

#eval (Exists_ [VarName_.mk "x", VarName_.mk "y"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x", VarName_.mk "y"])).toString


#lint
