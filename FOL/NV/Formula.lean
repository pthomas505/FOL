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
structure DefName_ extends String
  deriving Inhabited, DecidableEq, Repr

instance : ToString DefName_ :=
  { toString := DefName_.toString }


instance : Lean.ToJson DefName_ :=
  { toJson := fun (X : DefName_) => Lean.toJson X.toString }

instance : Lean.FromJson DefName_ :=
  { fromJson? := fun (json : Lean.Json) => do
    let str ← Lean.fromJson? json
    Except.ok (DefName_.mk str) }

#eval Lean.toJson (DefName_.mk "X")
#eval ((Lean.fromJson? "X") : Except String DefName_)


/--
  The type of formulas.
-/
inductive Formula_ : Type
  | pred_const_ : PredName_ → List VarName_ → Formula_
  | pred_var_ : PredName_ → List VarName_ → Formula_
  | eq_ : VarName_ → VarName_ → Formula_
  | true_ : Formula_
  | false_ : Formula_
  | not_ : Formula_ → Formula_
  | imp_ : Formula_ → Formula_ → Formula_
  | and_ : Formula_ → Formula_ → Formula_
  | or_ : Formula_ → Formula_ → Formula_
  | iff_ : Formula_ → Formula_ → Formula_
  | forall_ : VarName_ → Formula_ → Formula_
  | exists_ : VarName_ → Formula_ → Formula_
  | def_ : DefName_ → List VarName_ → Formula_
  deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

compile_inductive% Formula_

open Formula_

/--
  The string representation of formulas.
-/
def Formula_.toString : Formula_ → String
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

instance : ToString Formula_ :=
  { toString := Formula_.toString }


#eval Lean.toJson (pred_const_ (PredName_.mk "X") [])
#eval Lean.toJson (forall_ (VarName_.mk "x") (pred_const_ (PredName_.mk "X") []))

/--
  Parses a JSON formatted string into a `Formula_`.
-/
def json_string_to_formula
  (str : String) :
  Except String Formula_ :=
  match Lean.Json.parse str with
  | Except.ok json => ((Lean.fromJson? json) : Except String Formula_)
  | Except.error e => Except.error e

#eval json_string_to_formula "{\"pred_const_\": [\"X\", []]}"
#eval json_string_to_formula "{\"forall_\": [\"x\", {\"pred_const_\": [\"X\", []]}]}"


/--
  And_ [] := T

  And_ [phi] := phi ∧ T

  And_ [phi_0 ... phi_n] := phi_0 ∧ ... ∧ phi_n ∧ T
-/
def Formula_.And_ (l : List Formula_) : Formula_ :=
  List.foldr and_ true_ l

#eval (And_ []).toString

#eval (And_ [pred_var_ (PredName_.mk "X") []]).toString

#eval (And_ [pred_var_ (PredName_.mk "X") [], pred_var_ (PredName_.mk "Y") []]).toString


/--
  Or_ [] := F

  Or_ [phi] := phi ∨ F

  Or_ [phi_0 ... phi_n] := phi_0 ∨ ... ∨ phi_n ∨ F
-/
def Formula_.Or_ (l : List Formula_) : Formula_ :=
  List.foldr or_ false_ l

#eval (Or_ []).toString

#eval (Or_ [pred_var_ (PredName_.mk "X") []]).toString

#eval (Or_ [pred_var_ (PredName_.mk "X") [], pred_var_ (PredName_.mk "Y") []]).toString


/--
  Forall_ [x_0 ... x_n] phi := ∀ x_0 ... ∀ x_n phi
-/
def Formula_.Forall_ (xs : List VarName_) (phi : Formula_) : Formula_ :=
  List.foldr forall_ phi xs

#eval (Forall_ [] (pred_var_ (PredName_.mk "phi") [])).toString

#eval (Forall_ [VarName_.mk "x"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x"])).toString

#eval (Forall_ [VarName_.mk "x", VarName_.mk "y"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x", VarName_.mk "y"])).toString


/--
  Exists_ [x_0 ... x_n] phi := ∃ x_0 ... ∃ x_n phi
-/
def Formula_.Exists_ (xs : List VarName_) (phi : Formula_) : Formula_ :=
  List.foldr exists_ phi xs

#eval (Exists_ [] (pred_var_ (PredName_.mk "phi") [])).toString

#eval (Exists_ [VarName_.mk "x"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x"])).toString

#eval (Exists_ [VarName_.mk "x", VarName_.mk "y"] (pred_var_ (PredName_.mk "phi") [VarName_.mk "x", VarName_.mk "y"])).toString


/--
  `Formula_.no_abbrev F` := True if and only if there does not exist a subformula of the formula `F` of the form `false_`, `and_`, `or_`, `iff_`, or `exists_`.
-/
def Formula_.no_abbrev :
  Formula_ → Prop
  | pred_const_ _ _ => True
  | pred_var_ _ _ => True
  | eq_ _ _ => True
  | true_ => True
  | false_ => False
  | not_ phi => phi.no_abbrev
  | imp_ phi psi => phi.no_abbrev ∧ psi.no_abbrev
  | and_ _ _ => False
  | or_ _ _ => False
  | iff_ _ _ => False
  | forall_ _ phi => phi.no_abbrev
  | exists_ _ _ => False
  | def_ _ _ => True


#lint
