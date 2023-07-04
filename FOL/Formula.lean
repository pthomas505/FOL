import Std.Tactic.Lint.Frontend
import Mathlib.Util.CompileInductive


namespace FOL


/--
  The type of variable names.
-/
inductive VarName : Type
  | mk : String → VarName
  deriving Inhabited, DecidableEq

/--
  The string representation of variable names.
-/
def VarName.toString : VarName → String
  | VarName.mk x => x

instance : ToString VarName :=
  { toString := fun x => x.toString }

instance : Repr VarName :=
  { reprPrec := fun x _ => x.toString.toFormat }


/--
  The type of predicate names.
-/
inductive PredName : Type
  | mk : String → PredName
  deriving Inhabited, DecidableEq

/--
  The string representation of predicate names.
-/
def PredName.toString : PredName → String
  | PredName.mk X => X

instance : ToString PredName :=
  { toString := fun X => X.toString }

instance : Repr PredName :=
  { reprPrec := fun X _ => X.toString.toFormat }


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
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | pred_const_ X xs => s! "({X.toString} {xs.toString})"
  | pred_var_ X xs => s! "({X.toString} {xs.toString})"
  | eq_ x y => s! "({x.toString} = {y.toString})"
  | true_ => "T"
  | false_ => "F"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"
  | forall_ x phi => s! "(∀ {x.toString}. {phi.toString})"
  | exists_ x phi => s! "(∃ {x.toString}. {phi.toString})"


instance : ToString Formula :=
  { toString := fun F => F.toString }

instance : Repr Formula :=
  { reprPrec := fun F _ => F.toString.toFormat }


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

end FOL
