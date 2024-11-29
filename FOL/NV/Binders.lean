import FOL.NV.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula


/-
[margaris]
pg. 48

An occurrence of a variable `v` in a formula `P` is bound if and only if it occurs in a subformula of `P` of the form `\forall v Q`. An occurrence of `v` in `P` is free if and only if it is not a bound occurrence. The variable `v` is free or bound in `P` according as it has a free or bound occurrence in `P`.
-/

/--
  Formula.varSet F := The set of all of the variables that have an occurrence in the formula F.
-/
def Formula.varSet : Formula → Finset VarName
  | pred_const_ _ xs => xs.toFinset
  | pred_var_ _ xs => xs.toFinset
  | eq_ x y => {x, y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.varSet
  | imp_ phi psi => phi.varSet ∪ psi.varSet
  | and_ phi psi => phi.varSet ∪ psi.varSet
  | or_ phi psi => phi.varSet ∪ psi.varSet
  | iff_ phi psi => phi.varSet ∪ psi.varSet
  | forall_ x phi => phi.varSet ∪ {x}
  | exists_ x phi => phi.varSet ∪ {x}
  | def_ _ xs => xs.toFinset


/--
  occursIn v F := True if and only if there is an occurrence of the variable v in the formula F.
-/
def occursIn (v : VarName) : Formula → Prop
  | pred_const_ _ xs => v ∈ xs
  | pred_var_ _ xs => v ∈ xs
  | eq_ x y => v = x ∨ v = y
  | true_ => False
  | false_ => False
  | not_ phi => occursIn v phi
  | imp_ phi psi => occursIn v phi ∨ occursIn v psi
  | and_ phi psi => occursIn v phi ∨ occursIn v psi
  | or_ phi psi => occursIn v phi ∨ occursIn v psi
  | iff_ phi psi => occursIn v phi ∨ occursIn v psi
  | forall_ x phi => v = x ∨ occursIn v phi
  | exists_ x phi => v = x ∨ occursIn v phi
  | def_ _ xs => v ∈ xs


instance (v : VarName) (F : Formula) : Decidable (occursIn v F) :=
  by
  induction F
  all_goals
    simp only [occursIn]
    infer_instance


/--
  Formula.boundVarSet F := The set of all of the variables that have a bound occurrence in the formula F.
-/
def Formula.boundVarSet : Formula → Finset VarName
  | pred_const_ _ _ => ∅
  | pred_var_ _ _ => ∅
  | eq_ _ _ => ∅
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.boundVarSet
  | imp_ phi psi => phi.boundVarSet ∪ psi.boundVarSet
  | and_ phi psi => phi.boundVarSet ∪ psi.boundVarSet
  | or_ phi psi => phi.boundVarSet ∪ psi.boundVarSet
  | iff_ phi psi => phi.boundVarSet ∪ psi.boundVarSet
  | forall_ x phi => phi.boundVarSet ∪ {x}
  | exists_ x phi => phi.boundVarSet ∪ {x}
  | def_ _ _ => ∅


/--
  isBoundIn v F := True if and only if there is a bound occurrence of the variable v in the formula F.
-/
def isBoundIn (v : VarName) : Formula → Prop
  | pred_const_ _ _ => False
  | pred_var_ _ _ => False
  | eq_ _ _ => False
  | true_ => False
  | false_ => False
  | not_ phi => isBoundIn v phi
  | imp_ phi psi => isBoundIn v phi ∨ isBoundIn v psi
  | and_ phi psi => isBoundIn v phi ∨ isBoundIn v psi
  | or_ phi psi => isBoundIn v phi ∨ isBoundIn v psi
  | iff_ phi psi => isBoundIn v phi ∨ isBoundIn v psi
  | forall_ x phi => v = x ∨ isBoundIn v phi
  | exists_ x phi => v = x ∨ isBoundIn v phi
  | def_ _ _ => False


instance (v : VarName) (F : Formula) : Decidable (isBoundIn v F) :=
  by
  induction F
  all_goals
    simp only [isBoundIn]
    infer_instance


/--
  Formula.freeVarSet F := The set of all of the variables that have a free occurrence in the formula F.
-/
def Formula.freeVarSet : Formula → Finset VarName
  | pred_const_ _ xs => xs.toFinset
  | pred_var_ _ xs => xs.toFinset
  | eq_ x y => {x, y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | and_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | or_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | iff_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ x phi => phi.freeVarSet \ {x}
  | exists_ x phi => phi.freeVarSet \ {x}
  | def_ _ xs => xs.toFinset


/--
  isFreeIn v F := True if and only if there is a free occurrence of the variable v in the formula F.
-/
def isFreeIn (v : VarName) : Formula → Prop
  | pred_const_ _ xs => v ∈ xs
  | pred_var_ _ xs => v ∈ xs
  | eq_ x y => v = x ∨ v = y
  | true_ => False
  | false_ => False
  | not_ phi => isFreeIn v phi
  | imp_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | and_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | or_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | iff_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | forall_ x phi => ¬ v = x ∧ isFreeIn v phi
  | exists_ x phi => ¬ v = x ∧ isFreeIn v phi
  | def_ _ xs => v ∈ xs


instance (v : VarName) (F : Formula) : Decidable (isFreeIn v F) :=
  by
  induction F
  all_goals
    simp only [isFreeIn]
    infer_instance


/--
  isFreeInInd v F := True if and only if there is a free occurrence of the variable v in the formula F.
-/
inductive isFreeInInd
  (v : VarName) :
  Formula → Prop

  | pred_const_
    (X : PredName)
    (xs : List VarName) :
    v ∈ xs →
    isFreeInInd v (pred_const_ X xs)

  | pred_var_
    (X : PredName)
    (xs : List VarName) :
    v ∈ xs →
    isFreeInInd v (pred_var_ X xs)

  | eq_
    (x y : VarName) :
    v = x ∨ v = y →
    isFreeInInd v (eq_ x y)

  | not_
    (phi : Formula) :
    isFreeInInd v phi →
    isFreeInInd v (not_ phi)

  | imp_left_
    (phi psi : Formula) :
    isFreeInInd v phi →
    isFreeInInd v (imp_ phi psi)

  | imp_right_
    (phi psi : Formula) :
    isFreeInInd v psi →
    isFreeInInd v (imp_ phi psi)

  | and_left_
    (phi psi : Formula) :
    isFreeInInd v phi →
    isFreeInInd v (and_ phi psi)

  | and_right_
    (phi psi : Formula) :
    isFreeInInd v psi →
    isFreeInInd v (and_ phi psi)

  | or_left_
    (phi psi : Formula) :
    isFreeInInd v phi →
    isFreeInInd v (or_ phi psi)

  | or_right_
    (phi psi : Formula) :
    isFreeInInd v psi →
    isFreeInInd v (or_ phi psi)

  | iff_left_
    (phi psi : Formula) :
    isFreeInInd v phi →
    isFreeInInd v (iff_ phi psi)

  | iff_right_
    (phi psi : Formula) :
    isFreeInInd v psi →
    isFreeInInd v (iff_ phi psi)

  | forall_
    (x : VarName)
    (phi : Formula) :
    ¬ v = x →
    isFreeInInd v phi →
    isFreeInInd v (forall_ x phi)

  | exists_
    (x : VarName)
    (phi : Formula) :
    ¬ v = x →
    isFreeInInd v phi →
    isFreeInInd v (exists_ x phi)

  | def_
    (X : DefName)
    (xs : List VarName) :
    v ∈ xs →
    isFreeInInd v (def_ X xs)


/--
  Formula.predVarSet F := The set of all of the predicate variables that have an occurrence in the formula F.
-/
def Formula.predVarSet : Formula → Finset (PredName × ℕ)
  | pred_const_ _ _ => ∅
  | pred_var_ X xs => {(X, xs.length)}
  | eq_ _ _ => ∅
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.predVarSet
  | imp_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | and_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | or_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | iff_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | forall_ _ phi => phi.predVarSet
  | exists_ _ phi => phi.predVarSet
  | def_ _ _ => ∅


/--
  predVarOccursIn P n F := True if and only if there is an occurrence of the predicate variable named P of arity n in the formula F.
-/
def predVarOccursIn (P : PredName) (n : ℕ) : Formula → Prop
  | pred_const_ _ _ => False
  | pred_var_ X xs => P = X ∧ n = xs.length
  | eq_ _ _ => False
  | true_ => False
  | false_ => False
  | not_ phi => predVarOccursIn P n phi
  | imp_ phi psi => predVarOccursIn P n phi ∨ predVarOccursIn P n psi
  | and_ phi psi => predVarOccursIn P n phi ∨ predVarOccursIn P n psi
  | or_ phi psi => predVarOccursIn P n phi ∨ predVarOccursIn P n psi
  | iff_ phi psi => predVarOccursIn P n phi ∨ predVarOccursIn P n psi
  | forall_ _ phi => predVarOccursIn P n phi
  | exists_ _ phi => predVarOccursIn P n phi
  | def_ _ _ => False


instance (P : PredName) (n : ℕ) (F : Formula) : Decidable (predVarOccursIn P n F) :=
  by
  induction F
  all_goals
    simp only [predVarOccursIn]
    infer_instance


theorem occursIn_iff_mem_varSet
  (v : VarName)
  (F : Formula) :
  occursIn v F ↔ v ∈ F.varSet :=
  by
  induction F
  all_goals
    simp only [occursIn]
    simp only [Formula.varSet]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem isBoundIn_iff_mem_boundVarSet
  (v : VarName)
  (F : Formula) :
  isBoundIn v F ↔ v ∈ F.boundVarSet :=
  by
  induction F
  all_goals
    simp only [isBoundIn]
    simp only [Formula.boundVarSet]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem isFreeIn_iff_mem_freeVarSet
  (v : VarName)
  (F : Formula) :
  isFreeIn v F ↔ v ∈ F.freeVarSet :=
  by
  induction F
  all_goals
    simp only [isFreeIn]
    simp only [Formula.freeVarSet]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem isFreeIn_imp_isFreeInInd
  (v : VarName)
  (F : Formula)
  (h1 : isFreeIn v F) :
  isFreeInInd v F :=
  by
  induction F
  any_goals
    simp only [isFreeIn] at h1
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    first | exact isFreeInInd.pred_const_ X xs h1 | exact isFreeInInd.pred_var_ X xs h1 | exact isFreeInInd.eq_ x y h1 | exact isFreeInInd.def_ X xs h1
  case not_ phi phi_ih =>
    apply isFreeInInd.not_
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    cases h1
    case inl c1 =>
      first | apply isFreeInInd.imp_left_ | apply isFreeInInd.and_left_ | apply isFreeInInd.or_left_ | apply isFreeInInd.iff_left_
      exact phi_ih c1
    case inr c1 =>
      first | apply isFreeInInd.imp_right_ | apply isFreeInInd.and_right_ | apply isFreeInInd.or_right_ | apply isFreeInInd.iff_right_
      exact psi_ih c1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h1
    case _ h1_left h1_right =>
      first | apply isFreeInInd.forall_ | apply isFreeInInd.exists_
      · exact h1_left
      · exact phi_ih h1_right


theorem isFreeInInd_imp_isFreeIn
  (v : VarName)
  (F : Formula)
  (h1 : isFreeInInd v F) :
  isFreeIn v F :=
  by
  induction h1
  all_goals
    simp only [isFreeIn]
    tauto


theorem isFreeIn_iff_isFreeInInd
  (v : VarName)
  (F : Formula) :
  isFreeIn v F ↔ isFreeInInd v F :=
  by
  constructor
  · exact isFreeIn_imp_isFreeInInd v F
  · exact isFreeInInd_imp_isFreeIn v F


theorem predVarOccursIn_iff_mem_predVarSet
  (P : PredName)
  (n : ℕ)
  (F : Formula) :
  predVarOccursIn P n F ↔ (P, n) ∈ F.predVarSet :=
  by
  induction F
  all_goals
    simp only [predVarOccursIn]
    simp only [Formula.predVarSet]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    tauto


theorem isBoundIn_imp_occursIn
  (v : VarName)
  (F : Formula)
  (h1 : isBoundIn v F) :
  occursIn v F :=
  by
  induction F
  all_goals
    simp only [isBoundIn] at h1
  all_goals
    simp only [occursIn]
    tauto


theorem isFreeIn_imp_occursIn
  (v : VarName)
  (F : Formula)
  (h1 : isFreeIn v F) :
  occursIn v F :=
  by
  induction F
  all_goals
    simp only [isFreeIn] at h1
  all_goals
    simp only [occursIn]
    tauto


#lint
