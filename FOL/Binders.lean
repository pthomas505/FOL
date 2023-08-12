import FOL.Formula
import FOL.Tactics


namespace FOL

open Formula


/-
[margaris]
pg. 48

An occurrence of a variable $v$ in a formula $P$ is bound if and only if it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence of $v$ in $P$ is free if and only if it is not a bound occurrence. The variable $v$ is free or bound in $P$ according as it has a free or bound occurrence in $P$.
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
    unfold occursIn
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
    unfold isBoundIn
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
    unfold isFreeIn
    infer_instance


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
    unfold predVarOccursIn
    infer_instance


theorem occursIn_iff_mem_varSet
  (v : VarName)
  (F : Formula) :
  occursIn v F ↔ v ∈ F.varSet :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs =>
    unfold occursIn
    unfold Formula.varSet
    simp
  case eq_ x y =>
    unfold occursIn
    unfold Formula.varSet
    simp
  case true_ | false_ =>
    unfold occursIn
    unfold Formula.varSet
    simp
  case not_ _ phi_ih =>
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold occursIn
    unfold Formula.varSet
    simp
    simp only [phi_ih, psi_ih]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold occursIn
    unfold Formula.varSet
    simp
    simp only [phi_ih]
    tauto
  case def_ X xs =>
    unfold occursIn
    unfold Formula.varSet
    simp


theorem isBoundIn_iff_mem_boundVarSet
  (v : VarName)
  (F : Formula) :
  isBoundIn v F ↔ v ∈ F.boundVarSet :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    simp
  case eq_ x y =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    simp
  case true_ | false_ =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    simp
  case not_ phi phi_ih =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    simp
    simp only [phi_ih, psi_ih]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    simp
    simp only [phi_ih]
    tauto
  case def_ X xs =>
    unfold isBoundIn
    unfold Formula.boundVarSet
    simp


theorem isFreeIn_iff_mem_freeVarSet
  (v : VarName)
  (F : Formula) :
  isFreeIn v F ↔ v ∈ F.freeVarSet :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs =>
    unfold isFreeIn
    unfold Formula.freeVarSet
    simp
  case eq_ x y =>
    unfold isFreeIn
    unfold Formula.freeVarSet
    simp
  case true_ | false_ =>
    unfold isFreeIn
    unfold Formula.freeVarSet
    simp
  case not_ _ phi_ih =>
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isFreeIn
    unfold Formula.freeVarSet
    simp
    simp only [phi_ih, psi_ih]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isFreeIn
    unfold Formula.freeVarSet
    simp
    simp only [phi_ih]
    tauto
  case def_ X xs =>
    unfold isFreeIn
    unfold Formula.freeVarSet
    simp


theorem predVarOccursIn_iff_mem_predVarSet
  (P : PredName)
  (n : ℕ) 
  (F : Formula) :
  predVarOccursIn P n F ↔ (P, n) ∈ F.predVarSet :=
  by
  induction F
  case pred_const_ X xs =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    simp
  case pred_var_ X xs =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    simp
  case eq_ x y =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    simp
  case true_ | false_ =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    simp
  case not_ _ phi_ih =>
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    simp
    simp only [phi_ih, psi_ih]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    exact phi_ih
  case def_ X xs =>
    unfold predVarOccursIn
    unfold Formula.predVarSet
    simp


theorem isBoundIn_imp_occursIn
  (v : VarName)
  (F : Formula)
  (h1 : isBoundIn v F) :
  occursIn v F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs =>
    unfold isBoundIn at h1

    contradiction
  case eq_ x y =>
    unfold isBoundIn at h1

    contradiction
  case true_ | false_ =>
    unfold isBoundIn at h1

    contradiction
  case not_ phi phi_ih =>
    unfold isBoundIn at h1

    unfold occursIn
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isBoundIn at h1

    unfold occursIn
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isBoundIn at h1

    unfold occursIn
    tauto
  case def_ X xs =>
    unfold isBoundIn at h1

    contradiction


theorem isFreeIn_imp_occursIn
  (v : VarName)
  (F : Formula)
  (h1 : isFreeIn v F) :
  occursIn v F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs =>
    unfold isFreeIn at h1

    unfold occursIn
    exact h1
  case eq_ x y =>
    unfold isFreeIn at h1

    unfold occursIn
    exact h1
  case true_ | false_ =>
    unfold isFreeIn at h1

    contradiction
  case not_ phi phi_ih =>
    unfold isFreeIn at h1

    unfold occursIn
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isFreeIn at h1

    unfold occursIn
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isFreeIn at h1

    unfold occursIn
    tauto
  case def_ X xs =>
    unfold isFreeIn at h1

    unfold occursIn
    exact h1


#lint

end FOL
