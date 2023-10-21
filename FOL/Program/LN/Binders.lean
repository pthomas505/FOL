import FOL.Program.LN.Formula
import FOL.Tactics


namespace LN

open Formula


/--
  Var.isFree v := True if and only if v is a free variable.
-/
def Var.isFree : Var → Prop
  | free_ _ => True
  | bound_ _ => False

instance (v : Var) : Decidable v.isFree :=
  by
  cases v
  case free_ x =>
    simp only [Var.isFree]
    exact decidableTrue
  case bound_ i =>
    simp only [Var.isFree]
    exact decidableFalse


/--
  Var.isBound v := True if and only if v is a bound variable.
-/
def Var.isBound : Var → Prop
  | free_ _ => False
  | bound_ _ => True

instance (v : Var) : Decidable v.isBound :=
  by
  cases v
  case free_ x =>
    simp only [Var.isBound]
    exact decidableFalse
  case bound_ i =>
    simp only [Var.isBound]
    exact decidableTrue

--------------------------------------------------

/--
  Formula.var F := The set of all of the variables that have an occurrence in the formula F.
-/
def Formula.varSet : Formula → Finset Var
  | pred_ _ vs => vs.toFinset
  | not_ phi => phi.varSet
  | imp_ phi psi => phi.varSet ∪ psi.varSet
  | forall_ _ phi => phi.varSet


/--
  occursIn v F := True if and only if there is an occurrence of the variable v in the formula F.
-/
def occursIn (v : Var) : Formula → Prop
  | pred_ _ vs => v ∈ vs
  | not_ phi => occursIn v phi
  | imp_ phi psi => occursIn v phi ∨ occursIn v psi
  | forall_ _ phi => occursIn v phi


instance (v : Var) (F : Formula) : Decidable (occursIn v F) :=
  by
  induction F
  all_goals
    unfold occursIn
    infer_instance

--------------------------------------------------

/--
  Formula.freeVarSet F := The set of all of the free variables that have an occurrence in the formula F.
-/
def Formula.freeVarSet (F : Formula) : Finset Var :=
  F.varSet.filter Var.isFree

/--
  Formula.boundVarSet F := The set of all of the bound variables that have an occurrence in the formula F.
-/
def Formula.boundVarSet (F : Formula) : Finset Var :=
  F.varSet.filter Var.isBound

--------------------------------------------------

theorem occursIn_iff_mem_varSet
  (v : Var)
  (F : Formula) :
  occursIn v F ↔ v ∈ F.varSet :=
  by
  induction F
  case pred_ X vs =>
    simp only [occursIn]
    simp only [varSet]
    simp
  case not_ phi phi_ih =>
    simp only [occursIn]
    simp only [varSet]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn]
    simp only [varSet]
    simp
    congr!
  case forall_ _ phi phi_ih =>
    simp only [occursIn]
    simp only [varSet]
    exact phi_ih


theorem isFreeIn_iff_mem_freeVarSet
  (v : Var)
  (F : Formula) :
  occursIn v F ∧ v.isFree ↔ v ∈ F.freeVarSet :=
  by
  simp only [freeVarSet]
  simp
  intro _
  exact occursIn_iff_mem_varSet v F


theorem isBoundIn_iff_mem_boundVarSet
  (v : Var)
  (F : Formula) :
  occursIn v F ∧ v.isBound ↔ v ∈ F.boundVarSet :=
  by
  simp only [boundVarSet]
  simp
  intro _
  exact occursIn_iff_mem_varSet v F


#lint
