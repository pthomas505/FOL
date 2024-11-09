import FOL.LN.Formula
import FOL.LN.OpenClose
import FOL.LN.Semantics

set_option autoImplicit false


namespace LN

open Var Formula


def Var.sub_Var (σ : Var → Var) : Var → Var
  | free_ x => σ (free_ x)
  | bound_ i => bound_ i


def Formula.sub_Var (σ : Var → Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Var σ))
  | not_ phi => not_ (phi.sub_Var σ)
  | imp_ phi psi => imp_ (phi.sub_Var σ) (psi.sub_Var σ)
  | forall_ x phi => forall_ x (phi.sub_Var σ)

--------------------------------------------------

def Var.sub_Str (σ : String → String) : Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


def Formula.sub_Str (σ : String → String) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.sub_Str σ))
  | not_ phi => not_ (phi.sub_Str σ)
  | imp_ phi psi => imp_ (phi.sub_Str σ) (psi.sub_Str σ)
  | forall_ x phi => forall_ x (phi.sub_Str σ)

--------------------------------------------------

def str_fun_to_var_fun
  (σ : String → String) :
  Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


lemma SubOpenVar
  (v : Var)
  (σ : String → String)
  (k : ℕ)
  (y : String)
  (h1 : σ y = y) :
  Var.sub_Var (str_fun_to_var_fun σ) (openVar k (free_ y) v) =
    openVar k (free_ y) (Var.sub_Var (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case _ x =>
    simp only [openVar]
    simp only [Var.sub_Var]
    simp only [str_fun_to_var_fun]
  case _ i =>
    simp only [openVar]
    split
    case _ c1 =>
      simp only [Var.sub_Var]
      simp only [if_pos c1]
      simp only [str_fun_to_var_fun]
      simp only [h1]
    case _ c1 =>
      simp only [Var.sub_Var]
      simp only [if_neg c1]


lemma SubCloseVar
  (v : Var)
  (σ : String → String)
  (y : String)
  (k : ℕ)
  (h1 : σ y = y)
  (h2 : ∀ (x : String), ¬ y = σ x) :
  Var.sub_Var (str_fun_to_var_fun σ) (closeVar (free_ y) k v) =
    closeVar (free_ y) k (Var.sub_Var (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case free_ x =>
    simp only [closeVar]
    by_cases c1 : y = x
    · subst c1
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      simp only [h1]
      simp
    · simp
      simp only [if_neg c1]
      simp only [Var.sub_Var]
      simp only [str_fun_to_var_fun]
      specialize h2 x
      simp only [if_neg h2]
  case bound_ i =>
    simp only [closeVar]
    simp only [Var.sub_Var]


lemma SubOpenFormula
  (F : Formula)
  (σ : String → String)
  (k : ℕ)
  (x : String)
  (h1 : σ x = x) :
  Formula.sub_Var (str_fun_to_var_fun σ) (openFormulaAux k (free_ x) F) =
    openFormulaAux k (free_ x) (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    simp
    intro v _
    exact SubOpenVar v σ k x h1
  case not_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [openFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih


lemma SubCloseFormula
  (F : Formula)
  (σ : String → String)
  (x : String)
  (k : ℕ)
  (h1 : σ x = x)
  (h2 : ∀ (y : String), ¬ x = σ y) :
  Formula.sub_Var (str_fun_to_var_fun σ) (closeFormulaAux (free_ x) k F) = closeFormulaAux (free_ x) k (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing k
  case pred_ X vs =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    simp
    intro v _
    exact SubCloseVar v σ x k h1 h2
  case not_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [closeFormulaAux]
    simp only [Formula.sub_Var]
    congr! 1
    apply phi_ih

--------------------------------------------------

theorem shift_sub_Var
  (D : Type)
  (σ : String → String)
  (V : VarAssignment D)
  (d : D) :
  shift D (V ∘ Var.sub_Var (str_fun_to_var_fun σ)) d =
    shift D V d ∘ Var.sub_Var (str_fun_to_var_fun σ) :=
  by
  funext v
  simp
  cases v
  case _ x =>
    simp only [Var.sub_Var]
    simp only [shift]
    simp only [str_fun_to_var_fun]
    simp
    rfl
  case _ i =>
    cases i
    case zero =>
      simp only [Var.sub_Var]
      simp only [shift]
    case succ n =>
      simp only [Var.sub_Var]
      simp only [shift]
      simp
      rfl


theorem HoldsIffSubHolds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (σ : String → String)
  (F : Formula) :
  Holds D I (V ∘ (Var.sub_Var (str_fun_to_var_fun σ))) F ↔
    Holds D I V (Formula.sub_Var (str_fun_to_var_fun σ) F) :=
  by
  induction F generalizing V
  case pred_ X vs =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    congr! 1
    simp
  case not_ phi phi_ih =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ phi phi_ih =>
    simp only [Formula.sub_Var]
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr!
    apply shift_sub_Var
