import FOL.LN.Binders
import FOL.LN.Semantics
import MathlibExtra.List
import MathlibExtra.Finset

set_option autoImplicit false


namespace LN

open Var Formula


def Var.open
  (j : ℕ)
  (v : Var) :
  Var → Var
  | free_ x => free_ x
  | bound_ i =>
      if i < j
      then bound_ i
      else
        if i = j
        then v
        else bound_ (i - 1)


def Formula.open
  (j : ℕ)
  (v : Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.open j v))
  | not_ phi => not_ (Formula.open j v phi)
  | imp_ phi psi => imp_ (Formula.open j v phi) (Formula.open j v psi)
  | forall_ x phi => forall_ x (Formula.open (j + 1) v phi)


def Var.openList
  (j : Nat)
  (us : List Var) : Var → Var
  | free_ x => free_ x
  | bound_ i =>
      if i < j
      then bound_ i
      else
        let i := i - j
        if _ : i < us.length
        then us[i]
        else bound_ (i - us.length + j)


def Formula.openList
  (j : ℕ)
  (us : List Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.openList j us))
  | not_ phi => not_ (Formula.openList j us phi)
  | imp_ phi psi => imp_ (Formula.openList j us phi) (Formula.openList j us psi)
  | forall_ x phi => forall_ x (Formula.openList (j + 1) us phi)


def Var.close
  (j : ℕ)
  (v : Var) :
  Var → Var
  | free_ x =>
      if free_ x = v
      then bound_ j
      else free_ x
  | bound_ i =>
      if i < j
      then bound_ i
      else bound_ (i + 1)


def Formula.close
  (j : ℕ)
  (v : Var) :
  Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.close j v))
  | not_ phi => not_ (Formula.close j v phi)
  | imp_ phi psi => imp_ (Formula.close j v phi) (Formula.close j v psi)
  | forall_ x phi => forall_ x (Formula.close (1 + j) v phi)


def Var.subst (v t : Var) : Var → Var
  | free_ x =>
      if v = free_ x
      then t
      else free_ x
  | bound_ i => bound_ i


def Formula.subst (v t : Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.subst v t))
  | not_ phi => not_ (Formula.subst v t phi)
  | imp_ phi psi => imp_ (Formula.subst v t phi) (Formula.subst v t psi)
  | forall_ x phi => forall_ x (Formula.subst v t phi)


def Var.substFun (σ : Var → Var) : Var → Var
  | free_ x => σ (free_ x)
  | bound_ i => bound_ i


def Formula.substFun (σ : Var → Var) : Formula → Formula
  | pred_ X vs => pred_ X (vs.map (Var.substFun σ))
  | not_ phi => not_ (phi.substFun σ)
  | imp_ phi psi => imp_ (phi.substFun σ) (psi.substFun σ)
  | forall_ x phi => forall_ x (phi.substFun σ)


def Formula.predSub
  (τ : String → ℕ → Formula) :
  Formula → Formula
  | pred_ X vs => Formula.openList 0 vs (τ X vs.length)
  | not_ phi => not_ (phi.predSub τ)
  | imp_ phi psi => imp_ (phi.predSub τ) (psi.predSub τ)
  | forall_ x phi => forall_ x (phi.predSub τ)


inductive Formula.lc : Formula → Prop
  | pred_
    (X : String)
    (vs : List Var) :
    (∀ (v : Var), v ∈ vs → v.isFree) →
    lc (pred_ X vs)

  | not_
    (phi : Formula) :
    lc phi →
    lc (not_ phi)

  | imp_
    (phi psi : Formula) :
    lc phi →
    lc psi →
    lc (imp_ phi psi)
/-
  | forall_
    (x : String)
    (phi : Formula) :
    (∀ (z : String), lc (Formula.open 0 (Var.free_ z) phi)) →
    lc (forall_ x phi)
-/
  | forall_
    (x : String)
    (phi : Formula)
    (z : String) :
    lc (Formula.openList 0 [Var.free_ z] phi) →
    lc (forall_ x phi)


def Var.lc_at
  (j : ℕ) :
  Var → Prop
  | free_ _ => True
  | bound_ i => i < j


def Formula.lc_at
  (j : ℕ) :
  Formula → Prop
  | pred_ _ vs => ∀ (v : Var), v ∈ vs → Var.lc_at j v
  | not_ phi => Formula.lc_at j phi
  | imp_ phi psi => (Formula.lc_at j phi) ∧ (Formula.lc_at j psi)
  | forall_ _ phi => Formula.lc_at (j + 1) phi

--------------------------------------------------

lemma lc_at_zero_iff_is_free
  (v : Var) :
  Var.lc_at 0 v ↔ v.isFree :=
  by
  cases v
  case free_ x =>
    simp only [Var.lc_at]
    simp only [isFree]
  case bound_ i =>
    simp only [Var.lc_at]
    simp only [isFree]
    simp

--------------------------------------------------

lemma free_var_list_to_string_list
  (vs : List Var)
  (h1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v) :
  ∃ (xs : List String), vs = List.map free_ xs :=
  by
  induction vs
  case nil =>
    apply Exists.intro []
    simp
  case cons hd tl ih =>
    simp at h1

    cases h1
    case intro h1_left h1_right =>
      specialize ih h1_right
      apply Exists.elim ih
      intro xs a1
      cases hd
      case free_ x =>
        apply Exists.intro (x :: xs)
        simp
        exact a1
      case bound_ i =>
        simp only [Var.lc_at] at h1_left
        simp at h1_left

--------------------------------------------------

-- 1.

lemma VarOpenFreeVarSet
  (j : ℕ)
  (z : String)
  (v : Var) :
  (Var.open j (free_ z) v).freeVarSet ⊆ v.freeVarSet ∪ {free_ z} :=
  by
  cases v
  case free_ x =>
    simp only [Var.open]
    simp only [Var.freeVarSet]
    simp
  case bound_ i =>
    simp only [Var.open]
    split_ifs
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 c2 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 c2 =>
      simp only [Var.freeVarSet]
      simp


lemma FormulaOpenFreeVarSet
  (j : ℕ)
  (z : String)
  (F : Formula) :
  (Formula.open j (free_ z) F).freeVarSet ⊆ F.freeVarSet ∪ {free_ z} :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans Var.freeVarSet v ∪ {free_ z}
    · exact VarOpenFreeVarSet j z v
    · apply Finset.union_subset_union_left
      apply Finset.subset_biUnion_of_mem
      simp
      exact a1
  case not_ phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_union_left_right
    · exact phi_ih j
    · exact psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih

--------------------------------------------------

-- 1. for list

lemma VarOpenListFreeVarSet
  (j : ℕ)
  (zs : List String)
  (v : Var) :
  (Var.openList j (zs.map free_) v).freeVarSet ⊆ v.freeVarSet ∪ (zs.map free_).toFinset :=
  by
  cases v
  case free_ x =>
    simp only [Var.openList]
    simp only [Var.freeVarSet]
    simp
  case bound_ i =>
    simp only [Var.openList]
    split_ifs
    case pos c1 =>
      simp only [Var.freeVarSet]
      simp
    case pos c1 c2 =>
      simp
      simp only [Var.freeVarSet]
      simp
    case neg c1 c2 =>
      simp only [Var.freeVarSet]
      simp


lemma FormulaOpenListFreeVarSet
  (j : ℕ)
  (zs : List String)
  (F : Formula) :
  (Formula.openList j (zs.map free_) F).freeVarSet ⊆ F.freeVarSet ∪ (zs.map free_).toFinset :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans v.freeVarSet ∪ (zs.map free_).toFinset
    · exact VarOpenListFreeVarSet j zs v
    · apply Finset.union_subset_union_left
      apply Finset.subset_biUnion_of_mem
      simp
      exact a1
  case not_ phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_union_left_right
    · exact phi_ih j
    · exact psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.freeVarSet]
    apply phi_ih

--------------------------------------------------

-- 2.

lemma VarOpenFreeVarSet'
  (j : ℕ)
  (z : String)
  (v : Var) :
  v.freeVarSet ⊆ (Var.open j (free_ z) v).freeVarSet :=
  by
  cases v
  case free_ x =>
    simp only [Var.open]
    simp only [Var.freeVarSet]
    simp
  case bound_ i =>
    simp only [Var.open]
    split_ifs
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 c2 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 c2 =>
      simp only [Var.freeVarSet]
      simp


lemma FormulaOpenFreeVarSet'
  (j : ℕ)
  (z : String)
  (F : Formula) :
  F.freeVarSet ⊆ (Formula.open j (free_ z) F).freeVarSet :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans Var.freeVarSet (Var.open j (free_ z) v)
    · apply VarOpenFreeVarSet'
    · apply Finset.subset_biUnion_of_mem Var.freeVarSet
      apply List.mem_toFinset.mpr
      exact List.mem_map_of_mem (Var.open j (free_ z)) a1
  case not_ phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_left_right
    · exact phi_ih j
    · exact psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih

--------------------------------------------------

-- 3.

lemma VarCloseFreeVarSet
  (j : ℕ)
  (z : String)
  (v : Var) :
  (Var.close j (free_ z) v).freeVarSet ⊆ v.freeVarSet \ {free_ z} :=
  by
  cases v
  case free_ x =>
    simp only [Var.close]
    split_ifs
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
      simp at c1
      exact c1
  case bound_ i =>
    simp only [Var.close]
    split_ifs
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 =>
      simp only [Var.freeVarSet]
      simp


lemma FormulaCloseFreeVarSet
  (j : ℕ)
  (z : String)
  (F : Formula) :
  (Formula.close j (free_ z) F).freeVarSet ⊆ F.freeVarSet \ {free_ z} :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans Var.freeVarSet v \ {free_ z}
    · exact VarCloseFreeVarSet j z v
    · apply Finset.sdiff_subset_sdiff
      · apply Finset.subset_biUnion_of_mem
        simp
        exact a1
      · simp
  case not_ phi phi_ih =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_diff
    · exact phi_ih j
    · exact psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    apply phi_ih

--------------------------------------------------

-- 4.

lemma VarSubstFreeVarSet
  (z : String)
  (t : Var)
  (v : Var) :
  (Var.subst (Var.free_ z) t v).freeVarSet ⊆ t.freeVarSet ∪ v.freeVarSet \ {Var.free_ z} :=
  by
  cases v
  case free_ x =>
    simp only [Var.subst]
    split_ifs
    case pos c1 =>
      apply Finset.subset_union_left
    case neg c1 =>
      have s1 : Var.freeVarSet (free_ x) \ {free_ z} = {free_ x}
      simp only [Var.freeVarSet]
      simp
      simp at c1
      exact c1

      simp only [s1]
      apply Finset.subset_union_right
  case bound_ i =>
    simp only [Var.subst]
    conv =>
      lhs
      simp only [Var.freeVarSet]
    simp


lemma FormulaSubstFreeVarSet
  (z : String)
  (t : Var)
  (F : Formula) :
  (Formula.subst (Var.free_ z) t F).freeVarSet ⊆ t.freeVarSet ∪ F.freeVarSet \ {Var.free_ z} :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans Var.freeVarSet t ∪ Var.freeVarSet v \ {free_ z}
    · exact VarSubstFreeVarSet z t v
    · apply Finset.union_subset_union_right
      simp only [← List.mem_toFinset] at a1
      apply Finset.sdiff_subset_sdiff
      · apply Finset.subset_biUnion_of_mem Var.freeVarSet a1
      · simp
  case not_ phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    apply Finset.union_subset_left_right_diff
    · exact phi_ih
    · exact psi_ih
  case forall_ x phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih

--------------------------------------------------

lemma VarSubstFreeVarSet'
  (z : String)
  (t : Var)
  (v : Var) :
  v.freeVarSet \ {Var.free_ z} ⊆ (Var.subst (Var.free_ z) t v).freeVarSet :=
  by
  cases v
  case free_ x =>
    simp only [Var.subst]
    split_ifs
    case pos c1 =>
      simp only [c1]
      conv =>
        lhs
        simp only [Var.freeVarSet]
      simp
    case neg c1 =>
      simp only [Var.freeVarSet]
      exact Finset.sdiff_subset
  case bound_ i =>
    conv =>
      lhs
      simp only [Var.freeVarSet]
    simp


lemma FormulaSubstFreeVarSet'
  (z : String)
  (t : Var)
  (F : Formula) :
  F.freeVarSet \ {Var.free_ z} ⊆ (Formula.subst (Var.free_ z) t F).freeVarSet :=
  by
  induction F
  case pred_ X vs =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]

    induction vs
    case nil =>
      simp
    case cons hd tl ih =>
      simp

      have s1 : (Var.freeVarSet hd ∪ Finset.biUnion (List.toFinset tl) Var.freeVarSet) \ {free_ z} = (Var.freeVarSet hd \ {free_ z}) ∪ ((Finset.biUnion (List.toFinset tl) Var.freeVarSet) \ {free_ z})
      exact Finset.union_sdiff_distrib (Var.freeVarSet hd) (Finset.biUnion (List.toFinset tl) Var.freeVarSet) {free_ z}

      simp only [s1]
      exact Finset.union_subset_union (VarSubstFreeVarSet' z t hd) ih
  case not_ phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    apply Finset.diff_union_subset
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih =>
    simp only [Formula.subst]
    simp only [Formula.freeVarSet]
    exact phi_ih

--------------------------------------------------

def str_fun_to_var_fun
  (σ : String → String) :
  Var → Var
  | free_ x => free_ (σ x)
  | bound_ i => bound_ i


lemma SubOpenVar
  (v : Var)
  (σ : String → String)
  (j : ℕ)
  (z : String)
  (h1 : σ z = z) :
  Var.substFun (str_fun_to_var_fun σ) (Var.open j (free_ z) v) =
    Var.open j (free_ z) (Var.substFun (str_fun_to_var_fun σ) v) :=
  by
  cases v
  case free_ x =>
    conv =>
      lhs
      simp only [Var.open]
      simp only [Var.substFun]
      simp only [str_fun_to_var_fun]
    rfl
  case bound_ i =>
    conv =>
      lhs
      simp only [Var.open]
    split_ifs
    case pos c1 =>
      simp only [Var.substFun]
      simp only [Var.open]
      simp only [if_pos c1]
    case pos c1 c2 =>
      simp only [Var.substFun]
      simp only [str_fun_to_var_fun]
      simp only [Var.open]
      simp only [if_neg c1]
      simp only [if_pos c2]
      simp only [h1]
    case neg c1 c2 =>
      simp only [Var.substFun]
      simp only [Var.open]
      simp only [if_neg c1]
      simp only [if_neg c2]

/-
lemma SubCloseVar
  (v : Var)
  (σ : String → String)
  (y : String)
  (k : ℕ)
  (h1 : σ y = y)
  (h2 : ∀ (x : String), ¬ y = σ x) :
  Var.substFun (str_fun_to_var_fun σ) (Var.close k (free_ y) v) =
    Var.close (free_ y) k (Var.sub_Var (str_fun_to_var_fun σ) v) :=
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
    simp only [List.map_eq_map_iff]
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
    simp only [List.map_eq_map_iff]
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
  case _ i =>
    cases i
    case zero =>
      simp only [Var.sub_Var]
      simp only [shift]
    case succ n =>
      simp only [Var.sub_Var]
      simp only [shift]
      simp


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
-/
--------------------------------------------------

theorem ShiftVarOpenList
  (D : Type)
  (V : VarAssignment D)
  (j : ℕ)
  (zs : List String)
  (d : D) :
  shift D (V ∘ Var.openList j (List.map free_ zs)) d =
    shift D V d ∘ Var.openList (j + 1) (List.map free_ zs) :=
  by
  funext v
  simp
  cases v
  case _ x =>
    simp only [Var.openList]
    simp only [shift]
    simp
    rfl
  case _ i =>
    cases i
    case zero =>
      simp only [shift]
      simp only [Var.openList]
      simp
    case succ i =>
        simp only [shift]
        simp only [Var.openList]
        simp
        split_ifs
        case _ c1 =>
          have s1 : i + 1 < j + 1
          linarith
          simp only [if_pos s1]
          simp only [Var.openList]
          simp only [c1]
          simp
        case _ c1 c2 =>
          have s1 : ¬ i + 1 < j + 1
          linarith
          simp only [if_neg s1]
          simp only [Var.openList]
          simp only [c1]
          simp
          simp only [c2]
          simp
        case _ c1 c2 =>
          simp
          simp only [Var.openList]
          simp only [c1]
          simp
          simp only [c2]
          simp


lemma HoldsOpenList
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (j : Nat)
  (zs : List String)
  (F : Formula) :
  Holds D I (V ∘ Var.openList j (zs.map Var.free_)) F ↔
    Holds D I V (Formula.openList j (zs.map Var.free_) F) :=
  by
  induction F generalizing V j
  case pred_ X vs =>
    simp only [Holds]
    congr! 1
    simp
  case not_ phi phi_ih =>
    simp only [Holds]
    congr! 1
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Holds]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ _ phi phi_ih =>
    simp only [Holds]
    apply forall_congr'
    intro d
    simp only [← phi_ih]
    congr!
    apply ShiftVarOpenList

--------------------------------------------------

theorem ShiftListVarOpenList
  (D : Type)
  (V : VarAssignment D)
  (xs : List String) :
  V ∘ Var.openList 0 (List.map free_ xs) =
    shiftList D V (List.map (V ∘ free_) xs) :=
  by
  induction xs
  case nil =>
    funext v
    simp
    simp only [shiftList]
    cases v
    case _ x =>
      simp only [Var.openList]
    case _ i =>
      simp only [Var.openList]
      split
      case _ c1 =>
        rfl
      case _ c1 =>
        simp
  case _ hd tl ih =>
    funext v
    simp
    simp only [shiftList]
    cases v
    case _ x =>
      simp only [shift]
      simp only [← ih]
      simp only [Var.openList]
      simp
      rfl
    case _ i =>
      cases i
      case zero =>
        simp only [shift]
        simp only [Var.openList]
        simp
      case succ i =>
        simp only [shift]
        simp only [← ih]
        simp
        simp only [Var.openList]
        simp


lemma lc_at_iff_lc
  (F : Formula) :
  lc_at 0 F ↔ lc F :=
  by
  constructor
  · intro a1
    sorry
  · intro a1
    sorry


theorem HoldsCoincideVar
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (h1 : ∀ (v : Var), occursFreeIn v F → V v = V' v) :
  Holds D I V F ↔ Holds D I V' F :=
  by
  induction F generalizing V V'
  case pred_ X vs =>
    simp only [occursFreeIn] at h1

    simp only [Holds]
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case not_ phi phi_ih =>
    simp only [occursFreeIn] at h1

    simp only [Holds]
    congr! 1
    exact phi_ih V V' h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Holds]
    congr! 1
    · apply phi_ih
      intro v a1
      apply h1
      simp only [occursFreeIn]
      tauto
    · apply psi_ih
      intro v a1
      apply h1
      simp only [occursFreeIn]
      tauto
  case forall_ x phi phi_ih =>
    simp only [occursFreeIn] at h1

    simp only [Holds]
    apply forall_congr'
    intro d
    apply phi_ih
    intro v a1
    cases v
    case free_ x =>
      simp only [shift]
      apply h1
      exact a1
    case bound_ i =>
      cases i
      case zero =>
        simp only [shift]
      case succ i =>
        simp only [shift]
        apply h1
        simp only [lift]
        exact a1


lemma HoldsShift
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (F : Formula)
  (z : String)
  (h1 : ¬ occursFreeIn (free_ z) F) :
  (∀ (d : D), Holds D I (shift D V d) F) ↔ ∀ (d : D), Holds D I (Function.updateITE V (free_ z) d ∘ Var.openList 0 [free_ z]) F :=
  by
  apply forall_congr'
  intro d
  apply HoldsCoincideVar
  intro v a1
  simp
  simp only [Function.updateITE]
  cases v
  case _ x' =>
    simp only [shift]
    simp only [Var.openList]
    split_ifs
    case _ c1 =>
      simp at c1
      simp only [← c1] at h1
      contradiction
    case _ c1 =>
      rfl
  case _ i =>
    cases i
    case zero =>
      simp only [shift]
      simp only [Var.openList]
      simp
    case succ i =>
      simp only [shift]
      simp only [Var.openList]
      simp


lemma HoldsForall
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (x : String)
  (F : Formula)
  (z : String)
  (h1 : ¬ occursFreeIn (free_ z) F) :
  Holds D I V (forall_ x F) ↔ ∀ (d : D), Holds D I (Function.updateITE V (free_ z) d) (Formula.openList 0 [free_ z] F) :=
  by
  simp only [Holds]
  simp only [HoldsShift D I V F z h1]
  apply forall_congr'
  intro d
  obtain s1 := HoldsOpenList D I (Function.updateITE V (free_ z) d) 0 [z] F
  simp at s1
  exact s1


theorem extracted_1
  (D : Type)
  (V : VarAssignment D)
  (j : ℕ)
  (z : String)
  (d : D) :
  shift D V d ∘ Var.close (j + 1) (free_ z) = shift D (V ∘ Var.close j (free_ z)) d :=
  by
  funext v
  simp
  cases v
  case _ x =>
    conv =>
      rhs
      simp only [shift]
      simp
    simp only [Var.close]
    simp
    split_ifs
    case _ c1 =>
      simp only [shift]
    case _ c1 =>
      simp only [shift]
  case _ i =>
    cases i
    case zero =>
      conv =>
        rhs
        simp only [shift]
      simp only [Var.close]
      simp
      simp only [shift]
    case succ i =>
      conv =>
        rhs
        simp only [shift]
        simp
        simp only [Var.close]
      simp only [Var.close]
      split
      case _ c1 =>
        have s1 : i < j
        linarith
        simp only [if_pos s1]
        simp only [shift]
      case _ c1 =>
        simp at c1
        have s1 : ¬ i < j
        linarith
        simp only [if_neg s1]
        simp only [shift]


lemma HoldsClose
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (z : String)
  (F : Formula)
  (j : ℕ)
  (h1 : ¬ occursIn (free_ z) F)
  (h2 : F.lc_at j) :
  Holds D I V F ↔ Holds D I (V ∘ Var.close j (free_ z)) (Formula.openList j [free_ z] F) :=
  by
  induction F generalizing V j
  case pred_ X vs =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Formula.openList]
    simp only [Holds]
    congr! 1
    simp
    intro v a1
    specialize h2 v a1
    cases v
    case _ x =>
      simp only [Var.openList]
      simp only [Var.close]

      have s1 : ¬ free_ x = free_ z
      intro contra
      apply h1
      simp only [← contra]
      exact a1

      simp only [if_neg s1]
    case _ i =>
      simp only [Var.lc_at] at h2

      simp only [Var.openList]
      simp
      split_ifs
      simp only [Var.close]
      simp only [if_pos h2]
  case not_ phi phi_ih =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Holds]
    congr! 1
    exact phi_ih V j h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    simp only [occursIn] at h1
    push_neg at h1
    simp only [Formula.lc_at] at h2

    cases h1
    case _ h1_left h1_right =>
      cases h2
      case _ h2_left h2_right =>
        simp only [Holds]
        congr! 1
        · exact phi_ih V j h1_left h2_left
        · exact psi_ih V j h1_right h2_right
  case forall_ x phi phi_ih =>
    simp only [occursIn] at h1
    simp only [Formula.lc_at] at h2

    simp only [Formula.openList]
    simp only [Holds]
    apply forall_congr'
    intro d
    specialize phi_ih (shift D V d) (j + 1) h1 h2
    simp only [phi_ih]
    congr! 1
    apply extracted_1


lemma Formula.OpenListLC
  (F : Formula)
  (j : ℕ)
  (zs : List String)
  (h1 : F.lc_at j) :
  Formula.openList j (zs.map free_) F = F :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    simp
    apply List.map_mem_id
    intro v a1
    specialize h1 v a1
    cases v
    case _ x =>
      simp only [Var.openList]
    case _ i =>
      cases i
      case zero =>
        simp only [Var.lc_at] at h1
        simp only [Var.openList]
        simp only [if_pos h1]
      case succ i =>
        simp only [Var.lc_at] at h1
        simp only [Var.openList]
        simp only [if_pos h1]
  case not_ phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    congr!
    exact phi_ih j h1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    cases h1
    case _ h1_left h1_right =>
      congr!
      · exact phi_ih j h1_left
      · exact psi_ih j h1_right
  case forall_ x phi phi_ih =>
    simp only [Formula.lc_at] at h1

    simp only [Formula.openList]
    simp
    exact phi_ih (j + 1) h1


lemma lc_at_instantiate
  (F : Formula)
  (j : ℕ)
  (zs : List String) :
  Formula.lc_at j (Formula.openList j (zs.map Var.free_) F) ↔ Formula.lc_at (j + zs.length) F :=
  by
  induction F generalizing j zs
  case pred_ X vs =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    constructor
    · intro a1 v a2
      specialize a1 (Var.openList j (List.map free_ zs) v)
      simp at a1
      specialize a1 v a2
      simp at a1
      cases v
      case _ x =>
        simp only [Var.lc_at]
      case _ i =>
        simp only [Var.lc_at]
        simp only [Var.openList] at a1
        split at a1
        case _ c1 =>
          linarith
        case _ c1 =>
          split at a1
          case _ c2 =>
            simp at c2
            exact lt_add_of_tsub_lt_left c2
          case _ c2 =>
            simp only [Var.lc_at] at a1
            simp at a1
    · intro a1 v a2
      cases v
      case _ x =>
        simp only [Var.lc_at]
      case _ i =>
        simp only [Var.lc_at]
        simp at a2
        apply Exists.elim a2
        intro z a3
        clear a2
        cases a3
        case _ a3_left a3_right =>
          specialize a1 z a3_left
          cases z
          case _ x =>
            simp only [Var.openList] at a3_right
            simp at a3_right
          case _ i' =>
            simp only [Var.lc_at] at a1
            simp only [Var.openList] at a3_right
            split at a3_right
            case _ c1 =>
              simp at a3_right
              subst a3_right
              exact c1
            case _ c1 =>
              simp at c1
              simp at a3_right
              split at a3_right
              case _ c2 =>
                contradiction
              case _ c2 =>
                exfalso
                apply c2
                exact Nat.sub_lt_left_of_lt_add c1 a1
  case not_ phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ _ phi phi_ih =>
    simp only [Formula.openList]
    simp only [Formula.lc_at]
    simp only [phi_ih]
    have s1 : j + 1 + List.length zs = j + List.length zs + 1
    linarith;
    simp only [s1]


example
  (τ : String → ℕ → Formula)
  (j j' : ℕ)
  (zs zs' : List String)
  (F : Formula) :
  predSub τ (Formula.openList j (zs.map free_) F) = Formula.openList j' (zs'.map free_) (predSub τ F) := by
  induction F generalizing j j'
  case pred_ X vs =>
    simp only [predSub]
    simp
    sorry
  case forall_ x phi phi_ih =>
    simp only [predSub]
    simp only [Formula.openList]
    simp only [phi_ih (j + 1) (j' + 1)]
  all_goals
    sorry


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : String → ℕ → Formula)
  (F : Formula)
  (h1 : F.lc) :
  Holds D I V (F.predSub τ) ↔
    Holds D (Interpretation.usingPred D I fun (X : String) (ds : List D) => Holds D I (shiftList D V ds) (τ X ds.length)) V F :=
  by
  induction h1 generalizing V
  case pred_ X vs ih =>
    simp only [predSub]
    simp only [Interpretation.usingPred]
    simp only [Holds]
    simp

    have s1 : ∀ (v : Var), v ∈ vs → Var.lc_at 0 v
    intro v a1
    specialize ih v a1
    cases v
    case _ x =>
      simp only [Var.lc_at]
    case _ i =>
      simp only [Var.isFree] at ih

    obtain s2 := free_var_list_to_string_list vs s1
    apply Exists.elim s2
    intro zs a1

    obtain s3 := HoldsOpenList D I V 0 zs (τ X (List.length vs))
    simp only [← a1] at s3
    simp only [← s3]
    clear s2

    congr! 1
    simp only [a1]
    simp
    simp only [ShiftListVarOpenList]
  case forall_ x phi z ih_1 ih_2 =>
    simp only [← lc_at_iff_lc] at ih_1

    simp only [predSub]

    obtain s0 := lc_at_instantiate phi 0 [z]
    simp at s0
    simp only [s0] at ih_1
    clear s0

    simp only [Holds]
    apply forall_congr'
    intro d


    obtain s1 := HoldsForall D I V x (predSub τ phi) z
    simp only [Holds] at s1

    obtain s2 := ShiftListVarOpenList D V [z]
    simp at s2

    obtain s3 := Formula.OpenListLC phi 1 [z] ih_1
    simp at s3

    obtain s4 := HoldsClose D I V z



    sorry
  all_goals
    sorry
