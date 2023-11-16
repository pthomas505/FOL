import FOL.LN.Binders
import FOL.LN.Semantics
import FOL.List
import FOL.Finset
import FOL.Tactics

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
      else bound_ (1 + i)


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

  | forall_
    (x : String)
    (phi : Formula) :
    (∀ (z : String), lc (Formula.open 0 (Var.free_ z) phi)) →
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
      apply List.get_mem
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
    case _ c1 c2 =>
      simp only [Var.freeVarSet]
      simp
    case _ c1 c2 =>
      simp only [Var.freeVarSet]


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

-- leftmost and middle are reversed from paper

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
      exact Finset.sdiff_subset {free_ x} {free_ z}
  case bound_ i =>
    conv =>
      lhs
      simp only [Var.freeVarSet]


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
