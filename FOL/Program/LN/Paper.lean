import FOL.Program.LN.Binders
import FOL.Program.LN.Semantics
import FOL.List
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

lemma Finset.union_subset_union
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A ⊆ C ∪ E)
  (h2 : B ⊆ D ∪ E) :
  A ∪ B ⊆ C ∪ D ∪ E :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C ∪ E
    · exact h1
    · apply Finset.union_subset_union_left
      exact Finset.subset_union_left C D
  · trans D ∪ E
    · exact h2
    · apply Finset.union_subset_union_left
      exact Finset.subset_union_right C D


lemma Finset.union_subset_diff
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A ⊆ C \ E)
  (h2 : B ⊆ D \ E) :
  A ∪ B ⊆ (C ∪ D) \ E :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C \ E
    · exact h1
    · apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_left C D
      · rfl
  · trans D \ E
    · exact h2
    · apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_right C D
      · rfl

--------------------------------------------------

lemma VarOpenFreeVarSet
  (j : ℕ)
  (y : String)
  (v : Var) :
  (Var.open j (free_ y) v).freeVarSet ⊆ v.freeVarSet ∪ {free_ y} :=
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
  (y : String)
  (F : Formula) :
  (Formula.open j (free_ y) F).freeVarSet ⊆ F.freeVarSet ∪ {free_ y} :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans Var.freeVarSet v ∪ {free_ y}
    · exact VarOpenFreeVarSet j y v
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
    apply Finset.union_subset_union
    · exact phi_ih j
    · exact psi_ih j
  case forall_ x phi phi_ih =>
    simp only [Formula.open]
    simp only [Formula.freeVarSet]
    apply phi_ih


lemma VarCloseFreeVarSet
  (j : ℕ)
  (y : String)
  (v : Var) :
  (Var.close j (free_ y) v).freeVarSet ⊆ v.freeVarSet \ {free_ y} :=
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
  (y : String)
  (F : Formula) :
  (Formula.close j (free_ y) F).freeVarSet ⊆ F.freeVarSet \ {free_ y} :=
  by
  induction F generalizing j
  case pred_ X vs =>
    simp only [Formula.close]
    simp only [Formula.freeVarSet]
    simp
    intro v a1

    trans Var.freeVarSet v \ {free_ y}
    · exact VarCloseFreeVarSet j y v
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
  ∃ xs, vs = List.map free_ xs :=
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
