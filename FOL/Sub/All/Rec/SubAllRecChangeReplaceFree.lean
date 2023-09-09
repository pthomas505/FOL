import FOL.Formula
import FOL.Binders
import FOL.FunctionUpdateIte
import FOL.Semantics
import FOL.Tactics

import Mathlib.Data.String.Lemmas


namespace FOL

open Formula


def finset_var_name_max_len :
  Finset VarName → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 (String.length ∘ VarName.toString)


lemma finset_var_name_max_len_mem
  (x : VarName)
  (xs : Finset VarName)
  (h1 : x ∈ xs) :
  x.length <= finset_var_name_max_len xs :=
  by
  induction xs using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1

    cases h1
    case inl c1 =>
      subst c1
      unfold finset_var_name_max_len
      simp
    case inr c1 =>
      unfold finset_var_name_max_len at ih

      unfold finset_var_name_max_len
      simp
      right
      exact ih c1


def variant
  (x : VarName)
  (c : Char)
  (xs : Finset VarName) :
  VarName :=
  if h : x ∈ xs
  then
  have : finset_var_name_max_len xs + 1 - (x.length + c.toString.length) < finset_var_name_max_len xs + 1 - x.length :=
    by
    have s1 : c.toString.length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_var_name_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  variant (VarName.mk (x.toString ++ c.toString)) c xs
  else x
  termination_by variant x _ xs => finset_var_name_max_len xs + 1 - x.length


lemma variant_not_mem
  (x : VarName)
  (c : Char)
  (xs : Finset VarName) :
  variant x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_var_name_max_len xs + 1 - (x.length + c.toString.length) < finset_var_name_max_len xs + 1 - x.length :=
    by
    have s1 : c.toString.length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_var_name_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  by
    unfold variant
    simp
    simp only [if_pos h]
    apply variant_not_mem
  else by
    unfold variant
    simp
    simp [if_neg h]
    exact h
  termination_by variant_not_mem x _ xs => finset_var_name_max_len xs + 1 - x.length


def subVariant
  (σ : VarName → VarName)
  (c : Char) :
  Formula → Formula
| pred_const_ X xs => pred_const_ X (xs.map σ)
| pred_var_ X xs => pred_var_ X (xs.map σ)
| eq_ x y => eq_ (σ x) (σ y)
| true_ => true_
| false_ => false_
| not_ phi => not_ (subVariant σ c phi)
| imp_ phi psi => imp_ (subVariant σ c phi) (subVariant σ c psi)
| and_ phi psi => and_ (subVariant σ c phi) (subVariant σ c psi)
| or_ phi psi => or_ (subVariant σ c phi) (subVariant σ c psi)
| iff_ phi psi => iff_ (subVariant σ c phi) (subVariant σ c psi)
| forall_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((subVariant (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  forall_ x' (subVariant (Function.updateIte σ x x') c phi)
| exists_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((subVariant (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  exists_ x' (subVariant (Function.updateIte σ x x') c phi)
| def_ X xs => def_ X (xs.map σ)


example
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula)
  (x : VarName)
  (h1 : ∀ τ : VarName → VarName, (subVariant τ c F).freeVarSet =
    F.freeVarSet.image τ) :
  let x' :=
      if ∃ (y : VarName), y ∈ F.freeVarSet \ {x} ∧ σ y = x
      then variant x c (subVariant (Function.updateIte σ x x) c F).freeVarSet
      else x
  x' ∉ (F.freeVarSet \ {x}).image σ :=
  by
  have s1 : (F.freeVarSet \ {x}).image σ ⊆ (subVariant (Function.updateIte σ x x) c F).freeVarSet
  calc
        (F.freeVarSet \ {x}).image σ

    _ = (F.freeVarSet \ {x}).image (Function.updateIte σ x x) :=
      by
      apply Finset.image_congr
      unfold Set.EqOn
      intro y a1
      unfold Function.updateIte
      simp at a1
      cases a1
      case _ a1_left a1_right =>
        simp only [if_neg a1_right]

    _ ⊆ F.freeVarSet.image (Function.updateIte σ x x) :=
      by
      apply Finset.image_subset_image
      exact Finset.sdiff_subset (freeVarSet F) {x}

    _ = (subVariant (Function.updateIte σ x x) c F).freeVarSet :=
      by
      symm
      exact h1 (Function.updateIte σ x x)

  split
  case inl c1 =>
    obtain s2 := variant_not_mem x c (freeVarSet (subVariant (Function.updateIte σ x x) c F))
    exact Finset.not_mem_mono s1 s2
  case inr c1 =>
    simp at c1
    simp
    exact c1
