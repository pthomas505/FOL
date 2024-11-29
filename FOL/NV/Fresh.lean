import FOL.NV.Formula

import Mathlib.Tactic
import Mathlib.Data.String.Lemmas


set_option autoImplicit false


/--
  `finset_var_name_max_len xs` := The length of the longest variable name in the finite set of variable names `xs` or 0 if the set is empty.
-/
def finset_var_name_max_len :
  Finset VarName → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 (fun (x : VarName) => x.toString.length)


lemma finset_var_name_max_len_mem
  (x : VarName)
  (xs : Finset VarName)
  (h1 : x ∈ xs) :
  x.length ≤ finset_var_name_max_len xs :=
  by
  induction xs using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1

    cases h1
    case inl c1 =>
      subst c1
      simp only [finset_var_name_max_len]
      simp
    case inr c1 =>
      simp only [finset_var_name_max_len] at ih

      simp only [finset_var_name_max_len]
      simp
      right
      exact ih c1


/--
  `fresh x c xs` := If the variable name `x` is not a member of the finite set of variable names `xs` then `x` is returned. If `x` is a member of `xs` then the character `c` is repeatedly appended to `x` until the resulting variable name is not a member of `xs`. The resulting variable name is then returned.
-/
def fresh
  (x : VarName)
  (c : Char)
  (xs : Finset VarName) :
  VarName :=
  if h : x ∈ xs
  then
    have : finset_var_name_max_len xs - String.length x.toString < finset_var_name_max_len xs + 1 - String.length x.toString :=
      by
      obtain s1 := finset_var_name_max_len_mem x xs h
      simp only [tsub_lt_tsub_iff_right s1]
      simp
  fresh (VarName.mk (x.toString ++ c.toString)) c xs
  else x
  termination_by finset_var_name_max_len xs + 1 - x.length


lemma fresh_not_mem
  (x : VarName)
  (c : Char)
  (xs : Finset VarName) :
  fresh x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_var_name_max_len xs - String.length x.toString < finset_var_name_max_len xs + 1 - String.length x.toString :=
    by
    obtain s1 := finset_var_name_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s1]
    simp
  by
    unfold fresh
    simp
    simp only [if_pos h]
    apply fresh_not_mem
  else by
    unfold fresh
    simp
    simp [if_neg h]
    exact h
  termination_by finset_var_name_max_len xs + 1 - x.length


#lint
