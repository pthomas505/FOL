import FOL.NV.Formula

import Mathlib.Tactic
import Mathlib.Data.String.Lemmas


set_option autoImplicit false


/--
  `finset_var_name_max_len xs` := The length of the longest variable name in the finite set of variable names `xs` or 0 if the set is empty.
-/
def finset_var_name_max_len :
  Finset VarName_ → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 (fun (x : VarName_) => x.length)


lemma finset_var_name_max_len_mem
  (x : VarName_)
  (xs : Finset VarName_)
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
  (x : VarName_)
  (c : Char)
  (xs : Finset VarName_) :
  VarName_ :=
  if h : x ∈ xs
  then
    have : finset_var_name_max_len xs - x.length < finset_var_name_max_len xs + 1 - x.length :=
    by
      apply Nat.sub_lt_sub_right
      · apply finset_var_name_max_len_mem
        exact h
      · apply lt_add_one
  fresh (VarName_.mk (x.toString ++ c.toString)) c xs
  else x
  termination_by finset_var_name_max_len xs + 1 - x.length


lemma fresh_not_mem
  (x : VarName_)
  (c : Char)
  (xs : Finset VarName_) :
  fresh x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_var_name_max_len xs - x.length < finset_var_name_max_len xs + 1 - x.length :=
  by
    apply Nat.sub_lt_sub_right
    · apply finset_var_name_max_len_mem
      exact h
    · apply lt_add_one
  by
    unfold fresh
    split_ifs
    apply fresh_not_mem
  else by
    unfold fresh
    split_ifs
    exact h
  termination_by finset_var_name_max_len xs + 1 - x.length


#lint
