import Mathlib.Tactic
import Mathlib.Data.String.Lemmas


set_option autoImplicit false


/--
  finset_string_max_len xs := The length of the longest string in the finite set of strings xs or 0 if the set is empty.
-/
def finset_string_max_len :
  Finset String → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 String.length


lemma finset_string_max_len_mem
  (x : String)
  (xs : Finset String)
  (h1 : x ∈ xs) :
  x.length <= finset_string_max_len xs :=
  by
  induction xs using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1

    cases h1
    case inl c1 =>
      subst c1
      simp only [finset_string_max_len]
      simp
    case inr c1 =>
      simp only [finset_string_max_len] at ih

      simp only [finset_string_max_len]
      simp
      right
      exact ih c1


/--
  fresh x c xs := If the variable name x is not a member of the finite set of variable names xs then x is returned. If x is a member of xs then the character c is repeatedly appended to x until the resulting variable name is not a member of xs. The resulting variable name is then returned.
-/
def fresh
  (x : String)
  (c : Char)
  (xs : Finset String) :
  String :=
  if h : x ∈ xs
  then
    have : finset_string_max_len xs - String.length x < finset_string_max_len xs + 1 - String.length x :=
      by
      obtain s1 := finset_string_max_len_mem x xs h
      simp only [tsub_lt_tsub_iff_right s1]
      simp
  fresh (x ++ c.toString) c xs
  else x
  termination_by finset_string_max_len xs + 1 - x.length


lemma fresh_not_mem
  (x : String)
  (c : Char)
  (xs : Finset String) :
  fresh x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_string_max_len xs - String.length x < finset_string_max_len xs + 1 - String.length x :=
    by
    obtain s1 := finset_string_max_len_mem x xs h
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
  termination_by finset_string_max_len xs + 1 - x.length


#lint
