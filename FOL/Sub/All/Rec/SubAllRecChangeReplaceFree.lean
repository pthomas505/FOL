import FOL.Formula
import FOL.Binders
import FOL.FunctionUpdateIte

import Mathlib.Data.String.Lemmas


namespace FOL

open Formula


def List.str_max_len :
  List String → ℕ
| [] => 0
| hd :: tl => max hd.length (List.str_max_len tl)

lemma list_str_max_len_mem
  (s : String)
  (l : List String)
  (h1 : s ∈ l) :
  s.length <= List.str_max_len l :=
  by
  induction l
  case nil =>
    simp at h1
  case cons hd tl ih =>
    simp at h1

    unfold List.str_max_len
    cases h1
    case inl c1 =>
      simp only [c1]
      simp
    case inr c1 =>
      trans List.str_max_len tl
      · exact ih c1
      · simp

def variant
  (s : String)
  (c : Char)
  (l : List String) :
  String :=
  if h : s ∈ l
  then
  have : List.str_max_len l + 1 - (String.length s + String.length (Char.toString c)) < List.str_max_len l + 1 - String.length s :=
    by
    have s1 : (Char.toString c).length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := list_str_max_len_mem s l h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  variant (s ++ c.toString) c l
  else s
  termination_by variant s _ l => List.str_max_len l + 1 - s.length

lemma variant_spec
  (s : String)
  (c : Char)
  (l : List String) :
  ¬ variant s c l ∈ l :=
  if h : s ∈ l
  then
  have : List.str_max_len l + 1 - (String.length s + String.length (Char.toString c)) < List.str_max_len l + 1 - String.length s :=
    by
    have s1 : (Char.toString c).length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := list_str_max_len_mem s l h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  by
    unfold variant
    simp
    simp only [if_pos h]
    apply variant_spec
  else by
    unfold variant
    simp
    simp [if_neg h]
    exact h
  termination_by variant_spec s _ l => List.str_max_len l + 1 - s.length


def Finset.str_max_len :
  Finset String → ℕ :=
  Finset.fold (fun x x_1 => max x x_1) 0 String.length

lemma finset_str_max_len_mem
  (s : String)
  (l : Finset String)
  (h1 : s ∈ l) :
  s.length <= Finset.str_max_len l :=
  by
  induction l using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1
    cases h1
    case inl c1 =>
      subst c1
      unfold Finset.str_max_len
      simp
    case inr c1 =>
      unfold Finset.str_max_len at ih
      unfold Finset.str_max_len
      simp
      right
      exact ih c1

def FinsetVariant
  (s : String)
  (c : Char)
  (l : Finset String) :
  String :=
  if h : s ∈ l
  then
  have : Finset.str_max_len l + 1 - (String.length s + String.length (Char.toString c)) < Finset.str_max_len l + 1 - String.length s :=
    by
    have s1 : (Char.toString c).length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_str_max_len_mem s l h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  FinsetVariant (s ++ c.toString) c l
  else s
  termination_by FinsetVariant s _ l => Finset.str_max_len l + 1 - s.length


lemma variant_spec'
  (s : String)
  (c : Char)
  (l : Finset String) :
  ¬ FinsetVariant s c l ∈ l :=
  if h : s ∈ l
  then
  have : Finset.str_max_len l + 1 - (String.length s + String.length (Char.toString c)) < Finset.str_max_len l + 1 - String.length s :=
    by
    have s1 : (Char.toString c).length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_str_max_len_mem s l h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  by
    unfold FinsetVariant
    simp
    simp only [if_pos h]
    apply variant_spec'
  else by
    unfold FinsetVariant
    simp
    simp [if_neg h]
    exact h
  termination_by variant_spec' s _ l => Finset.str_max_len l + 1 - s.length


def Finset.var_name_max_len :
  Finset VarName → ℕ :=
  Finset.fold (fun x x_1 => max x x_1) 0 (String.length ∘ VarName.toString)

lemma finset_var_name_max_len_mem
  (s : VarName)
  (l : Finset VarName)
  (h1 : s ∈ l) :
  s.length <= Finset.var_name_max_len l :=
  by
  induction l using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1
    cases h1
    case inl c1 =>
      subst c1
      unfold Finset.var_name_max_len
      simp
    case inr c1 =>
      unfold Finset.var_name_max_len at ih
      unfold Finset.var_name_max_len
      simp
      right
      exact ih c1

def FinsetVarNameVariant
  (s : VarName)
  (c : Char)
  (l : Finset VarName) :
  VarName :=
  if h : s ∈ l
  then
  have : Finset.var_name_max_len l + 1 - (s.length + String.length (Char.toString c)) < Finset.var_name_max_len l + 1 - s.length :=
    by
    have s1 : (Char.toString c).length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_var_name_max_len_mem s l h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  FinsetVarNameVariant (VarName.mk (s.toString ++ c.toString)) c l
  else s
  termination_by FinsetVarNameVariant s _ l => Finset.var_name_max_len l + 1 - s.length


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
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ x = σ y
    then FinsetVarNameVariant x c ((subVariant (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  forall_ x' (subVariant (Function.updateIte σ x x') c phi)
| exists_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ x = σ y
    then FinsetVarNameVariant x c ((subVariant (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  exists_ x' (subVariant (Function.updateIte σ x x') c phi)
| def_ X xs => def_ X (xs.map σ)
