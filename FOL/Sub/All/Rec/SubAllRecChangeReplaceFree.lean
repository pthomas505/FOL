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


def sub
  (σ : VarName → VarName)
  (c : Char) :
  Formula → Formula
| pred_const_ X xs => pred_const_ X (xs.map σ)
| pred_var_ X xs => pred_var_ X (xs.map σ)
| eq_ x y => eq_ (σ x) (σ y)
| true_ => true_
| false_ => false_
| not_ phi => not_ (sub σ c phi)
| imp_ phi psi => imp_ (sub σ c phi) (sub σ c psi)
| and_ phi psi => and_ (sub σ c phi) (sub σ c psi)
| or_ phi psi => or_ (sub σ c phi) (sub σ c psi)
| iff_ phi psi => iff_ (sub σ c phi) (sub σ c psi)
| forall_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((sub (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  forall_ x' (sub (Function.updateIte σ x x') c phi)
| exists_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((sub (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  exists_ x' (sub (Function.updateIte σ x x') c phi)
| def_ X xs => def_ X (xs.map σ)


lemma lem_1
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula)
  (x : VarName)
  (h1 : ∀ τ : VarName → VarName, (sub τ c F).freeVarSet = F.freeVarSet.image τ) :
  let x' :=
    if ∃ (y : VarName), y ∈ F.freeVarSet \ {x} ∧ σ y = x
    then variant x c (sub (Function.updateIte σ x x) c F).freeVarSet
    else x
  x' ∉ (F.freeVarSet \ {x}).image σ :=
  by
  have s1 : (F.freeVarSet \ {x}).image σ ⊆ (sub (Function.updateIte σ x x) c F).freeVarSet
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

    _ = (sub (Function.updateIte σ x x) c F).freeVarSet :=
      by
      symm
      exact h1 (Function.updateIte σ x x)

  split
  case inl c1 =>
    obtain s2 := variant_not_mem x c (freeVarSet (sub (Function.updateIte σ x x) c F))
    exact Finset.not_mem_mono s1 s2
  case inr c1 =>
    simp at c1
    simp
    exact c1


lemma lem_2
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β)
  (h1 : f x = x') :
  (Finset.image f S) \ {x'} =
  (Finset.image f (S \ {x})) \ {x'} :=
  by
  subst h1
  apply Finset.ext
  intro a
  simp
  intro a1
  constructor
  · intro a2
    apply Exists.elim a2
    intro b a3
    apply Exists.intro b
    cases a3
    case _ a3_left a3_right =>
      subst a3_right
      tauto
  · intro a2
    apply Exists.elim a2
    intro b a3
    apply Exists.intro b
    cases a3
    case _ a3_left a3_right =>
      subst a3_right
      tauto


lemma lem_3
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β) :
  ((S \ {x}).image (Function.updateIte f x x')) =
  ((S \ {x}).image f) :=
  by
  apply Finset.image_congr
  unfold Set.EqOn
  intro a a1
  simp at a1
  unfold Function.updateIte
  cases a1
  case _ a1_left a1_right =>
    simp only [if_neg a1_right]


theorem lem_4
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  (sub σ c F).freeVarSet = F.freeVarSet.image σ :=
  by
  induction F generalizing σ
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    unfold sub
    unfold freeVarSet
    apply Finset.ext
    intro a
    simp
  case true_ | false_ =>
    unfold sub
    unfold freeVarSet
    simp
  case not_ phi phi_ih =>
    unfold sub
    unfold freeVarSet
    exact phi_ih σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold sub
    unfold freeVarSet
    simp only [Finset.image_union]
    congr!
    · exact phi_ih σ
    · exact psi_ih σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((sub (Function.updateIte σ x x) c phi).freeVarSet)
    else x
    calc
        (sub σ c (forall_ x phi)).freeVarSet
    _ = (forall_ x' (sub (Function.updateIte σ x x') c phi)).freeVarSet := by simp only [sub]

    _ = (sub (Function.updateIte σ x x') c phi).freeVarSet \ {x'} := by simp only [freeVarSet]

    _ = (phi.freeVarSet.image (Function.updateIte σ x x')) \ {x'} := by simp only [phi_ih (Function.updateIte σ x x')]

    _ = ((phi.freeVarSet \ {x}).image (Function.updateIte σ x x')) \ {x'} :=
      by
      apply lem_2
      unfold Function.updateIte
      simp

    _ = ((phi.freeVarSet \ {x}).image σ) \ {x'} :=
      by
      congr! 1
      apply lem_3

    _ = (phi.freeVarSet \ {x}).image σ :=
      by
      apply Finset.sdiff_singleton_eq_self
      exact lem_1 σ c phi x phi_ih


theorem substitution_fun_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  Holds D I V E (sub σ c F) ↔
    Holds D I (V ∘ σ) E F :=
  by
  induction F generalizing σ V
  case pred_const_ X xs =>
    unfold sub
    simp only [Holds]
    simp
  case forall_ x phi phi_ih =>
    let x' :=
      if ∃ y ∈ phi.freeVarSet \ {x}, σ y = x
      then variant x c (sub (Function.updateIte σ x x) c phi).freeVarSet
      else x
    have s1 : ∀ (a : D) (z : VarName), z ∈ phi.freeVarSet → ((Function.updateIte V x' a) ∘ (Function.updateIte σ x x')) z = (Function.updateIte (V ∘ σ) x a) z
    intro a z h1
    by_cases h2 : z = x
    case pos =>
      subst h2
      unfold Function.updateIte
      simp
    case neg =>
      have s2 : z ∈ phi.freeVarSet \ {x}
      simp
      tauto

      have s3 : x' ∉ (phi.freeVarSet \ {x}).image σ
      apply lem_1
      intro τ
      exact lem_4 τ c phi

      have s4 : σ z ∈ (phi.freeVarSet \ {x}).image σ
      apply Finset.mem_image_of_mem
      exact s2

      have s5 : ¬ x' = σ z
      intro contra
      apply s3
      simp only [contra]
      exact s4

      have s6 : ∀ (x : VarName), x = σ z → ¬ x = x'
      intro y a1
      subst a1
      tauto

      calc
          ((Function.updateIte V x' a) ∘ (Function.updateIte σ x x')) z
      _ = (Function.updateIte V x' a) ((Function.updateIte σ x x') z) := by simp
      _ = (Function.updateIte V x' a) z :=
          by
          unfold Function.updateIte
          simp only [if_neg h2]
          sorry
