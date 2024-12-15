import FOL.NV.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.subformula_set F` := The set of all of the subformulas of a formula `F`.
-/
def Formula_.subformula_set :
  Formula_ → Multiset Formula_
  | pred_const_ X xs => {pred_const_ X xs}
  | pred_var_ X xs => {pred_var_ X xs}
  | eq_ x y => {eq_ x y}
  | true_ => {true_}
  | false_ => {false_}
  | not_ phi => phi.subformula_set ∪ {not_ phi}
  | imp_ phi psi => phi.subformula_set ∪ psi.subformula_set ∪ {imp_ phi psi}
  | and_ phi psi => phi.subformula_set ∪ psi.subformula_set ∪ {and_ phi psi}
  | or_ phi psi => phi.subformula_set ∪ psi.subformula_set ∪ {or_ phi psi}
  | iff_ phi psi => phi.subformula_set ∪ psi.subformula_set ∪ {iff_ phi psi}
  | forall_ x phi => phi.subformula_set ∪ {forall_ x phi}
  | exists_ x phi => phi.subformula_set ∪ {exists_ x phi}
  | def_ X xs => {def_ X xs}


example
  (F : Formula_) :
  F ∈ F.subformula_set :=
  by
  cases F
  all_goals
    simp only [subformula_set]
    simp only [Multiset.mem_union, Multiset.mem_singleton, or_true]


example
  (F F' F'' : Formula_)
  (h1 : F ∈ F'.subformula_set)
  (h2 : F' ∈ F''.subformula_set) :
  F ∈ F''.subformula_set :=
  by
    induction F''
    case pred_const_ X xs | pred_var_ X xs | eq_ x y | true_ | false_ | def_ X xs =>
      unfold subformula_set at h2
      simp at h2
      rw [h2] at h1
      exact h1
    case not_ phi ih =>
      unfold subformula_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        unfold subformula_set
        simp
        tauto
      case inr h2 =>
        rw [h2] at h1
        exact h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold subformula_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        cases h2
        case inl h2 =>
          unfold subformula_set
          simp
          tauto
        case inr h2 =>
          unfold subformula_set
          simp
          tauto
      case inr h2 =>
        rw [h2] at h1
        exact h1
    case forall_ x phi ih | exists_ x phi ih =>
      unfold subformula_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        unfold subformula_set
        simp
        tauto
      case inr h2 =>
        rw [h2] at h1
        exact h1


/--
  `is_proper_subformula F F'` := True if and only if `F` is a proper subformula of the formula `F'`.
-/
def is_proper_subformula
  (F F' : Formula_) :
  Prop :=
  F ∈ F'.subformula_set ∧ ¬ F = F'


#lint
