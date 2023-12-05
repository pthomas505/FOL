import FOL.NV.Semantics


set_option autoImplicit false


namespace FOL

namespace NV

open Formula


def replaceAllVar
  (σ : VarName → VarName) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replaceAllVar σ phi)
  | imp_ phi psi => imp_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | and_ phi psi => and_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | or_ phi psi => or_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | iff_ phi psi => iff_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | forall_ x phi => forall_ (σ x) (replaceAllVar σ phi)
  | exists_ x phi => exists_ (σ x) (replaceAllVar σ phi)
  | def_ X xs => def_ X (xs.map σ)


example
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (F : Formula)
  (σ : VarName → VarName)
  (h1 : Function.Injective σ) :
  Holds D I (V ∘ σ) E F ↔
    Holds D I V E (replaceAllVar σ F) :=
  by
  induction F generalizing V
  case pred_const_ X xs | pred_var_ X xs =>
    unfold replaceAllVar
    simp only [Holds]
    simp
  case eq_ x y =>
    unfold replaceAllVar
    simp only [Holds]
    simp
  case true_ | false_ =>
    unfold replaceAllVar
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold replaceAllVar
    simp only [Holds]
    congr! 1
    exact phi_ih V
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replaceAllVar
    simp only [Holds]
    congr! 1
    · exact phi_ih V
    · exact psi_ih V
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold replaceAllVar
    simp only [Holds]

    first | apply forall_congr' | apply exists_congr
    intro a

    have s1 : Function.updateITE V (σ x) a ∘ σ = Function.updateITE (V ∘ σ) x a
    apply Function.updateITE_comp_right_injective
    apply h1

    simp only [← s1]

    exact phi_ih (Function.updateITE V (σ x) a)

  case def_ X xs =>
    induction E
    case nil =>
      unfold replaceAllVar
      simp only [Holds]
    case cons E_hd E_tl E_ih =>
      unfold replaceAllVar
      simp only [Holds]
      simp
      split_ifs
      case _ c1 =>
        cases c1
        case intro c1_left c1_right =>
          apply Holds_coincide_Var
          intro v a1
          simp only [isFreeIn_iff_mem_freeVarSet v E_hd.q] at a1
          apply Function.updateListITE_mem_eq_len
          · simp only [<- List.mem_toFinset]
            apply Finset.mem_of_subset E_hd.h1 a1
          · simp
            simp only [c1_right]

      case _ c1 =>
        apply E_ih
