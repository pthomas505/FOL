import FOL.NV.Semantics


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec.Inj

open Formula


/--
  replaceAll σ F := The simultaneous replacement of each occurrence of any variable v in the formula F by σ v.
-/
def replaceAll
  (σ : VarName → VarName) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replaceAll σ phi)
  | imp_ phi psi => imp_ (replaceAll σ phi) (replaceAll σ psi)
  | and_ phi psi => and_ (replaceAll σ phi) (replaceAll σ psi)
  | or_ phi psi => or_ (replaceAll σ phi) (replaceAll σ psi)
  | iff_ phi psi => iff_ (replaceAll σ phi) (replaceAll σ psi)
  | forall_ x phi => forall_ (σ x) (replaceAll σ phi)
  | exists_ x phi => exists_ (σ x) (replaceAll σ phi)
  | def_ X xs => def_ X (xs.map σ)


theorem substitution_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (F : Formula)
  (σ : VarName → VarName)
  (h1 : Function.Injective σ) :
  holds D I (V ∘ σ) E F ↔
    holds D I V E (replaceAll σ F) :=
  by
  induction F generalizing V
  all_goals
    simp only [replaceAll]
  any_goals
    simp only [holds]
  case pred_const_ X xs | pred_var_ X xs =>
    simp
  case eq_ x y =>
    simp
  case not_ phi phi_ih =>
    congr! 1
    exact phi_ih V
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr! 1
    · exact phi_ih V
    · exact psi_ih V
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
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
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [holds]
      simp
      split_ifs
      case _ c1 =>
        cases c1
        case intro c1_left c1_right =>
          apply Holds_coincide_Var
          intro v a1
          simp only [var_is_free_in_iff_mem_free_var_set v E_hd.q] at a1
          apply Function.updateListITE_mem_eq_len
          · simp only [<- List.mem_toFinset]
            apply Finset.mem_of_subset E_hd.h1 a1
          · simp
            simp only [c1_right]

      case _ c1 =>
        apply E_ih


theorem substitution_is_valid
  (F : Formula)
  (σ : VarName → VarName)
  (h1 : Function.Injective σ)
  (h2 : F.is_valid) :
  (replaceAll σ F).is_valid :=
  by
    simp only [is_valid] at h2

    simp only [is_valid]
    intro D I V E
    simp only [← substitution_theorem D I V E F σ h1]
    apply h2


#lint
