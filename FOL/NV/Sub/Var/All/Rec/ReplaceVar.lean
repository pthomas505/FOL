import FOL.NV.Semantics


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec.Inj

open Formula_


/--
  `replace_var_all_rec σ F` := The simultaneous replacement of each occurrence of any variable `v` in the formula `F` by `σ v`.
-/
def replace_var_all_rec
  (σ : VarName_ → VarName_) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_var_all_rec σ phi)
  | imp_ phi psi => imp_ (replace_var_all_rec σ phi) (replace_var_all_rec σ psi)
  | and_ phi psi => and_ (replace_var_all_rec σ phi) (replace_var_all_rec σ psi)
  | or_ phi psi => or_ (replace_var_all_rec σ phi) (replace_var_all_rec σ psi)
  | iff_ phi psi => iff_ (replace_var_all_rec σ phi) (replace_var_all_rec σ psi)
  | forall_ x phi => forall_ (σ x) (replace_var_all_rec σ phi)
  | exists_ x phi => exists_ (σ x) (replace_var_all_rec σ phi)
  | def_ X xs => def_ X (xs.map σ)


theorem substitution_theorem_replace_var_all_rec_inj
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F : Formula_)
  (σ : VarName_ → VarName_)
  (h1 : Function.Injective σ) :
  holds D I (V ∘ σ) E F ↔
    holds D I V E (replace_var_all_rec σ F) :=
  by
  induction F generalizing V
  all_goals
    simp only [replace_var_all_rec]
  any_goals
    simp only [holds]
  case pred_const_ X xs | pred_var_ X xs =>
    simp
  case eq_ x y =>
    simp
  case not_ phi phi_ih =>
    congr! 1
    apply phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    first | apply forall_congr' | apply exists_congr
    intro a

    have s1 : Function.updateITE V (σ x) a ∘ σ = Function.updateITE (V ∘ σ) x a :=
    by
      apply Function.updateITE_comp_right_injective
      apply h1

    simp only [← s1]
    apply phi_ih
  case def_ X xs =>
    induction E
    case nil =>
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [holds]
      simp
      split_ifs
      case _ c1 =>
        obtain ⟨c1_left, c1_right⟩ := c1
        apply holds_coincide_var
        intro v a1
        simp only [var_is_free_in_iff_mem_free_var_set v E_hd.q] at a1
        apply Function.updateListITE_mem_eq_len
        · simp only [<- List.mem_toFinset]
          exact Finset.mem_of_subset E_hd.h1 a1
        · simp
          simp only [c1_right]

      case _ c1 =>
        apply E_ih


theorem substitution_is_valid_replace_var_all_rec_inj
  (F : Formula_)
  (σ : VarName_ → VarName_)
  (h1 : Function.Injective σ)
  (h2 : F.is_valid) :
  (replace_var_all_rec σ F).is_valid :=
  by
    simp only [is_valid] at h2

    simp only [is_valid]
    intro D I V E
    simp only [← substitution_theorem_replace_var_all_rec_inj D I V E F σ h1]
    apply h2


#lint
