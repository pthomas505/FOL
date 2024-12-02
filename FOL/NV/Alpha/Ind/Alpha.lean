import FOL.NV.Sub.Var.One.Rec.ReplaceFree
import FOL.NV.Sub.Var.One.Rec.ReplaceVar
import FOL.NV.Semantics

import Mathlib.Data.List.Defs

set_option autoImplicit false


namespace FOL.NV

open Formula_


inductive are_alpha_equiv_ind_v1 : Formula_ → Formula_ → Prop
  | rename_forall_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_is_free_in y phi →
    ¬ var_is_bound_in y phi →
    are_alpha_equiv_ind_v1 (forall_ x phi) (forall_ y (replace_var_one_rec x y phi))

  | rename_exists_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_is_free_in y phi →
    ¬ var_is_bound_in y phi →
    are_alpha_equiv_ind_v1 (exists_ x phi) (exists_ y (replace_var_one_rec x y phi))

  | compat_not_
    (phi phi' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 (not_ phi) (not_ phi')

  | compat_imp_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 psi psi' →
    are_alpha_equiv_ind_v1 (imp_ phi psi) (imp_ phi' psi')

  | compat_and_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 psi psi' →
    are_alpha_equiv_ind_v1 (and_ phi psi) (and_ phi' psi')

  | compat_or_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 psi psi' →
    are_alpha_equiv_ind_v1 (or_ phi psi) (or_ phi' psi')

  | compat_iff_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 psi psi' →
    are_alpha_equiv_ind_v1 (iff_ phi psi) (iff_ phi' psi')

  | compat_forall_
    (phi phi' : Formula_)
    (x : VarName_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 (forall_ x phi) (forall_ x phi')

  | compat_exists_
    (phi phi' : Formula_)
    (x : VarName_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 (exists_ x phi) (exists_ x phi')

  | refl_
    (phi : Formula_) :
    are_alpha_equiv_ind_v1 phi phi

  | symm_
    (phi phi' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 phi' phi

  | trans_
    (phi phi' phi'' : Formula_) :
    are_alpha_equiv_ind_v1 phi phi' →
    are_alpha_equiv_ind_v1 phi' phi'' →
    are_alpha_equiv_ind_v1 phi phi''

-------------------------------------------------------------------------------

inductive are_alpha_equiv_ind_v2 : Formula_ → Formula_ → Prop
  | rename_forall_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_is_free_in y phi →
    ¬ var_is_bound_in y phi →
    are_alpha_equiv_ind_v2 (forall_ x phi) (forall_ y (Sub.Var.One.Rec.fast_replace_free_var_one_rec x y phi))

  | rename_exists_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_is_free_in y phi →
    ¬ var_is_bound_in y phi →
    are_alpha_equiv_ind_v2 (exists_ x phi) (exists_ y (Sub.Var.One.Rec.fast_replace_free_var_one_rec x y phi))

  | compat_not_
    (phi phi' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 (not_ phi) (not_ phi')

  | compat_imp_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 psi psi' →
    are_alpha_equiv_ind_v2 (imp_ phi psi) (imp_ phi' psi')

  | compat_and_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 psi psi' →
    are_alpha_equiv_ind_v2 (and_ phi psi) (and_ phi' psi')

  | compat_or_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 psi psi' →
    are_alpha_equiv_ind_v2 (or_ phi psi) (or_ phi' psi')

  | compat_iff_
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 psi psi' →
    are_alpha_equiv_ind_v2 (iff_ phi psi) (iff_ phi' psi')

  | compat_forall_
    (phi phi' : Formula_)
    (x : VarName_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 (forall_ x phi) (forall_ x phi')

  | compat_exists_
    (phi phi' : Formula_)
    (x : VarName_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 (exists_ x phi) (exists_ x phi')

  | refl_
    (phi : Formula_) :
    are_alpha_equiv_ind_v2 phi phi

  | symm_
    (phi phi' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 phi' phi

  | trans_
    (phi phi' phi'' : Formula_) :
    are_alpha_equiv_ind_v2 phi phi' →
    are_alpha_equiv_ind_v2 phi' phi'' →
    are_alpha_equiv_ind_v2 phi phi''

-------------------------------------------------------------------------------

lemma are_alpha_equiv_ind_v1_replace_var_one_rec_fast_replace_free_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : t ∉ F.var_set) :
  are_alpha_equiv_ind_v1 (replace_var_one_rec v t F) (Sub.Var.One.Rec.fast_replace_free_var_one_rec v t F) :=
  by
    induction F
    case pred_const_ X xs | pred_var_ X xs | def_ X xs | eq_ x y | true_ | false_ =>
      simp only [replace_var_one_rec]
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      apply are_alpha_equiv_ind_v1.refl_
    case not_ phi phi_ih =>
      apply are_alpha_equiv_ind_v1.compat_not_
      exact phi_ih h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp only [var_set] at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      first
        | apply are_alpha_equiv_ind_v1.compat_imp_
        | apply are_alpha_equiv_ind_v1.compat_and_
        | apply are_alpha_equiv_ind_v1.compat_or_
        | apply are_alpha_equiv_ind_v1.compat_iff_
      · exact phi_ih h1_left
      · exact psi_ih h1_right
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [var_set] at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      specialize phi_ih h1_left

      simp only [replace_var_one_rec]
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      split_ifs
      case pos c1 =>
        subst c1
        apply are_alpha_equiv_ind_v1.symm_
        first
          | apply are_alpha_equiv_ind_v1.rename_forall_
          | apply are_alpha_equiv_ind_v1.rename_exists_
        · simp only [var_is_free_in_iff_mem_free_var_set]
          apply not_mem_var_set_imp_not_mem_free_var_set
          exact h1_left
        · simp only [var_is_bound_in_iff_mem_bound_var_set]
          apply not_mem_var_set_imp_not_mem_bound_var_set
          exact h1_left
      case neg c1 =>
        first
        | apply are_alpha_equiv_ind_v1.compat_forall_
        | apply are_alpha_equiv_ind_v1.compat_exists_
        exact phi_ih


lemma are_alpha_equiv_v2_replace_free_replace_var
  (F : Formula_)
  (v t : VarName_)
  (h1 : t ∉ F.var_set) :
  are_alpha_equiv_ind_v2 (Sub.Var.One.Rec.fast_replace_free_var_one_rec v t F) (replace_var_one_rec v t F) :=
  by
    induction F
    case pred_const_ X xs | pred_var_ X xs | def_ X xs | eq_ x y | true_ | false_ =>
      simp only [replace_var_one_rec]
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      apply are_alpha_equiv_ind_v2.refl_
    case not_ phi phi_ih =>
      apply are_alpha_equiv_ind_v2.compat_not_
      exact phi_ih h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp only [var_set] at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      first
        | apply are_alpha_equiv_ind_v2.compat_imp_
        | apply are_alpha_equiv_ind_v2.compat_and_
        | apply are_alpha_equiv_ind_v2.compat_or_
        | apply are_alpha_equiv_ind_v2.compat_iff_
      · exact phi_ih h1_left
      · exact psi_ih h1_right
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [var_set] at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      specialize phi_ih h1_left

      simp only [replace_var_one_rec]
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      split_ifs
      case pos c1 =>
        subst c1
        apply are_alpha_equiv_ind_v2.trans_
        · first
            | apply are_alpha_equiv_ind_v2.rename_forall_
            | apply are_alpha_equiv_ind_v2.rename_exists_
          · simp only [var_is_free_in_iff_mem_free_var_set]
            apply not_mem_var_set_imp_not_mem_free_var_set
            exact h1_left
          · simp only [var_is_bound_in_iff_mem_bound_var_set]
            apply not_mem_var_set_imp_not_mem_bound_var_set
            exact h1_left
        · first
            | apply are_alpha_equiv_ind_v2.compat_forall_
            | apply are_alpha_equiv_ind_v2.compat_exists_
          exact phi_ih
      case neg c1 =>
        first
        | apply are_alpha_equiv_ind_v2.compat_forall_
        | apply are_alpha_equiv_ind_v2.compat_exists_
        exact phi_ih


-------------------------------------------------------------------------------

theorem replace_empty_Holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (u v : VarName_)
  (F : Formula_)
  (a : D)
  (h1 : ¬ var_is_free_in v F)
  (h2 : ¬ var_is_bound_in v F) :
  holds D I (Function.updateITE V u a) E F ↔
    holds D I (Function.updateITE V v a) E (Sub.Var.One.Rec.fast_replace_free_var_one_rec u v F) :=
  by
  induction E generalizing F V
  all_goals
    induction F generalizing V
    case pred_const_ X xs | pred_var_ X xs =>
      simp only [var_is_free_in] at h1

      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
      congr! 1
      simp
      intro x a1
      simp only [Function.updateITE]
      simp only [eq_comm]
      split_ifs
      case _ c1 c2 =>
        rfl
      case _ c1 c2 =>
        contradiction
      case _ c1 c2 =>
        subst c2
        contradiction
      case _ c1 c2 =>
        rfl
    case eq_ x y =>
      simp only [var_is_free_in] at h1

      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
      congr! 1
      · simp only [Function.updateITE]
        split_ifs <;> tauto
      · simp only [Function.updateITE]
        split_ifs <;> tauto
    case true_ | false_ =>
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
    case not_ phi phi_ih =>
      simp only [var_is_free_in] at h1

      simp only [var_is_bound_in] at h2

      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
      congr! 1
      exact phi_ih V h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp only [var_is_free_in] at h1
      push_neg at h1

      simp only [var_is_bound_in] at h2
      push_neg at h2

      cases h1
      case intro h1_left h1_right =>
        cases h2
        case intro h2_left h2_right =>
          simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
          simp only [holds]
          congr! 1
          · exact phi_ih V h1_left h2_left
          · exact psi_ih V h1_right h2_right
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [var_is_free_in] at h1
      push_neg at h1

      simp only [var_is_bound_in] at h2
      push_neg at h2

      cases h2
      case intro h2_left h2_right =>
        simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
        split_ifs
        case pos c1 =>
          subst c1
          apply holds_coincide_var
          intro x a1
          simp only [var_is_free_in] at a1
          cases a1
          case h1.intro a1_left a1_right =>
            simp only [Function.updateITE]
            simp only [if_neg a1_left]
            split_ifs
            case pos c2 =>
              subst c2
              tauto
            case neg c2 =>
              rfl
        case neg c1 =>
          simp only [holds]
          first | apply forall_congr' | apply exists_congr
          intro d
          simp only [Function.updateITE_comm V v x d a h2_left]
          simp only [Function.updateITE_comm V u x d a c1]
          apply phi_ih
          · exact h1 h2_left
          · exact h2_right
  case nil.def_ X xs =>
    simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
    simp only [holds]
  case cons.def_ hd tl ih X xs =>
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
      unfold Function.updateITE
      congr! 1
      case _ =>
        simp
      case _ c1 =>
        simp only [var_is_free_in] at h1

        apply holds_coincide_var
        intro v' a1
        simp

        have s1 : (List.map ((fun (a_1 : VarName_) => if a_1 = v then a else V a_1) ∘ fun (x : VarName_) => if u = x then v else x) xs) = (List.map (fun (a_1 : VarName_) => if a_1 = u then a else V a_1) xs)
        {
          simp only [List.map_eq_map_iff]
          intro x a2
          simp only [eq_comm]
          simp
          split_ifs
          case _ =>
            rfl
          case _ =>
            contradiction
          case _ c1 c2 =>
            subst c2
            contradiction
          case _ =>
            rfl
        }

        simp only [s1]
        apply Function.updateListITE_mem_eq_len
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset hd.h1 a1
        · simp at c1
          cases c1
          case intro c1_left c1_right =>
            simp
            simp only [eq_comm]
            exact c1_right
      case _ =>
        apply ih
        · exact h1
        · exact h2


theorem Holds_iff_alphaEqv_Holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F F' : Formula_)
  (h1 : are_alpha_equiv_ind_v2 F F') :
  holds D I V E F ↔ holds D I V E F' :=
  by
  induction h1 generalizing V
  case rename_forall_ h1_phi h1_x h1_y h1_1 h1_2 | rename_exists_ h1_phi h1_x h1_y h1_1 h1_2 =>
    simp only [holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    exact replace_empty_Holds D I V E h1_x h1_y h1_phi d h1_1 h1_2
  case compat_not_ h1_phi h1_phi' _ h1_ih =>
    simp only [holds]
    congr! 1
    exact h1_ih V
  case
    compat_imp_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_and_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_or_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_iff_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2 =>
    simp only [holds]
    congr! 1
    · exact h1_ih_1 V
    · exact h1_ih_2 V
  case compat_forall_ h1_phi h1_psi h1_x _ h1_ih | compat_exists_ h1_phi h1_psi h1_x _ h1_ih =>
    simp only [holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    exact h1_ih (Function.updateITE V h1_x d)
  case refl_ h1 =>
    rfl
  case symm_ h1_phi h1_phi' _ h1_ih =>
    symm
    exact h1_ih V
  case trans_ h1_phi h1_phi' h1_phi'' _ _ h1_ih_1 h1_ih_2 =>
    trans holds D I V E h1_phi'
    · exact h1_ih_1 V
    · exact h1_ih_2 V

-------------------------------------------------------------------------------

inductive are_alpha_equiv_var_ind_v3 :
  List (VarName_ × VarName_) → VarName_ → VarName_ → Prop
  | nil
    (x : VarName_) :
    are_alpha_equiv_var_ind_v3 [] x x

  | head
    (binders : List (VarName_ × VarName_))
    (x y : VarName_) :
    are_alpha_equiv_var_ind_v3 ((x, y) :: binders) x y

  | tail
    (binders : List (VarName_ × VarName_))
    (x y x' y' : VarName_) :
    ¬ x = x' →
    ¬ y = y' →
    are_alpha_equiv_var_ind_v3 binders x' y' →
    are_alpha_equiv_var_ind_v3 ((x, y) :: binders) x' y'


inductive are_alpha_equiv_ind_v3 :
  List (VarName_ × VarName_) → Formula_ → Formula_ → Prop

  | pred_var_
    (binders : List (VarName_ × VarName_))
    (X : PredName_)
    (xs ys : List VarName_) :
    List.Forall₂ (are_alpha_equiv_var_ind_v3 binders) xs ys →
    are_alpha_equiv_ind_v3 binders (pred_var_ X xs) (pred_var_ X ys)

  | pred_const_
    (binders : List (VarName_ × VarName_))
    (X : PredName_)
    (xs ys : List VarName_) :
    List.Forall₂ (are_alpha_equiv_var_ind_v3 binders) xs ys →
    are_alpha_equiv_ind_v3 binders (pred_const_ X xs) (pred_const_ X ys)

  | compat_true_
    (binders : List (VarName_ × VarName_)) :
    are_alpha_equiv_ind_v3 binders true_ true_

  | compat_false_
    (binders : List (VarName_ × VarName_)) :
    are_alpha_equiv_ind_v3 binders false_ false_

  | compat_not_
    (binders : List (VarName_ × VarName_))
    (phi phi' : Formula_) :
    are_alpha_equiv_ind_v3 binders phi phi' →
    are_alpha_equiv_ind_v3 binders (not_ phi) (not_ phi')

  | compat_imp_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v3 binders phi phi' →
    are_alpha_equiv_ind_v3 binders psi psi' →
    are_alpha_equiv_ind_v3 binders (imp_ phi psi) (imp_ phi' psi')

  | compat_and_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v3 binders phi phi' →
    are_alpha_equiv_ind_v3 binders psi psi' →
    are_alpha_equiv_ind_v3 binders (and_ phi psi) (and_ phi' psi')

  | compat_or_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v3 binders phi phi' →
    are_alpha_equiv_ind_v3 binders psi psi' →
    are_alpha_equiv_ind_v3 binders (or_ phi psi) (or_ phi' psi')

  | compat_iff_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_v3 binders phi phi' →
    are_alpha_equiv_ind_v3 binders psi psi' →
    are_alpha_equiv_ind_v3 binders (iff_ phi psi) (iff_ phi' psi')

  | compat_forall_
    (binders : List (VarName_ × VarName_))
    (phi phi' : Formula_)
    (x y : VarName_) :
    are_alpha_equiv_ind_v3 ((x, y) :: binders) phi phi' →
    are_alpha_equiv_ind_v3 binders (forall_ x phi) (forall_ y phi')

  | compat_exists_
    (binders : List (VarName_ × VarName_))
    (phi phi' : Formula_)
    (x y : VarName_) :
    are_alpha_equiv_ind_v3 ((x, y) :: binders) phi phi' →
    are_alpha_equiv_ind_v3 binders (exists_ x phi) (exists_ y phi')

-------------------------------------------------------------------------------
