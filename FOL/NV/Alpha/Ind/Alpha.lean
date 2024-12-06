import FOL.NV.Sub.Var.One.Rec.ReplaceFree
import FOL.NV.Sub.Var.One.Rec.ReplaceVar
import FOL.NV.Semantics

import Mathlib.Data.List.Defs

set_option autoImplicit false


namespace FOL.NV

open Formula_


/--
  `are_alpha_equiv_ind_v1 F F'` := True if and only if `F` and `F'` are alpha equivalent.
-/
inductive are_alpha_equiv_ind_v1 : Formula_ → Formula_ → Prop
  | rename_forall_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_occurs_in y phi →
    are_alpha_equiv_ind_v1 (forall_ x phi) (forall_ y (replace_var_one_rec x y phi))

  | rename_exists_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_occurs_in y phi →
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

/--
  `are_alpha_equiv_ind_v2 F F'` := True if and only if `F` and `F'` are alpha equivalent.
-/
inductive are_alpha_equiv_ind_v2 : Formula_ → Formula_ → Prop
  | rename_forall_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_occurs_in y phi →
    are_alpha_equiv_ind_v2 (forall_ x phi) (forall_ y (Sub.Var.One.Rec.fast_replace_free_var_one_rec x y phi))

  | rename_exists_
    (phi : Formula_)
    (x y : VarName_) :
    ¬ var_occurs_in y phi →
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
      simp only [var_occurs_in_iff_mem_var_set]
      exact h1_left
    case neg c1 =>
      first
      | apply are_alpha_equiv_ind_v1.compat_forall_
      | apply are_alpha_equiv_ind_v1.compat_exists_
      exact phi_ih


lemma are_alpha_equiv_ind_v2_fast_replace_free_var_one_rec_replace_var_one_rec
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
          | apply are_alpha_equiv_ind_v2.rename_forall_ phi v t
          | apply are_alpha_equiv_ind_v2.rename_exists_ phi v t
        · simp only [var_occurs_in_iff_mem_var_set]
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


lemma are_alpha_equiv_ind_v1_imp_are_alpha_equiv_ind_v2
  (F F' : Formula_)
  (h1 : are_alpha_equiv_ind_v1 F F') :
  are_alpha_equiv_ind_v2 F F' :=
  by
  induction h1
  case
      rename_forall_ phi x y ih_1
    | rename_exists_ phi x y ih_1 =>
    apply are_alpha_equiv_ind_v2.trans_
    · first
        | apply are_alpha_equiv_ind_v2.rename_forall_ phi x y
        | apply are_alpha_equiv_ind_v2.rename_exists_ phi x y
      exact ih_1
    · first
        | apply are_alpha_equiv_ind_v2.compat_forall_
        | apply are_alpha_equiv_ind_v2.compat_exists_
      apply are_alpha_equiv_ind_v2_fast_replace_free_var_one_rec_replace_var_one_rec
      rw [← var_occurs_in_iff_mem_var_set]
      intro contra
      obtain s1 := var_occurs_in_imp_var_is_bound_in_or_var_is_free_in y phi contra
      tauto
  case compat_not_ phi phi' ih_1 ih_2 =>
    apply are_alpha_equiv_ind_v2.compat_not_
    exact ih_2
  case
      compat_imp_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_and_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_or_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_iff_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4 =>
    first
      | apply are_alpha_equiv_ind_v2.compat_imp_
      | apply are_alpha_equiv_ind_v2.compat_and_
      | apply are_alpha_equiv_ind_v2.compat_or_
      | apply are_alpha_equiv_ind_v2.compat_iff_
    · exact ih_3
    · exact ih_4
  case
      compat_forall_ phi phi' x ih_1 ih_2
    | compat_exists_ phi phi' x ih_1 ih_2 =>
    first
      | apply are_alpha_equiv_ind_v2.compat_forall_
      | apply are_alpha_equiv_ind_v2.compat_exists_
    · exact ih_2
  case refl_ phi =>
    apply are_alpha_equiv_ind_v2.refl_
  case symm_ phi phi' _ ih_2 =>
    apply are_alpha_equiv_ind_v2.symm_
    exact ih_2
  case trans_ phi phi' phi'' ih_1 ih_2 ih_3 ih_4 =>
    apply are_alpha_equiv_ind_v2.trans_ phi phi'
    · exact ih_3
    · exact ih_4


lemma are_alpha_equiv_ind_v2_imp_are_alpha_equiv_ind_v1
  (F F' : Formula_)
  (h1 : are_alpha_equiv_ind_v2 F F') :
  are_alpha_equiv_ind_v1 F F' :=
  by
  induction h1
  case
      rename_forall_ phi x y ih_1
    | rename_exists_ phi x y ih_1 =>
    apply are_alpha_equiv_ind_v1.trans_
    · first
        | apply are_alpha_equiv_ind_v1.rename_forall_ phi x y
        | apply are_alpha_equiv_ind_v1.rename_exists_ phi x y
      exact ih_1
    · first
        | apply are_alpha_equiv_ind_v1.compat_forall_
        | apply are_alpha_equiv_ind_v1.compat_exists_
      apply are_alpha_equiv_ind_v1_replace_var_one_rec_fast_replace_free_var_one_rec
      rw [← var_occurs_in_iff_mem_var_set]
      intro contra
      obtain s1 := var_occurs_in_imp_var_is_bound_in_or_var_is_free_in y phi contra
      tauto
  case compat_not_ phi phi' ih_1 ih_2 =>
    apply are_alpha_equiv_ind_v1.compat_not_
    exact ih_2
  case
      compat_imp_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_and_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_or_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_iff_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4 =>
    first
      | apply are_alpha_equiv_ind_v1.compat_imp_
      | apply are_alpha_equiv_ind_v1.compat_and_
      | apply are_alpha_equiv_ind_v1.compat_or_
      | apply are_alpha_equiv_ind_v1.compat_iff_
    · exact ih_3
    · exact ih_4
  case
      compat_forall_ phi phi' x ih_1 ih_2
    | compat_exists_ phi phi' x ih_1 ih_2 =>
    first
      | apply are_alpha_equiv_ind_v1.compat_forall_
      | apply are_alpha_equiv_ind_v1.compat_exists_
    · exact ih_2
  case refl_ phi =>
    apply are_alpha_equiv_ind_v1.refl_
  case symm_ phi phi' _ ih_2 =>
    apply are_alpha_equiv_ind_v1.symm_
    exact ih_2
  case trans_ phi phi' phi'' ih_1 ih_2 ih_3 ih_4 =>
    apply are_alpha_equiv_ind_v1.trans_ phi phi'
    · exact ih_3
    · exact ih_4


lemma are_alpha_equiv_ind_v1_iff_are_alpha_equiv_ind_v2
  (F F' : Formula_) :
  are_alpha_equiv_ind_v1 F F' ↔ are_alpha_equiv_ind_v2 F F' :=
  by
  constructor
  · intro a1
    apply are_alpha_equiv_ind_v1_imp_are_alpha_equiv_ind_v2
    exact a1
  · intro a1
    apply are_alpha_equiv_ind_v2_imp_are_alpha_equiv_ind_v1
    exact a1

-------------------------------------------------------------------------------

example
  (F F' : Formula_)
  (h1 : are_alpha_equiv_ind_v1 F F') :
  F.free_var_set = F'.free_var_set :=
  by
  induction h1
  case rename_forall_ phi x y ih | rename_exists_ phi x y ih =>
    simp only [var_occurs_in_iff_mem_var_set] at ih

    simp only [free_var_set]
    apply replace_var_one_rec_free_var_set_sdiff
    exact ih
  case compat_not_ phi phi' ih_1 ih_2 =>
    simp only [free_var_set]
    exact ih_2
  case
      compat_imp_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_and_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_or_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4
    | compat_iff_ phi phi' psi psi' ih_1 ih_2 ih_3 ih_4 =>
    simp only [free_var_set]
    rw [ih_3]
    rw [ih_4]
  case compat_forall_ phi phi' x ih_1 ih_2 | compat_exists_ phi phi' x ih_1 ih_2 =>
    simp only [free_var_set]
    rw [ih_2]
  case refl_ phi =>
    rfl
  case symm_ phi phi' ih_1 ih_2 =>
    symm
    exact ih_2
  case trans_ phi phi' phi'' ih_1 ih_2 ih_3 ih_4 =>
    trans phi'.free_var_set
    · exact ih_3
    · exact ih_4


theorem replace_empty_holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (u v : VarName_)
  (F : Formula_)
  (a : D)
  (h1 : ¬ var_occurs_in v F) :
  holds D I (Function.updateITE V u a) E F ↔
    holds D I (Function.updateITE V v a) E (Sub.Var.One.Rec.fast_replace_free_var_one_rec u v F) :=
  by
  induction F generalizing V
  case pred_const_ X xs | pred_var_ X xs =>
    simp only [var_occurs_in] at h1

    simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
    simp only [holds]
    congr! 1
    simp
    intro x a1
    split_ifs
    case pos c1 =>
      rw [c1]
      simp only [Function.updateITE]
      simp
    case neg c1 =>
      have s1 : ¬ v = x :=
      by
        intro contra
        apply h1
        rw [contra]
        exact a1
      simp only [Function.updateITE]
      split_ifs <;> tauto
  case eq_ x y =>
    simp only [var_occurs_in] at h1

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
    simp only [var_occurs_in] at h1

    simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
    simp only [holds]
    congr! 1
    apply phi_ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [var_occurs_in] at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
    simp only [holds]
    congr! 1
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [var_occurs_in] at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
    split_ifs
    case pos c1 =>
      rw [c1]

      apply holds_coincide_var
      intro y a1
      simp only [var_is_free_in] at a1
      obtain ⟨a1_left, a1_right⟩ := a1

      have s1 : ¬ y = v :=
      by
        intro contra
        apply h1_right
        rw [← contra]
        apply var_is_free_in_imp_var_occurs_in
        exact a1_right

      simp only [Function.updateITE]
      split_ifs
      rfl
    case neg c1 =>
      simp only [holds]
      first
        | apply forall_congr'
        | apply exists_congr
      intro d
      simp only [Function.updateITE_comm V v x d a h1_left]
      simp only [Function.updateITE_comm V u x d a c1]
      apply phi_ih
      exact h1_right
  case def_ X xs =>
    induction E
    case nil =>
      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
    case cons hd tl ih =>
      simp only [var_occurs_in] at h1

      simp only [Sub.Var.One.Rec.fast_replace_free_var_one_rec]
      simp only [holds]
      congr! 1
      case _ =>
        simp
      case _ c1 =>
        simp at c1

        apply holds_coincide_var
        intro y a1

        simp
        apply Function.updateListITE_map_mem_ext
        · intro z a2

          have s1 : ¬ z = v :=
          by
            intro contra
            apply h1
            rw [← contra]
            exact a2

          simp
          by_cases c2 : z = u
          case pos =>
            rw [c2]
            simp
            simp only [Function.updateITE]
            simp
          case neg =>
            split_ifs
            case pos c3 =>
              rw [c3] at c2
              contradiction
            case neg c3 =>
              simp only [Function.updateITE]
              split_ifs
              rfl
        · tauto
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          obtain s1 := hd.h1
          obtain s2 := Finset.mem_of_subset s1 a1
          simp only [List.mem_toFinset] at s2
          exact s2


theorem holds_iff_are_alpha_equiv_ind_v2_holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F F' : Formula_)
  (h1 : are_alpha_equiv_ind_v2 F F') :
  holds D I V E F ↔ holds D I V E F' :=
  by
  induction h1 generalizing V
  case
    rename_forall_ h1_phi h1_x h1_y h1_1
  | rename_exists_ h1_phi h1_x h1_y h1_1 =>
    simp only [holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    apply replace_empty_holds
    exact h1_1
  case compat_not_ h1_phi h1_phi' _ h1_ih =>
    simp only [holds]
    congr! 1
    apply h1_ih
  case
    compat_imp_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_and_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_or_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_iff_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2 =>
    simp only [holds]
    congr! 1
    · apply h1_ih_1
    · apply h1_ih_2
  case
    compat_forall_ h1_phi h1_psi h1_x _ h1_ih
  | compat_exists_ h1_phi h1_psi h1_x _ h1_ih =>
    simp only [holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    apply h1_ih
  case refl_ h1 =>
    rfl
  case symm_ h1_phi h1_phi' _ h1_ih =>
    symm
    apply h1_ih
  case trans_ h1_phi h1_phi' h1_phi'' _ _ h1_ih_1 h1_ih_2 =>
    trans holds D I V E h1_phi'
    · apply h1_ih_1
    · apply h1_ih_2

-------------------------------------------------------------------------------

/--
  Helper definition for `are_alpha_equiv_ind_aux_v3`.
-/
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


/--
  Helper definition for `are_alpha_equiv_ind_v3`.
-/
inductive are_alpha_equiv_ind_aux_v3 :
  List (VarName_ × VarName_) → Formula_ → Formula_ → Prop

  | pred_var_
    (binders : List (VarName_ × VarName_))
    (X : PredName_)
    (xs ys : List VarName_) :
    List.Forall₂ (are_alpha_equiv_var_ind_v3 binders) xs ys →
    are_alpha_equiv_ind_aux_v3 binders (pred_var_ X xs) (pred_var_ X ys)

  | pred_const_
    (binders : List (VarName_ × VarName_))
    (X : PredName_)
    (xs ys : List VarName_) :
    List.Forall₂ (are_alpha_equiv_var_ind_v3 binders) xs ys →
    are_alpha_equiv_ind_aux_v3 binders (pred_const_ X xs) (pred_const_ X ys)

  | compat_true_
    (binders : List (VarName_ × VarName_)) :
    are_alpha_equiv_ind_aux_v3 binders true_ true_

  | compat_false_
    (binders : List (VarName_ × VarName_)) :
    are_alpha_equiv_ind_aux_v3 binders false_ false_

  | compat_not_
    (binders : List (VarName_ × VarName_))
    (phi phi' : Formula_) :
    are_alpha_equiv_ind_aux_v3 binders phi phi' →
    are_alpha_equiv_ind_aux_v3 binders (not_ phi) (not_ phi')

  | compat_imp_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_aux_v3 binders phi phi' →
    are_alpha_equiv_ind_aux_v3 binders psi psi' →
    are_alpha_equiv_ind_aux_v3 binders (imp_ phi psi) (imp_ phi' psi')

  | compat_and_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_aux_v3 binders phi phi' →
    are_alpha_equiv_ind_aux_v3 binders psi psi' →
    are_alpha_equiv_ind_aux_v3 binders (and_ phi psi) (and_ phi' psi')

  | compat_or_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_aux_v3 binders phi phi' →
    are_alpha_equiv_ind_aux_v3 binders psi psi' →
    are_alpha_equiv_ind_aux_v3 binders (or_ phi psi) (or_ phi' psi')

  | compat_iff_
    (binders : List (VarName_ × VarName_))
    (phi phi' psi psi' : Formula_) :
    are_alpha_equiv_ind_aux_v3 binders phi phi' →
    are_alpha_equiv_ind_aux_v3 binders psi psi' →
    are_alpha_equiv_ind_aux_v3 binders (iff_ phi psi) (iff_ phi' psi')

  | compat_forall_
    (binders : List (VarName_ × VarName_))
    (phi phi' : Formula_)
    (x y : VarName_) :
    are_alpha_equiv_ind_aux_v3 ((x, y) :: binders) phi phi' →
    are_alpha_equiv_ind_aux_v3 binders (forall_ x phi) (forall_ y phi')

  | compat_exists_
    (binders : List (VarName_ × VarName_))
    (phi phi' : Formula_)
    (x y : VarName_) :
    are_alpha_equiv_ind_aux_v3 ((x, y) :: binders) phi phi' →
    are_alpha_equiv_ind_aux_v3 binders (exists_ x phi) (exists_ y phi')


/--
  `are_alpha_equiv_ind_v3 F F'` := True if and only if `F` and `F'` are alpha equivalent.
-/
def are_alpha_equiv_ind_v3
  (F F' : Formula_) :
  Prop :=
  are_alpha_equiv_ind_aux_v3 [] F F'


#lint
