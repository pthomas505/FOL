import MathlibExtra.List
import FOL.NV.Binders


set_option autoImplicit false


open Formula_


/--
  `replace_var_one_rec v t P` :=

  `v → t` in `P` for each occurrence of `v` in `P`

  The result of replacing each occurrence of `v` in `P` by an occurrence of `t`.
-/
def replace_var_one_rec (v t : VarName_) : Formula_ → Formula_
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)
  | eq_ x y =>
      eq_
      (if v = x then t else x)
      (if v = y then t else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_var_one_rec v t phi)
  | imp_ phi psi => imp_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | and_ phi psi => and_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | or_ phi psi => or_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | iff_ phi psi => iff_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | forall_ x phi =>
      if v = x
      then forall_ t (replace_var_one_rec v t phi)
      else forall_ x (replace_var_one_rec v t phi)
  | exists_ x phi =>
      if v = x
      then exists_ t (replace_var_one_rec v t phi)
      else exists_ x (replace_var_one_rec v t phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)


theorem replace_var_one_rec_self
  (F : Formula_)
  (v : VarName_) :
  replace_var_one_rec v v F = F :=
  by
  induction F
  any_goals
    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
  case eq_ x y =>
    simp
  case not_ phi phi_ih =>
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    split_ifs
    case pos c1 =>
      rw [phi_ih]
      rw [c1]
    case neg c1 =>
      rw [phi_ih]


theorem not_var_occurs_in_replace_var_one_rec_self
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in v F) :
  replace_var_one_rec v t F = F :=
  by
  induction F
  any_goals
    simp only [var_occurs_in] at h1

    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
    intro x a1 a2
    subst a2
    contradiction
  case eq_ x y =>
    simp
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    split_ifs
    rw [phi_ih h1_right]


theorem replace_var_one_rec_inverse
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in t F) :
  replace_var_one_rec t v (replace_var_one_rec v t F) = F :=
  by
  induction F
  any_goals
    simp only [var_occurs_in] at h1

    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr!
    simp
    simp only [List.map_eq_self_iff]
    simp
    intro x a1
    by_cases c1 : v = x
    · simp only [if_pos c1]
      simp
      exact c1
    · simp only [if_neg c1]
      simp
      intro a2
      subst a2
      contradiction
  case eq_ x y =>
      congr!
      · split_ifs <;> tauto
      · split_ifs <;> tauto
  case not_ phi phi_ih =>
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
      congr! <;> tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    push_neg at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    split_ifs
    case pos c1 =>
      simp only [replace_var_one_rec]
      simp
      tauto
    case neg c1 =>
      simp only [replace_var_one_rec]
      simp only [if_neg h1_left]
      congr!
      exact phi_ih h1_right


theorem not_var_occurs_in_replace_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ v = t) :
  ¬ var_occurs_in v (replace_var_one_rec v t F) :=
  by
  induction F
  any_goals
    simp only [replace_var_one_rec]
    simp only [var_occurs_in]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x
    split_ifs <;> tauto
  case eq_ x y =>
    split_ifs <;> tauto
  case true_ | false_ =>
    simp
  case not_ phi phi_ih =>
    exact phi_ih
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [replace_var_one_rec]
    split_ifs
    case pos c1 =>
      simp only [var_occurs_in]
      simp
      exact ⟨h1, phi_ih⟩
    case neg c1 =>
      simp only [var_occurs_in]
      simp
      exact ⟨c1, phi_ih⟩


theorem replace_var_one_rec_free_var_set_sdiff
  (F : Formula_)
  (v t : VarName_)
  (h1 : t ∉ F.var_set) :
  F.free_var_set \ {v} = (replace_var_one_rec v t F).free_var_set \ {t} :=
  by
    induction F
    all_goals
      simp only [var_set] at h1
    case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
      simp only [replace_var_one_rec]
      simp only [free_var_set]
      ext x
      simp
      constructor
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · apply Exists.intro x
          simp only [eq_comm] at a1_right
          split_ifs
          exact ⟨a1_left, rfl⟩
        · intro contra
          apply h1
          rw [← contra]
          simp
          exact a1_left
      · intro a1
        obtain ⟨⟨y, ⟨a1_left_left, a1_left_right⟩⟩, a1_right⟩ := a1
        split_ifs at a1_left_right
        case pos c1 =>
          rw [a1_left_right] at a1_right
          contradiction
        case neg c1 =>
          subst a1_left_right
          tauto
    case eq_ x y =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var_one_rec]
      simp only [free_var_set]
      simp only [Finset.sdiff_singleton_eq_erase]
      split_ifs
      case pos c1 c2 =>
        rw [← c1]
        rw [← c2]
        simp
      case neg c1 c2 =>
        rw [← c1]
        simp_all
      case pos c1 c2 =>
        aesop
      case neg c1 c2 =>
        simp_all
    case true_ | false_ =>
      simp only [replace_var_one_rec]
      simp only [free_var_set]
      simp
    case not_ phi phi_ih =>
      simp only [replace_var_one_rec]
      simp only [free_var_set]
      exact phi_ih h1
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var_one_rec]
      simp only [free_var_set]
      simp only [Finset.union_sdiff_distrib]
      rw [phi_ih h1_left]
      rw [psi_ih h1_right]
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var_one_rec]
      split_ifs
      case pos c1 =>
        rw [← c1]
        simp only [free_var_set]
        simp
        exact phi_ih h1_left
      case neg c1 =>
        simp only [free_var_set]
        simp only [sdiff_sdiff_comm]
        congr 1
        exact phi_ih h1_left


#lint
