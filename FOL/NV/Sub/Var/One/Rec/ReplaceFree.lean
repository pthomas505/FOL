import MathlibExtra.List
import FOL.NV.Binders


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Rec

open Formula_


/-
[margaris]
pg. 48

If `P` is a formula, `v` is a variable, and `t` is a term, then `P(t/v)` is the result of replacing each free occurrence of `v` in `P` by an occurrence of `t`.
-/

/--
  Helper function for `replace_free_var_one_rec`.
-/
def replace_free_var_one_rec_aux
  (v t : VarName_)
  (binders : Finset VarName_) :
  Formula_ → Formula_
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName_) => if v = x ∧ x ∉ binders then t else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName_) => if v = x ∧ x ∉ binders then t else x)
  | eq_ x y =>
      eq_
      (if v = x ∧ x ∉ binders then t else x)
      (if v = y ∧ y ∉ binders then t else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_free_var_one_rec_aux v t binders phi)
  | imp_ phi psi =>
      imp_
      (replace_free_var_one_rec_aux v t binders phi)
      (replace_free_var_one_rec_aux v t binders psi)
  | and_ phi psi =>
      and_
      (replace_free_var_one_rec_aux v t binders phi)
      (replace_free_var_one_rec_aux v t binders psi)
  | or_ phi psi =>
      or_
      (replace_free_var_one_rec_aux v t binders phi)
      (replace_free_var_one_rec_aux v t binders psi)
  | iff_ phi psi =>
      iff_
      (replace_free_var_one_rec_aux v t binders phi)
      (replace_free_var_one_rec_aux v t binders psi)
  | forall_ x phi => forall_ x (replace_free_var_one_rec_aux v t (binders ∪ {x}) phi)
  | exists_ x phi => exists_ x (replace_free_var_one_rec_aux v t (binders ∪ {x}) phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName_) => if v = x ∧ x ∉ binders then t else x)

/--
  `replace_free_var_one_rec v t P` :=

  `P(t/v)`

  `v → t` in `P` for each free occurrence of `v` in `P`

  The result of replacing each free occurrence of `v` in `P` by an occurrence of `t`.
-/
def replace_free_var_one_rec (v t : VarName_) (F : Formula_) : Formula_ :=
  replace_free_var_one_rec_aux v t ∅ F


/--
  `fast_replace_free_var_one_rec v t P` :=

  `P(t/v)`

  `v → t` in `P` for each free occurrence of `v` in `P`

  The result of replacing each free occurrence of `v` in `P` by an occurrence of `t`.

  This is a more efficient version of `replace_free_var_one_rec`.
-/
def fast_replace_free_var_one_rec (v t : VarName_) : Formula_ → Formula_
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
  | not_ phi => not_ (fast_replace_free_var_one_rec v t phi)
  | imp_ phi psi => imp_ (fast_replace_free_var_one_rec v t phi) (fast_replace_free_var_one_rec v t psi)
  | and_ phi psi => and_ (fast_replace_free_var_one_rec v t phi) (fast_replace_free_var_one_rec v t psi)
  | or_ phi psi => or_ (fast_replace_free_var_one_rec v t phi) (fast_replace_free_var_one_rec v t psi)
  | iff_ phi psi => iff_ (fast_replace_free_var_one_rec v t phi) (fast_replace_free_var_one_rec v t psi)
  | forall_ x phi =>
      if v = x
      then forall_ x phi  -- `v` is not free in `forall_ x phi`
      else forall_ x (fast_replace_free_var_one_rec v t phi)
  | exists_ x phi =>
      if v = x
      then exists_ x phi  -- `v` is not free in `exists_ x phi`
      else exists_ x (fast_replace_free_var_one_rec v t phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)


-- `replace_free_var_one_rec` = `fast_replace_free_var_one_rec`

theorem replace_free_var_one_rec_aux_mem_binders
  (F : Formula_)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∈ binders) :
  replace_free_var_one_rec_aux v t binders F = F :=
  by
  induction F generalizing binders
  any_goals
    simp only [replace_free_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
    intro x _ a2 a3
    subst a2
    contradiction
  case eq_ x y =>
    simp
    constructor
    case left | right =>
      intro a1 a2
      subst a1
      contradiction
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
    simp
    apply phi_ih
    simp
    left
    exact h1


theorem replace_free_var_one_rec_aux_eq_fast_replace_free_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders) :
  replace_free_var_one_rec_aux v t binders F =
    fast_replace_free_var_one_rec v t F :=
  by
  induction F generalizing binders
  any_goals
    simp only [replace_free_var_one_rec_aux]
    simp only [fast_replace_free_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr!
    case _ x =>
      constructor
      case mp =>
        tauto
      case mpr =>
        intro a1
        subst a1
        tauto
  case eq_ x y =>
    congr!
    case _ | _ =>
      constructor
      case mp =>
        tauto
      case mpr =>
        intro a1
        subst a1
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
    split_ifs
    case pos c1 =>
      congr! 1
      apply replace_free_var_one_rec_aux_mem_binders
      simp
      right
      exact c1
    case neg c1 =>
      congr! 1
      apply phi_ih
      simp
      tauto


theorem replace_free_var_one_rec_eq_fast_replace_free_var_one_rec
  (F : Formula_)
  (v t : VarName_) :
  replace_free_var_one_rec v t F = fast_replace_free_var_one_rec v t F :=
  by
  simp only [replace_free_var_one_rec]
  apply replace_free_var_one_rec_aux_eq_fast_replace_free_var_one_rec
  simp

--

theorem fast_replace_free_var_one_rec_self
  (F : Formula_)
  (v : VarName_) :
  fast_replace_free_var_one_rec v v F = F :=
  by
  induction F
  any_goals
    simp only [fast_replace_free_var_one_rec]
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
    simp
    intro _
    exact phi_ih


theorem not_var_is_free_in_fast_replace_free_var_one_rec_self
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_is_free_in v F) :
  fast_replace_free_var_one_rec v t F = F :=
  by
  induction F
  any_goals
    simp only [var_is_free_in] at h1

    simp only [fast_replace_free_var_one_rec]
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
    simp
    tauto


theorem fast_replace_free_var_one_rec_inverse
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in t F) :
  fast_replace_free_var_one_rec t v (fast_replace_free_var_one_rec v t F) = F :=
  by
  induction F
  any_goals
    simp only [var_occurs_in] at h1

    simp only [fast_replace_free_var_one_rec]
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
      simp only [fast_replace_free_var_one_rec]
      simp only [if_neg h1_left]
      congr!
      apply not_var_is_free_in_fast_replace_free_var_one_rec_self
      contrapose! h1_right
      apply var_is_free_in_imp_var_occurs_in
      exact h1_right
    case neg c1 =>
      simp only [fast_replace_free_var_one_rec]
      simp only [if_neg h1_left]
      congr!
      exact phi_ih h1_right


theorem not_var_is_free_in_fast_replace_free_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ v = t) :
  ¬ var_is_free_in v (fast_replace_free_var_one_rec v t F) :=
  by
  induction F
  any_goals
    simp only [fast_replace_free_var_one_rec]
    simp only [var_is_free_in]
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
    simp only [fast_replace_free_var_one_rec]
    split_ifs
    case pos c1 =>
      simp only [var_is_free_in]
      simp
      intro a1
      contradiction
    case neg c1 =>
      simp only [var_is_free_in]
      simp
      intro _
      exact phi_ih


#lint
