import MathlibExtra.FunctionUpdateITE
import FOL.NV.Sub.Var.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec

open Formula_


/--
  Helper function for `replace_free_var_all_rec`.
-/
def replace_free_var_all_rec_aux
  (σ : VarName_ → VarName_)
  (binders : Finset VarName_) :
  Formula_ → Formula_
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName_) => if x ∉ binders then σ x else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName_) => if x ∉ binders then σ x else x)
  | eq_ x y =>
      eq_
      (if x ∉ binders then σ x else x)
      (if y ∉ binders then σ y else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_free_var_all_rec_aux σ binders phi)
  | imp_ phi psi =>
      imp_
      (replace_free_var_all_rec_aux σ binders phi)
      (replace_free_var_all_rec_aux σ binders psi)
  | and_ phi psi =>
      and_
      (replace_free_var_all_rec_aux σ binders phi)
      (replace_free_var_all_rec_aux σ binders psi)
  | or_ phi psi =>
      or_
      (replace_free_var_all_rec_aux σ binders phi)
      (replace_free_var_all_rec_aux σ binders psi)
  | iff_ phi psi =>
      iff_
      (replace_free_var_all_rec_aux σ binders phi)
      (replace_free_var_all_rec_aux σ binders psi)
  | forall_ x phi =>
      forall_ x (replace_free_var_all_rec_aux σ (binders ∪ {x}) phi)
  | exists_ x phi =>
      exists_ x (replace_free_var_all_rec_aux σ (binders ∪ {x}) phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName_) => if x ∉ binders then σ x else x)


/--
  `replace_free_var_all_rec σ F` := The simultaneous replacement of each free occurrence of any variable `v` in the formula `F` by `σ v`.
-/
def replace_free_var_all_rec
  (σ : VarName_ → VarName_)
  (F : Formula_) :
  Formula_ :=
  replace_free_var_all_rec_aux σ ∅ F


/--
  `fast_replace_free_var_all_rec σ F` := The simultaneous replacement of each free occurrence of any variable `v` in the formula `F` by `σ v`.
-/
def fast_replace_free_var_all_rec
  (σ : VarName_ → VarName_) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (fast_replace_free_var_all_rec σ phi)
  | imp_ phi psi =>
      imp_
      (fast_replace_free_var_all_rec σ phi)
      (fast_replace_free_var_all_rec σ psi)
  | and_ phi psi =>
      and_
      (fast_replace_free_var_all_rec σ phi)
      (fast_replace_free_var_all_rec σ psi)
  | or_ phi psi =>
      or_
      (fast_replace_free_var_all_rec σ phi)
      (fast_replace_free_var_all_rec σ psi)
  | iff_ phi psi =>
      iff_
      (fast_replace_free_var_all_rec σ phi)
      (fast_replace_free_var_all_rec σ psi)
  | forall_ x phi =>
      forall_ x (fast_replace_free_var_all_rec (Function.updateITE σ x x) phi)
  | exists_ x phi =>
      exists_ x (fast_replace_free_var_all_rec (Function.updateITE σ x x) phi)
  | def_ X xs => def_ X (xs.map σ)


theorem fast_replace_free_var_all_rec_id
  (F : Formula_) :
  fast_replace_free_var_all_rec id F = F :=
  by
  induction F
  all_goals
    simp only [fast_replace_free_var_all_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr!
    simp
  case eq_ x y =>
    congr!
  case not_ phi phi_ih =>
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    congr!
    simp only [Function.updateITE_id]
    exact phi_ih


example
  (F : Formula_)
  (v t : VarName_) :
  fast_replace_free_var_all_rec (Function.updateITE id v t) F =
    One.Rec.fast_replace_free_var_one_rec v t F :=
  by
  induction F
  all_goals
    simp only [fast_replace_free_var_all_rec]
    simp only [One.Rec.fast_replace_free_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x _
    simp only [Function.updateITE]
    simp only [eq_comm]
    simp
  case eq_ x y =>
    simp only [Function.updateITE]
    simp only [eq_comm]
    simp
  case not_ phi phi_ih =>
    simp
    exact phi_ih
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
      subst c1
      simp
      simp only [Function.updateITE_idem]
      simp only [Function.updateITE_id]
      apply fast_replace_free_var_all_rec_id
    case neg c1 =>
      simp
      simp only [← phi_ih]
      congr! 1
      apply Function.updateITE_comm_id x v t
      tauto


theorem fast_replace_free_var_all_rec_same_on_free
  (F : Formula_)
  (σ σ' : VarName_ → VarName_)
  (h1 : ∀ (v : VarName_), var_is_free_in v F → σ v = σ' v) :
  fast_replace_free_var_all_rec σ F = fast_replace_free_var_all_rec σ' F :=
  by
  induction F generalizing σ σ'
  all_goals
    simp only [var_is_free_in] at h1

    simp only [fast_replace_free_var_all_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case eq_ x y =>
    congr! 1
    · apply h1
      left
      rfl
    · apply h1
      right
      rfl
  case not_ phi phi_ih =>
    congr! 1
    apply phi_ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr! 1
    · apply phi_ih
      intro v a1
      apply h1
      left
      exact a1
    · apply psi_ih
      intro v a1
      apply h1
      right
      exact a1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    congr! 1
    apply phi_ih
    intro v a1
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      apply h1
      tauto


theorem replace_free_var_all_rec_aux_same_on_free
  (F : Formula_)
  (σ σ' : VarName_ → VarName_)
  (binders : Finset VarName_)
  (h1 : ∀ (v : VarName_), v ∉ binders → σ v = σ' v) :
  replace_free_var_all_rec_aux σ binders F =
    replace_free_var_all_rec_aux σ' binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [replace_free_var_all_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs <;> tauto
  case eq_ x y =>
    congr! 1
    · split_ifs <;> tauto
    · split_ifs <;> tauto
  case not_ phi phi_ih =>
    simp
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    congr! 1
    apply phi_ih
    simp
    tauto


example
  (F : Formula_)
  (σ : VarName_ → VarName_)
  (binders : Finset VarName_)
  (h1 : ∀ (v : VarName_), v ∈ binders → v = σ v) :
  replace_free_var_all_rec_aux σ binders F =
    fast_replace_free_var_all_rec σ F :=
  by
  induction F generalizing binders σ
  all_goals
    simp only [fast_replace_free_var_all_rec]
    simp only [replace_free_var_all_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs <;> tauto
  case eq_ x y =>
    congr! 1
    · split_ifs <;> tauto
    · split_ifs <;> tauto
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
    congr! 1

    have s1 : (∀ (v : VarName_), v ∈ binders ∪ {x} → v = Function.updateITE σ x x v) :=
    by
      intros v a1
      simp at a1
      simp only [Function.updateITE]
      cases a1
      case _ c1 =>
        split_ifs <;> tauto
      case _ c1 =>
        simp only [if_pos c1]
        exact c1

    simp only [← phi_ih (Function.updateITE σ x x) (binders ∪ {x}) s1]
    apply replace_free_var_all_rec_aux_same_on_free
    simp only [Function.updateITE]
    intro v a1
    simp at a1
    obtain ⟨a1_left, a1_right⟩ := a1
    simp only [if_neg a1_right]


#lint
