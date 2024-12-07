import FOL.NV.Sub.Var.One.Rec.ReplaceFree
import FOL.NV.Semantics

import Mathlib.Data.List.Defs

set_option autoImplicit false


open Formula_


/--
  Helper function for `are_alpha_equiv_var_list_rec`.
-/
def are_alpha_equiv_var_rec :
  List (VarName_ × VarName_) → VarName_ → VarName_ → Prop
  | [], x, y => x = y

  | hd :: tl, x, y =>
      (x = hd.fst ∧ y = hd.snd) ∨
        ((¬ x = hd.fst ∧ ¬ y = hd.snd) ∧ are_alpha_equiv_var_rec tl x y)

instance
  (binders : List (VarName_ × VarName_))
  (x y : VarName_) :
  Decidable (are_alpha_equiv_var_rec binders x y) :=
  by
  induction binders
  all_goals
    simp only [are_alpha_equiv_var_rec]
    infer_instance


/-
    if x = hd.fst
    then y = hd.snd
    else ¬ y = hd.snd ∧ is_alpha_eqv_var tl x y
-/
/--
  Helper function for `are_alpha_equiv_rec_aux`.
-/
def are_alpha_equiv_var_list_rec
  (binders : List (VarName_ × VarName_)) :
  List VarName_ → List VarName_ → Prop
  | [], [] => True

  | x_hd :: x_tl, y_hd :: y_tl =>
      are_alpha_equiv_var_rec binders x_hd y_hd ∧
        are_alpha_equiv_var_list_rec binders x_tl y_tl

  | _, _ => False

instance
  (binders : List (VarName_ × VarName_))
  (xs ys : List VarName_) :
  Decidable (are_alpha_equiv_var_list_rec binders xs ys) :=
  by
  induction xs generalizing ys
  all_goals
    cases ys
    all_goals
      simp only [are_alpha_equiv_var_list_rec]
      infer_instance


example
  (xs : List VarName_) :
  are_alpha_equiv_var_list_rec [] xs xs :=
  by
  induction xs
  case nil =>
    simp only [are_alpha_equiv_var_list_rec]
  case cons hd tl ih =>
    simp only [are_alpha_equiv_var_list_rec]
    constructor
    · simp only [are_alpha_equiv_var_rec]
    · exact ih


/--
  Helper function for `are_alpha_equiv_rec`.
-/
def are_alpha_equiv_rec_aux
  (binders : List (VarName_ × VarName_)) :
  Formula_ → Formula_ → Prop
  | pred_const_ X xs, pred_const_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | pred_var_ X xs, pred_var_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | eq_ x y, eq_ x' y' =>
      are_alpha_equiv_var_rec binders x x' ∧ are_alpha_equiv_var_rec binders y y'

  | true_, true_ => True

  | false_, false_ => True

  | not_ phi, not_ phi' => are_alpha_equiv_rec_aux binders phi phi'

  | imp_ phi psi, imp_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | and_ phi psi, and_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | or_ phi psi, or_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | iff_ phi psi, iff_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | forall_ x phi, forall_ x' phi' =>
      are_alpha_equiv_rec_aux ((x, x') :: binders) phi phi'

  | exists_ x phi, exists_ x' phi' =>
      are_alpha_equiv_rec_aux ((x, x') :: binders) phi phi'

  | def_ X xs, def_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | _, _ => False

instance
  (binders : List (VarName_ × VarName_))
  (F F' : Formula_) :
  Decidable (are_alpha_equiv_rec_aux binders F F') :=
  by
  induction F generalizing F' binders
  all_goals
    cases F'
    all_goals
      simp only [are_alpha_equiv_rec_aux]
      infer_instance


/--
  `are_alpha_equiv_rec F F'` := True if and only if `F` and `F'` are alpha equivalent.
-/
def are_alpha_equiv_rec (F F' : Formula_) : Prop :=
  are_alpha_equiv_rec_aux [] F F'

instance
  (F F' : Formula_) :
  Decidable (are_alpha_equiv_rec F F') :=
  by
  simp only [are_alpha_equiv_rec]
  infer_instance


/--
  Helper definition for proof of `holds_iff_are_alpha_equiv_rec_holds`.
-/
inductive alpha_equiv_var_valuation
  (D : Type) :
  List (VarName_ × VarName_) → Valuation_ D → Valuation_ D → Prop
  | nil
    (V : Valuation_ D) :
    alpha_equiv_var_valuation D [] V V

  | cons
    (binders : List (VarName_ × VarName_))
    (x y : VarName_)
    (V V' : Valuation_ D)
    (d : D) :
    alpha_equiv_var_valuation D binders V V' →
    alpha_equiv_var_valuation D ((x, y) :: binders) (Function.updateITE V x d) (Function.updateITE V' y d)

-------------------------------------------------------------------------------

theorem aux_1
  (D : Type)
  (binders : List (VarName_ × VarName_))
  (x y : VarName_)
  (V V' : Valuation_ D)
  (h1 : alpha_equiv_var_valuation D binders V V')
  (h2 : are_alpha_equiv_var_rec binders x y) :
  V x = V' y :=
  by
  induction h1
  case nil h1_V =>
    simp only [are_alpha_equiv_var_rec] at h2
    rw [h2]
  case cons h1_l h1_x h1_y h1_V h1_V' h1_d _ h1_ih =>
    simp only [are_alpha_equiv_var_rec] at h2

    simp only [Function.updateITE]
    cases h2
    case inl c1 =>
      obtain ⟨c1_left, c1_right⟩ := c1
      split_ifs
      rfl
    case inr c1 =>
      obtain ⟨⟨c1_left_left, c1_left_right⟩, c1_right⟩ := c1
      split_ifs
      apply h1_ih
      exact c1_right


theorem aux_2
  (D : Type)
  (binders : List (VarName_ × VarName_))
  (xs ys : List VarName_)
  (V V' : Valuation_ D)
  (h1 : alpha_equiv_var_valuation D binders V V')
  (h2 : are_alpha_equiv_var_list_rec binders xs ys) :
  List.map V xs = List.map V' ys :=
  by
  induction xs generalizing ys
  case nil =>
    cases ys
    case nil =>
      simp
    case cons ys_hd ys_tl =>
      simp only [are_alpha_equiv_var_list_rec] at h2
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [are_alpha_equiv_var_list_rec] at h2
    case cons ys_hd ys_tl =>
      simp only [are_alpha_equiv_var_list_rec] at h2
      obtain ⟨h2_left, h2_right⟩ := h2

      simp
      constructor
      · apply aux_1 D binders
        · exact h1
        · exact h2_left
      · apply xs_ih
        exact h2_right


lemma are_alpha_equiv_var_list_rec_length
  (binders : List (VarName_ × VarName_))
  (xs ys : List VarName_)
  (h1 : are_alpha_equiv_var_list_rec binders xs ys) :
  xs.length = ys.length :=
  by
  induction xs generalizing ys
  case nil =>
    cases ys
    case nil =>
      rfl
    case cons ys_hd ys_tl =>
      simp only [are_alpha_equiv_var_list_rec] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [are_alpha_equiv_var_list_rec] at h1
    case cons ys_hd ys_tl =>
      simp only [are_alpha_equiv_var_list_rec] at h1

      simp
      obtain ⟨h1_left, h1_right⟩ := h1
      apply xs_ih
      exact h1_right


lemma holds_iff_are_alpha_equiv_rec_holds_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (F F' : Formula_)
  (binders : List (VarName_ × VarName_))
  (h1 : alpha_equiv_var_valuation D binders V V')
  (h2 : are_alpha_equiv_rec_aux binders F F') :
  holds D I V E F ↔ holds D I V' E F' :=
  by
  induction F generalizing F' binders V V'
  all_goals
    cases F'

  any_goals
    simp only [are_alpha_equiv_rec_aux] at h2

  case
    pred_const_.pred_const_ X xs Y ys
  | pred_var_.pred_var_ X xs Y ys =>
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [holds]
    rw [h2_left]
    congr! 1
    apply aux_2 D binders
    · exact h1
    · exact h2_right

  case eq_.eq_ x x' y y' =>
    cases h2
    case intro h2_left h2_right =>
      simp only [holds]
      congr! 1
      · apply aux_1 D binders
        · exact h1
        · exact h2_left
      · apply aux_1 D binders
        · exact h1
        · exact h2_right

  case true_.true_ | false_.false_ =>
    simp only [holds]

  case not_.not_ phi phi_ih phi' =>
    simp only [holds]
    congr! 1
    exact phi_ih V V' phi' binders h1 h2

  case
    imp_.imp_ phi psi phi_ih psi_ih phi' psi'
  | and_.and_ phi psi phi_ih psi_ih phi' psi'
  | or_.or_ phi psi phi_ih psi_ih phi' psi'
  | iff_.iff_ phi psi phi_ih psi_ih phi' psi' =>
    obtain ⟨h2_left, h2_right⟩ := h2
    simp only [holds]
    congr! 1
    · exact phi_ih V V' phi' binders h1 h2_left
    · exact psi_ih V V' psi' binders h1 h2_right

  case
    forall_.forall_ x phi phi_ih y phi'
  | exists_.exists_ x phi phi_ih y phi' =>
      simp only [holds]
      first | apply forall_congr' | apply exists_congr
      intro d
      induction h1
      case nil h1_V =>
        apply phi_ih
        · apply alpha_equiv_var_valuation.cons
          apply alpha_equiv_var_valuation.nil
        · exact h2
      case cons h1_binders h1_x h1_y h1_V h1_V' h1_d h1_1 _ =>
        apply phi_ih
        · apply alpha_equiv_var_valuation.cons
          apply alpha_equiv_var_valuation.cons
          exact h1_1
        · exact h2
  case def_.def_ X xs Y ys =>
    induction E
    case nil =>
      simp only [holds]
    case cons hd tl ih =>
      simp only [holds]
      split_ifs
      case _ c1 c2 =>
        obtain ⟨h2_left, h2_right⟩ := h2
        apply holds_coincide_var
        intro v a1
        rw [aux_2 D binders xs ys V V' h1 h2_right]
        apply Function.updateListITE_mem_eq_len
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          exact Finset.mem_of_subset hd.h1 a1
        · simp
          tauto
      case _ c1 c2 =>
        obtain ⟨h2_left, h2_right⟩ := h2
        simp only [are_alpha_equiv_var_list_rec_length binders xs ys h2_right] at c1
        rw [h2_left] at c1
        contradiction
      case _ c1 c2 =>
        obtain ⟨h2_left, h2_right⟩ := h2
        simp only [← are_alpha_equiv_var_list_rec_length binders xs ys h2_right] at c2
        rw [h2_left] at c1
        contradiction
      case _ c1 c2 =>
        apply ih


theorem holds_iff_are_alpha_equiv_rec_holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F F' : Formula_)
  (h1 : are_alpha_equiv_rec F F') :
  holds D I V E F ↔ holds D I V E F' :=
  by
  simp only [are_alpha_equiv_rec] at h1

  apply holds_iff_are_alpha_equiv_rec_holds_aux D I V V E F F' []
  apply alpha_equiv_var_valuation.nil
  exact h1


#lint
