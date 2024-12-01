import FOL.NV.Sub.Var.One.Rec.ReplaceFree
import FOL.NV.Semantics

import Mathlib.Data.List.Defs

set_option autoImplicit false


namespace FOL.NV

open Formula_



def are_alpha_equiv_var_rec : List (VarName_ × VarName_) → VarName_ → VarName_ → Prop
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


lemma isAlphaEqvVarListId
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


def are_alpha_equiv_rec_aux : List (VarName_ × VarName_) → Formula_ → Formula_ → Prop
  | binders, pred_const_ X xs, pred_const_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | binders, pred_var_ X xs, pred_var_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | binders, eq_ x y, eq_ x' y' =>
      are_alpha_equiv_var_rec binders x x' ∧ are_alpha_equiv_var_rec binders y y'

  | _, true_, true_ => True

  | _, false_, false_ => True

  | binders, not_ phi, not_ phi' => are_alpha_equiv_rec_aux binders phi phi'

  | binders, imp_ phi psi, imp_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | binders, and_ phi psi, and_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | binders, or_ phi psi, or_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | binders, iff_ phi psi, iff_ phi' psi' =>
      are_alpha_equiv_rec_aux binders phi phi' ∧ are_alpha_equiv_rec_aux binders psi psi'

  | binders, forall_ x phi, forall_ x' phi' =>
      are_alpha_equiv_rec_aux ((x, x')::binders) phi phi'

  | binders, exists_ x phi, exists_ x' phi' =>
      are_alpha_equiv_rec_aux ((x, x')::binders) phi phi'

  | binders, def_ X xs, def_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | _, _, _ => False


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


def are_alpha_equiv_rec (F F' : Formula_) : Prop :=
  are_alpha_equiv_rec_aux [] F F'


instance
  (F F' : Formula_) :
  Decidable (are_alpha_equiv_rec F F') :=
  by
  simp only [are_alpha_equiv_rec]
  infer_instance


inductive AlphaEqvVarAssignment
  (D : Type) :
  List (VarName_ × VarName_) → Valuation_ D → Valuation_ D → Prop
  | nil {V} :
    AlphaEqvVarAssignment D [] V V

  | cons {binders x y V V' d} :
    AlphaEqvVarAssignment D binders V V' →
    AlphaEqvVarAssignment D ((x, y)::binders) (Function.updateITE V x d) (Function.updateITE V' y d)


theorem aux_1
  (D : Type)
  (binders : List (VarName_ × VarName_))
  (x y : VarName_)
  (V V' : Valuation_ D)
  (h1 : AlphaEqvVarAssignment D binders V V')
  (h2 : are_alpha_equiv_var_rec binders x y) :
  V x = V' y :=
  by
  induction h1
  case nil h1_V =>
    simp only [are_alpha_equiv_var_rec] at h2

    subst h2
    rfl
  case cons h1_l h1_x h1_y h1_V h1_V' h1_d _ h1_ih =>
    simp only [are_alpha_equiv_var_rec] at h2

    simp only [Function.updateITE]
    cases h2
    case inl h2 =>
      cases h2
      case intro h2_left h2_right =>
        simp only [if_pos h2_left, if_pos h2_right]
    case inr h2 =>
      cases h2
      case intro h2_left h2_right =>
        cases h2_left
        case intro h2_left_left h2_left_right =>
          simp only [if_neg h2_left_left, if_neg h2_left_right]
          exact h1_ih h2_right


theorem aux_2
  (D : Type)
  (binders : List (VarName_ × VarName_))
  (xs ys : List VarName_)
  (V V' : Valuation_ D)
  (h1 : AlphaEqvVarAssignment D binders V V')
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

      simp
      constructor
      · cases h2
        case left.intro h2_left h2_right =>
          exact aux_1 D binders xs_hd ys_hd V V' h1 h2_left
      · apply xs_ih ys_tl
        cases h2
        case right.intro h2_left h2_right =>
          exact h2_right


lemma isAlphaEqvVarList_length
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
      cases h1
      case intro h1_left h1_right =>
        exact xs_ih ys_tl h1_right


lemma isAlphaEqv_Holds_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (F F' : Formula_)
  (binders : List (VarName_ × VarName_))
  (h1 : AlphaEqvVarAssignment D binders V V')
  (h2 : are_alpha_equiv_rec_aux binders F F') :
  holds D I V E F ↔ holds D I V' E F' :=
  by
  induction E generalizing F F' binders V V'
  all_goals
    induction F generalizing F' binders V V'
    all_goals
      cases F'

    any_goals
      simp only [are_alpha_equiv_rec_aux] at h2

    case
      pred_const_.pred_const_ X xs Y ys
    | pred_var_.pred_var_ X xs Y ys =>
      cases h2
      case intro h2_left h2_right =>
        simp only [holds]
        subst h2_left
        congr! 1
        exact aux_2 D binders xs ys V V' h1 h2_right

    case eq_.eq_ x x' y y' =>
      cases h2
      case intro h2_left h2_right =>
        simp only [holds]
        congr! 1
        · exact aux_1 D binders x y V V' h1 h2_left
        · exact aux_1 D binders x' y' V V' h1 h2_right

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
      cases h2
      case intro h2_left h2_right =>
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
          · apply AlphaEqvVarAssignment.cons
            apply AlphaEqvVarAssignment.nil
          · exact h2
        case cons h1_binders h1_x h1_y h1_V h1_V' h1_d h1_1 _ =>
          apply phi_ih
          · apply AlphaEqvVarAssignment.cons
            apply AlphaEqvVarAssignment.cons
            exact h1_1
          · exact h2

  case nil.def_.def_ =>
    simp only [holds]
  case cons.def_.def_ hd tl ih X xs Y ys =>
    simp only [holds]
    split_ifs
    case _ c1 c2 =>
      cases h2
      case intro h2_left h2_right =>
        apply holds_coincide_var
        intro v a1
        simp only [aux_2 D binders xs ys V V' h1 h2_right]
        apply Function.updateListITE_mem_eq_len
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset hd.h1 a1
        · simp
          simp only [eq_comm]
          cases c2
          case intro c2_left c2_right =>
            exact c2_right
    case _ c1 c2 =>
      cases h2
      case intro h2_left h2_right =>
        simp only [isAlphaEqvVarList_length binders xs ys h2_right] at c1
        subst h2_left
        contradiction
    case _ c1 c2 =>
      cases h2
      case intro h2_left h2_right =>
        simp only [← isAlphaEqvVarList_length binders xs ys h2_right] at c2
        subst h2_left
        contradiction
    case _ c1 c2 =>
      exact ih V V' (def_ X xs) (def_ Y ys) binders h1 h2


lemma isalphaEqv_Holds
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (F F' : Formula_)
  (h1 : are_alpha_equiv_rec F F') :
  holds D I V E F ↔ holds D I V E F' :=
  by
  simp only [are_alpha_equiv_rec] at h1

  exact isAlphaEqv_Holds_aux D I V V E F F' [] AlphaEqvVarAssignment.nil h1


--#lint