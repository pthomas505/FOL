import FOL.NV.Sub.Var.One.Rec.ReplaceFree
import FOL.NV.Semantics

import Mathlib.Data.List.Defs

set_option autoImplicit false


namespace FOL.NV

open Formula_


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


def isAlphaEqvAux : List (VarName_ × VarName_) → Formula_ → Formula_ → Prop
  | binders, pred_const_ X xs, pred_const_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | binders, pred_var_ X xs, pred_var_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | binders, eq_ x y, eq_ x' y' =>
      are_alpha_equiv_var_rec binders x x' ∧ are_alpha_equiv_var_rec binders y y'

  | _, true_, true_ => True

  | _, false_, false_ => True

  | binders, not_ phi, not_ phi' => isAlphaEqvAux binders phi phi'

  | binders, imp_ phi psi, imp_ phi' psi' =>
      isAlphaEqvAux binders phi phi' ∧ isAlphaEqvAux binders psi psi'

  | binders, and_ phi psi, and_ phi' psi' =>
      isAlphaEqvAux binders phi phi' ∧ isAlphaEqvAux binders psi psi'

  | binders, or_ phi psi, or_ phi' psi' =>
      isAlphaEqvAux binders phi phi' ∧ isAlphaEqvAux binders psi psi'

  | binders, iff_ phi psi, iff_ phi' psi' =>
      isAlphaEqvAux binders phi phi' ∧ isAlphaEqvAux binders psi psi'

  | binders, forall_ x phi, forall_ x' phi' =>
      isAlphaEqvAux ((x, x')::binders) phi phi'

  | binders, exists_ x phi, exists_ x' phi' =>
      isAlphaEqvAux ((x, x')::binders) phi phi'

  | binders, def_ X xs, def_ Y ys =>
      X = Y ∧ are_alpha_equiv_var_list_rec binders xs ys

  | _, _, _ => False


instance
  (binders : List (VarName_ × VarName_))
  (F F' : Formula_) :
  Decidable (isAlphaEqvAux binders F F') :=
  by
  induction F generalizing F' binders
  all_goals
    cases F'
    all_goals
      simp only [isAlphaEqvAux]
      infer_instance


def isAlphaEqv (F F' : Formula_) : Prop :=
  isAlphaEqvAux [] F F'


instance
  (F F' : Formula_) :
  Decidable (isAlphaEqv F F') :=
  by
  simp only [isAlphaEqv]
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
  (h2 : isAlphaEqvAux binders F F') :
  holds D I V E F ↔ holds D I V' E F' :=
  by
  induction E generalizing F F' binders V V'
  all_goals
    induction F generalizing F' binders V V'
    all_goals
      cases F'

    any_goals
      simp only [isAlphaEqvAux] at h2

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
  (h1 : isAlphaEqv F F') :
  holds D I V E F ↔ holds D I V E F' :=
  by
  simp only [isAlphaEqv] at h1

  exact isAlphaEqv_Holds_aux D I V V E F F' [] AlphaEqvVarAssignment.nil h1


--#lint
