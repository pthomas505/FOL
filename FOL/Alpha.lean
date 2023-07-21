import FOL.Sub.One.Rec.SubOneRecReplaceFree
import FOL.Semantics
import FOL.Tactics


namespace FOL

open Formula


inductive AlphaEqv : Formula → Formula → Prop
  | rename_forall_
    (phi : Formula)
    (x y : VarName) :
    ¬ isFreeIn y phi →
    ¬ isBoundIn y phi →
    AlphaEqv (forall_ x phi) (forall_ y (fastReplaceFree x y phi))

  | rename_exists_
    (phi : Formula)
    (x y : VarName) :
    ¬ isFreeIn y phi →
    ¬ isBoundIn y phi →
    AlphaEqv (exists_ x phi) (exists_ y (fastReplaceFree x y phi))

  | compat_not_
    (phi phi' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv (not_ phi) (not_ phi')

  | compat_imp_
    (phi phi' psi psi' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv psi psi' →
    AlphaEqv (imp_ phi psi) (imp_ phi' psi')

  | compat_and_
    (phi phi' psi psi' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv psi psi' →
    AlphaEqv (and_ phi psi) (and_ phi' psi')

  | compat_or_
    (phi phi' psi psi' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv psi psi' →
    AlphaEqv (or_ phi psi) (or_ phi' psi')

  | compat_iff_
    (phi phi' psi psi' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv psi psi' →
    AlphaEqv (iff_ phi psi) (iff_ phi' psi')

  | compat_forall_
    (phi phi' : Formula)
    (x : VarName) :
    AlphaEqv phi phi' →
    AlphaEqv (forall_ x phi) (forall_ x phi')

  | compat_exists_
    (phi phi' : Formula)
    (x : VarName) :
    AlphaEqv phi phi' →
    AlphaEqv (exists_ x phi) (exists_ x phi')

  | refl_
    (phi : Formula) :
    AlphaEqv phi phi

  | symm_
    (phi phi' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv phi' phi

  | trans_
    (phi phi' phi'' : Formula) :
    AlphaEqv phi phi' →
    AlphaEqv phi' phi'' →
    AlphaEqv phi phi''


theorem replace_empty_Holds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (u v : VarName)
  (F : Formula)
  (a : D)
  (h1 : ¬ isFreeIn v F)
  (h2 : ¬ isBoundIn v F) :
  Holds D I (Function.updateIte V u a) E F ↔
    Holds D I (Function.updateIte V v a) E (fastReplaceFree u v F) :=
  by
  induction E generalizing F V
  all_goals
    induction F generalizing V
    case pred_const_ X xs | pred_var_ X xs =>
      unfold isFreeIn at h1

      unfold fastReplaceFree
      simp only [Holds]
      congr! 1
      simp
      simp only [List.map_eq_map_iff]
      intro x a1
      simp
      unfold Function.updateIte
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
      unfold isFreeIn at h1

      unfold fastReplaceFree
      simp only [Holds]
      congr! 1
      · unfold Function.updateIte
        split_ifs <;> tauto
      · unfold Function.updateIte
        split_ifs <;> tauto
    case true_ | false_ =>
      unfold fastReplaceFree
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold isFreeIn at h1

      unfold isBoundIn at h2

      unfold fastReplaceFree
      simp only [Holds]
      congr! 1
      exact phi_ih V h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold isFreeIn at h1
      push_neg at h1

      unfold isBoundIn at h2
      push_neg at h2

      cases h1
      case intro h1_left h1_right =>
        cases h2
        case intro h2_left h2_right =>
          unfold fastReplaceFree
          simp only [Holds]
          congr! 1
          · exact phi_ih V h1_left h2_left
          · exact psi_ih V h1_right h2_right
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      unfold isFreeIn at h1
      push_neg at h1

      unfold isBoundIn at h2
      push_neg at h2

      cases h2
      case intro h2_left h2_right =>
        unfold fastReplaceFree
        split_ifs
        case inl c1 =>
          subst c1
          apply Holds_coincide_Var
          intro x a1
          unfold isFreeIn at a1
          cases a1
          case h1.intro a1_left a1_right =>
            unfold Function.updateIte
            simp only [if_neg a1_left]
            split_ifs
            case inl c2 =>
              subst c2
              tauto
            case inr c2 =>
              rfl
        case inr c1 =>
          simp only [Holds]
          first | apply forall_congr' | apply exists_congr
          intro d
          simp only [Function.updateIte_comm V v x d a h2_left]
          simp only [Function.updateIte_comm V u x d a c1]
          apply phi_ih
          · exact h1 h2_left
          · exact h2_right
  case nil.def_ X xs =>
    unfold fastReplaceFree
    simp only [Holds]
  case cons.def_ hd tl ih X xs =>
      unfold fastReplaceFree
      simp only [Holds]
      unfold Function.updateIte
      congr! 1
      case _ =>
        simp
      case _ c1 =>
        unfold isFreeIn at h1

        apply Holds_coincide_Var
        intro v' a1
        simp

        have s1 : (List.map ((fun a_1 => if a_1 = v then a else V a_1) ∘ fun x => if u = x then v else x) xs) = (List.map (fun a_1 => if a_1 = u then a else V a_1) xs)
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
        apply Function.updateListIte_mem_eq_len
        · simp only [isFreeIn_iff_mem_freeVarSet] at a1
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
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (F F' : Formula)
  (h1 : AlphaEqv F F') :
  Holds D I V E F ↔ Holds D I V E F' :=
  by
  induction h1 generalizing V
  case rename_forall_ h1_phi h1_x h1_y h1_1 h1_2 | rename_exists_ h1_phi h1_x h1_y h1_1 h1_2 =>
    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    exact replace_empty_Holds D I V E h1_x h1_y h1_phi d h1_1 h1_2
  case compat_not_ h1_phi h1_phi' _ h1_ih =>
    simp only [Holds]
    congr! 1
    exact h1_ih V
  case
    compat_imp_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_and_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_or_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2
  | compat_iff_ h1_phi h1_phi' h1_psi h1_psi' _ _ h1_ih_1 h1_ih_2 =>
    simp only [Holds]
    congr! 1
    · exact h1_ih_1 V
    · exact h1_ih_2 V
  case compat_forall_ h1_phi h1_psi h1_x _ h1_ih | compat_exists_ h1_phi h1_psi h1_x _ h1_ih =>
    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    exact h1_ih (Function.updateIte V h1_x d)
  case refl_ h1 =>
    rfl
  case symm_ h1_phi h1_phi' _ h1_ih =>
    symm
    exact h1_ih V
  case trans_ h1_phi h1_phi' h1_phi'' _ _ h1_ih_1 h1_ih_2 =>
    trans Holds D I V E h1_phi'
    · exact h1_ih_1 V
    · exact h1_ih_2 V


def isAlphaEqvVar : List (VarName × VarName) → VarName → VarName → Prop
  | [], x, y => x = y

  | hd::tl, x, y =>
      (x = hd.fst ∧ y = hd.snd) ∨
        ((¬ x = hd.fst ∧ ¬ y = hd.snd) ∧ isAlphaEqvVar tl x y)


instance
  (binders : List (VarName × VarName))
  (x y : VarName) :
  Decidable (isAlphaEqvVar binders x y) :=
  by
  induction binders
  all_goals
    unfold isAlphaEqvVar
    infer_instance


/-
    if x = hd.fst
    then y = hd.snd
    else ¬ y = hd.snd ∧ is_alpha_eqv_var tl x y
-/
def isAlphaEqvVarList
  (binders : List (VarName × VarName)) :
  List VarName → List VarName → Prop
  | [], [] => True

  | x_hd::x_tl, y_hd::y_tl =>
      isAlphaEqvVar binders x_hd y_hd ∧
        isAlphaEqvVarList binders x_tl y_tl

  | _, _ => False


instance
  (binders : List (VarName × VarName))
  (xs ys : List VarName) :
  Decidable (isAlphaEqvVarList binders xs ys) :=
  by
  induction xs generalizing ys
  all_goals
    cases ys
    all_goals
      unfold isAlphaEqvVarList
      infer_instance


def isAlphaEqvAux : List (VarName × VarName) → Formula → Formula → Prop
  | binders, pred_const_ X xs, pred_const_ Y ys =>
      X = Y ∧ isAlphaEqvVarList binders xs ys

  | binders, pred_var_ X xs, pred_var_ Y ys =>
      X = Y ∧ isAlphaEqvVarList binders xs ys

  | binders, eq_ x y, eq_ x' y' =>
      isAlphaEqvVar binders x x' ∧ isAlphaEqvVar binders y y'

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
      X = Y ∧ isAlphaEqvVarList binders xs ys

  | _, _, _ => False


instance
  (binders : List (VarName × VarName))
  (F F' : Formula) :
  Decidable (isAlphaEqvAux binders F F') :=
  by
  induction F generalizing F' binders
  all_goals
    cases F'
    all_goals
      unfold isAlphaEqvAux
      infer_instance


def isAlphaEqv (F F' : Formula) : Prop :=
  isAlphaEqvAux [] F F'


instance
  (F F' : Formula) :
  Decidable (isAlphaEqv F F') :=
  by
  unfold isAlphaEqv
  infer_instance


inductive AlphaEqvVarAssignment
  (D : Type) :
  List (VarName × VarName) → VarAssignment D → VarAssignment D → Prop
  | nil {V} :
    AlphaEqvVarAssignment D [] V V

  | cons {binders x y V V' d} :
    AlphaEqvVarAssignment D binders V V' →
    AlphaEqvVarAssignment D ((x, y)::binders) (Function.updateIte V x d) (Function.updateIte V' y d)


theorem aux_1
  (D : Type)
  (binders : List (VarName × VarName))
  (x y : VarName)
  (V V' : VarAssignment D)
  (h1 : AlphaEqvVarAssignment D binders V V')
  (h2 : isAlphaEqvVar binders x y) :
  V x = V' y :=
  by
  induction h1
  case nil h1_V =>
    unfold isAlphaEqvVar at h2

    subst h2
    rfl
  case cons h1_l h1_x h1_y h1_V h1_V' h1_d _ h1_ih =>
    unfold isAlphaEqvVar at h2
    simp at h2

    unfold Function.updateIte
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
  (binders : List (VarName × VarName))
  (xs ys : List VarName)
  (V V' : VarAssignment D)
  (h1 : AlphaEqvVarAssignment D binders V V')
  (h2 : isAlphaEqvVarList binders xs ys) :
  List.map V xs = List.map V' ys :=
  by
  induction xs generalizing ys
  case nil =>
    cases ys
    case nil =>
      simp
    case cons ys_hd ys_tl =>
      unfold isAlphaEqvVarList at h2

      contradiction
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      unfold isAlphaEqvVarList at h2

      contradiction
    case cons ys_hd ys_tl =>
      unfold isAlphaEqvVarList at h2

      simp
      constructor
      · cases h2
        case left.intro h2_left h2_right =>
          exact aux_1 D binders xs_hd ys_hd V V' h1 h2_left
      · apply xs_ih ys_tl
        cases h2
        case right.intro h2_left h2_right =>
          exact h2_right


lemma isAlphaEqv_Holds_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (F F' : Formula)
  (binders : List (VarName × VarName))
  (h1 : AlphaEqvVarAssignment D binders V V')
  (h2 : isAlphaEqvAux binders F F') :
  Holds D I V E F ↔ Holds D I V' E F' :=
  by
  induction E generalizing F F' binders V V'
  all_goals
    induction F generalizing F' binders V V'
    all_goals
      cases F'

    any_goals
      unfold isAlphaEqvAux at h2
      contradiction

    case
      pred_const_.pred_const_ X xs Y ys
    | pred_var_.pred_var_ X xs Y ys =>
      unfold isAlphaEqvAux at h2

      cases h2
      case intro h2_left h2_right =>
        simp only [Holds]
        subst h2_left
        congr! 1
        exact aux_2 D binders xs ys V V' h1 h2_right

    case eq_.eq_ x x' y y' =>
      unfold isAlphaEqvAux at h2

      cases h2
      case intro h2_left h2_right =>
        simp only [Holds]
        congr! 1
        · exact aux_1 D binders x y V V' h1 h2_left
        · exact aux_1 D binders x' y' V V' h1 h2_right

    case true_.true_ | false_.false_ =>
      simp only [Holds]

    case not_.not_ phi phi_ih phi' =>
      unfold isAlphaEqvAux at h2

      simp only [Holds]
      congr! 1
      exact phi_ih V V' phi' binders h1 h2

    case
      imp_.imp_ phi psi phi_ih psi_ih phi' psi'
    | and_.and_ phi psi phi_ih psi_ih phi' psi'
    | or_.or_ phi psi phi_ih psi_ih phi' psi'
    | iff_.iff_ phi psi phi_ih psi_ih phi' psi' =>
      unfold isAlphaEqvAux at h2

      cases h2
      case intro h2_left h2_right =>
        simp only [Holds]
        congr! 1
        · exact phi_ih V V' phi' binders h1 h2_left
        · exact psi_ih V V' psi' binders h1 h2_right

    case
      forall_.forall_ x phi phi_ih y phi'
    | exists_.exists_ x phi phi_ih y phi' =>
        unfold isAlphaEqvAux at h2

        simp only [Holds]
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
    simp only [Holds]
  case cons.def_.def_ hd tl ih X xs Y ys =>
      unfold isAlphaEqvAux at h2

      simp only [Holds]
      split_ifs
      case _ c1 c2 =>
        cases h2
        case intro h2_left h2_right =>
          apply Holds_coincide_Var
          intro v a1
          simp only [aux_2 D binders xs ys V V' h1 h2_right]
          apply Function.updateListIte_mem_eq_len
          · simp only [isFreeIn_iff_mem_freeVarSet] at a1
            simp only [← List.mem_toFinset]
            apply Finset.mem_of_subset hd.h1 a1
          · simp
            simp only [eq_comm]
            cases c2
            case intro c2_left c2_right =>
              exact c2_right
      case _ c1 c2 =>
        sorry
      case _ c1 c2 =>
        sorry
      case _ c1 c2 =>
        exact ih V V' (def_ X xs) (def_ Y ys) binders h1 h2


lemma isalphaEqv_Holds
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (F F' : Formula)
  (h1 : isAlphaEqv F F') :
  Holds D I V E F ↔ Holds D I V E F' :=
  by
  unfold isAlphaEqv at h1

  exact isAlphaEqv_Holds_aux D I V V E F F' [] AlphaEqvVarAssignment.nil h1


--#lint

end FOL
