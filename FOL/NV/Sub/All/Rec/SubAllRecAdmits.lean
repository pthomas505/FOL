import FOL.NV.Sub.All.Rec.SubAllRecReplaceFree
import FOL.NV.Semantics


namespace FOL

namespace NV

open Formula


def admitsFunAux
  (σ : VarName → VarName) :
  Finset VarName → Formula → Prop
  | binders, pred_const_ _ xs =>
      ∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders
  | binders, pred_var_ _ xs =>
      ∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders
  | binders, eq_ x y =>
      (x ∉ binders → σ x ∉ binders) ∧
      (y ∉ binders → σ y ∉ binders)
  | _, true_ => True
  | _, false_ => True
  | binders, not_ phi => admitsFunAux σ binders phi
  | binders, imp_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, and_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, or_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, iff_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, forall_ x phi => admitsFunAux σ (binders ∪ {x}) phi
  | binders, exists_ x phi => admitsFunAux σ (binders ∪ {x}) phi
  | binders, def_ _ xs =>
      ∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders


instance
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula) :
  Decidable (admitsFunAux σ binders F) :=
  by
  induction F generalizing binders
  all_goals
    unfold admitsFunAux
    infer_instance


def admitsFun (σ : VarName → VarName) (phi : Formula) : Prop :=
  admitsFunAux σ ∅ phi


instance
  (σ : VarName → VarName)
  (F : Formula) :
  Decidable (admitsFun σ F) :=
  by
  unfold admitsFun
  infer_instance


theorem substitution_fun_theorem_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ σ' : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula)
  (h1 : admitsFunAux σ binders F)
  (h2 : ∀ v : VarName, v ∈ binders ∨ σ' v ∉ binders → V v = V' (σ' v))
  (h2' : ∀ v : VarName, v ∈ binders → v = σ' v)
  (h3 : ∀ v : VarName, v ∉ binders → σ' v = σ v) :
  Holds D I V E F ↔ Holds D I V' E (fastReplaceFreeFun σ' F) :=
  by
  induction E generalizing F binders V V' σ σ'
  all_goals
    induction F generalizing binders V V' σ σ'
    case pred_const_ X xs | pred_var_ X xs =>
      unfold admitsFunAux at h1

      unfold fastReplaceFreeFun
      simp only [Holds]
      congr! 1
      simp
      simp only [List.map_eq_map_iff]
      intro v a1
      apply h2
      by_cases c1 : v ∈ binders
      · left
        exact c1
      · right
        simp only [h3 v c1]
        exact h1 v a1 c1
    case eq_ x y =>
      unfold admitsFunAux at h1

      unfold fastReplaceFreeFun
      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · apply h2
          by_cases c1 : x ∈ binders
          · left
            exact c1
          · right
            simp only [h3 x c1]
            exact h1_left c1
        · apply h2
          by_cases c1 : y ∈ binders
          · left
            exact c1
          · right
            simp only [h3 y c1]
            exact h1_right c1
    case true_ | false_ =>
      unfold fastReplaceFreeFun
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold admitsFunAux at h1

      unfold fastReplaceFreeFun
      simp only [Holds]
      congr! 1
      exact phi_ih V V' σ σ' binders h1 h2 h2' h3
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold admitsFunAux at h1

      unfold fastReplaceFreeFun
      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · exact phi_ih V V' σ σ' binders h1_left h2 h2' h3
        · exact psi_ih V V' σ σ' binders h1_right h2 h2' h3
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      unfold admitsFunAux at h1

      unfold fastReplaceFreeFun
      simp only [Holds]
      first | apply forall_congr' | apply exists_congr
      intro d
      apply phi_ih (Function.updateITE V x d) (Function.updateITE V' x d) σ (Function.updateITE σ' x x) (binders ∪ {x}) h1
      · intro v a1
        unfold Function.updateITE at a1
        simp at a1
        push_neg at a1
        unfold Function.updateITE
        split_ifs
        case _ c1 c2 =>
          rfl
        case _ c1 c2 =>
          contradiction
        case _ c1 c2 =>
          subst c2
          tauto
        case _ c1 c2 =>
          apply h2
          simp only [if_neg c1] at a1
          tauto
      · intro v a1
        simp at a1
        unfold Function.updateITE
        split_ifs
        case _ c1 =>
          exact c1
        case _ c1 =>
          tauto
      · intro v a1
        simp at a1
        push_neg at a1
        cases a1
        case intro a1_left a1_right =>
          unfold Function.updateITE
          simp only [if_neg a1_right]
          exact h3 v a1_left

  case nil.def_ X xs =>
    unfold fastReplaceFreeFun
    simp only [Holds]
  case cons.def_ hd tl ih X xs =>
    unfold fastReplaceFreeFun
    simp only [Holds]
    split_ifs
    case _ c1 c2 =>
      unfold admitsFunAux at h1

      simp
      have s1 : List.map V xs = List.map (V' ∘ σ') xs
      {
        simp only [List.map_eq_map_iff]
        intro x a1
        simp
        apply h2
        by_cases c3 : x ∈ binders
        · left
          exact c3
        · right
          simp only [h3 x c3]
          exact h1 x a1 c3
      }

      simp only [s1]
      apply Holds_coincide_Var
      intro v a1
      apply Function.updateListITE_mem_eq_len
      · simp only [isFreeIn_iff_mem_freeVarSet] at a1
        simp only [← List.mem_toFinset]
        apply Finset.mem_of_subset hd.h1 a1
      · simp
        cases c1
        case intro c1_left c1_right =>
        simp only [eq_comm]
        exact c1_right
    case _ c1 c2 =>
      simp only [List.length_map] at c2
      contradiction
    case _ c1 c2 =>
      simp at c2
      contradiction
    case _ c1 c2 =>
      specialize ih V V' σ σ' binders (def_ X xs)
      unfold fastReplaceFreeFun at ih
      apply ih h1 h2 h2' h3


theorem substitution_fun_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (F : Formula)
  (h1 : admitsFun σ F) :
  Holds D I (V ∘ σ) E F ↔
    Holds D I V E (fastReplaceFreeFun σ F) :=
  by
  apply substitution_fun_theorem_aux D I (V ∘ σ) V E σ σ ∅ F h1
  · simp
  · simp
  · simp


theorem substitution_fun_valid
  (σ : VarName → VarName)
  (F : Formula)
  (h1 : admitsFun σ F)
  (h2 : F.IsValid) :
  (fastReplaceFreeFun σ F).IsValid :=
  by
  unfold IsValid at h2

  unfold IsValid
  intro D I V E
  simp only [← substitution_fun_theorem D I V E σ F h1]
  exact h2 D I (V ∘ σ) E


--#lint
