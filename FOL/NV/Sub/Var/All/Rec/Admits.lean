import FOL.NV.Semantics
import FOL.NV.Sub.Var.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec

open Formula


/--
  Helper function for admits.
-/
def admitsAux
  (σ : VarName → VarName) (binders : Finset VarName) : Formula → Prop
  | pred_const_ _ xs =>
      ∀ (v : VarName), v ∈ xs → v ∉ binders → σ v ∉ binders
  | pred_var_ _ xs =>
      ∀ (v : VarName), v ∈ xs → v ∉ binders → σ v ∉ binders
  | eq_ x y =>
      (x ∉ binders → σ x ∉ binders) ∧
      (y ∉ binders → σ y ∉ binders)
  | true_ => True
  | false_ => True
  | not_ phi => admitsAux σ binders phi
  | imp_ phi psi =>
      admitsAux σ binders phi ∧
      admitsAux σ binders psi
  | and_ phi psi =>
      admitsAux σ binders phi ∧
      admitsAux σ binders psi
  | or_ phi psi =>
      admitsAux σ binders phi ∧
      admitsAux σ binders psi
  | iff_ phi psi =>
      admitsAux σ binders phi ∧
      admitsAux σ binders psi
  | forall_ x phi => admitsAux σ (binders ∪ {x}) phi
  | exists_ x phi => admitsAux σ (binders ∪ {x}) phi
  | def_ _ xs =>
      ∀ (v : VarName), v ∈ xs → v ∉ binders → σ v ∉ binders


instance
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula) :
  Decidable (admitsAux σ binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [admitsAux]
    infer_instance


/--
  admits σ F := True if and only if there is no free occurrence of a variable in the formula F that becomes a bound occurrence in the formula (fastReplaceFree σ F).
-/
def admits (σ : VarName → VarName) (F : Formula) : Prop :=
  admitsAux σ ∅ F


instance
  (σ : VarName → VarName)
  (F : Formula) :
  Decidable (admits σ F) :=
  by
  simp only [admits]
  infer_instance


theorem substitution_theorem_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ σ' : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula)
  (h1 : admitsAux σ binders F)
  (h2 : ∀ (v : VarName), v ∈ binders ∨ σ' v ∉ binders → V v = V' (σ' v))
  (h2' : ∀ (v : VarName), v ∈ binders → v = σ' v)
  (h3 : ∀ (v : VarName), v ∉ binders → σ' v = σ v) :
  holds D I V E F ↔ holds D I V' E (fastReplaceFree σ' F) :=
  by
  induction E generalizing F binders V V' σ σ'
  all_goals
    induction F generalizing binders V V' σ σ'
    all_goals
      simp only [admitsAux] at h1

      simp only [fastReplaceFree]
      simp only [holds]
    case pred_const_ X xs | pred_var_ X xs =>
      congr! 1
      simp
      intro v a1
      apply h2
      by_cases c1 : v ∈ binders
      · left
        exact c1
      · right
        simp only [h3 v c1]
        exact h1 v a1 c1
    case eq_ x y =>
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
    case not_ phi phi_ih =>
      congr! 1
      exact phi_ih V V' σ σ' binders h1 h2 h2' h3
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · exact phi_ih V V' σ σ' binders h1_left h2 h2' h3
        · exact psi_ih V V' σ σ' binders h1_right h2 h2' h3
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      first | apply forall_congr' | apply exists_congr
      intro d
      apply phi_ih (Function.updateITE V x d) (Function.updateITE V' x d) σ (Function.updateITE σ' x x) (binders ∪ {x}) h1
      · intro v a1
        simp only [Function.updateITE] at a1
        simp at a1

        simp only [Function.updateITE]
        split_ifs
        case _ c1 c2 =>
          rfl
        case _ c1 c2 =>
          contradiction
        case _ c1 c2 =>
          subst c2
          tauto
        case _ c1 c2 =>
          simp only [if_neg c1] at a1
          apply h2
          tauto
      · intro v a1
        simp at a1

        simp only [Function.updateITE]
        split_ifs <;> tauto
      · intro v a1
        simp at a1

        simp only [Function.updateITE]
        split_ifs <;> tauto

  case cons.def_ hd tl ih X xs =>
    split_ifs
    case _ c1 c2 =>
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
      apply holds_coincide_var
      intro v a1
      apply Function.updateListITE_mem_eq_len
      · simp only [var_is_free_in_iff_mem_free_var_set] at a1
        simp only [← List.mem_toFinset]
        apply Finset.mem_of_subset hd.h1 a1
      · simp
        tauto
    case _ c1 c2 =>
      simp only [List.length_map] at c2
      contradiction
    case _ c1 c2 =>
      simp at c2
      contradiction
    case _ c1 c2 =>
      specialize ih V V' σ σ' binders (def_ X xs)
      simp only [fastReplaceFree] at ih
      apply ih h1 h2 h2' h3


theorem substitution_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (F : Formula)
  (h1 : admits σ F) :
  holds D I (V ∘ σ) E F ↔
    holds D I V E (fastReplaceFree σ F) :=
  by
  apply substitution_theorem_aux D I (V ∘ σ) V E σ σ ∅ F h1
  · simp
  · simp
  · simp


theorem substitution_is_valid
  (σ : VarName → VarName)
  (F : Formula)
  (h1 : admits σ F)
  (h2 : F.is_valid) :
  (fastReplaceFree σ F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem D I V E σ F h1]
  exact h2 D I (V ∘ σ) E


#lint
