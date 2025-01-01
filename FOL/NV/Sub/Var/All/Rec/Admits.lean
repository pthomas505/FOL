import FOL.NV.Semantics
import FOL.NV.Sub.Var.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec

open Formula_


/--
  Helper function for `admits_var_all_rec`.
-/
def admits_var_all_rec_aux
  (σ : VarName_ → VarName_)
  (binders : Finset VarName_) :
  Formula_ → Prop
  | pred_const_ _ xs =>
      ∀ (v : VarName_), v ∈ xs → v ∉ binders → σ v ∉ binders
  | pred_var_ _ xs =>
      ∀ (v : VarName_), v ∈ xs → v ∉ binders → σ v ∉ binders
  | eq_ x y =>
      (x ∉ binders → σ x ∉ binders) ∧
      (y ∉ binders → σ y ∉ binders)
  | true_ => True
  | false_ => True
  | not_ phi => admits_var_all_rec_aux σ binders phi
  | imp_ phi psi =>
      admits_var_all_rec_aux σ binders phi ∧
      admits_var_all_rec_aux σ binders psi
  | and_ phi psi =>
      admits_var_all_rec_aux σ binders phi ∧
      admits_var_all_rec_aux σ binders psi
  | or_ phi psi =>
      admits_var_all_rec_aux σ binders phi ∧
      admits_var_all_rec_aux σ binders psi
  | iff_ phi psi =>
      admits_var_all_rec_aux σ binders phi ∧
      admits_var_all_rec_aux σ binders psi
  | forall_ x phi => admits_var_all_rec_aux σ (binders ∪ {x}) phi
  | exists_ x phi => admits_var_all_rec_aux σ (binders ∪ {x}) phi
  | def_ _ xs =>
      ∀ (v : VarName_), v ∈ xs → v ∉ binders → σ v ∉ binders

instance
  (σ : VarName_ → VarName_)
  (binders : Finset VarName_)
  (F : Formula_) :
  Decidable (admits_var_all_rec_aux σ binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [admits_var_all_rec_aux]
    infer_instance


/--
  `admits_var_all_rec σ F` := True if and only if there is no free occurrence of a variable in the formula `F` that becomes a bound occurrence in the formula `fast_replace_free_var_all_rec σ F`.
-/
def admits_var_all_rec
  (σ : VarName_ → VarName_)
  (F : Formula_) :
  Prop :=
  admits_var_all_rec_aux σ ∅ F

instance
  (σ : VarName_ → VarName_)
  (F : Formula_) :
  Decidable (admits_var_all_rec σ F) :=
  by
  simp only [admits_var_all_rec]
  infer_instance


theorem substitution_theorem_admits_var_all_rec_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (σ σ' : VarName_ → VarName_)
  (binders : Finset VarName_)
  (F : Formula_)
  (h1 : admits_var_all_rec_aux σ binders F)
  (h2 : ∀ (v : VarName_), v ∈ binders ∨ σ' v ∉ binders → V v = V' (σ' v))
  (h2' : ∀ (v : VarName_), v ∈ binders → v = σ' v)
  (h3 : ∀ (v : VarName_), v ∉ binders → σ' v = σ v) :
  holds D I V E F ↔ holds D I V' E (fast_replace_free_var_all_rec σ' F) :=
  by
  induction E generalizing F binders V V' σ σ'
  all_goals
    induction F generalizing binders V V' σ σ'
    all_goals
      simp only [admits_var_all_rec_aux] at h1

      simp only [fast_replace_free_var_all_rec]
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
      obtain ⟨h1_left, h1_right⟩ := h1
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
      have s1 : List.map V xs = List.map (V' ∘ σ') xs :=
      by
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
      exact ih V V' σ σ' binders (def_ X xs) h1 h2 h2' h3


theorem substitution_theorem_admits_var_all_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (σ : VarName_ → VarName_)
  (F : Formula_)
  (h1 : admits_var_all_rec σ F) :
  holds D I (V ∘ σ) E F ↔
    holds D I V E (fast_replace_free_var_all_rec σ F) :=
  by
  apply substitution_theorem_admits_var_all_rec_aux D I (V ∘ σ) V E σ σ ∅ F h1
  · simp
  · simp
  · simp


theorem substitution_is_valid_admits_var_all_rec
  (σ : VarName_ → VarName_)
  (F : Formula_)
  (h1 : admits_var_all_rec σ F)
  (h2 : F.is_valid) :
  (fast_replace_free_var_all_rec σ F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem_admits_var_all_rec D I V E σ F h1]
  apply h2


lemma admits_var_all_rec_aux_mem_free_var_set_and_not_mem_binders
  (binders : Finset VarName_)
  (σ : VarName_ → VarName_)
  (F : Formula_)
  (h1 : admits_var_all_rec_aux σ binders F) :
  ∀ (v : VarName_), v ∈ F.free_var_set → v ∉ binders → σ v ∉ binders :=
  by
  induction F generalizing binders
  case
      pred_const_ X xs
    | pred_var_ X xs
    | eq_ x y
    | def_ X xs =>
    simp only [admits_var_all_rec_aux] at h1

    simp only [free_var_set]
    simp
    exact h1
  case
      true_
    | false_ =>
    simp only [free_var_set]
    simp
  case not_ phi ih =>
    simp only [admits_var_all_rec_aux] at h1

    simp only [free_var_set]
    apply ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admits_var_all_rec_aux] at h1

    simp only [free_var_set]
    simp
    tauto
  case
      forall_ x phi ih
    | exists_ x phi ih =>
    simp only [admits_var_all_rec_aux] at h1

    simp only [free_var_set]
    intro v a1 a2
    simp at a1
    obtain ⟨a1_left, a1_right⟩ := a1
    specialize ih (binders ∪ {x}) h1 v
    simp at ih
    specialize ih a1_left a2 a1_right
    tauto


lemma admits_var_all_rec_aux_del_binder
  (binders : Finset VarName_)
  (v : VarName_)
  (σ : VarName_ → VarName_)
  (F : Formula_)
  (h1 : admits_var_all_rec_aux σ ({v} ∪ binders) F) : admits_var_all_rec_aux (Function.updateITE σ v v) binders F :=
  by
  induction F generalizing binders
  case
      pred_const_ X xs
    | pred_var_ X xs
    | def_ X xs =>
    simp only [admits_var_all_rec_aux] at h1
    simp at h1

    simp only [admits_var_all_rec_aux]
    intro x a1 a2
    simp only [Function.updateITE]
    split_ifs
    case pos c1 =>
      rw [c1] at a2
      exact a2
    case neg c1 =>
      specialize h1 x a1 c1 a2
      tauto
  case eq_ x y =>
    simp only [admits_var_all_rec_aux] at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [admits_var_all_rec_aux]
    constructor
    · intro a1
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        rw [c1] at a1
        exact a1
      case neg c1 =>
        specialize h1_left c1 a1
        tauto
    · intro a1
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        rw [c1] at a1
        exact a1
      case neg c1 =>
        specialize h1_right c1 a1
        tauto
  case true_ | false_ =>
    simp only [admits_var_all_rec_aux]
  case not_ phi ih =>
    simp only [admits_var_all_rec_aux] at h1

    simp only [admits_var_all_rec_aux]
    apply ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admits_var_all_rec_aux] at h1

    simp only [admits_var_all_rec_aux]
    tauto
  case
      forall_ x phi ih
    | exists_ x phi ih =>
    simp only [admits_var_all_rec_aux] at h1
    simp at h1

    simp only [admits_var_all_rec_aux]
    apply ih
    exact h1


#lint
