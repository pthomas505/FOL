import FOL.NV.Semantics
import FOL.NV.Sub.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.All.Ind

open Formula


inductive IsSub :
  (VarName → VarName) →
  Finset VarName →
  Formula → Formula → Prop

  | pred_const_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (X : PredName)
    (xs : List VarName) :
    (∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    IsSub σ binders (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (X : PredName)
    (xs : List VarName) :
    (∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    IsSub σ binders (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (x y : VarName) :
    ∀ v : VarName, (v = x ∨ v = y) → v ∉ binders → σ v ∉ binders →
    IsSub σ binders (eq_ x y) (eq_ (σ x) (σ y))

  | true_
    (σ : VarName → VarName)
    (binders : Finset VarName) :
    IsSub σ binders true_ true_

  | false_
    (σ : VarName → VarName)
    (binders : Finset VarName) :
    IsSub σ binders false_ false_

  | not_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (phi : Formula)
    (phi' : Formula) :
    IsSub σ binders phi phi' →
    IsSub σ binders phi.not_ phi'.not_

  | imp_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsSub σ binders phi phi' →
    IsSub σ binders psi psi' →
    IsSub σ binders (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsSub σ binders phi phi' →
    IsSub σ binders psi psi' →
    IsSub σ binders (phi.and_ psi) (phi'.and_ psi')

  | or_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsSub σ binders phi phi' →
    IsSub σ binders psi psi' →
    IsSub σ binders (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsSub σ binders phi phi' →
    IsSub σ binders psi psi' →
    IsSub σ binders (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (x : VarName)
    (phi phi' : Formula) :
    IsSub (Function.updateITE σ x x) (binders ∪ {x}) phi phi' →
    IsSub σ binders (forall_ x phi) (forall_ x phi')

  | exists_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (x : VarName)
    (phi phi' : Formula) :
    IsSub (Function.updateITE σ x x) (binders ∪ {x}) phi phi' →
    IsSub σ binders (exists_ x phi) (exists_ x phi')

  | def_
    (σ : VarName → VarName)
    (binders : Finset VarName)
    (X : DefName)
    (xs : List VarName) :
    (∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    IsSub σ binders (def_ X xs) (def_ X (xs.map σ))


theorem substitution_theorem_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (F F' : Formula)
  (h1 : IsSub σ binders F F')
  (h2 : ∀ v : VarName, v ∈ binders → V v = V' (σ v))
  (h3 : ∀ v : VarName, σ v ∉ binders → V v = V' (σ v))
  (h4 : ∀ v : VarName, v ∈ binders → v = σ v) :
  Holds D I V E F ↔ Holds D I V' E F' :=
  by
  induction h1 generalizing V V'
  case pred_const_ σ' binders' X' xs' ih_1 | pred_var_ σ' binders' X' xs' ih_1 =>
    simp only [Holds]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x a1
    simp
    by_cases c1 : x ∈ binders'
    · exact h2 x c1
    · apply h3
      exact ih_1 x a1 c1
  case eq_ σ' binders' x y v ih_1 ih_2 ih_3 =>
    simp only [Holds]
    sorry
  case true_ | false_ =>
    simp only [Holds]
  case not_ σ' binders' phi phi' ih_1 ih_2 =>
    simp only [Holds]
    congr! 1
    exact ih_2 V V' h2 h3 h4
  case
      imp_ σ' binders' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
    | and_ σ' binders' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
    | or_ σ' binders' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
    | iff_ σ' binders' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2 =>
    simp only [Holds]
    congr! 1
    · apply phi_ih_2 V V' h2 h3 h4
    · apply psi_ih_2 V V' h2 h3 h4
  case forall_ σ' binders' x phi phi' ih_1 ih_2 | exists_ σ' binders' x phi phi' ih_1 ih_2 =>
    simp at ih_2

    have s1 : ∀ (v : VarName), ¬ v = x → v ∈ binders' → ¬ σ' v = x
    intro v a1 a2 contra
    apply a1
    simp only [← contra]
    exact h4 v a2

    simp only [Holds]
    first | apply forall_congr'| apply exists_congr
    intro d

    apply ih_2
    · intro v a1
      by_cases c1 : v = x
      · simp only [Function.updateITE]
        simp only [if_pos c1]
        simp
      · simp only [Function.updateITE]
        simp only [if_neg c1]
        cases a1
        case _ c2 =>
          simp only [s1 v c1 c2]
          simp
          exact h2 v c2
        case _ c2 =>
          contradiction
    · intro v a1
      by_cases c1 : v = x
      · simp only [Function.updateITE]
        simp only [if_pos c1]
        simp
      · simp only [Function.updateITE] at a1
        simp only [if_neg c1] at a1
        push_neg at a1

        simp only [Function.updateITE]
        simp only [if_neg c1]
        cases a1
        case _ a1_left a1_right =>
          simp only [if_neg a1_right]
          apply h3 v a1_left
    · intro v a1
      simp only [Function.updateITE]
      split_ifs
      case _ c1 =>
        exact c1
      case _ c1 =>
        cases a1
        case _ c2 =>
          exact h4 v c2
        case _ c2 =>
          contradiction
  case def_ σ' binders' X' xs' ih_1 =>
    induction E
    case nil =>
      simp only [Holds]
    case cons hd tl ih =>
      simp only [Holds]
      split_ifs
      case _ c1 c2 =>
        simp
        apply Holds_coincide_Var
        intro v a1

        have s1 : List.map V xs' = List.map (V' ∘ σ') xs'
        simp only [List.map_eq_map_iff]
        intro x a2
        by_cases c3 : x ∈ binders'
        · exact h2 x c3
        · apply h3 x
          apply ih_1 x a2 c3

        simp only [s1]
        apply Function.updateListITE_mem_eq_len
        simp only [isFreeIn_iff_mem_freeVarSet] at a1
        obtain s2 := hd.h1 a1
        simp at s2
        exact s2

        simp at c2
        simp
        tauto
      case _ c1 c2 =>
        simp only [List.length_map] at c2
        contradiction
      case _ c1 c2 =>
        simp at c2
        contradiction
      case _ c1 c2 =>
        exact ih
