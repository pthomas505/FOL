import FOL.FunctionUpdateIte
import FOL.Sub.One.Rec.SubOneRecReplaceFree
import FOL.Tactics


namespace FOL

open Formula


/--
  Helper function for replaceFreeFun.
-/
def replaceFreeFunAux (σ : VarName → VarName) : Finset VarName → Formula → Formula
  | binders, pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun x : VarName => if x ∉ binders then σ x else x)
  | binders, pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun x : VarName => if x ∉ binders then σ x else x)
  | binders, eq_ x y =>
      eq_
      (if x ∉ binders then σ x else x)
      (if y ∉ binders then σ y else y)
  | _, true_ => true_
  | _, false_ => false_
  | binders, not_ phi => not_ (replaceFreeFunAux σ binders phi)
  | binders, imp_ phi psi =>
      imp_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | binders, and_ phi psi =>
      and_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | binders, or_ phi psi =>
      or_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | binders, iff_ phi psi =>
      iff_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | binders, forall_ x phi =>
      forall_ x (replaceFreeFunAux σ (binders ∪ {x}) phi)
  | binders, exists_ x phi =>
      exists_ x (replaceFreeFunAux σ (binders ∪ {x}) phi)
  | binders, def_ X xs =>
      def_
      X
      (xs.map fun x : VarName => if x ∉ binders then σ x else x)

/--
  replaceFreeFun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def replaceFreeFun (σ : VarName → VarName) (F : Formula) : Formula :=
  replaceFreeFunAux σ ∅ F


/--
  fastReplaceFreeFun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def fastReplaceFreeFun : (VarName → VarName) → Formula → Formula
  | σ, pred_const_ X xs => pred_const_ X (xs.map σ)
  | σ, pred_var_ X xs => pred_var_ X (xs.map σ)
  | σ, eq_ x y => eq_ (σ x) (σ y)
  | _, true_ => true_
  | _, false_ => false_
  | σ, not_ phi => not_ (fastReplaceFreeFun σ phi)
  | σ, imp_ phi psi =>
      imp_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, and_ phi psi =>
      and_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, or_ phi psi =>
      or_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, iff_ phi psi =>
      iff_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, forall_ x phi =>
      forall_ x (fastReplaceFreeFun (Function.updateIte σ x x) phi)
  | σ, exists_ x phi =>
      exists_ x (fastReplaceFreeFun (Function.updateIte σ x x) phi)
  | σ, def_ X xs => def_ X (xs.map σ)


theorem fastReplaceFreeFun_id
  (F : Formula) :
  fastReplaceFreeFun id F = F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastReplaceFreeFun
    congr!
    simp
  case eq_ x y =>
    unfold fastReplaceFreeFun
    congr!
  case true_ | false_ =>
    unfold fastReplaceFreeFun
    rfl
  case not_ phi phi_ih =>
    unfold fastReplaceFreeFun
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastReplaceFreeFun
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastReplaceFreeFun
    congr!
    simp only [Function.updateIte_id]
    exact phi_ih


example
  (F : Formula)
  (v t : VarName) :
  fastReplaceFreeFun (Function.updateIte id v t) F =
    fastReplaceFree v t F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastReplaceFreeFun
    unfold fastReplaceFree
    unfold Function.updateIte
    simp only [eq_comm]
    rfl
  case eq_ x y =>
    unfold fastReplaceFreeFun
    unfold fastReplaceFree
    unfold Function.updateIte
    simp only [eq_comm]
    rfl
  case true_ | false_ =>
    rfl
  case not_ phi phi_ih =>
    unfold fastReplaceFreeFun
    unfold fastReplaceFree
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastReplaceFreeFun
    unfold fastReplaceFree
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastReplaceFreeFun
    unfold fastReplaceFree
    split_ifs
    case inl c1 =>
      subst c1
      congr!
      simp only [Function.updateIte_idem]
      simp only [Function.updateIte_id]
      apply fastReplaceFreeFun_id
    case inr c1 =>
      congr! 1
      simp only [← phi_ih]
      congr! 1
      apply Function.updateIte_comm_id x v t
      simp only [eq_comm]
      exact c1


theorem fastReplaceFreeFun_same_on_free
  (F : Formula)
  (σ σ' : VarName → VarName)
  (h1 : ∀ v : VarName, isFreeIn v F → σ v = σ' v) :
  fastReplaceFreeFun σ F = fastReplaceFreeFun σ' F :=
  by
  induction F generalizing σ σ'
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold isFreeIn at h1

    unfold fastReplaceFreeFun
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case eq_ x y =>
    unfold isFreeIn at h1
    unfold fastReplaceFreeFun
    congr! 1
    · apply h1
      left
      rfl
    · apply h1
      right
      rfl
  case true_ | false_ =>
    unfold fastReplaceFreeFun
    rfl
  case not_ phi phi_ih =>
    unfold isFreeIn at h1

    unfold fastReplaceFreeFun
    congr! 1
    exact phi_ih σ σ' h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isFreeIn at h1

    unfold fastReplaceFreeFun
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
    unfold fastReplaceFreeFun
    congr! 1
    apply phi_ih
    intro v a1
    unfold Function.updateIte
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      apply h1
      unfold isFreeIn
      constructor
      · exact c1
      · exact a1


theorem replaceFreeFunAux_same_on_free
  (F : Formula)
  (σ σ' : VarName → VarName)
  (binders : Finset VarName)
  (h1 : ∀ v : VarName, v ∉ binders → σ v = σ' v) :
  replaceFreeFunAux σ binders F =
    replaceFreeFunAux σ' binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold replaceFreeFunAux
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      exact h1 x c1
  case eq_ x y =>
    unfold replaceFreeFunAux
    congr! 1
    · split_ifs
      case _ c1 =>
        rfl
      case _ c1 =>
        exact h1 x c1
    · split_ifs
      case _ c1 =>
        rfl
      case _ c1 =>
        exact h1 y c1
  case true_ | false_ =>
    rfl
  case not_ phi phi_ih =>
    unfold replaceFreeFunAux
    congr! 1
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replaceFreeFunAux
    congr! 1
    · exact phi_ih binders h1
    · exact psi_ih binders h1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold replaceFreeFunAux
    congr! 1
    apply phi_ih
    intro v a1
    simp at a1
    push_neg at a1
    cases a1
    case _ a1_left a1_right =>
      exact h1 v a1_left


example
  (F : Formula)
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (h1 : ∀ v : VarName, v ∈ binders → v = σ v) :
  replaceFreeFunAux σ binders F =
    fastReplaceFreeFun σ F :=
  by
  induction F generalizing binders σ
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastReplaceFreeFun
    unfold replaceFreeFunAux
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs
    case _ c1 =>
      exact h1 x c1
    case _ c1 =>
      rfl
  case eq_ x y =>
    unfold fastReplaceFreeFun
    unfold replaceFreeFunAux
    congr! 1
    · split_ifs
      case _ c1 =>
        exact h1 x c1
      case _ c1 =>
        rfl
    · split_ifs
      case _ c1 =>
        exact h1 y c1
      case _ c1 =>
        rfl
  case true_ | false_ =>
    rfl
  case not_ phi phi_ih =>
    unfold fastReplaceFreeFun
    unfold replaceFreeFunAux
    congr! 1
    exact phi_ih σ binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastReplaceFreeFun
    unfold replaceFreeFunAux
    congr! 1
    · exact phi_ih σ binders h1
    · exact psi_ih σ binders h1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastReplaceFreeFun
    unfold replaceFreeFunAux
    congr! 1

    have s1 : (∀ (v : VarName), v ∈ binders ∪ {x} → v = Function.updateIte σ x x v)
    intros v a1
    simp at a1
    unfold Function.updateIte
    cases a1
    case _ c1 =>
      split_ifs
      case _ c2 =>
        exact c2
      case _ c2 =>
        exact h1 v c1
    case _ c1 =>
      simp only [if_pos c1]
      exact c1

    simp only [← phi_ih (Function.updateIte σ x x) (binders ∪ {x}) s1]
    apply replaceFreeFunAux_same_on_free phi σ (Function.updateIte σ x x) (binders ∪ {x})
    unfold Function.updateIte
    intro v a1
    simp at a1
    push_neg at a1
    cases a1
    case _ a1_left a1_right =>
      simp only [if_neg a1_right]


#lint

end FOL
