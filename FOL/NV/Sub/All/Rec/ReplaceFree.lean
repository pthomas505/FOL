import FOL.FunctionUpdateITE
import FOL.NV.Sub.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.All.Rec

open Formula


/--
  Helper function for replaceFreeFun.
-/
def replaceFreeFunAux (σ : VarName → VarName) (binders : Finset VarName) : Formula → Formula
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName) => if x ∉ binders then σ x else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName) => if x ∉ binders then σ x else x)
  | eq_ x y =>
      eq_
      (if x ∉ binders then σ x else x)
      (if y ∉ binders then σ y else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replaceFreeFunAux σ binders phi)
  | imp_ phi psi =>
      imp_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | and_ phi psi =>
      and_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | or_ phi psi =>
      or_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | iff_ phi psi =>
      iff_
      (replaceFreeFunAux σ binders phi)
      (replaceFreeFunAux σ binders psi)
  | forall_ x phi =>
      forall_ x (replaceFreeFunAux σ (binders ∪ {x}) phi)
  | exists_ x phi =>
      exists_ x (replaceFreeFunAux σ (binders ∪ {x}) phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName) => if x ∉ binders then σ x else x)


/--
  replaceFreeFun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def replaceFreeFun (σ : VarName → VarName) (F : Formula) : Formula :=
  replaceFreeFunAux σ ∅ F


/--
  fastReplaceFreeFun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def fastReplaceFreeFun (σ : VarName → VarName) : Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (fastReplaceFreeFun σ phi)
  | imp_ phi psi =>
      imp_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | and_ phi psi =>
      and_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | or_ phi psi =>
      or_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | iff_ phi psi =>
      iff_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | forall_ x phi =>
      forall_ x (fastReplaceFreeFun (Function.updateITE σ x x) phi)
  | exists_ x phi =>
      exists_ x (fastReplaceFreeFun (Function.updateITE σ x x) phi)
  | def_ X xs => def_ X (xs.map σ)


theorem fastReplaceFreeFun_id
  (F : Formula) :
  fastReplaceFreeFun id F = F :=
  by
  induction F
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp only [fastReplaceFreeFun]
    congr!
    simp
  case eq_ x y =>
    simp only [fastReplaceFreeFun]
    congr!
  case true_ | false_ =>
    simp only [fastReplaceFreeFun]
  case not_ phi phi_ih =>
    simp only [fastReplaceFreeFun]
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [fastReplaceFreeFun]
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [fastReplaceFreeFun]
    congr!
    simp only [Function.updateITE_id]
    exact phi_ih


example
  (F : Formula)
  (v t : VarName) :
  fastReplaceFreeFun (Function.updateITE id v t) F =
    One.Rec.fastReplaceFree v t F :=
  by
  induction F
  all_goals
    simp only [fastReplaceFreeFun]
    simp only [One.Rec.fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_map_iff]
    intro x a1
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
      apply fastReplaceFreeFun_id
    case neg c1 =>
      simp
      simp only [← phi_ih]
      congr! 1
      apply Function.updateITE_comm_id x v t
      tauto


theorem fastReplaceFreeFun_same_on_free
  (F : Formula)
  (σ σ' : VarName → VarName)
  (h1 : ∀ v : VarName, isFreeIn v F → σ v = σ' v) :
  fastReplaceFreeFun σ F = fastReplaceFreeFun σ' F :=
  by
  induction F generalizing σ σ'
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp only [isFreeIn] at h1

    simp only [fastReplaceFreeFun]
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case eq_ x y =>
    simp only [isFreeIn] at h1
    simp only [fastReplaceFreeFun]
    congr! 1
    · apply h1
      left
      rfl
    · apply h1
      right
      rfl
  case true_ | false_ =>
    simp only [fastReplaceFreeFun]
  case not_ phi phi_ih =>
    simp only [isFreeIn] at h1

    simp only [fastReplaceFreeFun]
    congr! 1
    exact phi_ih σ σ' h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [isFreeIn] at h1

    simp only [fastReplaceFreeFun]
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
    simp only [fastReplaceFreeFun]
    congr! 1
    apply phi_ih
    intro v a1
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      apply h1
      simp only [isFreeIn]
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
    simp only [replaceFreeFunAux]
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      exact h1 x c1
  case eq_ x y =>
    simp only [replaceFreeFunAux]
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
    simp only [replaceFreeFunAux]
    congr! 1
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [replaceFreeFunAux]
    congr! 1
    · exact phi_ih binders h1
    · exact psi_ih binders h1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [replaceFreeFunAux]
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
    simp only [fastReplaceFreeFun]
    simp only [replaceFreeFunAux]
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs
    case _ c1 =>
      exact h1 x c1
    case _ c1 =>
      rfl
  case eq_ x y =>
    simp only [fastReplaceFreeFun]
    simp only [replaceFreeFunAux]
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
    simp only [fastReplaceFreeFun]
    simp only [replaceFreeFunAux]
    congr! 1
    exact phi_ih σ binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [fastReplaceFreeFun]
    simp only [replaceFreeFunAux]
    congr! 1
    · exact phi_ih σ binders h1
    · exact psi_ih σ binders h1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [fastReplaceFreeFun]
    simp only [replaceFreeFunAux]
    congr! 1

    have s1 : (∀ (v : VarName), v ∈ binders ∪ {x} → v = Function.updateITE σ x x v)
    intros v a1
    simp at a1
    simp only [Function.updateITE]
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

    simp only [← phi_ih (Function.updateITE σ x x) (binders ∪ {x}) s1]
    apply replaceFreeFunAux_same_on_free phi σ (Function.updateITE σ x x) (binders ∪ {x})
    simp only [Function.updateITE]
    intro v a1
    simp at a1
    push_neg at a1
    cases a1
    case _ a1_left a1_right =>
      simp only [if_neg a1_right]


#lint
