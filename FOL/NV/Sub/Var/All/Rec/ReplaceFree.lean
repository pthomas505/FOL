import MathlibExtra.FunctionUpdateITE
import FOL.NV.Sub.Var.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Rec

open Formula


/--
  Helper function for replaceFree.
-/
def replaceFreeAux (σ : VarName → VarName) (binders : Finset VarName) : Formula → Formula
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
  | not_ phi => not_ (replaceFreeAux σ binders phi)
  | imp_ phi psi =>
      imp_
      (replaceFreeAux σ binders phi)
      (replaceFreeAux σ binders psi)
  | and_ phi psi =>
      and_
      (replaceFreeAux σ binders phi)
      (replaceFreeAux σ binders psi)
  | or_ phi psi =>
      or_
      (replaceFreeAux σ binders phi)
      (replaceFreeAux σ binders psi)
  | iff_ phi psi =>
      iff_
      (replaceFreeAux σ binders phi)
      (replaceFreeAux σ binders psi)
  | forall_ x phi =>
      forall_ x (replaceFreeAux σ (binders ∪ {x}) phi)
  | exists_ x phi =>
      exists_ x (replaceFreeAux σ (binders ∪ {x}) phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName) => if x ∉ binders then σ x else x)


/--
  replaceFree σ F := The simultaneous replacement of each free occurrence of any variable v in the formula F by σ v.
-/
def replaceFree (σ : VarName → VarName) (F : Formula) : Formula :=
  replaceFreeAux σ ∅ F


/--
  fastReplaceFree σ F := The simultaneous replacement of each free occurrence of any variable v in the formula F by σ v.
-/
def fastReplaceFree (σ : VarName → VarName) : Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (fastReplaceFree σ phi)
  | imp_ phi psi =>
      imp_
      (fastReplaceFree σ phi)
      (fastReplaceFree σ psi)
  | and_ phi psi =>
      and_
      (fastReplaceFree σ phi)
      (fastReplaceFree σ psi)
  | or_ phi psi =>
      or_
      (fastReplaceFree σ phi)
      (fastReplaceFree σ psi)
  | iff_ phi psi =>
      iff_
      (fastReplaceFree σ phi)
      (fastReplaceFree σ psi)
  | forall_ x phi =>
      forall_ x (fastReplaceFree (Function.updateITE σ x x) phi)
  | exists_ x phi =>
      exists_ x (fastReplaceFree (Function.updateITE σ x x) phi)
  | def_ X xs => def_ X (xs.map σ)


theorem fastReplaceFree_id
  (F : Formula) :
  fastReplaceFree id F = F :=
  by
  induction F
  all_goals
    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr!
    simp
  case eq_ x y =>
    congr!
  case not_ phi phi_ih =>
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    congr!
    simp only [Function.updateITE_id]
    exact phi_ih


example
  (F : Formula)
  (v t : VarName) :
  fastReplaceFree (Function.updateITE id v t) F =
    One.Rec.fastReplaceFree v t F :=
  by
  induction F
  all_goals
    simp only [fastReplaceFree]
    simp only [One.Rec.fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x _
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
      apply fastReplaceFree_id
    case neg c1 =>
      simp
      simp only [← phi_ih]
      congr! 1
      apply Function.updateITE_comm_id x v t
      tauto


theorem fastReplaceFree_same_on_free
  (F : Formula)
  (σ σ' : VarName → VarName)
  (h1 : ∀ (v : VarName), isFreeIn v F → σ v = σ' v) :
  fastReplaceFree σ F = fastReplaceFree σ' F :=
  by
  induction F generalizing σ σ'
  all_goals
    simp only [isFreeIn] at h1

    simp only [fastReplaceFree]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case eq_ x y =>
    congr! 1
    · apply h1
      left
      rfl
    · apply h1
      right
      rfl
  case not_ phi phi_ih =>
    congr! 1
    exact phi_ih σ σ' h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
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
    congr! 1
    apply phi_ih
    intro v a1
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      apply h1
      tauto


theorem replaceFreeAux_same_on_free
  (F : Formula)
  (σ σ' : VarName → VarName)
  (binders : Finset VarName)
  (h1 : ∀ (v : VarName), v ∉ binders → σ v = σ' v) :
  replaceFreeAux σ binders F =
    replaceFreeAux σ' binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [replaceFreeAux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs <;> tauto
  case eq_ x y =>
    congr! 1
    · split_ifs <;> tauto
    · split_ifs <;> tauto
  case not_ phi phi_ih =>
    simp
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    congr! 1
    apply phi_ih
    simp
    tauto


example
  (F : Formula)
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (h1 : ∀ (v : VarName), v ∈ binders → v = σ v) :
  replaceFreeAux σ binders F =
    fastReplaceFree σ F :=
  by
  induction F generalizing binders σ
  all_goals
    simp only [fastReplaceFree]
    simp only [replaceFreeAux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x _
    split_ifs <;> tauto
  case eq_ x y =>
    congr! 1
    · split_ifs <;> tauto
    · split_ifs <;> tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    congr! 1

    have s1 : (∀ (v : VarName), v ∈ binders ∪ {x} → v = Function.updateITE σ x x v)
    intros v a1
    simp at a1
    simp only [Function.updateITE]
    cases a1
    case _ c1 =>
      split_ifs <;> tauto
    case _ c1 =>
      simp only [if_pos c1]
      exact c1

    simp only [← phi_ih (Function.updateITE σ x x) (binders ∪ {x}) s1]
    apply replaceFreeAux_same_on_free phi σ (Function.updateITE σ x x) (binders ∪ {x})
    simp only [Function.updateITE]
    intro v a1
    simp at a1
    push_neg at a1
    cases a1
    case _ a1_left a1_right =>
      simp only [if_neg a1_right]


#lint
