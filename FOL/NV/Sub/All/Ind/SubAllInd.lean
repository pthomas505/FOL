import FOL.NV.Sub.All.Rec.SubAllRecReplaceFree
import FOL.NV.Semantics
import FOL.Tactics


namespace FOL

namespace NV

open Formula


inductive IsReplaceFreeFun : (σ : VarName → VarName) → Formula → Formula → Prop

  | pred_const_
    (X : PredName)
    (xs : List VarName) :
    IsReplaceFreeFun σ (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (X : PredName)
    (xs : List VarName) :
    IsReplaceFreeFun σ (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (x y : VarName) :
    IsReplaceFreeFun σ (eq_ x y) (eq_ (σ x) (σ y))

  | true_ :
    IsReplaceFreeFun σ true_ true_

  | false_ :
    IsReplaceFreeFun σ false_ false_

  | not_
    (phi : Formula)
    (phi' : Formula) :
    IsReplaceFreeFun σ phi phi' →
    IsReplaceFreeFun σ phi.not_ phi'.not_

  | imp_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFreeFun σ phi phi' →
    IsReplaceFreeFun σ psi psi' →
    IsReplaceFreeFun σ (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFreeFun σ phi phi' →
    IsReplaceFreeFun σ psi psi' →
    IsReplaceFreeFun σ (phi.and_ psi) (phi'.and_ psi')

  | or_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFreeFun σ phi phi' →
    IsReplaceFreeFun σ psi psi' →
    IsReplaceFreeFun σ (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFreeFun σ phi phi' →
    IsReplaceFreeFun σ psi psi' →
    IsReplaceFreeFun σ (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (x : VarName)
    (phi phi' : Formula) :
    IsReplaceFreeFun (Function.updateITE σ x x) phi phi' →
    IsReplaceFreeFun σ (forall_ x phi) (forall_ x phi')

  | exists_
    (x : VarName)
    (phi phi' : Formula) :
    IsReplaceFreeFun (Function.updateITE σ x x) phi phi' →
    IsReplaceFreeFun σ (exists_ x phi) (exists_ x phi')

  | def_
    (X : DefName)
    (xs : List VarName) :
    IsReplaceFreeFun σ (def_ X xs) (def_ X (xs.map σ))


example
  (F F' : Formula)
  (σ : VarName → VarName)
  (h1 : fastReplaceFreeFun σ F = F') :
  IsReplaceFreeFun σ F F' :=
  by
  subst h1
  induction F generalizing σ
  case pred_const_ X xs =>
    simp only [fastReplaceFreeFun]
    apply IsReplaceFreeFun.pred_const_
  case forall_ x phi phi_ih =>
    simp only [fastReplaceFreeFun]
    apply IsReplaceFreeFun.forall_
    apply phi_ih
  all_goals
    sorry


inductive IsFreeSubFun :
  (σ : VarName → VarName) →
  (binders : Finset VarName)
  → Formula → Formula → Prop

  | pred_const_
    (X : PredName)
    (xs : List VarName) :
    (∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    IsFreeSubFun σ binders (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (X : PredName)
    (xs : List VarName) :
    (∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders) →
    IsFreeSubFun σ binders (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (x y : VarName) :
    ∀ v : VarName, (v = x ∨ v = y) → v ∉ binders → σ v ∉ binders →
    IsFreeSubFun σ binders (eq_ x y) (eq_ (σ x) (σ y))

  | true_ :
    IsFreeSubFun σ binders true_ true_

  | false_ :
    IsFreeSubFun σ binders false_ false_

  | not_
    (phi : Formula)
    (phi' : Formula) :
    IsFreeSubFun σ binders phi phi' →
    IsFreeSubFun σ binders phi.not_ phi'.not_

  | imp_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ binders phi phi' →
    IsFreeSubFun σ binders psi psi' →
    IsFreeSubFun σ binders (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ binders phi phi' →
    IsFreeSubFun σ binders psi psi' →
    IsFreeSubFun σ binders (phi.and_ psi) (phi'.and_ psi')

  | or_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ binders phi phi' →
    IsFreeSubFun σ binders psi psi' →
    IsFreeSubFun σ binders (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ binders phi phi' →
    IsFreeSubFun σ binders psi psi' →
    IsFreeSubFun σ binders (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (x : VarName)
    (phi phi' : Formula) :
    IsFreeSubFun (Function.updateITE σ x x) (binders ∪ {x}) phi phi' →
    --IsFreeSubFun σ (binders ∪ {x}) phi phi' →
    IsFreeSubFun σ binders (forall_ x phi) (forall_ x phi')

  | def_
    (X : DefName)
    (xs : List VarName) :
    IsFreeSubFun σ binders (def_ X xs) (def_ X (xs.map σ))


example
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (F F' : Formula)
  (h1 : IsFreeSubFun σ binders F F')
  --(h2 : ∀ v : VarName, v ∈ binders ∨ σ v ∉ binders → V v = V' (σ v))
  (h2 : ∀ v : VarName, v ∈ binders → V v = V' (σ v))
  (h2' : ∀ v : VarName, σ v ∉ binders → V v = V' (σ v))
  (h3 : ∀ v : VarName, v ∈ binders → v = σ v) :
  Holds D I V E F ↔ Holds D I V' E F' :=
  by
  induction h1 generalizing V V'
  case pred_const_ binders' σ' X' xs' ih_1 | pred_var_ binders' σ' X' xs' ih_1 =>
    simp only [Holds]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x a1
    simp
    by_cases c1 : x ∈ binders'
    · exact h2 x c1
    · apply h2'
      exact ih_1 x a1 c1
  case forall_ σ' binders' x phi phi' ih_1 ih_2 =>
    simp at ih_2

    have s1 : ∀ (v : VarName), ¬ v = x → v ∈ binders' → ¬ σ' v = x
    intro v a1 a2 contra
    apply a1
    simp only [← contra]
    exact h3 v a2

    simp only [Holds]
    apply forall_congr'
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
          apply h2' v a1_left
    · intro v a1
      simp only [Function.updateITE]
      split_ifs
      case _ c1 =>
        exact c1
      case _ c1 =>
        cases a1
        case _ c2 =>
          exact h3 v c2
        case _ c2 =>
          contradiction
  all_goals
    sorry
