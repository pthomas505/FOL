import FOL.NV.PredSub.All.Rec.PredSubAllRecOption
import FOL.NV.Alpha


namespace FOL

namespace NV

open Formula


def predVarFreeVarSet
  (τ : PredName → ℕ → Option (List VarName × Formula)) :=
  fun (p, n) =>
    let opt := τ p n
    if h : Option.isSome opt
    then
      let val := Option.get opt h
      let zs := val.fst
      let H := val.snd
      H.freeVarSet \ zs.toFinset
    else ∅


def subPredAlphaAux
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (α : VarName → VarName) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map α)
  | pred_var_ X xs => pred_var_ X (xs.map α)
  | eq_ x y => eq_ (α x) (α y)
  | true_ => true_
  | false_ => false_
  | not_ phi =>
      not_ (subPredAlphaAux c τ α phi)
  | imp_ phi psi =>
      imp_
      (subPredAlphaAux c τ α phi)
      (subPredAlphaAux c τ α psi)
  | and_ phi psi =>
      and_
      (subPredAlphaAux c τ α phi)
      (subPredAlphaAux c τ α psi)
  | or_ phi psi =>
      or_
      (subPredAlphaAux c τ α phi)
      (subPredAlphaAux c τ α psi)
  | iff_ phi psi =>
      iff_
      (subPredAlphaAux c τ α phi)
      (subPredAlphaAux c τ α psi)
  | forall_ x phi =>
      let vs : Finset VarName := sorry
      let x' : VarName :=
        if x ∈ vs
        then fresh x c vs
        else x
      forall_ x' (subPredAlphaAux c τ (Function.updateITE α x x') phi)
  | exists_ x phi =>
      let vs : Finset VarName := sorry
      let x' : VarName :=
        if x ∈ vs
        then fresh x c vs
        else x
      exists_ x' (subPredAlphaAux c τ (Function.updateITE α x x') phi)
  | def_ X xs => def_ X (xs.map α)


example
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (F : Formula) :
  AlphaEqv F (subPredAlphaAux c τ α F) :=
  by
  induction F
  case pred_var_ X xs =>
    simp only [subPredAlphaAux]
    sorry

  case forall_ x phi phi_ih =>
    simp only [subPredAlphaAux]

    obtain s1 := fresh_not_mem x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))

    generalize fresh x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)) = x' at *

    split_ifs
    case pos c1 =>

      sorry
    case neg c1 =>
      sorry
  all_goals
    sorry


example
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (α : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula)
  (h1 : ∀ (x : VarName), x ∈ binders → x ∉ (Finset.biUnion F.predVarSet (predVarFreeVarSet τ))) :
  admitsPredFunAux τ binders (subPredAlphaAux c τ α F) :=
  by
  induction F generalizing α binders
  case pred_const_ X xs | true_ | false_ | eq_ | def_ =>
    simp only [subPredAlphaAux]
    simp only [admitsPredFunAux]
  case pred_var_ X xs =>
    simp only [predVarSet] at h1
    simp at h1

    simp only [subPredAlphaAux]
    simp only [admitsPredFunAux]
    split_ifs
    case _ c1 c2 =>
      simp at c1

      apply Finset.eq_empty_of_forall_not_mem
      simp
      intro x a1 a2
      specialize h1 x a1
      simp only [predVarFreeVarSet] at h1
      simp only [c1] at h1
      simp at h1
      exact h1 a2
  case not_ phi phi_ih =>
    simp only [predVarSet] at h1

    simp only [subPredAlphaAux]
    simp only [admitsPredFunAux]
    apply phi_ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [predVarSet] at h1
    simp at h1

    simp only [subPredAlphaAux]
    simp only [admitsPredFunAux]
    constructor
    · apply phi_ih
      simp
      intro x a1 X n a2
      apply h1 x a1 X n
      left
      exact a2
    · apply psi_ih
      simp
      intro x a1 X n a2
      apply h1 x a1 X n
      right
      exact a2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [predVarSet] at h1

    simp only [subPredAlphaAux]
    simp only [admitsPredFunAux]
    split_ifs
    case pos c1 =>
      obtain s1 := fresh_not_mem x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))

      generalize (fresh x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))) = x' at *

      have s2 : ¬ x' = x
      intro contra
      subst contra
      apply s1
      sorry

      apply phi_ih
      intro x_1 a1
      simp at a1
      cases a1
      case _ c2 =>
        apply h1
        exact c2
      case _ c2 =>
        subst c2
        sorry
    case neg c1 =>
      apply phi_ih
      intro x_1 a1
      simp at a1
      cases a1
      case _ c2 =>
        apply h1
        exact c2
      case _ c2 =>
        subst c2
        sorry
