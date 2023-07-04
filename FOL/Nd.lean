import FOL.Alpha
import FOL.Sub.One.Rec.SubOneRecAdmits
import FOL.PredSub.All.Rec.PredSubAllRec

import FOL.Tactics

import Mathlib.Data.Finset.Basic


namespace FOL

open Formula


inductive IsDeduct : Finset Formula → Formula → Prop
  | true_intro_
    (Δ : Finset Formula) :
    IsDeduct Δ true_

  | false_elim_
    (Δ : Finset Formula)
    (phi : Formula) :
    IsDeduct Δ false_ →
    IsDeduct Δ phi

  | not_intro_
    (Δ : Finset Formula)
    (phi : Formula) :
    IsDeduct (Δ ∪ {phi}) false_ →
    IsDeduct Δ (not_ phi)

  | not_elim_
    (Δ : Finset Formula)
    (phi : Formula) :
    IsDeduct Δ (not_ phi) →
    IsDeduct Δ phi →
    IsDeduct Δ false_

  | imp_intro_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct (Δ ∪ {phi}) psi →
    IsDeduct Δ (phi.imp_ psi)

  | imp_elim_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ (phi.imp_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi

  | and_intro_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ phi →
    IsDeduct Δ psi →
    IsDeduct Δ (phi.and_ psi)

  | and_elim_left_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ (phi.and_ psi) →
    IsDeduct Δ phi

  | and_elim_right_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ (phi.and_ psi) →
    IsDeduct Δ psi

  | or_intro_left_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ phi →
    IsDeduct Δ (phi.or_ psi)

  | or_intro_right_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ psi →
    IsDeduct Δ (phi.or_ psi)

  | or_elim_
    (Δ : Finset Formula)
    (phi psi chi : Formula) :
    IsDeduct Δ (phi.or_ psi) →
    IsDeduct (Δ ∪ {phi}) chi →
    IsDeduct (Δ ∪ {psi}) chi →
    IsDeduct Δ chi

  | iff_intro_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct (Δ ∪ {phi}) psi →
    IsDeduct (Δ ∪ {psi}) phi →
    IsDeduct Δ (phi.iff_ psi)

  | iff_elim_left_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ (phi.iff_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi

  | iff_elim_right_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ (phi.iff_ psi) →
    IsDeduct Δ psi →
    IsDeduct Δ phi

    -- classical
  | contra_
    (Δ : Finset Formula)
    (phi : Formula) :
    IsDeduct (Δ ∪ {not_ phi}) false_ →
    IsDeduct Δ phi

  | refl_
    (Δ : Finset Formula)
    (x : VarName) :
    IsDeduct Δ (Formula.eq_ x x)

  | subst_
    (Δ : Finset Formula)
    (phi : Formula)
    (x y : VarName) :
    IsDeduct Δ (Formula.eq_ x y) →
    IsDeduct Δ phi →
    fastAdmits x y phi →
    IsDeduct Δ (fastReplaceFree x y phi)

  | forall_intro_
    (Δ : Finset Formula)
    (phi : Formula)
    (x : VarName) :
    IsDeduct Δ phi →
    (∀ H : Formula, H ∈ Δ → ¬ isFreeIn x H) →
    IsDeduct Δ (forall_ x phi)

  | forall_elim_
    (Δ : Finset Formula)
    (phi : Formula)
    (x y : VarName) :
    IsDeduct Δ (forall_ x phi) →
    fastAdmits x y phi →
    IsDeduct Δ (fastReplaceFree x y phi)

  | exists_intro_
    (Δ : Finset Formula)
    (phi : Formula)
    (x y : VarName) :
    fastAdmits x y phi →
    IsDeduct Δ (fastReplaceFree x y phi) →
    IsDeduct Δ (exists_ x phi)

  | exists_elim_
    (Δ : Finset Formula)
    (phi psi : Formula)
    (x : VarName) :
    IsDeduct Δ (exists_ x phi) →
    IsDeduct (Δ ∪ {phi}) psi →
    (∀ H : Formula, H ∈ Δ →
    ¬ isFreeIn x H) →
    ¬ isFreeIn x psi →
    IsDeduct Δ psi

  | pred_sub_
    (Δ : Finset Formula)
    (phi : Formula)
    (τ : PredName → ℕ → List VarName × Formula) :
    IsDeduct Δ phi →
    admitsPredFun τ phi →
    (∀ H : Formula, H ∈ Δ → admitsPredFun τ H) →
    IsDeduct (Δ.image (replacePredFun τ)) (replacePredFun τ phi)

  | weaken_
    (Δ Δ' : Finset Formula)
    (phi : Formula) :
    IsDeduct Δ phi →
    IsDeduct (Δ ∪ Δ') phi

  | hyp_
    (Δ : Finset Formula)
    (phi : Formula) :
    phi ∈ Δ →
    IsDeduct Δ phi

  | alpha_
    (Δ : Finset Formula)
    (phi psi : Formula) :
    IsDeduct Δ phi →
    isAlphaEqv phi psi →
    IsDeduct Δ psi


--#lint

end FOL
