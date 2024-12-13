import FOL.NV.Alpha.Rec.Alpha
import FOL.NV.Sub.Var.One.Rec.Admits
import FOL.NV.Sub.Pred.All.Rec.Admits

import Mathlib.Data.Finset.Basic


set_option autoImplicit false


namespace FOL.NV

open Formula_


/--
  IsDeduct Δ F := True if and only if there is a deduction of F from Δ in classical propositional logic.
-/
inductive IsDeduct : Finset Formula_ → Formula_ → Prop
  | true_intro_
    (Δ : Finset Formula_) :
    IsDeduct Δ true_

  | false_elim_
    (Δ : Finset Formula_)
    (phi : Formula_) :
    IsDeduct Δ false_ →
    IsDeduct Δ phi

  | not_intro_
    (Δ : Finset Formula_)
    (phi : Formula_) :
    IsDeduct (Δ ∪ {phi}) false_ →
    IsDeduct Δ (not_ phi)

  | not_elim_
    (Δ : Finset Formula_)
    (phi : Formula_) :
    IsDeduct Δ (not_ phi) →
    IsDeduct Δ phi →
    IsDeduct Δ false_

  | imp_intro_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct (Δ ∪ {phi}) psi →
    IsDeduct Δ (phi.imp_ psi)

  | imp_elim_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ (phi.imp_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi

  | and_intro_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ phi →
    IsDeduct Δ psi →
    IsDeduct Δ (phi.and_ psi)

  | and_elim_left_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ (phi.and_ psi) →
    IsDeduct Δ phi

  | and_elim_right_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ (phi.and_ psi) →
    IsDeduct Δ psi

  | or_intro_left_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ phi →
    IsDeduct Δ (phi.or_ psi)

  | or_intro_right_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ psi →
    IsDeduct Δ (phi.or_ psi)

  | or_elim_
    (Δ : Finset Formula_)
    (phi psi chi : Formula_) :
    IsDeduct Δ (phi.or_ psi) →
    IsDeduct (Δ ∪ {phi}) chi →
    IsDeduct (Δ ∪ {psi}) chi →
    IsDeduct Δ chi

  | iff_intro_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct (Δ ∪ {phi}) psi →
    IsDeduct (Δ ∪ {psi}) phi →
    IsDeduct Δ (phi.iff_ psi)

  | iff_elim_left_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ (phi.iff_ psi) →
    IsDeduct Δ phi →
    IsDeduct Δ psi

  | iff_elim_right_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ (phi.iff_ psi) →
    IsDeduct Δ psi →
    IsDeduct Δ phi

    -- classical
  | contra_
    (Δ : Finset Formula_)
    (phi : Formula_) :
    IsDeduct (Δ ∪ {not_ phi}) false_ →
    IsDeduct Δ phi

  | refl_
    (Δ : Finset Formula_)
    (x : VarName_) :
    IsDeduct Δ (Formula_.eq_ x x)

  | subst_
    (Δ : Finset Formula_)
    (phi : Formula_)
    (x y : VarName_) :
    IsDeduct Δ (Formula_.eq_ x y) →
    IsDeduct Δ phi →
    Sub.Var.One.Rec.fast_admits_var_one_rec x y phi →
    IsDeduct Δ (Sub.Var.One.Rec.fast_replace_free_var_one_rec x y phi)

  | forall_intro_
    (Δ : Finset Formula_)
    (phi : Formula_)
    (x : VarName_) :
    IsDeduct Δ phi →
    (∀ H : Formula_, H ∈ Δ → ¬ var_is_free_in x H) →
    IsDeduct Δ (forall_ x phi)

  | forall_elim_
    (Δ : Finset Formula_)
    (phi : Formula_)
    (x y : VarName_) :
    IsDeduct Δ (forall_ x phi) →
    Sub.Var.One.Rec.fast_admits_var_one_rec x y phi →
    IsDeduct Δ (Sub.Var.One.Rec.fast_replace_free_var_one_rec x y phi)

  | exists_intro_
    (Δ : Finset Formula_)
    (phi : Formula_)
    (x y : VarName_) :
    Sub.Var.One.Rec.fast_admits_var_one_rec x y phi →
    IsDeduct Δ (Sub.Var.One.Rec.fast_replace_free_var_one_rec x y phi) →
    IsDeduct Δ (exists_ x phi)

  | exists_elim_
    (Δ : Finset Formula_)
    (phi psi : Formula_)
    (x : VarName_) :
    IsDeduct Δ (exists_ x phi) →
    IsDeduct (Δ ∪ {phi}) psi →
    (∀ H : Formula_, H ∈ Δ →
    ¬ var_is_free_in x H) →
    ¬ var_is_free_in x psi →
    IsDeduct Δ psi

  | pred_sub_
    (Δ : Finset Formula_)
    (phi : Formula_)
    (τ : PredName_ → ℕ → List VarName_ × Formula_) :
    IsDeduct Δ phi →
    Sub.Pred.All.Rec.admits_pred_all_rec τ phi →
    (∀ H : Formula_, H ∈ Δ → Sub.Pred.All.Rec.admits_pred_all_rec τ H) →
    IsDeduct (Δ.image (Sub.Pred.All.Rec.replace_pred_all_rec τ)) (Sub.Pred.All.Rec.replace_pred_all_rec τ phi)

  | weaken_
    (Δ Δ' : Finset Formula_)
    (phi : Formula_) :
    IsDeduct Δ phi →
    IsDeduct (Δ ∪ Δ') phi

  | hyp_
    (Δ : Finset Formula_)
    (phi : Formula_) :
    phi ∈ Δ →
    IsDeduct Δ phi

  | alpha_
    (Δ : Finset Formula_)
    (phi psi : Formula_) :
    IsDeduct Δ phi →
    are_alpha_equiv_rec phi psi →
    IsDeduct Δ psi


#lint
