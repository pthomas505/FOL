import FOL.NV.Sub.All.Rec.SubAllRecAdmits
import FOL.Tactics


namespace FOL

namespace NV

open Formula


inductive IsFreeSubFun (σ : VarName → VarName) : Formula → Formula → Prop

  | pred_const_
    (X : PredName)
    (xs : List VarName) :
    IsFreeSubFun σ (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (X : PredName)
    (xs : List VarName) :
    IsFreeSubFun σ (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (x y : VarName) :
    IsFreeSubFun σ (eq_ x y) (eq_ (σ x) (σ y))

  | true_ :
    IsFreeSubFun σ true_ true_

  | false_ :
    IsFreeSubFun σ false_ false_

  | not_
    (phi : Formula)
    (phi' : Formula) :
    IsFreeSubFun σ phi phi' →
    IsFreeSubFun σ phi.not_ phi'.not_

  | imp_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ phi phi' →
    IsFreeSubFun σ psi psi' →
    IsFreeSubFun σ (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ phi phi' →
    IsFreeSubFun σ psi psi' →
    IsFreeSubFun σ (phi.and_ psi) (phi'.and_ psi')

  | or_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ phi phi' →
    IsFreeSubFun σ psi psi' →
    IsFreeSubFun σ (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsFreeSubFun σ phi phi' →
    IsFreeSubFun σ psi psi' →
    IsFreeSubFun σ (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (x : VarName)
    (phi phi' : Formula) :
    (∀ (v : VarName), v ∈ (forall_ x phi).freeVarSet → ¬ σ v = x) →
    IsFreeSubFun σ phi phi' →
    IsFreeSubFun σ (forall_ x phi) (forall_ x phi')

  | def_
    (X : DefName)
    (xs : List VarName) :
    IsFreeSubFun σ (def_ X xs) (def_ X (xs.map σ))


theorem admitsFunAux_and_fastReplaceFreeFun_imp_IsFreeSubFun
  (F F' : Formula)
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (h1 : admitsFunAux σ binders F)
  (h2 : fastReplaceFreeFun σ F = F') :
  IsFreeSubFun σ F F' :=
  by
  subst h2
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | true_ | false_ | def_ X xs =>
    simp only [fastReplaceFreeFun]
    first | apply IsFreeSubFun.pred_const_ | apply IsFreeSubFun.pred_var_ | apply IsFreeSubFun.eq_ | apply IsFreeSubFun.true_ | apply IsFreeSubFun.false_ | apply IsFreeSubFun.def_
  case not_ phi phi_ih =>
    simp only [admitsFunAux] at h1

    simp only [fastReplaceFreeFun]
    apply IsFreeSubFun.not_
    exact phi_ih binders h1
  all_goals
    sorry
