import FOL.NV.Semantics
import FOL.NV.Sub.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.All.Ind

open Formula


inductive IsReplaceFree : (VarName → VarName) → Formula → Formula → Prop

  | pred_const_
    (σ : VarName → VarName)
    (X : PredName)
    (xs : List VarName) :
    IsReplaceFree σ (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (σ : VarName → VarName)
    (X : PredName)
    (xs : List VarName) :
    IsReplaceFree σ (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (σ : VarName → VarName)
    (x y : VarName) :
    IsReplaceFree σ (eq_ x y) (eq_ (σ x) (σ y))

  | true_
    (σ : VarName → VarName) :
    IsReplaceFree σ true_ true_

  | false_
    (σ : VarName → VarName) :
    IsReplaceFree σ false_ false_

  | not_
    (σ : VarName → VarName)
    (phi : Formula)
    (phi' : Formula) :
    IsReplaceFree σ phi phi' →
    IsReplaceFree σ phi.not_ phi'.not_

  | imp_
    (σ : VarName → VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFree σ phi phi' →
    IsReplaceFree σ psi psi' →
    IsReplaceFree σ (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (σ : VarName → VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFree σ phi phi' →
    IsReplaceFree σ psi psi' →
    IsReplaceFree σ (phi.and_ psi) (phi'.and_ psi')

  | or_
    (σ : VarName → VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFree σ phi phi' →
    IsReplaceFree σ psi psi' →
    IsReplaceFree σ (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (σ : VarName → VarName)
    (phi psi : Formula)
    (phi' psi' : Formula) :
    IsReplaceFree σ phi phi' →
    IsReplaceFree σ psi psi' →
    IsReplaceFree σ (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (σ : VarName → VarName)
    (x : VarName)
    (phi phi' : Formula) :
    IsReplaceFree (Function.updateITE σ x x) phi phi' →
    IsReplaceFree σ (forall_ x phi) (forall_ x phi')

  | exists_
    (σ : VarName → VarName)
    (x : VarName)
    (phi phi' : Formula) :
    IsReplaceFree (Function.updateITE σ x x) phi phi' →
    IsReplaceFree σ (exists_ x phi) (exists_ x phi')

  | def_
    (σ : VarName → VarName)
    (X : DefName)
    (xs : List VarName) :
    IsReplaceFree σ (def_ X xs) (def_ X (xs.map σ))


example
  (F F' : Formula)
  (σ : VarName → VarName)
  (h1 : Rec.fastReplaceFree σ F = F') :
  IsReplaceFree σ F F' :=
  by
  subst h1
  induction F generalizing σ
  case pred_const_ X xs =>
    simp only [Rec.fastReplaceFree]
    apply IsReplaceFree.pred_const_
  case forall_ x phi phi_ih =>
    simp only [Rec.fastReplaceFree]
    apply IsReplaceFree.forall_
    apply phi_ih
  all_goals
    sorry
