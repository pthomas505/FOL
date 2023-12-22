import FOL.NV.Semantics
import FOL.NV.Sub.Var.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Ind

open Formula


/--
  IsReplaceFree σ F F' := True if and only if F' is the result of the simultaneous replacement of each free occurrence of any variable v in the formula F by σ v.
-/
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
  all_goals
    simp only [Rec.fastReplaceFree]
  case pred_const_ X xs =>
    apply IsReplaceFree.pred_const_
  case pred_var_ X xs =>
    apply IsReplaceFree.pred_var_
  case eq_ x y =>
    apply IsReplaceFree.eq_
  case true_ =>
    apply IsReplaceFree.true_
  case false_ =>
    apply IsReplaceFree.false_
  case not_ phi phi_ih =>
    apply IsReplaceFree.not_
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    apply IsReplaceFree.imp_
    · apply phi_ih
    · apply psi_ih
  case and_ phi psi phi_ih psi_ih =>
    apply IsReplaceFree.and_
    · apply phi_ih
    · apply psi_ih
  case or_ phi psi phi_ih psi_ih =>
    apply IsReplaceFree.or_
    · apply phi_ih
    · apply psi_ih
  case iff_ phi psi phi_ih psi_ih =>
    apply IsReplaceFree.iff_
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih =>
    apply IsReplaceFree.forall_
    apply phi_ih
  case exists_ x phi phi_ih =>
    apply IsReplaceFree.exists_
    · apply phi_ih
  case def_ X xs =>
    apply IsReplaceFree.def_


example
  (F F' : Formula)
  (σ : VarName → VarName)
  (h1 : IsReplaceFree σ F F') :
  Rec.fastReplaceFree σ F = F' :=
  by
  induction h1
  all_goals
    simp only [Rec.fastReplaceFree]
  case not_ σ' phi phi' ih_1 ih_2 =>
    simp
    exact ih_2
  case
      imp_ σ' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
    | and_ σ' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
    | or_ σ' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2
    | iff_ σ' phi psi phi' psi' phi_ih_1 psi_ih_1 phi_ih_2 psi_ih_2 =>
    simp
    tauto
  case
      forall_ σ' x phi phi' ih_1 ih_2
    | exists_ σ' x phi phi' ih_1 ih_2 =>
    simp
    exact ih_2


#lint
