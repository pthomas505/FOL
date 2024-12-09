import FOL.NV.Semantics
import FOL.NV.Sub.Var.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.All.Ind

open Formula_


/--
  `is_replace_free_var_all_ind σ F F'` := True if and only if `F'` is the result of the simultaneous replacement of each free occurrence of any variable `v` in the formula `F` by `σ v`.
-/
inductive is_replace_free_var_all_ind : (VarName_ → VarName_) → Formula_ → Formula_ → Prop

  | pred_const_
    (σ : VarName_ → VarName_)
    (X : PredName_)
    (xs : List VarName_) :
    is_replace_free_var_all_ind σ (pred_const_ X xs) (pred_const_ X (xs.map σ))

  | pred_var_
    (σ : VarName_ → VarName_)
    (X : PredName_)
    (xs : List VarName_) :
    is_replace_free_var_all_ind σ (pred_var_ X xs) (pred_var_ X (xs.map σ))

  | eq_
    (σ : VarName_ → VarName_)
    (x y : VarName_) :
    is_replace_free_var_all_ind σ (eq_ x y) (eq_ (σ x) (σ y))

  | true_
    (σ : VarName_ → VarName_) :
    is_replace_free_var_all_ind σ true_ true_

  | false_
    (σ : VarName_ → VarName_) :
    is_replace_free_var_all_ind σ false_ false_

  | not_
    (σ : VarName_ → VarName_)
    (phi : Formula_)
    (phi' : Formula_) :
    is_replace_free_var_all_ind σ phi phi' →
    is_replace_free_var_all_ind σ phi.not_ phi'.not_

  | imp_
    (σ : VarName_ → VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_replace_free_var_all_ind σ phi phi' →
    is_replace_free_var_all_ind σ psi psi' →
    is_replace_free_var_all_ind σ (phi.imp_ psi) (phi'.imp_ psi')

  | and_
    (σ : VarName_ → VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_replace_free_var_all_ind σ phi phi' →
    is_replace_free_var_all_ind σ psi psi' →
    is_replace_free_var_all_ind σ (phi.and_ psi) (phi'.and_ psi')

  | or_
    (σ : VarName_ → VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_replace_free_var_all_ind σ phi phi' →
    is_replace_free_var_all_ind σ psi psi' →
    is_replace_free_var_all_ind σ (phi.or_ psi) (phi'.or_ psi')

  | iff_
    (σ : VarName_ → VarName_)
    (phi psi : Formula_)
    (phi' psi' : Formula_) :
    is_replace_free_var_all_ind σ phi phi' →
    is_replace_free_var_all_ind σ psi psi' →
    is_replace_free_var_all_ind σ (phi.iff_ psi) (phi'.iff_ psi')

  | forall_
    (σ : VarName_ → VarName_)
    (x : VarName_)
    (phi phi' : Formula_) :
    is_replace_free_var_all_ind (Function.updateITE σ x x) phi phi' →
    is_replace_free_var_all_ind σ (forall_ x phi) (forall_ x phi')

  | exists_
    (σ : VarName_ → VarName_)
    (x : VarName_)
    (phi phi' : Formula_) :
    is_replace_free_var_all_ind (Function.updateITE σ x x) phi phi' →
    is_replace_free_var_all_ind σ (exists_ x phi) (exists_ x phi')

  | def_
    (σ : VarName_ → VarName_)
    (X : DefName_)
    (xs : List VarName_) :
    is_replace_free_var_all_ind σ (def_ X xs) (def_ X (xs.map σ))


example
  (F F' : Formula_)
  (σ : VarName_ → VarName_)
  (h1 : Rec.fast_replace_free_var_all_rec σ F = F') :
  is_replace_free_var_all_ind σ F F' :=
  by
  subst h1
  induction F generalizing σ
  all_goals
    simp only [Rec.fast_replace_free_var_all_rec]
  case pred_const_ X xs =>
    apply is_replace_free_var_all_ind.pred_const_
  case pred_var_ X xs =>
    apply is_replace_free_var_all_ind.pred_var_
  case eq_ x y =>
    apply is_replace_free_var_all_ind.eq_
  case true_ =>
    apply is_replace_free_var_all_ind.true_
  case false_ =>
    apply is_replace_free_var_all_ind.false_
  case not_ phi phi_ih =>
    apply is_replace_free_var_all_ind.not_
    apply phi_ih
  case imp_ phi psi phi_ih psi_ih =>
    apply is_replace_free_var_all_ind.imp_
    · apply phi_ih
    · apply psi_ih
  case and_ phi psi phi_ih psi_ih =>
    apply is_replace_free_var_all_ind.and_
    · apply phi_ih
    · apply psi_ih
  case or_ phi psi phi_ih psi_ih =>
    apply is_replace_free_var_all_ind.or_
    · apply phi_ih
    · apply psi_ih
  case iff_ phi psi phi_ih psi_ih =>
    apply is_replace_free_var_all_ind.iff_
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih =>
    apply is_replace_free_var_all_ind.forall_
    apply phi_ih
  case exists_ x phi phi_ih =>
    apply is_replace_free_var_all_ind.exists_
    · apply phi_ih
  case def_ X xs =>
    apply is_replace_free_var_all_ind.def_


example
  (F F' : Formula_)
  (σ : VarName_ → VarName_)
  (h1 : is_replace_free_var_all_ind σ F F') :
  Rec.fast_replace_free_var_all_rec σ F = F' :=
  by
  induction h1
  all_goals
    simp only [Rec.fast_replace_free_var_all_rec]
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
