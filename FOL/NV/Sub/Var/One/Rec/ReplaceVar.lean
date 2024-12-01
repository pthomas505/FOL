import MathlibExtra.List
import FOL.NV.Binders


set_option autoImplicit false


open Formula_


def replace_var_one_rec (v t : VarName_) : Formula_ → Formula_
  | pred_const_ X xs =>
      pred_const_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)
  | pred_var_ X xs =>
      pred_var_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)
  | eq_ x y =>
    eq_
    (if v = x then t else x)
    (if v = y then t else y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_var_one_rec v t phi)
  | imp_ phi psi => imp_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | and_ phi psi => and_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | or_ phi psi => or_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | iff_ phi psi => iff_ (replace_var_one_rec v t phi) (replace_var_one_rec v t psi)
  | forall_ x phi =>
      if v = x
      then forall_ t (replace_var_one_rec v t phi)
      else forall_ x (replace_var_one_rec v t phi)
  | exists_ x phi =>
      if v = x
      then exists_ t (replace_var_one_rec v t phi)
      else exists_ x (replace_var_one_rec v t phi)
  | def_ X xs =>
      def_
      X
      (xs.map fun (x : VarName_) => if v = x then t else x)


theorem replace_var_one_rec_self
  (F : Formula_)
  (v : VarName_) :
  replace_var_one_rec v v F = F :=
  by
  induction F
  any_goals
    simp only [replace_var_one_rec]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    simp only [List.map_eq_self_iff]
    simp
  case eq_ x y =>
    simp
  case not_ phi phi_ih =>
    congr!
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr!
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
