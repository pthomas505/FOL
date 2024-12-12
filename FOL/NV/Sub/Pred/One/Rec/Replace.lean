import FOL.NV.Sub.Var.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.One.Rec

open Formula_


-- predicate substitution
-- single
-- https://math.stackexchange.com/a/1374989
/--
  The simultaneous replacement of a predicate variable in a formula.
-/
def replace_pred_one_rec
  (P : PredName_)
  (zs : List VarName_)
  (H : Formula_) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      if X = P ∧ xs.length = zs.length
      then Sub.Var.All.Rec.fast_replace_free_var_all_rec (Function.updateListITE id zs xs) H
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_pred_one_rec P zs H phi)
  | imp_ phi psi =>
      imp_
      (replace_pred_one_rec P zs H phi)
      (replace_pred_one_rec P zs H psi)
  | and_ phi psi =>
      and_
      (replace_pred_one_rec P zs H phi)
      (replace_pred_one_rec P zs H psi)
  | or_ phi psi =>
      or_
      (replace_pred_one_rec P zs H phi)
      (replace_pred_one_rec P zs H psi)
  | iff_ phi psi =>
      iff_
      (replace_pred_one_rec P zs H phi)
      (replace_pred_one_rec P zs H psi)
  | forall_ x phi => forall_ x (replace_pred_one_rec P zs H phi)
  | exists_ x phi => exists_ x (replace_pred_one_rec P zs H phi)
  | def_ X xs => def_ X xs


#lint
