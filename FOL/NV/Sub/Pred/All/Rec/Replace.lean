import FOL.NV.Sub.Var.All.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.All.Rec

open Formula_


-- multiple

/--
  The simultaneous substitution of all of the predicate variables in a formula.
-/
def replace_pred_all_rec
  (τ : PredName_ → ℕ → (List VarName_ × Formula_)) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      let zs := (τ X xs.length).fst
      let H := (τ X xs.length).snd
      if xs.length = zs.length
      then Sub.Var.All.Rec.fast_replace_free_var_all_rec (Function.updateListITE id zs xs) H
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_pred_all_rec τ phi)
  | imp_ phi psi =>
      imp_
      (replace_pred_all_rec τ phi)
      (replace_pred_all_rec τ psi)
  | and_ phi psi =>
      and_
      (replace_pred_all_rec τ phi)
      (replace_pred_all_rec τ psi)
  | or_ phi psi =>
      or_
      (replace_pred_all_rec τ phi)
      (replace_pred_all_rec τ psi)
  | iff_ phi psi =>
      iff_
      (replace_pred_all_rec τ phi)
      (replace_pred_all_rec τ psi)
  | forall_ x phi => forall_ x (replace_pred_all_rec τ phi)
  | exists_ x phi => exists_ x (replace_pred_all_rec τ phi)
  | def_ X xs => def_ X xs


#lint
