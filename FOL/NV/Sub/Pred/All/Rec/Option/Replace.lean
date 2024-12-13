import FOL.NV.Sub.Var.All.Rec.Sub


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.All.Rec.Option

open Formula_


def replace_pred_all_rec_opt
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then Sub.Var.All.Rec.Fresh.sub_var_all_rec (Function.updateListITE id zs xs) c H
        else pred_var_ X xs
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace_pred_all_rec_opt c τ phi)
  | imp_ phi psi =>
      imp_
      (replace_pred_all_rec_opt c τ phi)
      (replace_pred_all_rec_opt c τ psi)
  | and_ phi psi =>
      and_
      (replace_pred_all_rec_opt c τ phi)
      (replace_pred_all_rec_opt c τ psi)
  | or_ phi psi =>
      or_
      (replace_pred_all_rec_opt c τ phi)
      (replace_pred_all_rec_opt c τ psi)
  | iff_ phi psi =>
      iff_
      (replace_pred_all_rec_opt c τ phi)
      (replace_pred_all_rec_opt c τ psi)
  | forall_ x phi => forall_ x (replace_pred_all_rec_opt c τ phi)
  | exists_ x phi => exists_ x (replace_pred_all_rec_opt c τ phi)
  | def_ X xs => def_ X xs
