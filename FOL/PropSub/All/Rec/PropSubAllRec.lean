import FOL.Semantics


namespace FOL

open Formula


-- proposition substitution

/--
  The recursive simultaneous uniform substitution of all of the propositional variables in a formula.
-/
def replacePropFun (τ : PredName → PredName) : Formula → Formula
  | pred_const_ P ts => pred_const_ P ts
  | pred_var_ P ts =>
      if ts = List.nil
      then pred_var_ (τ P) List.nil
      else pred_var_ P ts
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replacePropFun τ phi)
  | imp_ phi psi => imp_ (replacePropFun τ phi) (replacePropFun τ psi)
  | and_ phi psi => and_ (replacePropFun τ phi) (replacePropFun τ psi)
  | or_ phi psi => or_ (replacePropFun τ phi) (replacePropFun τ psi)
  | iff_ phi psi => iff_ (replacePropFun τ phi) (replacePropFun τ psi)
  | forall_ x phi => forall_ x (replacePropFun τ phi)
  | exists_ x phi => exists_ x (replacePropFun τ phi)


instance {xs : List α} : Decidable (xs = []) :=
  by
  cases xs
  case nil =>
    simp
    exact instDecidableTrue
  case cons hd tl =>
    simp
    exact instDecidableFalse


theorem prop_sub_aux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (τ : PredName → PredName)
  (F : Formula) :
  Holds D I V (replacePropFun τ F) ↔
    Holds D
      ⟨
        I.nonempty,
        I.pred_const_,
        fun (P : PredName) (ds : List D) =>
          if ds = List.nil
          then Holds D I V (pred_var_ (τ P) List.nil)
          else I.pred_var_ P ds
      ⟩
      V F :=
  by
  induction F generalizing V
  case pred_const_ X xs =>
    unfold replacePropFun
    unfold Holds
    simp
  case pred_var_ X xs =>
      unfold replacePropFun
      split_ifs
      case inl c1 =>
        simp only [Holds]
        unfold Interpretation.pred_var_
        simp
        simp only [if_pos c1]
      case inr c1 =>
        simp only [Holds]
        unfold Interpretation.pred_var_
        simp
        simp only [if_neg c1]
  case eq_ x y =>
    unfold replacePropFun
    unfold Holds
    rfl
  case true_ | false_ =>
    unfold replacePropFun
    unfold Holds
    rfl
  case not_ phi phi_ih =>
    unfold replacePropFun
    unfold Holds
    congr! 1
    apply phi_ih
  case
    imp_ phi psi phi_ih psi_ih
  | and_ phi psi phi_ih psi_ih
  | or_ phi psi phi_ih psi_ih
  | iff_ phi psi phi_ih psi_ih =>
    unfold replacePropFun
    unfold Holds
    congr! 1
    · apply phi_ih
    · apply psi_ih
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold replacePropFun
    unfold Holds
    first | apply forall_congr' | apply exists_congr
    intros d
    apply phi_ih


theorem prop_sub_isValid
  (phi : Formula)
  (h1 : phi.IsValid)
  (τ : PredName → PredName) :
  (replacePropFun τ phi).IsValid :=
  by
  unfold IsValid at h1

  unfold IsValid
  intro D I V
  simp only [prop_sub_aux D I V τ phi]
  apply h1


#lint

end FOL
