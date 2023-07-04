import FOL.Binders
import FOL.FunctionUpdateIte
import FOL.Tactics


namespace FOL

open Formula


/--
  The interpretation of a first order language. The assignment of a denotation to each non-logical symbol.

  D is the domain of discourse.
-/
structure Interpretation (D : Type) : Type :=
  /--
    The domain of discourse is not empty.
  -/
  (nonempty : Nonempty D)

  /--
    The assignment to each predicate symbol of a function mapping lists of elements of the domain of discourse to {T, F}.
  -/
  (pred_const_ : PredName → (List D → Prop))

  /--
    The assignment to each predicate symbol of a function mapping lists of elements of the domain of discourse to {T, F}.
  -/
  (pred_var_ : PredName → (List D → Prop))

instance (D : Type) [Inhabited D] : Inhabited (Interpretation D) :=
  Inhabited.mk {
    nonempty := by infer_instance
    pred_const_ := fun _ _ => False
    pred_var_ := fun _ _ => False
  }

/--
  The assignment of an element of the domain of discourse to each variable.
-/
def VarAssignment (D : Type) : Type := VarName → D

instance (D : Type) [Inhabited D] : Inhabited (VarAssignment D) :=
  by
  unfold VarAssignment
  exact inferInstance


/--
  The evaluation of formulas to truth values.
-/
def Holds
  (D : Type)
  (I : Interpretation D) :
  VarAssignment D → Formula → Prop
  | V, pred_const_ X xs => I.pred_const_ X (xs.map V)
  | V, pred_var_ X xs => I.pred_var_ X (xs.map V)
  | V, eq_ x y => V x = V y
  | _, true_ => True
  | _, false_ => False
  | V, not_ phi => ¬ Holds D I V phi
  | V, imp_ phi psi => Holds D I V phi → Holds D I V psi
  | V, and_ phi psi => Holds D I V phi ∧ Holds D I V psi
  | V, or_ phi psi => Holds D I V phi ∨ Holds D I V psi
  | V, iff_ phi psi => Holds D I V phi ↔ Holds D I V psi
  | V, forall_ x phi => ∀ d : D, Holds D I (Function.updateIte V x d) phi
  | V, exists_ x phi => ∃ d : D, Holds D I (Function.updateIte V x d) phi


/--
  The definition of valid formulas.

  Formula.isValid F := True if and only if F evaluates to True in every combination of domain of discourse, interpretation and variable assignment.
-/
def Formula.IsValid (F : Formula) : Prop :=
  ∀ (D : Type) (I : Interpretation D) (V : VarAssignment D), Holds D I V F


theorem Holds_coincide_Var
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (F : Formula)
  (h1 : ∀ v : VarName, isFreeIn v F → V v = V' v) :
  Holds D I V F ↔ Holds D I V' F :=
  by
  induction F generalizing V V'
  case pred_const_ X xs | pred_var_ X xs =>
    unfold isFreeIn at h1

    unfold Holds
    congr! 1
    simp only [List.map_eq_map_iff]
    exact h1
  case eq_ x y =>
    unfold isFreeIn at h1
    simp at h1

    unfold Holds
    cases h1
    case intro h1_left h1_right =>
      simp only [h1_left, h1_right]
  case true_ | false_ =>
    unfold Holds
    rfl
  case not_ phi phi_ih =>
    unfold Holds
    congr! 1
    exact phi_ih V V' h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isFreeIn at h1

    unfold Holds
    congr! 1
    · apply phi_ih V V'
      intro v a1
      apply h1
      left
      exact a1
    · apply psi_ih V V'
      intro v a1
      apply h1
      right
      exact a1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isFreeIn at h1
    simp at h1

    unfold Holds
    first | apply forall_congr' | apply exists_congr
    intro d
    apply phi_ih
    intro v a1
    simp only [Function.updateIte]
    split_ifs
    case _ c1 =>
      rfl
    case _ c1 =>
      exact h1 v c1 a1


theorem Holds_coincide_PredVar
  (D : Type)
  (I I' : Interpretation D)
  (V : VarAssignment D)
  (F : Formula)
  (h1 : I.pred_const_ = I'.pred_const_)
  (h2 : ∀ (P : PredName) (ds : List D),
    predVarOccursIn P ds.length F →
      (I.pred_var_ P ds ↔ I'.pred_var_ P ds)) :
  Holds D I V F ↔ Holds D I' V F :=
  by
  induction F generalizing V
  case pred_const_ X xs =>
    unfold Holds
    simp only [h1]
  case pred_var_ X xs =>
    unfold predVarOccursIn at h2
    simp at h2

    unfold Holds
    apply h2
    · rfl
    · simp
  case eq_ x y =>
    unfold Holds
    rfl
  case true_ | false_ =>
    unfold Holds
    rfl
  case not_ phi phi_ih =>
    unfold predVarOccursIn at h2

    unfold Holds
    congr! 1
    exact phi_ih V h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold predVarOccursIn at h2

    unfold Holds
    congr! 1
    · apply phi_ih
      intro P ds a1
      apply h2
      left
      exact a1
    · apply psi_ih
      intro P ds a1
      apply h2
      right
      exact a1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold predVarOccursIn at h2

    unfold Holds
    first | apply forall_congr' | apply exists_congr
    intro d
    exact phi_ih (Function.updateIte V x d) h2


#lint

end FOL
