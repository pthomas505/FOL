import FOL.Semantics


namespace FOL

namespace NV

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
  | def_ P ts => def_ P ts


instance {xs : List α} : Decidable (xs = []) :=
  by
  cases xs
  case nil =>
    simp
    exact instDecidableTrue
  case cons hd tl =>
    simp
    exact instDecidableFalse


lemma replacePropFun_no_predVar
  (F : Formula)
  (τ : PredName → PredName)
  (h1 : F.predVarSet = ∅) :
  replacePropFun τ F = F :=
  by
  induction F
  case pred_const_ X xs =>
    unfold replacePropFun
    rfl
  case pred_var_ X xs =>
    unfold predVarSet at h1

    simp at h1
  case eq_ x y =>
    unfold replacePropFun
    rfl
  case true_ | false_ =>
    unfold replacePropFun
    rfl
  case not_ phi phi_ih =>
    unfold predVarSet at h1

    unfold replacePropFun
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold predVarSet at h1
    simp only [Finset.union_eq_empty_iff] at h1

    cases h1
    case intro h1_left h1_right =>
      unfold replacePropFun
      congr!
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold predVarSet at h1

    unfold replacePropFun
    congr!
    exact phi_ih h1
  case def_ X xs =>
    unfold replacePropFun
    rfl


theorem prop_sub_aux
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (τ : PredName → PredName)
  (F : Formula) :
  Holds D I V E (replacePropFun τ F) ↔
    Holds D
      ⟨
        I.nonempty,
        I.pred_const_,
        fun (P : PredName) (ds : List D) =>
          if ds = List.nil
          then Holds D I V E (pred_var_ (τ P) List.nil)
          else I.pred_var_ P ds
      ⟩
      V E F :=
  by
  induction E generalizing F V
  all_goals
    induction F generalizing V
    case pred_const_ X xs =>
      unfold replacePropFun
      simp only [Holds]
    case pred_var_ X xs =>
        unfold replacePropFun
        split_ifs
        case pos c1 =>
          simp only [Holds]
          unfold Interpretation.pred_var_
          simp
          simp only [if_pos c1]
        case neg c1 =>
          simp only [Holds]
          unfold Interpretation.pred_var_
          simp
          simp only [if_neg c1]
    case eq_ x y =>
      unfold replacePropFun
      simp only [Holds]
    case true_ | false_ =>
      unfold replacePropFun
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold replacePropFun
      simp only [Holds] at phi_ih

      simp only [Holds]
      congr! 1
      apply phi_ih
    case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
      simp only [Holds] at phi_ih
      simp only [Holds] at psi_ih

      unfold replacePropFun
      simp only [Holds]
      congr! 1
      · apply phi_ih
      · apply psi_ih
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [Holds] at phi_ih

      unfold replacePropFun
      simp only [Holds]
      first | apply forall_congr' | apply exists_congr
      intros d
      apply phi_ih

  case nil.def_ X xs =>
    unfold replacePropFun
    simp only [Holds]
  case cons.def_ hd tl ih X xs =>
    simp only [Holds] at ih
    simp at ih

    unfold replacePropFun
    simp only [Holds]
    split_ifs
    case _ c1 =>
      specialize ih (Function.updateListIte V hd.args (List.map V xs)) hd.q
      simp only [replacePropFun_no_predVar hd.q τ hd.h2] at ih
      apply ih
    case _ c1 =>
      specialize ih V (def_ X xs)
      unfold replacePropFun at ih
      exact ih


theorem prop_sub_isValid
  (phi : Formula)
  (h1 : phi.IsValid)
  (τ : PredName → PredName) :
  (replacePropFun τ phi).IsValid :=
  by
  unfold IsValid at h1

  unfold IsValid
  intro D I V E
  simp only [prop_sub_aux D I V E τ phi]
  apply h1


#lint
