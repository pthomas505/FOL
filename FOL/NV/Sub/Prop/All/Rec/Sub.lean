import FOL.NV.Semantics


set_option autoImplicit false


namespace FOL.NV.Sub.Prop.All.Rec

open Formula_


-- proposition substitution

/--
  The recursive simultaneous uniform substitution of all of the propositional variables in a formula.
-/
def sub_prop_all_rec (τ : PredName_ → PredName_) : Formula_ → Formula_
  | pred_const_ P ts => pred_const_ P ts
  | pred_var_ P ts =>
      if ts = List.nil
      then pred_var_ (τ P) List.nil
      else pred_var_ P ts
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (sub_prop_all_rec τ phi)
  | imp_ phi psi => imp_ (sub_prop_all_rec τ phi) (sub_prop_all_rec τ psi)
  | and_ phi psi => and_ (sub_prop_all_rec τ phi) (sub_prop_all_rec τ psi)
  | or_ phi psi => or_ (sub_prop_all_rec τ phi) (sub_prop_all_rec τ psi)
  | iff_ phi psi => iff_ (sub_prop_all_rec τ phi) (sub_prop_all_rec τ psi)
  | forall_ x phi => forall_ x (sub_prop_all_rec τ phi)
  | exists_ x phi => exists_ x (sub_prop_all_rec τ phi)
  | def_ P ts => def_ P ts

instance {α : Type} {xs : List α} : Decidable (xs = []) :=
  by
  cases xs
  case nil =>
    simp
    exact instDecidableTrue
  case cons hd tl =>
    simp
    exact instDecidableFalse


lemma sub_prop_all_rec_pred_var_set_is_empty
  (F : Formula_)
  (τ : PredName_ → PredName_)
  (h1 : F.pred_var_set = ∅) :
  sub_prop_all_rec τ F = F :=
  by
  induction F
  case pred_const_ X xs =>
    simp only [sub_prop_all_rec]
  case pred_var_ X xs =>
    simp only [pred_var_set] at h1

    simp at h1
  case eq_ x y =>
    simp only [sub_prop_all_rec]
  case true_ | false_ =>
    simp only [sub_prop_all_rec]
  case not_ phi phi_ih =>
    simp only [pred_var_set] at h1

    simp only [sub_prop_all_rec]
    congr!
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [pred_var_set] at h1
    simp only [Finset.union_eq_empty] at h1

    cases h1
    case intro h1_left h1_right =>
      simp only [sub_prop_all_rec]
      congr!
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [pred_var_set] at h1

    simp only [sub_prop_all_rec]
    congr!
    exact phi_ih h1
  case def_ X xs =>
    simp only [sub_prop_all_rec]


theorem substitution_theorem_sub_prop_all_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (τ : PredName_ → PredName_)
  (F : Formula_) :
  holds D I V E (sub_prop_all_rec τ F) ↔
    holds D
      ⟨
        I.nonempty,
        I.pred_const_,
        fun (P : PredName_) (ds : List D) =>
          if ds = List.nil
          then holds D I V E (pred_var_ (τ P) List.nil)
          else I.pred_var_ P ds
      ⟩
      V E F :=
  by
  induction E generalizing F V
  all_goals
    induction F generalizing V
    case pred_const_ X xs =>
      simp only [sub_prop_all_rec]
      simp only [holds]
    case pred_var_ X xs =>
        simp only [sub_prop_all_rec]
        split_ifs
        case pos c1 =>
          simp only [holds]
          simp
          simp only [if_pos c1]
        case neg c1 =>
          simp only [holds]
          simp
          simp only [if_neg c1]
    case eq_ x y =>
      simp only [sub_prop_all_rec]
      simp only [holds]
    case true_ | false_ =>
      simp only [sub_prop_all_rec]
      simp only [holds]
    case not_ phi phi_ih =>
      simp only [holds] at phi_ih

      simp only [sub_prop_all_rec]
      simp only [holds]
      congr! 1
      apply phi_ih
    case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
      simp only [holds] at phi_ih
      simp only [holds] at psi_ih

      simp only [sub_prop_all_rec]
      simp only [holds]
      congr! 1
      · apply phi_ih
      · apply psi_ih
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      simp only [holds] at phi_ih

      simp only [sub_prop_all_rec]
      simp only [holds]
      first | apply forall_congr' | apply exists_congr
      intros d
      apply phi_ih

  case nil.def_ X xs =>
    simp only [sub_prop_all_rec]
    simp only [holds]
  case cons.def_ hd tl ih X xs =>
    simp only [holds] at ih
    simp at ih

    simp only [sub_prop_all_rec]
    simp only [holds]
    split_ifs
    case _ c1 =>
      specialize ih (Function.updateListITE V hd.args (List.map V xs)) hd.q
      simp only [sub_prop_all_rec_pred_var_set_is_empty hd.q τ hd.h2] at ih
      apply ih
    case _ c1 =>
      specialize ih V (def_ X xs)
      simp only [sub_prop_all_rec] at ih
      exact ih


theorem substitution_is_valid_sub_prop_all_rec
  (F : Formula_)
  (τ : PredName_ → PredName_)
  (h1 : F.is_valid) :
  (sub_prop_all_rec τ F).is_valid :=
  by
  simp only [is_valid] at h1

  simp only [is_valid]
  intro D I V E
  simp only [substitution_theorem_sub_prop_all_rec D I V E τ F]
  apply h1


#lint
