import FOL.NV.Sub.Var.All.Rec.Admits


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.All.Rec

open Formula


-- multiple

/--
  The recursive simultaneous uniform substitution of all of the predicate variables in a formula.
-/
def replacePredFun (τ : PredName → ℕ → (List VarName × Formula)) : Formula → Formula
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      let zs := (τ X xs.length).fst
      let H := (τ X xs.length).snd
      if xs.length = zs.length
      then Sub.Var.All.Rec.fastReplaceFree (Function.updateListITE id zs xs) H
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replacePredFun τ phi)
  | imp_ phi psi =>
      imp_
      (replacePredFun τ phi)
      (replacePredFun τ psi)
  | and_ phi psi =>
      and_
      (replacePredFun τ phi)
      (replacePredFun τ psi)
  | or_ phi psi =>
      or_
      (replacePredFun τ phi)
      (replacePredFun τ psi)
  | iff_ phi psi =>
      iff_
      (replacePredFun τ phi)
      (replacePredFun τ psi)
  | forall_ x phi => forall_ x (replacePredFun τ phi)
  | exists_ x phi => exists_ x (replacePredFun τ phi)
  | def_ X xs => def_ X xs


def admitsPredFunAux
  (τ : PredName → ℕ → List VarName × Formula)
  (binders : Finset VarName) : Formula → Prop
  | pred_const_ _ _ => True
  | pred_var_ X xs =>
    let zs := (τ X xs.length).fst
    let H := (τ X xs.length).snd
    Sub.Var.All.Rec.admits (Function.updateListITE id zs xs) H ∧ (∀ x : VarName, x ∈ binders → ¬ (isFreeIn x H ∧ x ∉ zs)) ∧ xs.length = zs.length
  | true_ => True
  | false_ => True
  | eq_ _ _ => True
  | not_ phi => admitsPredFunAux τ binders phi
  | imp_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | and_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | or_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | iff_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | forall_ x phi => admitsPredFunAux τ (binders ∪ {x}) phi
  | exists_ x phi => admitsPredFunAux τ (binders ∪ {x}) phi
  | def_ _ _ => True

instance
  (τ : PredName → ℕ → List VarName × Formula)
  (binders : Finset VarName)
  (F : Formula) :
  Decidable (admitsPredFunAux τ binders F) :=
  by
  induction F generalizing binders
  all_goals
    unfold admitsPredFunAux
    infer_instance


def admitsPredFun (τ : PredName → ℕ → List VarName × Formula) (F : Formula) : Prop :=
  admitsPredFunAux τ ∅ F


instance
  (τ : PredName → ℕ → List VarName × Formula)
  (F : Formula) :
  Decidable (admitsPredFun τ F) :=
  by
  unfold admitsPredFun
  infer_instance


theorem predSub_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (τ : PredName → ℕ → List VarName × Formula)
  (binders : Finset VarName)
  (F : Formula)
  (h1 : admitsPredFunAux τ binders F)
  (h2 : ∀ x : VarName, x ∉ binders → V x = V' x) :
  Holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName) (ds : List D) =>
        if ds.length = (τ X ds.length).fst.length
        then Holds D I (Function.updateListITE V' (τ X ds.length).fst ds) E (τ X ds.length).snd
        else I.pred_var_ X ds
      ⟩
      V E F ↔ Holds D I V E (replacePredFun τ F) :=
  by
  induction F generalizing binders V
  case pred_const_ X xs =>
    unfold replacePredFun
    simp only [Holds]
  case pred_var_ X xs =>
    unfold admitsPredFunAux at h1
    simp at h1

    cases h1
    case intro h1_left h1_right =>
      cases h1_right
      case intro h1_right_left h1_right_right =>
        obtain s1 :=
        Sub.Var.All.Rec.substitution_theorem D I V E (Function.updateListITE id (τ X xs.length).fst xs)
          (τ X xs.length).snd h1_left
        simp only [Function.updateListITE_comp] at s1
        simp at s1

        have s2 :
          Holds D I (Function.updateListITE V (τ X xs.length).fst (List.map V xs)) E
            (τ X xs.length).snd ↔
          Holds D I (Function.updateListITE V' (τ X xs.length).fst (List.map V xs)) E
            (τ X xs.length).snd :=
        by
          apply Holds_coincide_Var
          intro v a1
          by_cases c1 : v ∈ (τ X xs.length).fst
          · apply Function.updateListITE_mem_eq_len V V' v (τ X xs.length).fst (List.map V xs) c1
            simp
            symm
            exact h1_right_right
          · by_cases c2 : v ∈ binders
            · specialize h1_right_left v c2 a1
              contradiction
            · specialize h2 v c2
              apply Function.updateListITE_mem'
              exact h2
        simp only [s2] at s1
        clear s2

        simp only [Holds]
        unfold replacePredFun
        simp
        simp only [if_pos h1_right_right]
        exact s1
  case eq_ x y =>
    unfold replacePredFun
    simp only [Holds]
  case true_ | false_ =>
    unfold replacePredFun
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold admitsPredFunAux at h1

    unfold replacePredFun
    simp only [Holds]
    congr! 1
    exact phi_ih V binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsPredFunAux at h1

    unfold replacePredFun
    simp only [Holds]

    cases h1
    case intro h1_left h1_right =>
      congr! 1
      · exact phi_ih V binders h1_left h2
      · exact psi_ih V binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsPredFunAux at h1

    unfold replacePredFun
    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
    intro v a1
    unfold Function.updateITE
    simp at a1
    push_neg at a1
    cases a1
    case h.intro a1_left a1_right =>
      simp only [if_neg a1_right]
      exact h2 v a1_left
  case def_ X xs =>
    cases E
    case nil =>
      unfold replacePredFun
      simp only [Holds]
    case cons hd tl =>
      unfold replacePredFun
      simp only [Holds]
      split_ifs
      case _ c1 =>
        apply Holds_coincide_PredVar
        · simp
        · simp only [predVarOccursIn_iff_mem_predVarSet]
          simp only [hd.h2]
          simp
      case _ c1 =>
        apply Holds_coincide_PredVar
        · simp
        · unfold predVarOccursIn
          simp


theorem predSub
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (τ : PredName → ℕ → List VarName × Formula)
  (F : Formula)
  (h1 : admitsPredFun τ F) :
  Holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName) (ds : List D) =>
        let zs := (τ X ds.length).fst
        let H := (τ X ds.length).snd
        if ds.length = zs.length
        then Holds D I (Function.updateListITE V zs ds) E H
        else I.pred_var_ X ds
      ⟩
      V E F ↔ Holds D I V E (replacePredFun τ F) :=
  by
  apply predSub_aux D I V V E τ ∅ F
  · unfold admitsPredFun at h1
    exact h1
  · intro X _
    rfl


theorem predSub_valid
  (phi : Formula)
  (τ : PredName → ℕ → List VarName × Formula)
  (h1 : admitsPredFun τ phi)
  (h2 : phi.IsValid) :
  (replacePredFun τ phi).IsValid :=
  by
  unfold IsValid at h2

  unfold IsValid
  intro D I V E
  obtain s1 := predSub D I V E τ phi h1
  simp only [← s1]
  apply h2


--#lint
