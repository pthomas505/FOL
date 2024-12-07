import FOL.NV.Sub.Var.All.Rec.Sub


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.All.Rec.Option

open Formula_


def replace
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
        then Sub.Var.All.Rec.Fresh.sub (Function.updateListITE id zs xs) c H
        else pred_var_ X xs
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replace c τ phi)
  | imp_ phi psi =>
      imp_
      (replace c τ phi)
      (replace c τ psi)
  | and_ phi psi =>
      and_
      (replace c τ phi)
      (replace c τ psi)
  | or_ phi psi =>
      or_
      (replace c τ phi)
      (replace c τ psi)
  | iff_ phi psi =>
      iff_
      (replace c τ phi)
      (replace c τ psi)
  | forall_ x phi => forall_ x (replace c τ phi)
  | exists_ x phi => exists_ x (replace c τ phi)
  | def_ X xs => def_ X xs


def admitsAux
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (binders : Finset VarName_) : Formula_ → Prop
  | pred_const_ _ _ => True
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then binders ∩ (H.free_var_set \ zs.toFinset) = ∅
        --then ∀ x : VarName_, x ∈ binders → ¬ (var_is_free_in x H ∧ x ∉ zs)
        else True
      else True
  | true_ => True
  | false_ => True
  | eq_ _ _ => True
  | not_ phi => admitsAux τ binders phi
  | imp_ phi psi =>
      admitsAux τ binders phi ∧
      admitsAux τ binders psi
  | and_ phi psi =>
      admitsAux τ binders phi ∧
      admitsAux τ binders psi
  | or_ phi psi =>
      admitsAux τ binders phi ∧
      admitsAux τ binders psi
  | iff_ phi psi =>
      admitsAux τ binders phi ∧
      admitsAux τ binders psi
  | forall_ x phi => admitsAux τ (binders ∪ {x}) phi
  | exists_ x phi => admitsAux τ (binders ∪ {x}) phi
  | def_ _ _ => True


theorem substitution_theorem_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (binders : Finset VarName_)
  (F : Formula_)
  (h1 : admitsAux τ binders F)
  (h2 : ∀ x : VarName_, x ∉ binders → V' x = V x) :
  holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName_) (ds : List D) =>
      let opt := τ X ds.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if ds.length = zs.length
        then holds D I (Function.updateListITE V' zs ds) E H
        else I.pred_var_ X ds
      else I.pred_var_ X ds
    ⟩
    V E F ↔ holds D I V E (replace c τ F) :=
  by
  induction F generalizing binders V
  case pred_const_ X xs =>
    simp only [replace]
    simp only [holds]
  case pred_var_ X xs =>
    simp only [admitsAux] at h1
    simp at h1

    simp only [replace]
    simp only [holds]
    simp
    split_ifs
    case _ c1 c2 =>
      let opt := τ X xs.length
      let val := Option.get opt c1
      let zs := val.fst
      let H := val.snd
      obtain s1 := Sub.Var.All.Rec.Fresh.substitution_theorem D I V E (Function.updateListITE id zs xs) c H
      simp only [Function.updateListITE_comp] at s1
      simp at s1
      simp only [s1]

      apply holds_coincide_var
      intro v a1
      by_cases c3 : v ∈ zs
      · apply Function.updateListITE_mem_eq_len V' V v zs (List.map V xs) c3
        simp
        simp only [← c2]
      · simp only [Function.updateListITE_not_mem V v zs (List.map V xs) c3]
        simp only [Function.updateListITE_not_mem V' v zs (List.map V xs) c3]
        apply h2
        intro contra
        simp only [var_is_free_in_iff_mem_free_var_set] at a1
        simp only [Finset.eq_empty_iff_forall_not_mem] at h1
        simp only [c1] at h1
        simp only [← c2] at h1
        simp at h1
        specialize h1 v contra a1
        contradiction
    case _ c1 c2 =>
      simp only [holds]
    case _ c1 =>
      simp only [holds]

  case eq_ x y =>
    simp only [replace]
    simp only [holds]
  case true_ | false_ =>
    simp only [replace]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [admitsAux] at h1

    simp only [replace]
    simp only [holds]
    congr! 1
    exact phi_ih V binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [admitsAux] at h1

    simp only [replace]
    simp only [holds]

    cases h1
    case intro h1_left h1_right =>
      congr! 1
      · exact phi_ih V binders h1_left h2
      · exact psi_ih V binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [admitsAux] at h1

    simp only [replace]
    simp only [holds]
    first | apply forall_congr' | apply exists_congr
    intro d
    apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
    intro v a1
    simp only [Function.updateITE]
    simp at a1
    push_neg at a1
    cases a1
    case h.intro a1_left a1_right =>
      simp only [if_neg a1_right]
      exact h2 v a1_left
  case def_ X xs =>
    cases E
    case nil =>
      simp only [replace]
      simp only [holds]
    case cons hd tl =>
      simp only [replace]
      simp only [holds]
      split_ifs
      case _ c1 =>
        apply holds_coincide_pred_var
        · simp
        · simp only [pred_var_occurs_in_iff_mem_pred_var_set]
          simp only [hd.h2]
          simp
      case _ c1 =>
        apply holds_coincide_pred_var
        · simp
        · simp only [pred_var_occurs_in]
          simp
