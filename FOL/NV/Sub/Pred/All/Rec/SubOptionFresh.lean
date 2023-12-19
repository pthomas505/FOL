import FOL.NV.Alpha
import FOL.NV.Sub.Var.All.Rec.SubFresh
import FOL.NV.Sub.Pred.All.Rec.SubOption


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.All.Rec

open Formula


def predVarFreeVarSet
  (τ : PredName → ℕ → Option (List VarName × Formula)) :=
  fun ((X : PredName), (n : ℕ)) =>
    let opt := τ X n
    if h : Option.isSome opt
    then
      let val := Option.get opt h
      let zs := val.fst
      let H := val.snd
      H.freeVarSet \ zs.toFinset
    else ∅


def subPredAlphaAux
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (σ : VarName → VarName)
  (S T : Finset VarName) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then Sub.Var.All.Rec.subFresh (Function.updateListITE id zs (xs.map σ)) c H
        else pred_var_ X (xs.map σ)
      else pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi =>
      not_ (subPredAlphaAux c τ σ S T phi)
  | imp_ phi psi =>
      imp_
      (subPredAlphaAux c τ σ S T phi)
      (subPredAlphaAux c τ σ S T psi)
  | and_ phi psi =>
      and_
      (subPredAlphaAux c τ σ S T phi)
      (subPredAlphaAux c τ σ S T psi)
  | or_ phi psi =>
      or_
      (subPredAlphaAux c τ σ S T phi)
      (subPredAlphaAux c τ σ S T psi)
  | iff_ phi psi =>
      iff_
      (subPredAlphaAux c τ σ S T phi)
      (subPredAlphaAux c τ σ S T psi)
  | forall_ x phi =>
      let x' : VarName :=
        if x ∈ (((FOL.NV.Sub.Var.All.Rec.subFresh (Function.updateITE σ x x) c phi).freeVarSet) ∪ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))
        then fresh x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi))
        else x
      forall_ x' (subPredAlphaAux c τ (Function.updateITE σ x x') S T phi)
  | exists_ x phi =>
      let vs : Finset VarName := sorry
      let x' : VarName :=
        if x ∈ vs
        then fresh x c vs
        else x
      exists_ x' (subPredAlphaAux c τ (Function.updateITE σ x x') S T phi)
  | def_ X xs => def_ X (xs.map σ)


def Interpretation.usingPred
  (D : Type)
  (I : Interpretation D)
  (pred_ : PredName → List D → Prop) :
  Interpretation D := {
    nonempty := I.nonempty
    pred_const_ := I.pred_const_
    pred_var_ := pred_ }


example
  (D : Type)
  (I : Interpretation D)
  (V V' V'': VarAssignment D)
  (E : Env)
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (σ : VarName → VarName)
  (S T : Finset VarName)
  (F : Formula)
  (h1 : ∀ (x : VarName), isFreeIn x F → V' x = V (σ x))
  (h2 : ∀ (x : VarName), x ∈ F.predVarSet.biUnion (predVarFreeVarSet τ) → V'' x = V x)
  :
  let I' := (Interpretation.usingPred D I (
      fun (X : PredName) (ds : List D) =>
      let opt := τ X ds.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if ds.length = zs.length
        then Holds D I (Function.updateListITE V'' zs ds) E H
        else I.pred_var_ X ds
      else I.pred_var_ X ds) )
  Holds D I' V' E F ↔ Holds D I V E (subPredAlphaAux c τ σ S T F) :=
  by
  intro I'
  induction F generalizing V V' σ
  case pred_const_ X xs =>
    simp only [isFreeIn] at h1

    simp only [subPredAlphaAux]
    simp only [Holds]
    simp only [Interpretation.usingPred]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x a1
    simp
    exact h1 x a1
  case pred_var_ X xs =>
    simp only [isFreeIn] at h1

    simp only [subPredAlphaAux]
    simp only [Holds]
    simp only [Interpretation.usingPred]
    simp
    split_ifs
    case _ c1 c2 =>
      generalize (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).1 = zs at *

      generalize (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).2 = H at *

      obtain s1 := Sub.Var.All.Rec.substitution_theorem D I V E (Function.updateListITE id zs (xs.map σ)) c H
      simp only [Function.updateListITE_comp] at s1

      simp at s1
      simp only [s1]
      clear s1

      apply Holds_coincide_Var
      intro x a1
      by_cases c3 : x ∈ zs
      · apply Function.updateListITE_map_mem_ext
        · simp
          exact h1
        · simp only [c2]
        · exact c3
      · simp only [Function.updateListITE_not_mem V'' x zs (List.map V' xs) c3]
        simp only [Function.updateListITE_not_mem V x zs (List.map (V ∘ σ ) xs) c3]
        sorry
    case _ c1 c2 =>
      simp only [Holds]
      simp
      congr! 1
      simp only [List.map_eq_map_iff]
      intro x a1
      simp
      exact h1 x a1
    case _ c1 =>
      simp only [Holds]
      simp
      congr! 1
      simp only [List.map_eq_map_iff]
      intro x a1
      simp
      exact h1 x a1
  case forall_ x phi ih =>
    simp only [isFreeIn] at h1

    simp only [subPredAlphaAux]
    simp only [Interpretation.usingPred]
    simp only [Holds]

    apply forall_congr'
    intro d

    apply ih
    · intro v a1
      split_ifs
      case _ c1 =>
        simp only [Function.updateITE]
        split_ifs
        case _ c2 c3 =>
          rfl
        case _ c2 c3 =>
          contradiction
        case _ c2 c3 =>
          obtain s1 := fresh_not_mem x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi))
          simp only [← c3] at s1
          obtain s2 := Sub.Var.All.Rec.freeVarSet_subFresh_eq_freeVarSet_image (Function.updateITE σ x x) c phi
          simp only [s2] at c1

          simp only [isFreeIn_iff_mem_freeVarSet] at a1
          exfalso
          apply s1
          obtain s5 := Finset.mem_image_of_mem (Function.updateITE σ x x) a1
          simp only [Function.updateITE] at s5
          simp only [if_neg c2] at s5
          exact s5
        case _ c2 c3 =>
          apply h1
          tauto
      case _ c1 =>
        simp only [Function.updateITE]
        by_cases c2 : v = x
        · simp only [if_pos c2]
          simp
        · simp only [if_neg c2]
          split_ifs
          case _ c3 =>
            obtain s1 := Sub.Var.All.Rec.freeVarSet_subFresh_eq_freeVarSet_image (Function.updateITE σ x x) c phi
            simp only [s1] at c1
            exfalso
            apply c1
            simp only [← c3]
            simp only [isFreeIn_iff_mem_freeVarSet] at a1
            obtain s5 := Finset.mem_image_of_mem (Function.updateITE σ (σ v) (σ v)) a1
            simp only [Function.updateITE] at s5
            simp only [Finset.mem_union]
            left

            split_ifs at s5
            · exact s5
            · exact s5
          case _ c3 =>
            apply h1
            tauto
    · intro v a1
      simp only [predVarSet] at h2
      specialize h2 v a1
      split_ifs
      case _ c1 =>
        simp only [Function.updateITE]
        split_ifs
        case _ c2 =>
          simp only [Finset.mem_union] at c1
          obtain s1 := Sub.Var.All.Rec.freeVarSet_subFresh_eq_freeVarSet_image (Function.updateITE σ x x) c phi
          --simp only [s1] at c1
          simp only [<- s1] at c2
          obtain s30 := fresh_not_mem x c (freeVarSet (Var.All.Rec.subFresh (Function.updateITE σ x x) c phi))
          simp only [← c2] at s30
          cases c1
          case _ c1 =>
            have s50 : ¬ v = x
            intro contra
            subst contra
            apply s30
            exact c1

            sorry
          case _ c1 =>

            sorry
        case _ c2 =>
          exact h2
      case _ c1 =>
        simp only [Finset.mem_union] at c1
        push_neg at c1
        cases c1
        case _ c1_left c1_right =>
          have s20 : ¬ v = x
          intro contra
          apply c1_right
          subst contra
          exact a1
          simp only [Function.updateITE]
          simp only [if_neg s20]
          exact h2


  all_goals
    sorry
