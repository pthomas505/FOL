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
  (σ : VarName → VarName) :
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
      not_ (subPredAlphaAux c τ σ phi)
  | imp_ phi psi =>
      imp_
      (subPredAlphaAux c τ σ phi)
      (subPredAlphaAux c τ σ psi)
  | and_ phi psi =>
      and_
      (subPredAlphaAux c τ σ phi)
      (subPredAlphaAux c τ σ psi)
  | or_ phi psi =>
      or_
      (subPredAlphaAux c τ σ phi)
      (subPredAlphaAux c τ σ psi)
  | iff_ phi psi =>
      iff_
      (subPredAlphaAux c τ σ phi)
      (subPredAlphaAux c τ σ psi)
  | forall_ x phi =>
      let x' : VarName :=
        if x ∈ ((FOL.NV.Sub.Var.All.Rec.subFresh (Function.updateITE σ x x) c phi).freeVarSet ∪ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))
        then fresh x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi) ∪ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))
        else x
      forall_ x' (subPredAlphaAux c τ (Function.updateITE σ x x') phi)
  | exists_ x phi =>
      let x' : VarName :=
        if x ∈ ((FOL.NV.Sub.Var.All.Rec.subFresh (Function.updateITE σ x x) c phi).freeVarSet ∪ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))
        then fresh x c (Finset.image (Function.updateITE σ x x) (freeVarSet phi) ∪ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))
        else x
      exists_ x' (subPredAlphaAux c τ (Function.updateITE σ x x') phi)
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
  (F : Formula)
  (h1 : ∀ (x : VarName), isFreeIn x F → V' x = V (σ x))
  (h2 : ∀ (x : VarName), x ∈ F.predVarSet.biUnion (predVarFreeVarSet τ) → V'' x = V x) :
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
  Holds D I' V' E F ↔ Holds D I V E (subPredAlphaAux c τ σ F) :=
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

    simp only [predVarSet] at h2
    simp at h2
    simp only [predVarFreeVarSet] at h2

    simp only [subPredAlphaAux]
    simp only [Holds]
    simp only [Interpretation.usingPred]
    simp
    split_ifs
    case _ c1 c2 =>
      simp only [c1] at h2
      simp at h2

      set zs := (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).1

      set H := (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).2

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
        · simp at c2
          simp only [← c2]
        · exact c3
      · simp only [Function.updateListITE_not_mem V'' x zs (List.map V' xs) c3]
        simp only [Function.updateListITE_not_mem V x zs (List.map (V ∘ σ ) xs) c3]
        apply h2
        · simp only [isFreeIn_iff_mem_freeVarSet] at a1
          exact a1
        · exact c3
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
  case forall_ x phi ih | exists_ x phi ih =>
    simp only [isFreeIn] at h1

    simp only [predVarSet] at h2

    simp only [subPredAlphaAux]
    simp only [Interpretation.usingPred]
    simp only [Holds]

    first | apply forall_congr' | apply exists_congr
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
          obtain s1 := fresh_not_mem x c ((Finset.image (Function.updateITE σ x x) (freeVarSet phi)) ∪ (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)))
          simp only [← c3] at s1

          exfalso
          apply s1

          simp only [isFreeIn_iff_mem_freeVarSet] at a1

          obtain s2 := Finset.mem_image_of_mem (Function.updateITE σ x x) a1
          simp only [Function.updateITE] at s2
          simp only [if_neg c2] at s2

          simp only [Finset.mem_union]
          left
          exact s2
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

            obtain s2 := Finset.mem_image_of_mem (Function.updateITE σ (σ v) (σ v)) a1
            simp only [Function.updateITE] at s2
            simp only [ite_self] at s2

            simp only [Finset.mem_union]
            left
            exact s2
          case _ c3 =>
            apply h1
            tauto
    · intro v a1
      split_ifs
      case _ c1 =>
        simp only [Finset.mem_union] at c1

        simp only [Function.updateITE]
        split_ifs
        case _ c2 =>
          obtain s1 := Sub.Var.All.Rec.freeVarSet_subFresh_eq_freeVarSet_image (Function.updateITE σ x x) c phi
          simp only [← s1] at c2

          obtain s30 := fresh_not_mem x c ((freeVarSet (Var.All.Rec.subFresh (Function.updateITE σ x x) c phi)) ∪ (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)))
          simp only [← c2] at s30
          cases c1
          case _ c1 =>
            have s50 : ¬ v = x
            intro contra
            subst contra
            apply s30
            simp only [Finset.mem_union]
            left
            exact c1
            simp only [Finset.mem_union] at s30
            push_neg at s30
            cases s30
            case _ s30_left s30_right =>
              contradiction
          case _ c1 =>
            simp only [Finset.mem_union] at s30
            push_neg at s30
            cases s30
            case _ s30_left s30_right =>
              contradiction
        case _ c2 =>
          exact h2 v a1
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
          exact h2 v a1



  all_goals
    sorry
