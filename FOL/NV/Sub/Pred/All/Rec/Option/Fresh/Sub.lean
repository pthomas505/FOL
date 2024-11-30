import FOL.NV.Sub.Var.All.Rec.Fresh.Sub


set_option autoImplicit false


namespace FOL.NV.Sub.Pred.All.Rec.Option.Fresh

open Formula_


def predVarFreeVarSet
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :=
  fun ((X : PredName_), (n : ℕ)) =>
    let opt := τ X n
    if h : Option.isSome opt
    then
      let val := Option.get opt h
      let zs := val.fst
      let H := val.snd
      H.free_var_set \ zs.toFinset
    else ∅


def subAux
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (σ : VarName_ → VarName_) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then Sub.Var.All.Rec.Fresh.sub (Function.updateListITE id zs (xs.map σ)) c H
        else pred_var_ X (xs.map σ)
      else pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi =>
      not_ (subAux c τ σ phi)
  | imp_ phi psi =>
      imp_
      (subAux c τ σ phi)
      (subAux c τ σ psi)
  | and_ phi psi =>
      and_
      (subAux c τ σ phi)
      (subAux c τ σ psi)
  | or_ phi psi =>
      or_
      (subAux c τ σ phi)
      (subAux c τ σ psi)
  | iff_ phi psi =>
      iff_
      (subAux c τ σ phi)
      (subAux c τ σ psi)
  | forall_ x phi =>
      let S : Finset VarName_ := (Finset.image (Function.updateITE σ x x) (free_var_set phi) ∪ Finset.biUnion (pred_var_set phi) (predVarFreeVarSet τ))

      let x' : VarName_ :=
        if x ∈ S
        then fresh x c S
        else x

      forall_ x' (subAux c τ (Function.updateITE σ x x') phi)
  | exists_ x phi =>
      let S : Finset VarName_ := (Finset.image (Function.updateITE σ x x) (free_var_set phi) ∪ Finset.biUnion (pred_var_set phi) (predVarFreeVarSet τ))

      let x' : VarName_ :=
        if x ∈ S
        then fresh x c S
        else x

      exists_ x' (subAux c τ (Function.updateITE σ x x') phi)
  | def_ X xs => def_ X (xs.map σ)


def sub
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (F : Formula_) :
  Formula_ :=
  subAux c τ id F


def Interpretation_.usingPred
  (D : Type)
  (I : Interpretation_ D)
  (pred_ : PredName_ → List D → Prop) :
  Interpretation_ D := {
    nonempty := I.nonempty
    pred_const_ := I.pred_const_
    pred_var_ := pred_ }


def I'
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :
  Interpretation_ D :=
  (Interpretation_.usingPred D I (
  fun (X : PredName_) (ds : List D) =>
  let opt := τ X ds.length
  if h : Option.isSome opt
  then
    let val := Option.get opt h
    let zs := val.fst
    let H := val.snd
    if ds.length = zs.length
    then holds D I (Function.updateListITE V zs ds) E H
    else I.pred_var_ X ds
  else I.pred_var_ X ds) )


lemma substitution_theorem_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' V'': Valuation_ D)
  (E : Env_)
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (σ : VarName_ → VarName_)
  (F : Formula_)
  (h1 : ∀ (x : VarName_), var_is_free_in x F → V' x = V (σ x))
  (h2 : ∀ (x : VarName_), x ∈ F.pred_var_set.biUnion (predVarFreeVarSet τ) → V'' x = V x) :
  holds D (I' D I V'' E τ) V' E F ↔ holds D I V E (subAux c τ σ F) :=
  by
  induction F generalizing V V' σ
  case pred_const_ X xs =>
    simp only [var_is_free_in] at h1

    simp only [subAux]
    simp only [holds]
    simp only [I']
    simp only [Interpretation_.usingPred]
    simp
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x a1
    simp
    exact h1 x a1
  case pred_var_ X xs =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2
    simp at h2
    simp only [predVarFreeVarSet] at h2

    simp only [subAux]
    simp only [holds]
    simp only [I']
    simp only [Interpretation_.usingPred]
    simp
    split_ifs
    case _ c1 c2 =>
      simp only [c1] at h2
      simp at h2

      set zs := (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).1

      set H := (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).2

      obtain s1 := Sub.Var.All.Rec.Fresh.substitution_theorem D I V E (Function.updateListITE id zs (xs.map σ)) c H
      simp only [Function.updateListITE_comp] at s1

      simp at s1
      simp only [s1]
      clear s1

      apply holds_coincide_var
      intro x a1
      by_cases c3 : x ∈ zs
      · apply Function.updateListITE_map_mem_ext
        · simp
          exact h1
        · simp only [← c2]
        · exact c3
      · simp only [Function.updateListITE_not_mem V'' x zs (List.map V' xs) c3]
        simp only [Function.updateListITE_not_mem V x zs (List.map (V ∘ σ ) xs) c3]
        apply h2
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          exact a1
        · exact c3
    case _ c1 c2 =>
      simp only [holds]
      simp
      congr! 1
      simp only [List.map_eq_map_iff]
      intro x a1
      simp
      exact h1 x a1
    case _ c1 =>
      simp only [holds]
      simp
      congr! 1
      simp only [List.map_eq_map_iff]
      intro x a1
      simp
      exact h1 x a1
  case eq_ x y =>
    simp only [var_is_free_in] at h1

    simp only [subAux]
    simp only [holds]

    have s1 : V' x = V (σ x)
    apply h1
    simp
    simp only [s1]

    have s2 : V' y = V (σ y)
    apply h1
    simp
    simp only [s2]
  case true_ | false_ =>
    simp only [subAux]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2

    simp only [subAux]
    simp only [holds]
    congr! 1
    exact phi_ih V V' σ h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2

    simp only [subAux]
    simp only [holds]
    congr! 1
    · apply phi_ih V V' σ
      · intro x a1
        apply h1
        left
        exact a1
      · intro x a1
        apply h2
        simp only [Finset.mem_biUnion, Finset.mem_union] at a1
        apply Exists.elim a1
        intro a a2

        simp only [Finset.mem_biUnion, Finset.mem_union]
        apply Exists.intro a
        tauto
    · apply psi_ih V V' σ
      · intro x a1
        apply h1
        right
        exact a1
      · intro x a1
        apply h2
        simp only [Finset.mem_biUnion, Finset.mem_union] at a1
        apply Exists.elim a1
        intro a a2

        simp only [Finset.mem_biUnion, Finset.mem_union]
        apply Exists.intro a
        tauto
  case forall_ x phi ih | exists_ x phi ih =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2

    simp only [subAux]
    simp only [I']
    simp only [Interpretation_.usingPred]
    simp only [holds]

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
          obtain s1 := fresh_not_mem x c ((Finset.image (Function.updateITE σ x x) (free_var_set phi)) ∪ (Finset.biUnion (pred_var_set phi) (predVarFreeVarSet τ)))
          simp only [← c3] at s1
          simp only [Finset.mem_union] at s1

          simp only [var_is_free_in_iff_mem_free_var_set] at a1

          obtain s2 := Finset.mem_image_of_mem (Function.updateITE σ x x) a1
          simp only [Function.updateITE] at s2
          simp only [if_neg c2] at s2

          exfalso
          apply s1
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
            obtain s1 := Sub.Var.All.Rec.Fresh.freeVarSet_sub_eq_freeVarSet_image (Function.updateITE σ x x) c phi
            simp only [s1] at c1

            simp only [← c3] at c1
            simp only [Finset.mem_union] at c1

            simp only [var_is_free_in_iff_mem_free_var_set] at a1

            obtain s2 := Finset.mem_image_of_mem (Function.updateITE σ (σ v) (σ v)) a1
            simp only [Function.updateITE] at s2
            simp only [ite_self] at s2

            exfalso
            apply c1
            left
            exact s2
          case _ c3 =>
            apply h1
            tauto
    · intro v a1
      split_ifs
      case _ c1 =>
        simp only [Function.updateITE]
        split_ifs
        case _ c2 =>
          obtain s1 := Sub.Var.All.Rec.Fresh.freeVarSet_sub_eq_freeVarSet_image (Function.updateITE σ x x) c phi
          simp only [← s1] at c2

          obtain s2 := fresh_not_mem x c ((free_var_set (Var.All.Rec.Fresh.sub (Function.updateITE σ x x) c phi)) ∪ (Finset.biUnion (pred_var_set phi) (predVarFreeVarSet τ)))
          simp only [← c2] at s2
          simp only [Finset.mem_union] at s2

          push_neg at s2
          cases s2
          case _ s2_left s2_right =>
            contradiction
        case _ c2 =>
          exact h2 v a1
      case _ c1 =>
        simp only [Finset.mem_union] at c1
        push_neg at c1
        cases c1
        case _ c1_left c1_right =>
          have s1 : ¬ v = x
          intro contra
          apply c1_right
          subst contra
          exact a1

          simp only [Function.updateITE]
          simp only [if_neg s1]
          exact h2 v a1
  case def_ X xs =>
    simp only [subAux]

    induction E generalizing V V' σ
    case nil =>
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [var_is_free_in] at h1

      simp only [holds]

      have s1 : (List.map V' xs) = (List.map (V ∘ σ) xs)
      simp only [List.map_eq_map_iff]
      intro x a1
      exact h1 x a1
      simp only [s1]
      clear s1

      split_ifs
      case _ c1 c2 =>
        have s2 : holds D I (Function.updateListITE V' E_hd.args (List.map (V ∘ σ) xs)) E_tl E_hd.q ↔ holds D I (Function.updateListITE V E_hd.args (List.map (V ∘ σ) xs)) E_tl E_hd.q
        apply holds_coincide_var
        intro x a1
        apply Function.updateListITE_map_mem_ext
        · simp
        · simp at c1
          tauto
        · simp only [var_is_free_in_iff_mem_free_var_set] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset E_hd.h1 a1

        simp
        simp only [← s2]
        clear s2

        simp only [subAux] at E_ih
        apply holds_coincide_pred_var
        · simp only [I']
          simp only [Interpretation_.usingPred]
        · intro P ds a1
          simp only [pred_var_occurs_in_iff_mem_pred_var_set] at a1
          simp only [E_hd.h2] at a1
          simp at a1
      case _ c1 c2 =>
        simp only [List.length_map] at c2
        contradiction
      case _ c1 c2 =>
        simp only [List.length_map] at c2
        contradiction
      case _ c1 c2 =>
        obtain s2 := E_ih V V' σ
        simp only [var_is_free_in] at s2
        specialize s2 h1 h2
        simp only [← s2]
        apply holds_coincide_pred_var
        · simp only [I']
          simp only [Interpretation_.usingPred]
        · intro P ds a1
          simp only [pred_var_occurs_in] at a1


theorem substitution_theorem
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (F : Formula_) :
  holds D (I' D I V E τ) V E F ↔ holds D I V E (sub c τ F) :=
  by
  apply substitution_theorem_aux
  · simp
  · simp


theorem substitution_is_valid
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (F : Formula_)
  (h1 : is_valid F) :
  is_valid (sub c τ F) :=
  by
  simp only [is_valid] at h1

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem]
  apply h1
