import FOL.Formula
import FOL.Binders
import FOL.FunctionUpdateIte
import FOL.Semantics
import FOL.Tactics

import Mathlib.Data.String.Lemmas


namespace FOL

open Formula


def finset_var_name_max_len :
  Finset VarName → ℕ :=
  Finset.fold (fun (m n : ℕ) => max m n) 0 (String.length ∘ VarName.toString)


lemma finset_var_name_max_len_mem
  (x : VarName)
  (xs : Finset VarName)
  (h1 : x ∈ xs) :
  x.length <= finset_var_name_max_len xs :=
  by
  induction xs using Finset.induction_on
  case empty =>
    simp at h1
  case insert hd tl a1 ih =>
    simp at h1

    cases h1
    case inl c1 =>
      subst c1
      unfold finset_var_name_max_len
      simp
    case inr c1 =>
      unfold finset_var_name_max_len at ih

      unfold finset_var_name_max_len
      simp
      right
      exact ih c1


def variant
  (x : VarName)
  (c : Char)
  (xs : Finset VarName) :
  VarName :=
  if h : x ∈ xs
  then
  have : finset_var_name_max_len xs + 1 - (x.length + c.toString.length) < finset_var_name_max_len xs + 1 - x.length :=
    by
    have s1 : c.toString.length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_var_name_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  variant (VarName.mk (x.toString ++ c.toString)) c xs
  else x
  termination_by variant x _ xs => finset_var_name_max_len xs + 1 - x.length


lemma variant_not_mem
  (x : VarName)
  (c : Char)
  (xs : Finset VarName) :
  variant x c xs ∉ xs :=
  if h : x ∈ xs
  then
  have : finset_var_name_max_len xs + 1 - (x.length + c.toString.length) < finset_var_name_max_len xs + 1 - x.length :=
    by
    have s1 : c.toString.length = 1
    rfl

    simp only [s1]
    simp
    obtain s2 := finset_var_name_max_len_mem x xs h
    simp only [tsub_lt_tsub_iff_right s2]
    simp
  by
    unfold variant
    simp
    simp only [if_pos h]
    apply variant_not_mem
  else by
    unfold variant
    simp
    simp [if_neg h]
    exact h
  termination_by variant_not_mem x _ xs => finset_var_name_max_len xs + 1 - x.length


def sub
  (σ : VarName → VarName)
  (c : Char) :
  Formula → Formula
| pred_const_ X xs => pred_const_ X (xs.map σ)
| pred_var_ X xs => pred_var_ X (xs.map σ)
| eq_ x y => eq_ (σ x) (σ y)
| true_ => true_
| false_ => false_
| not_ phi => not_ (sub σ c phi)
| imp_ phi psi => imp_ (sub σ c phi) (sub σ c psi)
| and_ phi psi => and_ (sub σ c phi) (sub σ c psi)
| or_ phi psi => or_ (sub σ c phi) (sub σ c psi)
| iff_ phi psi => iff_ (sub σ c phi) (sub σ c psi)
| forall_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((sub (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  forall_ x' (sub (Function.updateIte σ x x') c phi)
| exists_ x phi =>
  let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((sub (Function.updateIte σ x x) c phi).freeVarSet)
    else x
  exists_ x' (sub (Function.updateIte σ x x') c phi)
| def_ X xs => def_ X (xs.map σ)


lemma lem_1
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula)
  (x : VarName)
  (h1 : ∀ τ : VarName → VarName, (sub τ c F).freeVarSet = F.freeVarSet.image τ) :
  let x' :=
    if ∃ (y : VarName), y ∈ F.freeVarSet \ {x} ∧ σ y = x
    then variant x c (sub (Function.updateIte σ x x) c F).freeVarSet
    else x
  x' ∉ (F.freeVarSet \ {x}).image σ :=
  by
  have s1 : (F.freeVarSet \ {x}).image σ ⊆ (sub (Function.updateIte σ x x) c F).freeVarSet
  calc
        (F.freeVarSet \ {x}).image σ

    _ = (F.freeVarSet \ {x}).image (Function.updateIte σ x x) :=
      by
      apply Finset.image_congr
      unfold Set.EqOn
      intro y a1
      unfold Function.updateIte
      simp at a1
      cases a1
      case _ a1_left a1_right =>
        simp only [if_neg a1_right]

    _ ⊆ F.freeVarSet.image (Function.updateIte σ x x) :=
      by
      apply Finset.image_subset_image
      exact Finset.sdiff_subset (freeVarSet F) {x}

    _ = (sub (Function.updateIte σ x x) c F).freeVarSet :=
      by
      symm
      exact h1 (Function.updateIte σ x x)

  split
  case inl c1 =>
    obtain s2 := variant_not_mem x c (freeVarSet (sub (Function.updateIte σ x x) c F))
    exact Finset.not_mem_mono s1 s2
  case inr c1 =>
    simp at c1
    simp
    exact c1


lemma lem_2
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β)
  (h1 : f x = x') :
  (Finset.image f S) \ {x'} =
  (Finset.image f (S \ {x})) \ {x'} :=
  by
  subst h1
  apply Finset.ext
  intro a
  simp
  intro a1
  constructor
  · intro a2
    apply Exists.elim a2
    intro b a3
    apply Exists.intro b
    cases a3
    case _ a3_left a3_right =>
      subst a3_right
      tauto
  · intro a2
    apply Exists.elim a2
    intro b a3
    apply Exists.intro b
    cases a3
    case _ a3_left a3_right =>
      subst a3_right
      tauto


lemma lem_3
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β) :
  ((S \ {x}).image (Function.updateIte f x x')) =
  ((S \ {x}).image f) :=
  by
  apply Finset.image_congr
  unfold Set.EqOn
  intro a a1
  simp at a1
  unfold Function.updateIte
  cases a1
  case _ a1_left a1_right =>
    simp only [if_neg a1_right]


theorem lem_4
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  (sub σ c F).freeVarSet = F.freeVarSet.image σ :=
  by
  induction F generalizing σ
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    unfold sub
    unfold freeVarSet
    apply Finset.ext
    intro a
    simp
  case true_ | false_ =>
    unfold sub
    unfold freeVarSet
    simp
  case not_ phi phi_ih =>
    unfold sub
    unfold freeVarSet
    exact phi_ih σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold sub
    unfold freeVarSet
    simp only [Finset.image_union]
    congr!
    · exact phi_ih σ
    · exact psi_ih σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    let x' : VarName :=
    if ∃ (y : VarName), y ∈ phi.freeVarSet \ {x} ∧ σ y = x
    then variant x c ((sub (Function.updateIte σ x x) c phi).freeVarSet)
    else x
    calc
        (sub σ c (forall_ x phi)).freeVarSet
    _ = (forall_ x' (sub (Function.updateIte σ x x') c phi)).freeVarSet := by simp only [sub]

    _ = (sub (Function.updateIte σ x x') c phi).freeVarSet \ {x'} := by simp only [freeVarSet]

    _ = (phi.freeVarSet.image (Function.updateIte σ x x')) \ {x'} := by simp only [phi_ih (Function.updateIte σ x x')]

    _ = ((phi.freeVarSet \ {x}).image (Function.updateIte σ x x')) \ {x'} :=
      by
      apply lem_2
      unfold Function.updateIte
      simp

    _ = ((phi.freeVarSet \ {x}).image σ) \ {x'} :=
      by
      congr! 1
      apply lem_3

    _ = (phi.freeVarSet \ {x}).image σ :=
      by
      apply Finset.sdiff_singleton_eq_self
      exact lem_1 σ c phi x phi_ih


theorem substitution_fun_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  Holds D I V E (sub σ c F) ↔
    Holds D I (V ∘ σ) E F :=
  by
  induction F generalizing σ V
  case pred_const_ X xs | pred_var_ X xs | eq_ x y =>
    unfold sub
    simp only [Holds]
    simp
  case true_ | false_ =>
    unfold sub
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold sub
    simp only [Holds]
    congr! 1
    exact phi_ih V σ
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold sub
    simp only [Holds]
    congr! 1
    · exact phi_ih V σ
    · exact psi_ih V σ
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    let x' :=
      if ∃ y ∈ phi.freeVarSet \ {x}, σ y = x
      then variant x c (sub (Function.updateIte σ x x) c phi).freeVarSet
      else x

    have s1 : ∀ (a : D) (z : VarName), z ∈ phi.freeVarSet → ((Function.updateIte V x' a) ∘ (Function.updateIte σ x x')) z = (Function.updateIte (V ∘ σ) x a) z
    intro a z h1
    by_cases h2 : z = x
    case pos =>
      subst h2
      unfold Function.updateIte
      simp
    case neg =>
      have s3 : x' ∉ (phi.freeVarSet \ {x}).image σ
      apply lem_1
      intro τ
      exact lem_4 τ c phi

      have s4 : σ z ∈ (phi.freeVarSet \ {x}).image σ
      apply Finset.mem_image_of_mem
      simp
      tauto

      have s5 : ¬ σ z = x'
      intro contra
      apply s3
      simp only [<- contra]
      exact s4

      unfold Function.updateIte
      simp (config := {zeta := false})
      simp (config := {zeta := false}) only [if_neg h2]
      split_ifs
      case inl c1 =>
        tauto
      case inr c1 =>
        rfl

    simp only [sub]
    simp only [Holds]
    first | apply forall_congr' | apply exists_congr
    intro a
    simp only [phi_ih]
    apply Holds_coincide_Var
    intro v a1
    apply s1
    simp only [isFreeIn_iff_mem_freeVarSet] at a1
    exact a1

  case def_ X xs =>
    induction E
    case nil =>
      unfold sub
      simp only [Holds]
    case cons E_hd E_tl E_ih =>
      unfold sub at E_ih

      unfold sub
      simp only [Holds]
      simp
      split_ifs
      case inl c1 =>
        apply Holds_coincide_Var
        intro v a1
        apply Function.updateListIte_map_mem_ext
        · simp
        · cases c1
          case _ c1_left c1_right =>
            symm
            exact c1_right
        · simp only [isFreeIn_iff_mem_freeVarSet] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset E_hd.h1 a1
      case inr c1 =>
        exact E_ih


theorem sub_valid
  (σ : VarName → VarName)
  (c : Char)
  (phi : Formula)
  (h1 : IsValid phi) :
  IsValid (sub σ c phi) :=
  by
  unfold IsValid at h1

  unfold IsValid
  intros D I V E
  simp only [substitution_fun_theorem]
  apply h1


def replacePredFun
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula)) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then sub (Function.updateListIte id zs xs) c H
        else pred_var_ X xs
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replacePredFun c τ phi)
  | imp_ phi psi =>
      imp_
      (replacePredFun c τ phi)
      (replacePredFun c τ psi)
  | and_ phi psi =>
      and_
      (replacePredFun c τ phi)
      (replacePredFun c τ psi)
  | or_ phi psi =>
      or_
      (replacePredFun c τ phi)
      (replacePredFun c τ psi)
  | iff_ phi psi =>
      iff_
      (replacePredFun c τ phi)
      (replacePredFun c τ psi)
  | forall_ x phi => forall_ x (replacePredFun c τ phi)
  | exists_ x phi => exists_ x (replacePredFun c τ phi)
  | def_ X xs => def_ X xs


def admitsPredFunAux
  (τ : PredName → ℕ → Option (List VarName × Formula)) :
  Finset VarName → Formula → Prop
  | _, pred_const_ _ _ => True
  | binders, pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then ∀ x : VarName, x ∈ binders → ¬ (isFreeIn x H ∧ x ∉ zs)
        else True
      else True
  | _, true_ => True
  | _, false_ => True
  | _, eq_ _ _ => True
  | binders, not_ phi => admitsPredFunAux τ binders phi
  | binders, imp_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | binders, and_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | binders, or_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | binders, iff_ phi psi =>
      admitsPredFunAux τ binders phi ∧
      admitsPredFunAux τ binders psi
  | binders, forall_ x phi => admitsPredFunAux τ (binders ∪ {x}) phi
  | binders, exists_ x phi => admitsPredFunAux τ (binders ∪ {x}) phi
  | _, def_ _ _ => True


theorem predSub_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (binders : Finset VarName)
  (F : Formula)
  (h1 : admitsPredFunAux τ binders F)
  (h2 : ∀ x : VarName, x ∉ binders → V x = V' x) :
  Holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName) (ds : List D) =>
      let opt := τ X ds.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if ds.length = zs.length
        then Holds D I (Function.updateListIte V' zs ds) E H
        else I.pred_var_ X ds
      else I.pred_var_ X ds
    ⟩ 
    V E F ↔ Holds D I V E (replacePredFun c τ F) :=
  by
  induction F generalizing binders V
  case pred_const_ X xs =>
    unfold replacePredFun
    simp only [Holds]
  case pred_var_ X xs =>
    unfold admitsPredFunAux at h1
    simp at h1

    unfold replacePredFun
    simp only [Holds]
    simp
    split_ifs at h1
    case inl c1 =>
      cases h1
      case inl c2 =>
        split_ifs
        simp only [Holds]
      case inr c2 =>
        split_ifs
        case inl c3 =>
          let opt := τ X xs.length
          let val := Option.get opt c1
          let zs := val.fst
          let H := val.snd
          obtain s1 := substitution_fun_theorem D I V E (Function.updateListIte id zs xs) c H
          simp only [Function.updateListIte_comp] at s1
          simp at s1

          have s2 : Holds D I (Function.updateListIte V zs (List.map V xs)) E H ↔ Holds D I (Function.updateListIte V' zs (List.map V xs)) E H
          {
            apply Holds_coincide_Var
            intro v a1
            by_cases s2_c1 : v ∈ zs
            · apply Function.updateListIte_mem_eq_len V V' v zs (List.map V xs) s2_c1
              simp
              simp only [← c3]
            · by_cases s2_c2 : v ∈ binders
              · specialize c2 v s2_c2 a1
                contradiction
              · specialize h2 v s2_c2
                apply Function.updateListIte_mem'
                exact h2
          }
          simp only [s2] at s1
          simp only [s1]
        case inr c3 =>
          simp only [Holds]
    case inr c1 =>
      split_ifs
      simp only [Holds]
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
    apply phi_ih (Function.updateIte V x d) (binders ∪ {x}) h1
    intro v a1
    unfold Function.updateIte
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


def Formula.length : Formula → ℕ
  | pred_const_ _ _ => 0
  | pred_var_ _ _ => 0
  | eq_ _ _ => 0
  | true_ => 0
  | false_ => 0
  | not_ phi => 1 + phi.length
  | imp_ phi psi => 1 + phi.length + psi.length
  | and_ phi psi => 1 + phi.length + psi.length
  | or_ phi psi => 1 + phi.length + psi.length
  | iff_ phi psi => 1 + phi.length + psi.length
  | forall_ _ phi => 1 + phi.length
  | exists_ _ phi => 1 + phi.length
  | def_ _ _ => 0


lemma sub_formula_length_same
  (σ : VarName → VarName)
  (c : Char)
  (F : Formula) :
  (sub σ c F).length = F.length :=
  by
  induction F generalizing σ
  case not_ phi phi_ih =>
    unfold sub
    unfold Formula.length
    simp only [phi_ih]
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold sub
    unfold Formula.length
    simp only [phi_ih σ]
    simp only [psi_ih σ]
  case forall_ x phi phi_ih | exists_ x phi_ih =>
    unfold sub
    unfold Formula.length
    simp
    apply phi_ih
  all_goals
    unfold sub
    unfold Formula.length
    simp


def predVarFreeVarSet
  (τ : PredName → ℕ → Option (List VarName × Formula)) :=
  fun (p, n) =>
  match τ p n with
  | none => {}
  | some (zs, H) => H.freeVarSet \ zs.toFinset

def subPredAux
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula)) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then sub (Function.updateListIte id zs xs) c H
        else pred_var_ X xs
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi =>
    have : length phi < length (not_ phi) := by simp only [Formula.length]; simp
    not_ (subPredAux c τ phi)
  | imp_ phi psi =>
      have : length phi < length (imp_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (imp_ phi psi) := by simp only [Formula.length]; simp;
      imp_ (subPredAux c τ phi) (subPredAux c τ psi)
  | and_ phi psi =>
      have : length phi < length (and_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (and_ phi psi) := by simp only [Formula.length]; simp;
      and_ (subPredAux c τ phi) (subPredAux c τ psi)
  | or_ phi psi =>
      have : length phi < length (or_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (or_ phi psi) := by simp only [Formula.length]; simp;
      or_ (subPredAux c τ phi) (subPredAux c τ psi)
  | iff_ phi psi =>
      have : length phi < length (iff_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (iff_ phi psi) := by simp only [Formula.length]; simp;
      iff_ (subPredAux c τ phi) (subPredAux c τ psi)
  | forall_ x phi =>
      have : length (sub (Function.updateIte id x (if x ∈ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ) then variant x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)) else x)) c phi) < length (forall_ x phi) := by simp only [Formula.length]; simp only [sub_formula_length_same]; simp;
      let vs : Finset VarName := Finset.biUnion phi.predVarSet (predVarFreeVarSet τ)
      let x' : VarName :=
        if x ∈ vs
        then variant x c vs
        else x
      forall_ x' (subPredAux c τ (sub (Function.updateIte id x x') c phi))
  | exists_ x phi =>
      have : length (sub (Function.updateIte id x (if x ∈ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ) then variant x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)) else x)) c phi) < length (forall_ x phi) := by simp only [Formula.length]; simp only [sub_formula_length_same]; simp;
      let vs : Finset VarName := Finset.biUnion phi.predVarSet (predVarFreeVarSet τ)
      let x' : VarName :=
        if x ∈ vs
        then variant x c vs
        else x
      exists_ x' (subPredAux c τ (sub (Function.updateIte id x x') c phi))
  | def_ X xs => def_ X xs
  termination_by subPredAux c τ F => F.length


example
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (F : Formula)
  (h1 : ∀ x : VarName, V x = V' x) :
  Holds D
    ⟨
      I.nonempty,
      I.pred_const_,
      fun (X : PredName) (ds : List D) =>
      let opt := τ X ds.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if ds.length = zs.length
        then Holds D I (Function.updateListIte V' zs ds) E H
        else I.pred_var_ X ds
      else I.pred_var_ X ds
    ⟩ 
    V E F ↔ Holds D I V E (subPredAux c τ F) :=
  by
  induction F generalizing V
  case pred_const_ X xs =>
    unfold subPredAux
    simp only [Holds]
  case pred_var_ X xs =>
    unfold subPredAux
    simp only [Holds]
    simp
    sorry
  all_goals sorry;
