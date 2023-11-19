import FOL.NV.PredSub.All.Rec.PredSubAllRecOption

namespace FOL

namespace NV

open Formula


def predVarFreeVarSet
  (τ : PredName → ℕ → Option (List VarName × Formula)) :=
  fun (p, n) =>
  match τ p n with
  | none => {}
  | some (zs, H) => H.freeVarSet \ zs.toFinset

def subPredFresh
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
        then subFresh (Function.updateListITE id zs xs) c H
        else pred_var_ X xs
      else pred_var_ X xs
  | eq_ x y => eq_ x y
  | true_ => true_
  | false_ => false_
  | not_ phi =>
    have : length phi < length (not_ phi) := by simp only [Formula.length]; simp
    not_ (subPredFresh c τ phi)
  | imp_ phi psi =>
      have : length phi < length (imp_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (imp_ phi psi) := by simp only [Formula.length]; simp;
      imp_ (subPredFresh c τ phi) (subPredFresh c τ psi)
  | and_ phi psi =>
      have : length phi < length (and_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (and_ phi psi) := by simp only [Formula.length]; simp;
      and_ (subPredFresh c τ phi) (subPredFresh c τ psi)
  | or_ phi psi =>
      have : length phi < length (or_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (or_ phi psi) := by simp only [Formula.length]; simp;
      or_ (subPredFresh c τ phi) (subPredFresh c τ psi)
  | iff_ phi psi =>
      have : length phi < length (iff_ phi psi) := by simp only [Formula.length]; apply Nat.lt_add_right; simp;
      have : length psi < length (iff_ phi psi) := by simp only [Formula.length]; simp;
      iff_ (subPredFresh c τ phi) (subPredFresh c τ psi)
  | forall_ x phi =>
      have : length (subFresh (Function.updateITE id x (if x ∈ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ) then fresh x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)) else x)) c phi) < length (forall_ x phi) := by simp only [Formula.length]; simp only [sub_formula_length_same]; simp;
      let vs : Finset VarName := Finset.biUnion phi.predVarSet (predVarFreeVarSet τ)
      let x' : VarName :=
        if x ∈ vs
        then fresh x c vs
        else x
      forall_ x' (subPredFresh c τ (subFresh (Function.updateITE id x x') c phi))
  | exists_ x phi =>
      have : length (subFresh
      (Function.updateITE id x
        (if x ∈ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ) then
          fresh x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ) ∪ freeVarSet phi \ {x})
        else x))
      c phi) <
  length (exists_ x phi) := by simp only [Formula.length]; simp only [sub_formula_length_same]; simp;
      let vs : Finset VarName := Finset.biUnion phi.predVarSet (predVarFreeVarSet τ)
      let x' : VarName :=
        if x ∈ vs
        then fresh x c (vs ∪ (phi.freeVarSet \ {x}))
        else x
      exists_ x' (subPredFresh c τ (subFresh (Function.updateITE id x x') c phi))
  | def_ X xs => def_ X xs
  termination_by subPredFresh c τ F => F.length


example
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ : VarName → VarName)
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (F : Formula) :
  --(h1 : ∀ (x : VarName), x ∈ Finset.biUnion (predVarSet F) (predVarFreeVarSet τ) → V' x = V x) :
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
        then Holds D I (Function.updateListITE V' zs ds) E H
        else I.pred_var_ X ds
      else I.pred_var_ X ds
    ⟩
    V E F ↔ Holds D I V E (subPredFresh c τ F) :=
  by
  induction F generalizing V
  case pred_const_ X xs =>
    unfold subPredFresh
    simp only [Holds]
  case pred_var_ X xs =>
    --simp only [predVarSet] at h1
    --simp at h1

    unfold subPredFresh
    simp only [Holds]
    simp
    split_ifs
    case _ c1 c2 =>
      let opt := τ X xs.length
      let val := Option.get opt c1
      let zs := val.fst
      let H := val.snd
      obtain s1 := substitution_fun_theorem' D I V E (Function.updateListITE id zs xs) c H
      simp only [Function.updateListITE_comp] at s1
      simp at s1
      simp only [s1]
      clear s1

      apply Holds_coincide_Var
      intro v a1
      by_cases c3 : v ∈ zs
      · apply Function.updateListITE_mem_eq_len V' V v zs (List.map V xs) c3
        simp
        simp only [← c2]
      · simp only [Function.updateListITE_not_mem V v zs (List.map V xs) c3]
        simp only [Function.updateListITE_not_mem V' v zs (List.map V xs) c3]
        --apply h1
        sorry
    case _ c1 c2 =>
      simp only [Holds]
    case _ c1 =>
      simp only [Holds]

  case forall_ x phi phi_ih =>
    --simp only [predVarSet] at h1

    unfold subPredFresh
    simp only [Holds]
    apply forall_congr'
    intro d

    set pred_var_' := (fun X ds =>
      let opt := τ X (List.length ds);
      if h : Option.isSome opt = true
      then
        let val := Option.get opt h;
        let zs := val.fst;
        let H := val.snd;
        if List.length ds = List.length zs
        then Holds D I (Function.updateListITE V' zs ds) E H
        else Interpretation.pred_var_ I X ds
      else Interpretation.pred_var_ I X ds)

    set I' := ({ nonempty := (_ : Nonempty D), pred_const_ := I.pred_const_, pred_var_ := pred_var_' } : Interpretation D)

    obtain s1 := fresh_not_mem x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))

    generalize (fresh x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))) = x' at *

    split_ifs
    case _ c1 =>
      obtain s2 := substitution_fun_theorem D I
      simp only [phi_ih]
      sorry
    case _ c1 =>
      simp only [Function.updateITE_id]
      simp only [SubId]
      apply phi_ih
/-
      intro z a1
      simp only [Function.updateITE]
      split_ifs
      case _ c2 =>
        subst c2
        contradiction
      case _ c2 =>
        exact h1 z a1
-/
  all_goals sorry;

--------------------------------------------------

def subPredCapturedAux
  (binders : Finset VarName)
  (τ : PredName → ℕ → Option (List VarName × Formula)) :
  Formula → Finset VarName
  | pred_const_ _ _ => ∅
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then binders ∩ (H.freeVarSet \ zs.toFinset)
        else ∅
      else ∅
  | eq_ _ _ => ∅
  | true_ => ∅
  | false_ => ∅
  | not_ phi => subPredCapturedAux binders τ phi
  | imp_ phi psi => subPredCapturedAux binders τ phi ∪ subPredCapturedAux binders τ psi
  | and_ phi psi => subPredCapturedAux binders τ phi ∪ subPredCapturedAux binders τ psi
  | or_ phi psi => subPredCapturedAux binders τ phi ∪ subPredCapturedAux binders τ psi
  | iff_ phi psi => subPredCapturedAux binders τ phi ∪ subPredCapturedAux binders τ psi
  | forall_ x phi => subPredCapturedAux (binders ∪ {x}) τ phi
  | exists_ x phi => subPredCapturedAux (binders ∪ {x}) τ phi
  | def_ _ _ => ∅


def subPredCaptured
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (F : Formula) :
  Finset VarName :=
  subPredCapturedAux ∅ τ F


def subPredAlphaAux
  (c : Char)
  (τ : PredName → ℕ → Option (List VarName × Formula))
  (α : VarName → VarName)
  (binders : Finset VarName) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map α)
  | pred_var_ X xs => pred_var_ X (xs.map α)
  | eq_ x y => eq_ (α x) (α y)
  | true_ => true_
  | false_ => false_
  | not_ phi =>
    not_ (subPredAlphaAux c τ α binders phi)
  | imp_ phi psi =>
      imp_
      (subPredAlphaAux c τ α binders phi)
      (subPredAlphaAux c τ α binders psi)
  | and_ phi psi =>
      and_
      (subPredAlphaAux c τ α binders phi)
      (subPredAlphaAux c τ α binders psi)
  | or_ phi psi =>
      or_
      (subPredAlphaAux c τ α binders phi)
      (subPredAlphaAux c τ α binders psi)
  | iff_ phi psi =>
      iff_
      (subPredAlphaAux c τ α binders phi)
      (subPredAlphaAux c τ α binders psi)
  | forall_ x phi =>
      let free := phi.freeVarSet \ (binders ∪ {x})
      let replaced_free := (replacePredFun c τ phi).freeVarSet
      let captured := subPredCapturedAux (binders ∪ {x}) τ phi
      let x' :=
        if captured = ∅
        then x
        else fresh x c (replaced_free ∪ free)
      forall_ x' (subPredAlphaAux c τ (Function.updateITE α x x') (binders ∪ {x'}) phi)
  | exists_ x phi => sorry
  | def_ X xs => def_ X (xs.map α)
