import FOL.NV.Sub.All.Rec.SubAllRecFresh


namespace FOL

namespace NV

open Formula


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
        then subFresh (Function.updateListITE id zs xs) c H
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
      have : length (subFresh (Function.updateITE id x (if x ∈ Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ) then fresh x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ)) else x)) c phi) < length (forall_ x phi) := by simp only [Formula.length]; simp only [sub_formula_length_same]; simp;
      let vs : Finset VarName := Finset.biUnion phi.predVarSet (predVarFreeVarSet τ)
      let x' : VarName :=
        if x ∈ vs
        then fresh x c vs
        else x
      forall_ x' (subPredAux c τ (subFresh (Function.updateITE id x x') c phi))
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
      exists_ x' (subPredAux c τ (subFresh (Function.updateITE id x x') c phi))
  | def_ X xs => def_ X xs
  termination_by subPredAux c τ F => F.length



def subPredCaptured
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
  | not_ phi => subPredCaptured binders τ phi
  | imp_ phi psi => subPredCaptured binders τ phi ∪ subPredCaptured binders τ psi
  | and_ phi psi => subPredCaptured binders τ phi ∪ subPredCaptured binders τ psi
  | or_ phi psi => subPredCaptured binders τ phi ∪ subPredCaptured binders τ psi
  | iff_ phi psi => subPredCaptured binders τ phi ∪ subPredCaptured binders τ psi
  | forall_ x phi => subPredCaptured (binders ∪ {x}) τ phi
  | exists_ x phi => subPredCaptured (binders ∪ {x}) τ phi
  | def_ _ _ => ∅


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
    not_ (subPredAlphaAux c σ τ phi)
  | imp_ phi psi =>
      imp_ (subPredAlphaAux c σ τ phi) (subPredAlphaAux c σ τ psi)
  | and_ phi psi =>
      and_ (subPredAlphaAux c σ τ phi) (subPredAlphaAux c σ τ psi)
  | or_ phi psi =>
      or_ (subPredAlphaAux c σ τ phi) (subPredAlphaAux c σ τ psi)
  | iff_ phi psi =>
      iff_ (subPredAlphaAux c σ τ phi) (subPredAlphaAux c σ τ psi)
  | forall_ x phi =>
      let free := phi.freeVarSet \ (binders ∪ {x})
      let free_after_sub := (replacePredFun c τ phi).freeVarSet
      sorry
  | exists_ x phi => sorry
  | def_ X xs => def_ X (xs.map α)


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
    V E F ↔ Holds D I V E (subPredAux c τ F) :=
  by
  induction F generalizing V
  case pred_const_ X xs =>
    unfold subPredAux
    simp only [Holds]
  case pred_var_ X xs =>
    --simp only [predVarSet] at h1
    --simp at h1

    unfold subPredAux
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

    unfold subPredAux
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

    obtain s1 := variant_not_mem x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))

    generalize (variant x c (Finset.biUnion (predVarSet phi) (predVarFreeVarSet τ))) = x' at *

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




def replaceVarOption
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (v : VarName) :
  Option VarName :=
  if v ∉ binders
  then
    if σ v ∉ binders
    then Option.some (σ v)
    else Option.none
  else v

def subOption
  (σ : VarName → VarName) :
  Finset VarName → Formula → Option Formula
  | binders, pred_const_ X xs => do
      let xs' ← xs.mapM (replaceVarOption σ binders)
      pred_const_ X xs'
  | binders, pred_var_ X xs => do
      let xs' ← xs.mapM (replaceVarOption σ binders)
      pred_var_ X xs'
  | binders, eq_ x y => do
      let x' ← replaceVarOption σ binders x
      let y' ← replaceVarOption σ binders y
      eq_ x' y'
  | _, true_ => true_
  | _, false_ => false_
  | binders, not_ phi => do
      let phi' ← subOption σ binders phi
      not_ phi'
  | binders, imp_ phi psi => do
      let phi' ← subOption σ binders phi
      let psi' ← subOption σ binders psi
      imp_ phi' psi'
  | binders, and_ phi psi => do
      let phi' ← subOption σ binders phi
      let psi' ← subOption σ binders psi
      and_ phi' psi'
  | binders, or_ phi psi => do
      let phi' ← subOption σ binders phi
      let psi' ← subOption σ binders psi
      or_ phi' psi'
  | binders, iff_ phi psi => do
      let phi' ← subOption σ binders phi
      let psi' ← subOption σ binders psi
      iff_ phi' psi'
  | binders, forall_ x phi => do
      let phi' ← subOption σ (binders ∪ {x}) phi
      forall_ x phi'
  | binders, exists_ x phi => do
      let phi' ← subOption σ (binders ∪ {x}) phi
      exists_ x phi'
  | binders, def_ X xs => do
      let xs' ← xs.mapM (replaceVarOption σ binders)
      def_ X xs'


example
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (σ σ' : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula)
  (h1 : Option.isSome (subOption σ' binders F))
  (h2 : ∀ v : VarName, v ∈ binders ∨ σ' v ∉ binders → V v = V' (σ' v))
  (h2' : ∀ v : VarName, v ∈ binders → v = σ' v)
  (h3 : ∀ v : VarName, v ∉ binders → σ' v = σ v) :
  let opt := subOption σ' binders F
  Holds D I V E F ↔ Holds D I V' E (Option.get opt h1) :=
  by
    sorry
