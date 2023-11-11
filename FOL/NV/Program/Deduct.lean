import Mathlib.Data.Finset.Basic
import Mathlib.Util.CompileInductive


/--
  The type of variable names.
-/
structure VarName extends String
  deriving Inhabited, DecidableEq

instance : ToString VarName :=
  { toString := fun x => x.toString }

instance : Repr VarName :=
  { reprPrec := fun x _ => x.toString.toFormat }


/--
  The type of predicate names.
-/
structure PredName extends String
  deriving Inhabited, DecidableEq

instance : ToString PredName :=
  { toString := fun X => X.toString }

instance : Repr PredName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of definition names.
-/
structure DefName extends String
  deriving Inhabited, DecidableEq

instance : ToString DefName :=
  { toString := fun X => X.toString }

instance : Repr DefName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of formulas.
-/
inductive Formula : Type
  | pred_const_ : PredName → List VarName → Formula
  | pred_var_ : PredName → List VarName → Formula
  | eq_ : VarName → VarName → Formula
  | true_ : Formula
  | false_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | and_ : Formula → Formula → Formula
  | or_ : Formula → Formula → Formula
  | iff_ : Formula → Formula → Formula
  | forall_ : VarName → Formula → Formula
  | exists_ : VarName → Formula → Formula
  | def_ : DefName → List VarName → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula

/--
  The string representation of formulas.
-/
def Formula.toString : Formula → String
  | pred_const_ X xs => s! "({X} {xs})"
  | pred_var_ X xs => s! "({X} {xs})"
  | eq_ x y => s! "({x} = {y})"
  | true_ => "T"
  | false_ => "F"
  | not_ phi => s! "(¬ {phi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"
  | forall_ x phi => s! "(∀ {x}. {phi.toString})"
  | exists_ x phi => s! "(∃ {x}. {phi.toString})"
  | def_ X xs => s! "def ({X} {xs})"


instance : ToString Formula :=
  { toString := fun F => F.toString }

instance : Repr Formula :=
  { reprPrec := fun F _ => F.toString.toFormat }


/--
  And_ [] := T

  And_ [phi] := phi ∧ T

  And_ [phi_0 ... phi_n] := phi_0 ∧ ... ∧ phi_n ∧ T
-/
def Formula.And_ (l : List Formula) : Formula :=
  List.foldr Formula.and_ true_ l


/--
  Formula.freeVarSet F := The set of all of the variables that have a free occurrence in the formula F.
-/
def Formula.freeVarSet : Formula → Finset VarName
  | pred_const_ _ xs => xs.toFinset
  | pred_var_ _ xs => xs.toFinset
  | eq_ x y => {x, y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.freeVarSet
  | imp_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | and_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | or_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | iff_ phi psi => phi.freeVarSet ∪ psi.freeVarSet
  | forall_ x phi => phi.freeVarSet \ {x}
  | exists_ x phi => phi.freeVarSet \ {x}
  | def_ _ xs => xs.toFinset


/--
  isFreeIn v F := True if and only if there is a free occurrence of the variable v in the formula F.
-/
def isFreeIn (v : VarName) : Formula → Prop
  | pred_const_ _ xs => v ∈ xs
  | pred_var_ _ xs => v ∈ xs
  | eq_ x y => v = x ∨ v = y
  | true_ => False
  | false_ => False
  | not_ phi => isFreeIn v phi
  | imp_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | and_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | or_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | iff_ phi psi => isFreeIn v phi ∨ isFreeIn v psi
  | forall_ x phi => ¬ v = x ∧ isFreeIn v phi
  | exists_ x phi => ¬ v = x ∧ isFreeIn v phi
  | def_ _ xs => v ∈ xs

instance (v : VarName) (F : Formula) : Decidable (isFreeIn v F) :=
  by
  induction F
  all_goals
    unfold isFreeIn
    infer_instance


/--
  Formula.predVarSet F := The set of all of the predicate variables that have an occurrence in the formula F.
-/
def Formula.predVarSet : Formula → Finset (PredName × ℕ)
  | pred_const_ _ _ => ∅
  | pred_var_ X xs => {(X, xs.length)}
  | eq_ _ _ => ∅
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.predVarSet
  | imp_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | and_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | or_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | iff_ phi psi => phi.predVarSet ∪ psi.predVarSet
  | forall_ _ phi => phi.predVarSet
  | exists_ _ phi => phi.predVarSet
  | def_ _ _ => ∅


/--
  Specialized version of Function.update for non-dependent functions.
  Function.updateIte f a' b := Replaces the value of f at a' by b.
-/
def Function.updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a' : α)
  (b : β)
  (a : α) :
  β :=
  if a = a' then b else f a


/--
  fastReplaceFreeFun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def fastReplaceFreeFun : (VarName → VarName) → Formula → Formula
  | σ, pred_const_ X xs => pred_const_ X (xs.map σ)
  | σ, pred_var_ X xs => pred_var_ X (xs.map σ)
  | σ, eq_ x y => eq_ (σ x) (σ y)
  | _, true_ => true_
  | _, false_ => false_
  | σ, not_ phi => not_ (fastReplaceFreeFun σ phi)
  | σ, imp_ phi psi =>
      imp_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, and_ phi psi =>
      and_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, or_ phi psi =>
      or_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, iff_ phi psi =>
      iff_
      (fastReplaceFreeFun σ phi)
      (fastReplaceFreeFun σ psi)
  | σ, forall_ x phi =>
      forall_ x (fastReplaceFreeFun (Function.updateIte σ x x) phi)
  | σ, exists_ x phi =>
      exists_ x (fastReplaceFreeFun (Function.updateIte σ x x) phi)
  | σ, def_ X xs => def_ X (xs.map σ)


def admitsFunAux
  (σ : VarName → VarName) :
  Finset VarName → Formula → Prop
  | binders, pred_const_ _ xs =>
      ∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders
  | binders, pred_var_ _ xs =>
      ∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders
  | binders, eq_ x y =>
      (x ∉ binders → σ x ∉ binders) ∧
      (y ∉ binders → σ y ∉ binders)
  | _, true_ => True
  | _, false_ => True
  | binders, not_ phi => admitsFunAux σ binders phi
  | binders, imp_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, and_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, or_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, iff_ phi psi =>
      admitsFunAux σ binders phi ∧
      admitsFunAux σ binders psi
  | binders, forall_ x phi => admitsFunAux σ (binders ∪ {x}) phi
  | binders, exists_ x phi => admitsFunAux σ (binders ∪ {x}) phi
  | binders, def_ _ xs =>
      ∀ v : VarName, v ∈ xs → v ∉ binders → σ v ∉ binders


instance
  (σ : VarName → VarName)
  (binders : Finset VarName)
  (F : Formula) :
  Decidable (admitsFunAux σ binders F) :=
  by
  induction F generalizing binders
  all_goals
    unfold admitsFunAux
    infer_instance


def admitsFun (σ : VarName → VarName) (phi : Formula) : Prop :=
  admitsFunAux σ ∅ phi


instance
  (σ : VarName → VarName)
  (F : Formula) :
  Decidable (admitsFun σ F) :=
  by
  unfold admitsFun
  infer_instance


/--
  Function.updateIte at multiple points.
  Function.updateListIte f xs ys := Replaces the value of f at each point in xs by the value in ys at the same index.
  If there are duplicate values in xs then the value at the smallest index is used.
  If the lengths of xs and ys do not match then the longer is effectively truncated to the length of the smaller.
-/
def Function.updateListIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x::xs, y::ys => Function.updateIte (Function.updateListIte f xs ys) x y
  | _, _ => f


/--
  The recursive simultaneous uniform substitution of all of the predicate variables in a formula.
-/
def replacePredFun (τ : PredName → ℕ → (List VarName × Formula)) : Formula → Formula
  | pred_const_ X xs => pred_const_ X xs
  | pred_var_ X xs =>
      if xs.length = (τ X xs.length).fst.length
      then fastReplaceFreeFun (Function.updateListIte id (τ X xs.length).fst xs) (τ X xs.length).snd
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
  (τ : PredName → ℕ → List VarName × Formula) :
  Finset VarName → Formula → Prop
  | _, pred_const_ _ _ => True
  | binders, pred_var_ X xs =>
    admitsFun (Function.updateListIte id (τ X xs.length).fst xs) (τ X xs.length).snd ∧
      (∀ x : VarName, x ∈ binders → ¬ (isFreeIn x (τ X xs.length).snd ∧ x ∉ (τ X xs.length).fst)) ∧
        xs.length = (τ X xs.length).fst.length
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


structure Definition : Type :=
(name : DefName)
(args : List VarName)
(F : Formula)
deriving Inhabited, DecidableEq

abbrev Env : Type := List Definition

def Formula.all_def_in_env (E : Env) : Formula → Prop
| pred_const_ _ _ => True
| pred_var_ _ _ => True
| eq_ _ _ => True
| true_ => True
| false_ => True
| not_ phi => phi.all_def_in_env E
| imp_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| and_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| or_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| iff_ phi psi =>
    phi.all_def_in_env E ∧
    psi.all_def_in_env E
| forall_ _ phi => phi.all_def_in_env E
| exists_ _ phi => phi.all_def_in_env E
| def_ X xs =>
  ∃ (d : Definition), d ∈ E ∧ X = d.name ∧ xs.length = d.args.length

instance (E : Env) (F : Formula) : Decidable (F.all_def_in_env E) :=
  by
  induction F
  all_goals
    unfold Formula.all_def_in_env
    infer_instance


def admitsUnfoldDef
  (d : Definition) :
  Formula → Prop
| pred_const_ _ _ => True
| pred_var_ _ _ => True
| eq_ _ _ => True
| true_ => True
| false_ => True
| not_ phi => admitsUnfoldDef d phi
| imp_ phi psi => (admitsUnfoldDef d phi) ∧ (admitsUnfoldDef d psi)
| and_ phi psi => (admitsUnfoldDef d phi) ∧ (admitsUnfoldDef d psi)
| or_ phi psi => (admitsUnfoldDef d phi) ∧ (admitsUnfoldDef d psi)
| iff_ phi psi => (admitsUnfoldDef d phi) ∧ (admitsUnfoldDef d psi)
| forall_ _ phi => admitsUnfoldDef d phi
| exists_ _ phi => admitsUnfoldDef d phi
| def_ X xs =>
    if X = d.name ∧ xs.length = d.args.length
    then admitsFun (Function.updateListIte id d.args xs) d.F
    else True

instance
  (d : Definition)
  (F : Formula) :
  Decidable (admitsUnfoldDef d F) :=
  by
  induction F
  all_goals
    unfold admitsUnfoldDef
    infer_instance


def unfoldDef
  (d : Definition) :
  Formula → Formula
| pred_const_ X xs => pred_const_ X xs
| pred_var_ X xs => pred_var_ X xs
| eq_ x y => eq_ x y
| true_ => true_
| false_ => false_
| not_ phi => not_ (unfoldDef d phi)
| imp_ phi psi => imp_ (unfoldDef d phi) (unfoldDef d psi)
| and_ phi psi => and_ (unfoldDef d phi) (unfoldDef d psi)
| or_ phi psi => or_ (unfoldDef d phi) (unfoldDef d psi)
| iff_ phi psi => iff_ (unfoldDef d phi) (unfoldDef d psi)
| forall_ x phi => forall_ x (unfoldDef d phi)
| exists_ x phi => exists_ x (unfoldDef d phi)
| def_ X xs =>
    if X = d.name ∧ xs.length = d.args.length
    then fastReplaceFreeFun (Function.updateListIte id d.args xs) d.F
    else def_ X xs


/--
  A substitution mapping.
  A bijective function mapping variable names to variable names.
-/
def Instantiation : Type :=
  { σ : VarName → VarName // ∃ σ' : VarName → VarName, σ ∘ σ' = id ∧ σ' ∘ σ = id }

def replaceAllVar
  (σ : VarName → VarName) :
  Formula → Formula
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs => pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi => not_ (replaceAllVar σ phi)
  | imp_ phi psi => imp_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | and_ phi psi => and_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | or_ phi psi => or_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | iff_ phi psi => iff_ (replaceAllVar σ phi) (replaceAllVar σ psi)
  | forall_ x phi => forall_ (σ x) (replaceAllVar σ phi)
  | exists_ x phi => exists_ (σ x) (replaceAllVar σ phi)
  | def_ X xs => def_ X (xs.map σ)


inductive IsConv (E : Env) : Formula → Formula → Prop
  | conv_refl
    (phi : Formula) :
    IsConv E phi phi

  | conv_symm
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E phi' phi

  | conv_trans
    (phi phi' phi'' : Formula) :
    IsConv E phi phi' →
    IsConv E phi' phi'' →
    IsConv E phi phi''

  | conv_not
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E (not_ phi) (not_ phi')

  | conv_imp
    (phi phi' psi psi' : Formula) :
    IsConv E phi phi' →
    IsConv E psi psi' →
    IsConv E (imp_ phi psi) (imp_ phi' psi')

  | conv_forall
    (x : VarName)
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E (forall_ x phi) (forall_ x phi')

  | conv_unfold
    (d : Definition)
    (σ : Instantiation) :
    d ∈ E →
    IsConv E (def_ d.name (d.args.map σ.1)) (replaceAllVar σ.1 d.F)

  | conv_unfold'
    (d : Definition)
    (σ : VarName → VarName) :
    d ∈ E →
    admitsFun σ d.F →
    IsConv E (def_ d.name (d.args.map σ)) (fastReplaceFreeFun σ d.F)


inductive IsDeduct : Env → List Formula → Formula → Prop
  | struct_1_
    (E : Env)
    (Δ : List Formula)
    (H phi : Formula) :
    IsDeduct E Δ phi →
    IsDeduct E (H :: Δ) phi

  | struct_2_
    (E : Env)
    (Δ : List Formula)
    (H phi : Formula) :
    IsDeduct E (H :: H :: Δ) phi →
    IsDeduct E (H :: Δ) phi

  | struct_3_
    (E : Env)
    (Δ_1 Δ_2 : List Formula)
    (H1 H2 phi : Formula) :
    IsDeduct E (Δ_1 ++ [H1] ++ [H2] ++ Δ_2) phi →
    IsDeduct E (Δ_1 ++ [H2] ++ [H1] ++ Δ_2) phi

  /-
    Δ, phi ⊢ phi
  -/
  | assumption_
    (E : Env)
    (Δ : List Formula)
    (phi : Formula) :
    IsDeduct E (phi :: Δ) phi

  /-
    Δ ⊢ ⊤
  -/
  | prop_true_
    (E : Env)
    (Δ : List Formula) :
    IsDeduct E Δ true_

  /-
    Δ ⊢ phi → (psi → phi)
  -/
  | prop_1_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ (phi.imp_ (psi.imp_ phi))

  /-
    Δ ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
  -/
  | prop_2_
    (E : Env)
    (Δ : List Formula)
    (phi psi chi : Formula) :
    IsDeduct E Δ
      ((phi.imp_ (psi.imp_ chi)).imp_
        ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  /-
    Δ ⊢ (¬ phi → ¬ psi) → (psi → phi)
  -/
  | prop_3_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ
      (((not_ phi).imp_ (not_ psi)).imp_
        (psi.imp_ phi))

  /-
    Δ ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
  -/
  | pred_1_
    (E : Env)
    (Δ : List Formula)
    (v : VarName)
    (phi psi : Formula) :
    IsDeduct E Δ
      ((forall_ v (phi.imp_ psi)).imp_
        ((forall_ v phi).imp_
          (forall_ v psi)))

  /-
    Δ ⊢ (∀ v phi) → phi(t/v)
    provided phi admits t for v
  -/
  | pred_2_
    (E : Env)
    (Δ : List Formula)
    (v t : VarName)
    (phi : Formula) :
    admitsFun (Function.updateIte id v t) phi →
    IsDeduct E Δ ((forall_ v phi).imp_ (fastReplaceFreeFun (Function.updateIte id v t) phi))

  /-
    Δ ⊢ phi → (∀ v phi)
    provided v is not free in phi
  -/
  | pred_3_
    (E : Env)
    (Δ : List Formula)
    (v : VarName)
    (phi : Formula) :
    ¬ isFreeIn v phi →
    IsDeduct E Δ (phi.imp_ (forall_ v phi))

  /-
    Δ ⊢ v = v
  -/
  | eq_1_
    (E : Env)
    (Δ : List Formula)
    (v : VarName) :
    IsDeduct E Δ (eq_ v v)

  /-
    Δ ⊢ ((x_0 = y_0) ∧ ... ∧ (x_n = y_n)) →
          (pred_const_ name [x_0 ... x_n] → pred_const_ name [y_0 ... y_n])
  -/
  | eq_2_pred_const_
    (E : Env)
    (Δ : List Formula)
    (name : PredName)
    (xs ys : List VarName) :
    xs.length = ys.length →
    IsDeduct E Δ
    ((And_ (List.zipWith eq_ xs ys)).imp_
      ((pred_const_ name xs).imp_ (pred_const_ name ys)))

  /-
    Δ ⊢ ((x_0 = y_0) ∧ ... ∧ (x_n = y_n)) →
          (pred_var_ name [x_0 ... x_n] → pred_var_ name [y_0 ... y_n])
  -/
  | eq_2_pred_var_
    (E : Env)
    (Δ : List Formula)
    (name : PredName)
    (xs ys : List VarName) :
    xs.length = ys.length →
    IsDeduct E Δ
    ((And_ (List.zipWith eq_ xs ys)).imp_
      ((pred_var_ name xs).imp_ (pred_var_ name ys)))

  /-
    Δ ⊢ ((x_0 = y_0) ∧ (x_1 = y_1)) →
          ((eq_ x_0 x_1) → (eq_ y_0 y_1))
  -/
  | eq_2_eq_
    (E : Env)
    (Δ : List Formula)
    (x_0 x_1 y_0 y_1 : VarName) :
    IsDeduct E Δ
    ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
      ((eq_ x_0 x_1).imp_ (eq_ y_0 y_1)))

  /-
    Δ ⊢ phi ⇒ Δ ⊢ ∀ v phi
    provided v is not free in any formula in Δ
  -/
  | gen_
    (E : Env)
    (Δ : List Formula)
    (v : VarName)
    (phi : Formula) :
    (∀ H : Formula, H ∈ Δ → ¬ isFreeIn v H) →
    IsDeduct E Δ phi →
    IsDeduct E Δ (forall_ v phi)

  /-
    Δ ⊢ phi → psi ⇒
    Δ ⊢ phi ⇒
    Δ ⊢ psi
  -/
  | mp_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ (phi.imp_ psi) →
    IsDeduct E Δ phi →
    IsDeduct E Δ psi

  /-
    Δ ⊢ ⊥ ↔ ¬ ⊤
  -/
  | def_false_
    (E : Env)
    (Δ : List Formula) :
    IsDeduct E Δ (false_.iff_ (not_ true_))

  /-
    Δ ⊢ (phi ∧ psi) ↔ ¬ (phi → ¬ psi)
  -/
  | def_and_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ ((phi.and_ psi).iff_ (not_ (phi.imp_ (not_ psi))))

  /-
    Δ ⊢ (phi ∨ psi) ↔ ((¬ phi) → psi)
  -/
  | def_or_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ ((phi.or_ psi).iff_ ((not_ phi).imp_ psi))

  /-
    ⊢ (phi ↔ psi) ↔ ((phi → psi) ∧ (psi → phi))
    ⊢ (phi ↔ psi) ↔ ¬ ((phi → psi) → ¬ (psi → phi))
    ⊢ ((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) ∧ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi))
    ⊢ ¬ (((phi ↔ psi) → (¬ ((phi → psi) → ¬ (psi → phi)))) → ¬ (¬ ((phi → psi) → ¬ (psi → phi)) → (phi ↔ psi)))
  -/
  | def_iff_
    (E : Env)
    (Δ : List Formula)
    (phi psi : Formula) :
    IsDeduct E Δ (not_ (((phi.iff_ psi).imp_ (not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi))))).imp_ (not_ ((not_ ((phi.imp_ psi).imp_ (not_ (psi.imp_ phi)))).imp_ (phi.iff_ psi)))))

  | add_def_
    (E : Env)
    (Δ : List Formula)
    (phi : Formula)
    (d : Definition) :
    (∀ d' : Definition, d' ∈ E → d.name = d'.name → d.args.length = d'.args.length → False) →
    d.F.all_def_in_env E →
    d.args.Nodup →
    (∀ v : VarName, isFreeIn v F → v ∈ d.args.toFinset) →
    d.F.predVarSet = ∅ →
    IsDeduct E Δ phi →
    IsDeduct (d :: E) Δ phi

  | unfold_def_
    (E : Env)
    (Δ : List Formula)
    (phi : Formula)
    (d : Definition) :
    d ∈ E →
    admitsUnfoldDef d phi →
    IsDeduct E Δ phi →
    IsDeduct E Δ (unfoldDef d phi)

  | pred_sub_
    (E : Env)
    (Δ : List Formula)
    (phi : Formula)
    (τ : PredName → ℕ → List VarName × Formula) :
    IsDeduct E Δ phi →
    admitsPredFun τ phi →
    (∀ H : Formula, H ∈ Δ → admitsPredFun τ H) →
    IsDeduct E (Δ.map (replacePredFun τ)) (replacePredFun τ phi)

  | thm
    (Δ Δ' : List Formula)
    (phi : Formula)
    (σ : Instantiation) :
    (∀ H : Formula, H ∈ Δ → IsDeduct E Δ' (replaceAllVar σ.1 H)) →
    IsDeduct E Δ phi →
    IsDeduct E Δ' (replaceAllVar σ.1 phi)
