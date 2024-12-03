import FOL.NV.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/-
[margaris]
pg. 48

An occurrence of a variable `v` in a formula `P` is bound if and only if it occurs in a subformula of `P` of the form `\forall v Q`. An occurrence of `v` in `P` is free if and only if it is not a bound occurrence. The variable `v` is free or bound in `P` according as it has a free or bound occurrence in `P`.
-/

/--
  `Formula_.var_set F` := The set of all of the variables that have an occurrence in the formula `F`.
-/
def Formula_.var_set : Formula_ → Finset VarName_
  | pred_const_ _ xs => xs.toFinset
  | pred_var_ _ xs => xs.toFinset
  | eq_ x y => {x, y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.var_set
  | imp_ phi psi => phi.var_set ∪ psi.var_set
  | and_ phi psi => phi.var_set ∪ psi.var_set
  | or_ phi psi => phi.var_set ∪ psi.var_set
  | iff_ phi psi => phi.var_set ∪ psi.var_set
  | forall_ x phi => phi.var_set ∪ {x}
  | exists_ x phi => phi.var_set ∪ {x}
  | def_ _ xs => xs.toFinset


/--
  `var_occurs_in v F` := True if and only if there is an occurrence of the variable `v` in the formula `F`.
-/
def var_occurs_in (v : VarName_) : Formula_ → Prop
  | pred_const_ _ xs => v ∈ xs
  | pred_var_ _ xs => v ∈ xs
  | eq_ x y => v = x ∨ v = y
  | true_ => False
  | false_ => False
  | not_ phi => var_occurs_in v phi
  | imp_ phi psi => var_occurs_in v phi ∨ var_occurs_in v psi
  | and_ phi psi => var_occurs_in v phi ∨ var_occurs_in v psi
  | or_ phi psi => var_occurs_in v phi ∨ var_occurs_in v psi
  | iff_ phi psi => var_occurs_in v phi ∨ var_occurs_in v psi
  | forall_ x phi => v = x ∨ var_occurs_in v phi
  | exists_ x phi => v = x ∨ var_occurs_in v phi
  | def_ _ xs => v ∈ xs

instance (v : VarName_) (F : Formula_) : Decidable (var_occurs_in v F) :=
  by
  induction F
  all_goals
    simp only [var_occurs_in]
    infer_instance


/--
  `Formula_.bound_var_set F` := The set of all of the variables that have a bound occurrence in the formula `F`.
-/
def Formula_.bound_var_set : Formula_ → Finset VarName_
  | pred_const_ _ _ => ∅
  | pred_var_ _ _ => ∅
  | eq_ _ _ => ∅
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.bound_var_set
  | imp_ phi psi => phi.bound_var_set ∪ psi.bound_var_set
  | and_ phi psi => phi.bound_var_set ∪ psi.bound_var_set
  | or_ phi psi => phi.bound_var_set ∪ psi.bound_var_set
  | iff_ phi psi => phi.bound_var_set ∪ psi.bound_var_set
  | forall_ x phi => phi.bound_var_set ∪ {x}
  | exists_ x phi => phi.bound_var_set ∪ {x}
  | def_ _ _ => ∅


/--
  `var_is_bound_in v F` := True if and only if there is a bound occurrence of the variable `v` in the formula `F`.
-/
def var_is_bound_in (v : VarName_) : Formula_ → Prop
  | pred_const_ _ _ => False
  | pred_var_ _ _ => False
  | eq_ _ _ => False
  | true_ => False
  | false_ => False
  | not_ phi => var_is_bound_in v phi
  | imp_ phi psi => var_is_bound_in v phi ∨ var_is_bound_in v psi
  | and_ phi psi => var_is_bound_in v phi ∨ var_is_bound_in v psi
  | or_ phi psi => var_is_bound_in v phi ∨ var_is_bound_in v psi
  | iff_ phi psi => var_is_bound_in v phi ∨ var_is_bound_in v psi
  | forall_ x phi => v = x ∨ var_is_bound_in v phi
  | exists_ x phi => v = x ∨ var_is_bound_in v phi
  | def_ _ _ => False

instance (v : VarName_) (F : Formula_) : Decidable (var_is_bound_in v F) :=
  by
  induction F
  all_goals
    simp only [var_is_bound_in]
    infer_instance


/--
  `Formula_.free_var_set F` := The set of all of the variables that have a free occurrence in the formula `F`.
-/
def Formula_.free_var_set : Formula_ → Finset VarName_
  | pred_const_ _ xs => xs.toFinset
  | pred_var_ _ xs => xs.toFinset
  | eq_ x y => {x, y}
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.free_var_set
  | imp_ phi psi => phi.free_var_set ∪ psi.free_var_set
  | and_ phi psi => phi.free_var_set ∪ psi.free_var_set
  | or_ phi psi => phi.free_var_set ∪ psi.free_var_set
  | iff_ phi psi => phi.free_var_set ∪ psi.free_var_set
  | forall_ x phi => phi.free_var_set \ {x}
  | exists_ x phi => phi.free_var_set \ {x}
  | def_ _ xs => xs.toFinset


/--
  `var_is_free_in v F` := True if and only if there is a free occurrence of the variable `v` in the formula `F`.
-/
def var_is_free_in (v : VarName_) : Formula_ → Prop
  | pred_const_ _ xs => v ∈ xs
  | pred_var_ _ xs => v ∈ xs
  | eq_ x y => v = x ∨ v = y
  | true_ => False
  | false_ => False
  | not_ phi => var_is_free_in v phi
  | imp_ phi psi => var_is_free_in v phi ∨ var_is_free_in v psi
  | and_ phi psi => var_is_free_in v phi ∨ var_is_free_in v psi
  | or_ phi psi => var_is_free_in v phi ∨ var_is_free_in v psi
  | iff_ phi psi => var_is_free_in v phi ∨ var_is_free_in v psi
  | forall_ x phi => ¬ v = x ∧ var_is_free_in v phi
  | exists_ x phi => ¬ v = x ∧ var_is_free_in v phi
  | def_ _ xs => v ∈ xs

instance (v : VarName_) (F : Formula_) : Decidable (var_is_free_in v F) :=
  by
  induction F
  all_goals
    simp only [var_is_free_in]
    infer_instance


/--
  `Formula_.pred_var_set F` := The set of all of the predicate variables that have an occurrence in the formula `F`.
-/
def Formula_.pred_var_set : Formula_ → Finset (PredName_ × ℕ)
  | pred_const_ _ _ => ∅
  | pred_var_ X xs => {(X, xs.length)}
  | eq_ _ _ => ∅
  | true_ => ∅
  | false_ => ∅
  | not_ phi => phi.pred_var_set
  | imp_ phi psi => phi.pred_var_set ∪ psi.pred_var_set
  | and_ phi psi => phi.pred_var_set ∪ psi.pred_var_set
  | or_ phi psi => phi.pred_var_set ∪ psi.pred_var_set
  | iff_ phi psi => phi.pred_var_set ∪ psi.pred_var_set
  | forall_ _ phi => phi.pred_var_set
  | exists_ _ phi => phi.pred_var_set
  | def_ _ _ => ∅


/--
  `pred_var_occurs_in P n F` := True if and only if there is an occurrence of the predicate variable named `P` of arity `n` in the formula `F`.
-/
def pred_var_occurs_in (P : PredName_) (n : ℕ) : Formula_ → Prop
  | pred_const_ _ _ => False
  | pred_var_ X xs => P = X ∧ n = xs.length
  | eq_ _ _ => False
  | true_ => False
  | false_ => False
  | not_ phi => pred_var_occurs_in P n phi
  | imp_ phi psi => pred_var_occurs_in P n phi ∨ pred_var_occurs_in P n psi
  | and_ phi psi => pred_var_occurs_in P n phi ∨ pred_var_occurs_in P n psi
  | or_ phi psi => pred_var_occurs_in P n phi ∨ pred_var_occurs_in P n psi
  | iff_ phi psi => pred_var_occurs_in P n phi ∨ pred_var_occurs_in P n psi
  | forall_ _ phi => pred_var_occurs_in P n phi
  | exists_ _ phi => pred_var_occurs_in P n phi
  | def_ _ _ => False

instance (P : PredName_) (n : ℕ) (F : Formula_) : Decidable (pred_var_occurs_in P n F) :=
  by
  induction F
  all_goals
    simp only [pred_var_occurs_in]
    infer_instance

-------------------------------------------------------------------------------

theorem var_occurs_in_iff_mem_var_set
  (v : VarName_)
  (F : Formula_) :
  var_occurs_in v F ↔ v ∈ F.var_set :=
  by
  induction F
  all_goals
    simp only [var_occurs_in]
    simp only [var_set]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem var_is_bound_in_iff_mem_bound_var_set
  (v : VarName_)
  (F : Formula_) :
  var_is_bound_in v F ↔ v ∈ F.bound_var_set :=
  by
  induction F
  all_goals
    simp only [var_is_bound_in]
    simp only [bound_var_set]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem var_is_free_in_iff_mem_free_var_set
  (v : VarName_)
  (F : Formula_) :
  var_is_free_in v F ↔ v ∈ F.free_var_set :=
  by
  induction F
  all_goals
    simp only [var_is_free_in]
    simp only [free_var_set]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    tauto


theorem pred_var_occurs_in_iff_mem_pred_var_set
  (P : PredName_)
  (n : ℕ)
  (F : Formula_) :
  pred_var_occurs_in P n F ↔ (P, n) ∈ F.pred_var_set :=
  by
  induction F
  all_goals
    simp only [pred_var_occurs_in]
    simp only [pred_var_set]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
  case eq_ x y =>
    simp
  case true_ | false_ =>
    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    tauto

-------------------------------------------------------------------------------

theorem var_is_bound_in_imp_var_occurs_in
  (v : VarName_)
  (F : Formula_)
  (h1 : var_is_bound_in v F) :
  var_occurs_in v F :=
  by
  induction F
  all_goals
    simp only [var_is_bound_in] at h1
  all_goals
    simp only [var_occurs_in]
    tauto


theorem var_is_free_in_imp_var_occurs_in
  (v : VarName_)
  (F : Formula_)
  (h1 : var_is_free_in v F) :
  var_occurs_in v F :=
  by
  induction F
  all_goals
    simp only [var_is_free_in] at h1
  all_goals
    simp only [var_occurs_in]
    tauto


theorem var_occurs_in_imp_var_is_bound_in_or_var_is_free_in
  (v : VarName_)
  (F : Formula_)
  (h1 : var_occurs_in v F) :
  var_is_bound_in v F ∨ var_is_free_in v F :=
  by
  induction F
  all_goals
    simp only [var_occurs_in] at h1
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp only [var_is_free_in]
    right
    exact h1
  case eq_ x y =>
    simp only [var_is_free_in]
    right
    exact h1
  case not_ phi phi_ih =>
    simp only [var_is_bound_in]
    simp only [var_is_free_in]
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [var_is_bound_in]
    simp only [var_is_free_in]
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [var_is_bound_in]
    simp only [var_is_free_in]
    tauto


theorem var_occurs_in_iff_var_is_bound_in_or_var_is_free_in
  (v : VarName_)
  (F : Formula_) :
  var_occurs_in v F ↔ var_is_bound_in v F ∨ var_is_free_in v F :=
  by
  constructor
  · intro a1
    apply var_occurs_in_imp_var_is_bound_in_or_var_is_free_in
    exact a1
  · intro a1
    cases a1
    case _ c1 =>
      apply var_is_bound_in_imp_var_occurs_in
      exact c1
    case _ c1 =>
      apply var_is_free_in_imp_var_occurs_in
      exact c1

-------------------------------------------------------------------------------

theorem mem_var_set_iff_mem_bound_var_set_or_mem_free_var_set
  (v : VarName_)
  (F : Formula_) :
  v ∈ F.var_set ↔ v ∈ F.bound_var_set ∨ v ∈ F.free_var_set :=
  by
  rw [← var_occurs_in_iff_mem_var_set]
  rw [← var_is_bound_in_iff_mem_bound_var_set]
  rw [← var_is_free_in_iff_mem_free_var_set]
  apply var_occurs_in_iff_var_is_bound_in_or_var_is_free_in

-------------------------------------------------------------------------------

/--
  `var_is_free_in_ind v F` := True if and only if there is a free occurrence of the variable `v` in the formula `F`.
-/
inductive var_is_free_in_ind
  (v : VarName_) :
  Formula_ → Prop

  | pred_const_
    (X : PredName_)
    (xs : List VarName_) :
    v ∈ xs →
    var_is_free_in_ind v (pred_const_ X xs)

  | pred_var_
    (X : PredName_)
    (xs : List VarName_) :
    v ∈ xs →
    var_is_free_in_ind v (pred_var_ X xs)

  | eq_
    (x y : VarName_) :
    v = x ∨ v = y →
    var_is_free_in_ind v (eq_ x y)

  | not_
    (phi : Formula_) :
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (not_ phi)

  | imp_left_
    (phi psi : Formula_) :
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (imp_ phi psi)

  | imp_right_
    (phi psi : Formula_) :
    var_is_free_in_ind v psi →
    var_is_free_in_ind v (imp_ phi psi)

  | and_left_
    (phi psi : Formula_) :
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (and_ phi psi)

  | and_right_
    (phi psi : Formula_) :
    var_is_free_in_ind v psi →
    var_is_free_in_ind v (and_ phi psi)

  | or_left_
    (phi psi : Formula_) :
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (or_ phi psi)

  | or_right_
    (phi psi : Formula_) :
    var_is_free_in_ind v psi →
    var_is_free_in_ind v (or_ phi psi)

  | iff_left_
    (phi psi : Formula_) :
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (iff_ phi psi)

  | iff_right_
    (phi psi : Formula_) :
    var_is_free_in_ind v psi →
    var_is_free_in_ind v (iff_ phi psi)

  | forall_
    (x : VarName_)
    (phi : Formula_) :
    ¬ v = x →
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (forall_ x phi)

  | exists_
    (x : VarName_)
    (phi : Formula_) :
    ¬ v = x →
    var_is_free_in_ind v phi →
    var_is_free_in_ind v (exists_ x phi)

  | def_
    (X : DefName_)
    (xs : List VarName_) :
    v ∈ xs →
    var_is_free_in_ind v (def_ X xs)


theorem var_is_free_in_imp_var_is_free_in_ind
  (v : VarName_)
  (F : Formula_)
  (h1 : var_is_free_in v F) :
  var_is_free_in_ind v F :=
  by
  induction F
  any_goals
    simp only [var_is_free_in] at h1
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    first
      | apply var_is_free_in_ind.pred_const_
      | apply var_is_free_in_ind.pred_var_
      | apply var_is_free_in_ind.eq_
      | apply var_is_free_in_ind.def_
    exact h1
  case not_ phi phi_ih =>
    apply var_is_free_in_ind.not_
    exact phi_ih h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    cases h1
    case inl c1 =>
      first
        | apply var_is_free_in_ind.imp_left_
        | apply var_is_free_in_ind.and_left_
        | apply var_is_free_in_ind.or_left_
        | apply var_is_free_in_ind.iff_left_
      exact phi_ih c1
    case inr c1 =>
      first
        | apply var_is_free_in_ind.imp_right_
        | apply var_is_free_in_ind.and_right_
        | apply var_is_free_in_ind.or_right_
        | apply var_is_free_in_ind.iff_right_
      exact psi_ih c1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h1
    case _ h1_left h1_right =>
      first
        | apply var_is_free_in_ind.forall_
        | apply var_is_free_in_ind.exists_
      · exact h1_left
      · exact phi_ih h1_right


theorem var_is_free_in_ind_imp_var_is_free_in
  (v : VarName_)
  (F : Formula_)
  (h1 : var_is_free_in_ind v F) :
  var_is_free_in v F :=
  by
  induction h1
  all_goals
    simp only [var_is_free_in]
    tauto


theorem var_is_free_in_iff_var_is_free_in_ind
  (v : VarName_)
  (F : Formula_) :
  var_is_free_in v F ↔ var_is_free_in_ind v F :=
  by
  constructor
  · apply var_is_free_in_imp_var_is_free_in_ind
  · apply var_is_free_in_ind_imp_var_is_free_in


#lint
