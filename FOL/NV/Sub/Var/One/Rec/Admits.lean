import MathlibExtra.Finset
import FOL.NV.Semantics
import FOL.NV.Sub.Var.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Rec

open Formula_


/-
[margaris]
pg. 48

If `v` and `u` are variables and `P` is a formula, then `P` admits `u` for `v` if and only if there is no free occurrence of `v` in `P` that becomes a bound occurrence of `u` in `P(u/v)`. If `t` is a term, then `P` admits `t` for `v` if and only if `P` admits for `v` every variable in `t`.
-/
/--
  Helper function for `admits_var_one_rec`.
-/
def admits_var_one_rec_aux (v u : VarName_) (binders : Finset VarName_) : Formula_ → Prop
  | pred_const_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`
  | pred_var_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`
  | eq_ x y =>
      (v = x ∨ v = y) ∧ v ∉ binders → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`
  | true_ => True
  | false_ => True
  | not_ phi => admits_var_one_rec_aux v u binders phi
  | imp_ phi psi =>
      admits_var_one_rec_aux v u binders phi ∧ admits_var_one_rec_aux v u binders psi
  | and_ phi psi =>
      admits_var_one_rec_aux v u binders phi ∧ admits_var_one_rec_aux v u binders psi
  | or_ phi psi =>
      admits_var_one_rec_aux v u binders phi ∧ admits_var_one_rec_aux v u binders psi
  | iff_ phi psi =>
      admits_var_one_rec_aux v u binders phi ∧ admits_var_one_rec_aux v u binders psi
  | forall_ x phi => admits_var_one_rec_aux v u (binders ∪ {x}) phi
  | exists_ x phi => admits_var_one_rec_aux v u (binders ∪ {x}) phi
  | def_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`

instance
  (v u : VarName_)
  (binders : Finset VarName_)
  (F : Formula_) :
  Decidable (admits_var_one_rec_aux v u binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [admits_var_one_rec_aux]
    infer_instance


/--
  `admits_var_one_rec v u P` := True if and only if there is no free occurrence of the variable `v` in the formula `P` that becomes a bound occurrence of the variable `u` in `P(u/v)`.

  `P` admits `u` for `v`

  `v → u` in `P`
-/
def admits_var_one_rec (v u : VarName_) (F : Formula_) : Prop :=
  admits_var_one_rec_aux v u ∅ F

instance
  (v u : VarName_)
  (F : Formula_) :
  Decidable (admits_var_one_rec v u F) :=
  by
  simp only [admits_var_one_rec]
  infer_instance


/--
  Helper function for `fast_admits_var_one_rec`.
-/
def fast_admits_var_one_rec_aux (v u : VarName_) (binders : Finset VarName_) : Formula_ → Prop
  | pred_const_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`
  | pred_var_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`
  | eq_ x y =>
      (v = x ∨ v = y) → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`
  | true_ => True
  | false_ => True
  | not_ phi => fast_admits_var_one_rec_aux v u binders phi
  | imp_ phi psi =>
      fast_admits_var_one_rec_aux v u binders phi ∧ fast_admits_var_one_rec_aux v u binders psi
  | and_ phi psi =>
      fast_admits_var_one_rec_aux v u binders phi ∧ fast_admits_var_one_rec_aux v u binders psi
  | or_ phi psi =>
      fast_admits_var_one_rec_aux v u binders phi ∧ fast_admits_var_one_rec_aux v u binders psi
  | iff_ phi psi =>
      fast_admits_var_one_rec_aux v u binders phi ∧ fast_admits_var_one_rec_aux v u binders psi
  | forall_ x phi => v = x ∨ fast_admits_var_one_rec_aux v u (binders ∪ {x}) phi
  | exists_ x phi => v = x ∨ fast_admits_var_one_rec_aux v u (binders ∪ {x}) phi
  | def_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of `v` in `P`
        u ∉ binders -- then it does not become a bound occurrence of `u` in `P(u/v)`

instance
  (v u : VarName_)
  (binders : Finset VarName_)
  (F : Formula_) :
  Decidable (fast_admits_var_one_rec_aux v u binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [fast_admits_var_one_rec_aux]
    infer_instance


/--
  `fast_admits_var_one_rec v u P` := True if and only if there is no free occurrence of the variable `v` in the formula `P` that becomes a bound occurrence of the variable `u` in `P(u/v)`.

  `P` admits `u` for `v`

  `v → u` in `P`

  This is a more efficient version of `admits_var_one_rec`.
-/
def fast_admits_var_one_rec (v u : VarName_) (F : Formula_) : Prop :=
  fast_admits_var_one_rec_aux v u ∅ F

instance
  (v u : VarName_)
  (F : Formula_) :
  Decidable (fast_admits_var_one_rec v u F) :=
  by
  simp only [fast_admits_var_one_rec]
  infer_instance


/--
  Used to label each occurrence of a variable in a formula as free or bound.
-/
inductive BoolFormula : Type
  | pred_const_ : PredName_ → List Bool → BoolFormula
  | pred_var_ : PredName_ → List Bool → BoolFormula
  | eq_ : Bool → Bool → BoolFormula
  | true_ : BoolFormula
  | false_ : BoolFormula
  | not_ : BoolFormula → BoolFormula
  | imp_ : BoolFormula → BoolFormula → BoolFormula
  | and_ : BoolFormula → BoolFormula → BoolFormula
  | or_ : BoolFormula → BoolFormula → BoolFormula
  | iff_ : BoolFormula → BoolFormula → BoolFormula
  | forall_ : Bool → BoolFormula → BoolFormula
  | exists_ : Bool → BoolFormula → BoolFormula
  | def_ : DefName_ → List Bool → BoolFormula
  deriving Inhabited, DecidableEq


/--
  Helper function for `to_is_bound_var_one_rec`.
-/
def to_is_bound_var_one_rec_aux (binders : Finset VarName_) : Formula_ → BoolFormula
  | pred_const_ X xs =>
      BoolFormula.pred_const_ X (xs.map fun (v : VarName_) => v ∈ binders)

  | pred_var_ X xs =>
      BoolFormula.pred_var_ X (xs.map fun (v : VarName_) => v ∈ binders)

  | eq_ x y =>
      BoolFormula.eq_ (x ∈ binders) (y ∈ binders)

  | true_ => BoolFormula.true_

  | false_ => BoolFormula.false_

  | not_ phi => BoolFormula.not_ (to_is_bound_var_one_rec_aux binders phi)

  | imp_ phi psi =>
      BoolFormula.imp_ (to_is_bound_var_one_rec_aux binders phi) (to_is_bound_var_one_rec_aux binders psi)

  | and_ phi psi =>
      BoolFormula.and_ (to_is_bound_var_one_rec_aux binders phi) (to_is_bound_var_one_rec_aux binders psi)

  | or_ phi psi =>
      BoolFormula.or_ (to_is_bound_var_one_rec_aux binders phi) (to_is_bound_var_one_rec_aux binders psi)

  | iff_ phi psi =>
      BoolFormula.iff_ (to_is_bound_var_one_rec_aux binders phi) (to_is_bound_var_one_rec_aux binders psi)

  | forall_ x phi =>
      BoolFormula.forall_ True (to_is_bound_var_one_rec_aux (binders ∪ {x}) phi)

  | exists_ x phi =>
      BoolFormula.forall_ True (to_is_bound_var_one_rec_aux (binders ∪ {x}) phi)

  | def_ X xs =>
      BoolFormula.def_ X (xs.map fun (v : VarName_) => v ∈ binders)

/--
  Creates a `BoolFormula` from a formula. Each bound occurence of a variable in the formula is mapped to true in the bool formula. Each free occurence of a variable in the formula is mapped to false in the bool formula.
-/
def to_is_bound_var_one_rec (F : Formula_) : BoolFormula :=
  to_is_bound_var_one_rec_aux ∅ F


-- `admits_var_one_rec` ↔ `fast_admits_var_one_rec`

theorem admits_var_one_rec_aux_imp_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders)
  (h2 : admits_var_one_rec_aux v u binders F) :
  fast_admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [admits_var_one_rec_aux] at h2

    simp only [fast_admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    by_cases c1 : v = x
    · left
      exact c1
    · right
      apply phi_ih
      · simp
        tauto
      · exact h2
  all_goals
    tauto


theorem mem_binders_imp_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∈ binders) :
  admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    apply phi_ih
    simp
    left
    exact h1
  all_goals
    tauto


theorem fast_admits_var_one_rec_aux_imp_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : fast_admits_var_one_rec_aux v u binders F) :
  admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [fast_admits_var_one_rec_aux] at h1

    simp only [admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h1
    case inl h1 =>
      apply mem_binders_imp_admits_var_one_rec_aux
      subst h1
      simp
    case inr h1 =>
      apply phi_ih
      exact h1
  all_goals
    tauto


theorem admits_var_one_rec_iff_fast_admits_var_one_rec
  (F : Formula_)
  (v u : VarName_) :
  admits_var_one_rec v u F ↔ fast_admits_var_one_rec v u F :=
  by
  simp only [admits_var_one_rec]
  simp only [fast_admits_var_one_rec]
  constructor
  · apply admits_var_one_rec_aux_imp_fast_admits_var_one_rec_aux
    simp
  · apply fast_admits_var_one_rec_aux_imp_admits_var_one_rec_aux


-- `fast_admits_var_one_rec`

theorem fast_admits_var_one_rec_aux_self
  (F : Formula_)
  (v : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders) :
  fast_admits_var_one_rec_aux v v binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [fast_admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    by_cases c1 : v = x
    · left
      exact c1
    · right
      apply phi_ih
      simp
      tauto
  all_goals
    tauto


theorem fast_admits_var_one_rec_self
  (F : Formula_)
  (v : VarName_) :
  fast_admits_var_one_rec v v F :=
  by
  simp only [fast_admits_var_one_rec]
  apply fast_admits_var_one_rec_aux_self
  simp

--

theorem not_var_is_free_in_imp_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_is_free_in v F) :
  fast_admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_is_free_in] at h1

    simp only [fast_admits_var_one_rec_aux]
  all_goals
    tauto


theorem not_var_is_free_in_imp_fast_admits_var_one_rec
  (F : Formula_)
  (v u : VarName_)
  (h1 : ¬ var_is_free_in v F) :
  fast_admits_var_one_rec v u F :=
  by
  simp only [fast_admits_var_one_rec]
  apply not_var_is_free_in_imp_fast_admits_var_one_rec_aux
  exact h1

--

theorem not_var_is_bound_in_imp_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_is_bound_in u F)
  (h2 : u ∉ binders) :
  fast_admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_is_bound_in] at h1

    simp only [fast_admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    right
    apply phi_ih
    · exact h1_right
    · simp
      tauto
  all_goals
    tauto


theorem not_var_is_bound_in_imp_fast_admits_var_one_rec
  (F : Formula_)
  (v u : VarName_)
  (h1 : ¬ var_is_bound_in u F) :
  fast_admits_var_one_rec v u F :=
  by
  simp only [fast_admits_var_one_rec]
  apply not_var_is_bound_in_imp_fast_admits_var_one_rec_aux F v u ∅ h1
  simp

--

theorem fast_replace_free_var_one_rec_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_occurs_in t F)
  (h2 : v ∉ binders) :
  fast_admits_var_one_rec_aux t v binders (fast_replace_free_var_one_rec v t F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_occurs_in] at h1

    simp only [fast_replace_free_var_one_rec]
  any_goals
    simp only [fast_admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    split_ifs
    case pos c1 =>
      simp only [fast_admits_var_one_rec_aux]
      subst c1
      right
      apply not_var_is_free_in_imp_fast_admits_var_one_rec_aux
      intro contra
      apply h1_right
      apply var_is_free_in_imp_var_occurs_in
      exact contra
    case neg c1 =>
      simp only [fast_admits_var_one_rec_aux]
      right
      apply phi_ih
      · exact h1_right
      · simp
        tauto
  all_goals
    tauto


theorem fast_replace_free_var_one_rec_fast_admits_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in t F) :
  fast_admits_var_one_rec t v (fast_replace_free_var_one_rec v t F) :=
  by
  simp only [fast_admits_var_one_rec]
  apply fast_replace_free_var_one_rec_fast_admits_var_one_rec_aux
  · exact h1
  · simp

--

theorem replace_free_var_one_rec_aux_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_occurs_in t F) :
  fast_admits_var_one_rec_aux t v binders (replace_free_var_one_rec_aux v t binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_occurs_in] at h1

    simp only [replace_free_var_one_rec_aux]
    simp only [fast_admits_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x a1 a2
    by_cases c1 : v = x ∧ x ∉ binders
    · obtain ⟨c1_left, c1_right⟩ := c1
      rw [c1_left]
      exact c1_right
    · push_neg at c1
      specialize a2 c1
      rw [a2] at a1
      contradiction
  case eq_ x y =>
    intros a1
    split_ifs at a1
    case _ c1 c2 =>
      obtain ⟨c1_left, c1_right⟩ := c1
      rw [c1_left]
      exact c1_right
    case _ c1 c2 =>
      obtain ⟨c1_left, c1_right⟩ := c1
      rw [c1_left]
      exact c1_right
    case _ c1 c2 =>
      obtain ⟨c2_left, c2_right⟩ := c2
      rw [c2_left]
      exact c2_right
    case _ c1 c2 =>
      tauto
  all_goals
    tauto


theorem replace_free_var_one_rec_fast_admits_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in t F) :
  fast_admits_var_one_rec t v (replace_free_var_one_rec v t F) :=
  by
  simp only [replace_free_var_one_rec]
  simp only [fast_admits_var_one_rec]
  apply replace_free_var_one_rec_aux_fast_admits_var_one_rec_aux
  exact h1

--

theorem fast_admits_var_one_rec_aux_add_binders
  (F : Formula_)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : fast_admits_var_one_rec_aux v u S F)
  (h2 : u ∉ T) :
  fast_admits_var_one_rec_aux v u (S ∪ T) F :=
  by
  induction F generalizing S
  all_goals
    simp only [fast_admits_var_one_rec_aux] at h1

    simp only [fast_admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    cases h1
    case inl h1 =>
      tauto
    case inr h1 =>
      right
      simp only [Finset.union_right_comm_assoc]
      apply phi_ih
      exact h1
  any_goals
    simp only [Finset.mem_union]
  all_goals
    tauto


theorem fast_admits_var_one_rec_aux_del_binders
  (F : Formula_)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : fast_admits_var_one_rec_aux v u (S ∪ T) F) :
  fast_admits_var_one_rec_aux v u S F :=
  by
  induction F generalizing S
  all_goals
    simp only [fast_admits_var_one_rec_aux] at h1

    simp only [fast_admits_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp at h1

    tauto
  case eq_ x y =>
    simp at h1

    tauto
  case not_ phi phi_ih =>
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [Finset.union_right_comm S T {x}] at h1

    tauto

--

theorem fast_admits_var_one_rec_aux_var_is_free_in
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : fast_admits_var_one_rec_aux v u binders F)
  (h2 : var_is_free_in v F) :
  u ∉ binders :=
  by
  induction F generalizing binders
  all_goals
    simp only [fast_admits_var_one_rec_aux] at h1

    simp only [var_is_free_in] at h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    obtain ⟨h2_left, h2_right⟩ := h2
    cases h1
    case inl h1 =>
      contradiction
    case inr h1 =>
      apply phi_ih
      · exact fast_admits_var_one_rec_aux_del_binders phi v u binders {x} h1
      · exact h2_right
  all_goals
    tauto


theorem fast_admits_var_one_rec_aux_mem_binders
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : fast_admits_var_one_rec_aux v u binders F)
  (h2 : u ∈ binders) :
  ¬ var_is_free_in v F :=
  by
  contrapose! h2
  exact fast_admits_var_one_rec_aux_var_is_free_in F v u binders h1 h2

--

theorem fast_admits_var_one_rec_aux_imp_free_and_bound_unchanged
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders)
  (h2 : fast_admits_var_one_rec_aux v u binders F) :
  to_is_bound_var_one_rec_aux binders F =
    to_is_bound_var_one_rec_aux binders (fast_replace_free_var_one_rec v u F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [fast_admits_var_one_rec_aux] at h2

    simp only [fast_replace_free_var_one_rec]
  any_goals
    simp only [to_is_bound_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x a1
    by_cases c1 : v = x
    · subst c1
      simp
      tauto
    · simp only [if_neg c1]
  case eq_ x y =>
    simp
    constructor
    case left | right =>
      split_ifs
      case pos c1 =>
        subst c1
        tauto
      case neg c1 =>
        rfl
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
    split_ifs
    case pos c1 =>
      rfl
    case neg c1 =>
      simp only [to_is_bound_var_one_rec_aux]
      simp
      apply phi_ih
      · simp
        tauto
      · tauto


theorem free_and_bound_unchanged_imp_fast_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders)
  (h2 : to_is_bound_var_one_rec_aux binders F =
    to_is_bound_var_one_rec_aux binders (fast_replace_free_var_one_rec v u F)) :
  fast_admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [fast_replace_free_var_one_rec] at h2

    simp only [fast_admits_var_one_rec_aux]
  any_goals
    simp only [to_is_bound_var_one_rec_aux] at h2
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp at h2

    intro a1
    specialize h2 v a1
    simp at h2
    tauto
  case eq_ x y =>
    simp at h2

    obtain ⟨h2_left, h2_right⟩ := h2
    intros a1
    cases a1
    case inl a1 =>
      subst a1
      simp at h2_left
      tauto
    case inr a1 =>
      subst a1
      simp at h2_right
      tauto
  case not_ phi phi_ih =>
    simp at h2

    apply phi_ih
    · exact h1
    · exact h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp at h2

    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    split_ifs at h2
    case pos c1 =>
      left
      exact c1
    case neg c1 =>
      right
      apply phi_ih
      · simp
        tauto
      · simp only [to_is_bound_var_one_rec_aux] at h2
        simp at h2
        exact h2


example
  (F : Formula_)
  (v u : VarName_) :
  fast_admits_var_one_rec v u F ↔
    to_is_bound_var_one_rec F = to_is_bound_var_one_rec (fast_replace_free_var_one_rec v u F) :=
  by
  simp only [fast_admits_var_one_rec]
  simp only [to_is_bound_var_one_rec]
  constructor
  · apply fast_admits_var_one_rec_aux_imp_free_and_bound_unchanged
    simp
  · apply free_and_bound_unchanged_imp_fast_admits_var_one_rec_aux
    simp


-- admits

theorem admits_var_one_rec_aux_self
  (F : Formula_)
  (v : VarName_)
  (binders : Finset VarName_) :
  admits_var_one_rec_aux v v binders F := by
  induction F generalizing binders
  all_goals
    simp only [admits_var_one_rec_aux]
  all_goals
    tauto


theorem admits_var_one_rec_self
  (F : Formula_)
  (v : VarName_) :
  admits_var_one_rec v v F :=
  by
  simp only [admits_var_one_rec]
  apply admits_var_one_rec_aux_self

--

theorem not_var_is_free_in_imp_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_is_free_in v F) :
  admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_is_free_in] at h1

    simp only [admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    by_cases c1 : v = x
    · apply mem_binders_imp_admits_var_one_rec_aux
      simp
      tauto
    · apply phi_ih
      tauto
  all_goals
    tauto


theorem not_var_is_free_in_imp_admits_var_one_rec
  (F : Formula_)
  (v u : VarName_)
  (h1 : ¬ var_is_free_in v F) :
  admits_var_one_rec v u F :=
  by
  simp only [admits_var_one_rec]
  apply not_var_is_free_in_imp_admits_var_one_rec_aux
  exact h1

--

theorem not_var_is_bound_in_imp_admits_var_one_rec_aux
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_is_bound_in u F)
  (h2 : u ∉ binders) :
  admits_var_one_rec_aux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_is_bound_in] at h1

    simp only [admits_var_one_rec_aux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    apply phi_ih
    · exact h1_right
    · simp
      tauto
  all_goals
    tauto


theorem not_var_is_bound_in_imp_admits_var_one_rec
  (F : Formula_)
  (v u : VarName_)
  (h1 : ¬ var_is_bound_in u F) :
  admits_var_one_rec v u F :=
  by
  simp only [admits_var_one_rec]
  apply not_var_is_bound_in_imp_admits_var_one_rec_aux
  · exact h1
  · simp

--

theorem replace_free_var_one_rec_aux_admits_var_one_rec_aux
  (F : Formula_)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_occurs_in t F) :
  admits_var_one_rec_aux t v binders (replace_free_var_one_rec_aux v t binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_occurs_in] at h1

    simp only [replace_free_var_one_rec_aux]
    simp only [admits_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x a1 a2 a3
    by_cases c1 : v = x ∧ x ∉ binders
    case pos =>
      obtain ⟨c1_left, c1_right⟩ := c1
      rw [c1_left]
      exact c1_right
    case neg =>
      simp at c1
      specialize a2 c1
      rw [a2] at a1
      contradiction
  case eq_ x y =>
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    intro a1
    split_ifs at a1
    case _ c1 c2 =>
      obtain ⟨c1_left, c1_right⟩ := c1
      rw [c1_left]
      exact c1_right
    case _ c1 c2 =>
      obtain ⟨c1_left, c1_right⟩ := c1
      rw [c1_left]
      exact c1_right
    case _ c1 c2 =>
      obtain ⟨c2_left, c2_right⟩ := c2
      rw [c2_left]
      exact c2_right
    case _ c1 c2 =>
      tauto
  all_goals
    tauto


theorem replace_free_var_one_rec_admits_var_one_rec
  (F : Formula_)
  (v t : VarName_)
  (h1 : ¬ var_occurs_in t F) :
  admits_var_one_rec t v (replace_free_var_one_rec v t F) :=
  by
  simp only [replace_free_var_one_rec]
  simp only [admits_var_one_rec]
  apply replace_free_var_one_rec_aux_admits_var_one_rec_aux
  exact h1

--

theorem admits_var_one_rec_aux_add_binders
  (F : Formula_)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : admits_var_one_rec_aux v u S F)
  (h2 : u ∉ T) :
  admits_var_one_rec_aux v u (S ∪ T) F :=
  by
  induction F generalizing S
  all_goals
    simp only [admits_var_one_rec_aux] at h1

    simp only [admits_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | eq_ x y |def_ X xs =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [Finset.union_right_comm S T {x}]
    tauto
  all_goals
    tauto


theorem admits_var_one_rec_aux_del_binders
  (F : Formula_)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : admits_var_one_rec_aux v u (S ∪ T) F)
  (h2 : v ∉ T) :
  admits_var_one_rec_aux v u S F :=
  by
  induction F generalizing S
  all_goals
    simp only [admits_var_one_rec_aux] at h1

    simp only [admits_var_one_rec_aux]
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    simp at h1

    tauto
  case not_ phi phi_ih =>
    apply phi_ih
    exact h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [Finset.union_right_comm S T {x}] at h1

    tauto


theorem admits_var_one_rec_aux_var_is_free_in
  (F : Formula_)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : admits_var_one_rec_aux v u binders F)
  (h2 : var_is_free_in v F)
  (h3 : v ∉ binders) :
  u ∉ binders :=
  by
  induction F generalizing binders
  all_goals
    simp only [admits_var_one_rec_aux] at h1

    simp only [var_is_free_in] at h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    obtain ⟨h2_left, h2_right⟩ := h2
    apply phi_ih
    · apply admits_var_one_rec_aux_del_binders phi v u binders {x}
      · exact h1
      · simp
        exact h2_left
    · exact h2_right
    · exact h3
  all_goals
    tauto


theorem substitution_theorem_fast_admits_var_one_rec_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env_)
  (v t : VarName_)
  (binders : Finset VarName_)
  (F : Formula_)
  (h1 : fast_admits_var_one_rec_aux v t binders F)
  (h2 : ∀ (v : VarName_), ¬ v ∈ binders → V' v = V v) :
  holds D I (Function.updateITE V v (V' t)) E F ↔
    holds D I V E (fast_replace_free_var_one_rec v t F) :=
  by
  induction E generalizing F binders V
  all_goals
    induction F generalizing binders V
    all_goals
      simp only [fast_admits_var_one_rec_aux] at h1

      simp only [fast_replace_free_var_one_rec]
      simp only [holds]
    case pred_const_ X xs | pred_var_ X xs =>
      simp
      congr! 1
      simp only [List.map_eq_map_iff]
      intro x a1
      simp
      simp only [Function.updateITE]
      split_ifs
      case _ c1 c2 =>
        subst c1
        tauto
      case _ c1 c2 =>
        subst c1
        contradiction
      case _ c1 c2 =>
        subst c2
        contradiction
      case _ c1 c2 =>
        rfl
    case eq_ x y =>
      simp only [Function.updateITE]
      simp only [eq_comm]
      congr! 1
      all_goals
        split_ifs
        case _ c1 =>
          subst c1
          tauto
        case _ c1 =>
          rfl
    case not_ phi phi_ih =>
      congr! 1
      exact phi_ih V binders h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      obtain ⟨h1_left, h1_right⟩ := h1
      congr! 1
      · exact phi_ih V binders h1_left h2
      · exact psi_ih V binders h1_right h2
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      split_ifs
      case _ c1 =>
        subst c1
        simp only [holds]
        first | apply forall_congr' | apply exists_congr
        intro d

        congr! 1
        funext x
        simp only [Function.updateITE]
        split_ifs <;> rfl
      case _ c1 =>
        simp only [holds]
        first | apply forall_congr' | apply exists_congr
        intro d

        cases h1
        case inl h1 =>
          contradiction
        case inr h1 =>
          simp only [Function.updateITE_comm V v x d (V' t) c1]
          apply phi_ih (Function.updateITE V x d) (binders ∪ {x}) h1
          simp only [Function.updateITE]
          simp
          intros v' a1 a2
          simp only [if_neg a2]
          apply h2
          exact a1

  case cons.def_ hd tl ih X xs =>
    unfold Function.updateITE
    congr! 1
    case _ =>
      simp
    case _ c1 =>
      apply holds_coincide_var
      intro v' a1
      simp
      simp only [eq_comm]

      have s1 :
        (List.map (fun (x : VarName_) =>
          if v = x then V' t else V x) xs) =
            (List.map (V ∘ fun (x : VarName_) =>
              if v = x then t else x) xs) :=
      by
        simp only [List.map_eq_map_iff]
        intro x a2
        simp
        split_ifs
        case _ c2 =>
          apply h2
          subst c2
          apply h1
          exact a2
        case _ c2 =>
          rfl

      simp only [s1]
      apply Function.updateListITE_mem_eq_len
      · simp only [var_is_free_in_iff_mem_free_var_set] at a1
        simp only [← List.mem_toFinset]
        exact Finset.mem_of_subset hd.h1 a1
      · simp at c1
        simp
        tauto
    case _ _ =>
      apply ih V binders
      · simp only [fast_admits_var_one_rec_aux]
        exact h1
      · exact h2


theorem substitution_theorem_fast_admits_var_one_rec
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (v t : VarName_)
  (F : Formula_)
  (h1 : fast_admits_var_one_rec v t F) :
  holds D I (Function.updateITE V v (V t)) E F ↔
    holds D I V E (fast_replace_free_var_one_rec v t F) :=
  by
  simp only [fast_admits_var_one_rec] at h1

  apply substitution_theorem_fast_admits_var_one_rec_aux D I V V E v t ∅ F h1
  simp


theorem substitution_is_valid_fast_admits_var_one_rec
  (v t : VarName_)
  (F : Formula_)
  (h1 : fast_admits_var_one_rec v t F)
  (h2 : F.is_valid) :
  (fast_replace_free_var_one_rec v t F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem_fast_admits_var_one_rec D I V E v t F h1]
  apply h2


#lint
