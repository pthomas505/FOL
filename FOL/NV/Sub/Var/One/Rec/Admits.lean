import MathlibExtra.Finset
import FOL.NV.Semantics
import FOL.NV.Sub.Var.One.Rec.ReplaceFree


set_option autoImplicit false


namespace FOL.NV.Sub.Var.One.Rec

open Formula


/-
[margaris]
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/
/--
  Helper function for admits.
-/
def admitsAux (v u : VarName_) (binders : Finset VarName_) : Formula → Prop
  | pred_const_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | pred_var_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | eq_ x y =>
      (v = x ∨ v = y) ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | true_ => True
  | false_ => True
  | not_ phi => admitsAux v u binders phi
  | imp_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | and_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | or_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | iff_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | forall_ x phi => admitsAux v u (binders ∪ {x}) phi
  | exists_ x phi => admitsAux v u (binders ∪ {x}) phi
  | def_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)


instance
  (v u : VarName_)
  (binders : Finset VarName_)
  (F : Formula) :
  Decidable (admitsAux v u binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [admitsAux]
    infer_instance


/--
  admits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P
-/
def admits (v u : VarName_) (F : Formula) : Prop :=
  admitsAux v u ∅ F


instance
  (v u : VarName_)
  (F : Formula) :
  Decidable (admits v u F) :=
  by
  simp only [admits]
  infer_instance


/--
  Helper function for fastAdmits.
-/
def fastAdmitsAux (v u : VarName_) (binders : Finset VarName_) : Formula → Prop
  | pred_const_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | pred_var_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | eq_ x y =>
      (v = x ∨ v = y) → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | true_ => True
  | false_ => True
  | not_ phi => fastAdmitsAux v u binders phi
  | imp_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | and_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | or_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | iff_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | forall_ x phi => v = x ∨ fastAdmitsAux v u (binders ∪ {x}) phi
  | exists_ x phi => v = x ∨ fastAdmitsAux v u (binders ∪ {x}) phi
  | def_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)


instance
  (v u : VarName_)
  (binders : Finset VarName_)
  (F : Formula) :
  Decidable (fastAdmitsAux v u binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [fastAdmitsAux]
    infer_instance


/--
  fastAdmits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P

  This is a more efficient version of admits.
-/
def fastAdmits (v u : VarName_) (F : Formula) : Prop :=
  fastAdmitsAux v u ∅ F


instance
  (v u : VarName_)
  (F : Formula) :
  Decidable (fastAdmits v u F) :=
  by
  simp only [fastAdmits]
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
  | def_ : DefName → List Bool → BoolFormula
  deriving Inhabited, DecidableEq


/--
  Helper function for toIsBound.
-/
def toIsBoundAux (binders : Finset VarName_) : Formula → BoolFormula
  | pred_const_ X xs =>
      BoolFormula.pred_const_ X (xs.map fun (v : VarName_) => v ∈ binders)

  | pred_var_ X xs =>
      BoolFormula.pred_var_ X (xs.map fun (v : VarName_) => v ∈ binders)

  | eq_ x y =>
      BoolFormula.eq_ (x ∈ binders) (y ∈ binders)

  | true_ => BoolFormula.true_

  | false_ => BoolFormula.false_

  | not_ phi => BoolFormula.not_ (toIsBoundAux binders phi)

  | imp_ phi psi =>
      BoolFormula.imp_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | and_ phi psi =>
      BoolFormula.and_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | or_ phi psi =>
      BoolFormula.or_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | iff_ phi psi =>
      BoolFormula.iff_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | forall_ x phi =>
      BoolFormula.forall_ True (toIsBoundAux (binders ∪ {x}) phi)

  | exists_ x phi =>
      BoolFormula.forall_ True (toIsBoundAux (binders ∪ {x}) phi)

  | def_ X xs =>
      BoolFormula.def_ X (xs.map fun (v : VarName_) => v ∈ binders)

/--
  Creates a BoolFormula from a formula. Each bound occurence of a variable in the formula is mapped to true in the bool formula. Each free occurence of a variable in the formula is mapped to false in the bool formula.
-/
def toIsBound (F : Formula) : BoolFormula :=
  toIsBoundAux ∅ F


-- admits ↔ fastAdmits

theorem admitsAux_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders)
  (h2 : admitsAux v u binders F) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [admitsAux] at h2

    simp only [fastAdmitsAux]
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


theorem mem_binders_imp_admitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∈ binders) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [admitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    apply phi_ih
    simp
    left
    exact h1
  all_goals
    tauto


theorem fastAdmitsAux_imp_admitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : fastAdmitsAux v u binders F) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [fastAdmitsAux] at h1

    simp only [admitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h1
    case inl h1 =>
      apply mem_binders_imp_admitsAux
      subst h1
      simp
    case inr h1 =>
      apply phi_ih
      exact h1
  all_goals
    tauto


theorem admits_iff_fastAdmits
  (F : Formula)
  (v u : VarName_) :
  admits v u F ↔ fastAdmits v u F :=
  by
  simp only [admits]
  simp only [fastAdmits]
  constructor
  · apply admitsAux_imp_fastAdmitsAux
    simp
  · exact fastAdmitsAux_imp_admitsAux F v u ∅


-- fastAdmits

theorem fastAdmitsAux_self
  (F : Formula)
  (v : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders) :
  fastAdmitsAux v v binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [fastAdmitsAux]
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


theorem fastAdmits_self
  (F : Formula)
  (v : VarName_) :
  fastAdmits v v F :=
  by
  simp only [fastAdmits]
  apply fastAdmitsAux_self
  simp

--

theorem not_isFreeIn_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_is_free_in v F) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_is_free_in] at h1

    simp only [fastAdmitsAux]
  all_goals
    tauto


theorem not_isFreeIn_imp_fastAdmits
  (F : Formula)
  (v u : VarName_)
  (h1 : ¬ var_is_free_in v F) :
  fastAdmits v u F :=
  by
  simp only [fastAdmits]
  exact not_isFreeIn_imp_fastAdmitsAux F v u ∅ h1

--

theorem not_isBoundIn_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ isBoundIn u F)
  (h2 : u ∉ binders) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [isBoundIn] at h1

    simp only [fastAdmitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      right
      apply phi_ih (binders ∪ {x}) h1_right
      · simp
        tauto
  all_goals
    tauto


theorem not_isBoundIn_imp_fastAdmits
  (F : Formula)
  (v u : VarName_)
  (h1 : ¬ isBoundIn u F) :
  fastAdmits v u F :=
  by
  simp only [fastAdmits]
  apply not_isBoundIn_imp_fastAdmitsAux F v u ∅ h1
  simp

--

theorem fastReplaceFree_aux_fastAdmitsAux
  (F : Formula)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ occursIn t F)
  (h2 : v ∉ binders) :
  fastAdmitsAux t v binders (fastReplaceFree v t F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [occursIn] at h1

    simp only [fastReplaceFree]
  any_goals
    simp only [fastAdmitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      split_ifs
      case pos c1 =>
        simp only [fastAdmitsAux]
        subst c1
        right
        apply not_isFreeIn_imp_fastAdmitsAux
        intro contra
        apply h1_right
        apply isFreeIn_imp_occursIn
        exact contra
      case neg c1 =>
        simp only [fastAdmitsAux]
        right
        apply phi_ih (binders ∪ {x}) h1_right
        simp
        tauto
  all_goals
    tauto


theorem fastReplaceFree_fastAdmits
  (F : Formula)
  (v t : VarName_)
  (h1 : ¬ occursIn t F) :
  fastAdmits t v (fastReplaceFree v t F) :=
  by
  simp only [fastAdmits]
  apply fastReplaceFree_aux_fastAdmitsAux F v t ∅ h1
  simp

--

theorem replaceFreeAux_fastAdmitsAux
  (F : Formula)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ occursIn t F) :
  fastAdmitsAux t v binders (replaceFreeAux v t binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [occursIn] at h1

    simp only [replaceFreeAux]
    simp only [fastAdmitsAux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x a1 a2
    by_cases c1 : v = x ∧ x ∉ binders
    · cases c1
      case _ c1_left c1_right =>
        subst c1_left
        exact c1_right
    · push_neg at c1
      specialize a2 c1
      subst a2
      contradiction
  case eq_ x y =>
    push_neg at h1

    intros a1
    split_ifs at a1
    case _ c1 c2 =>
      cases c1
      case intro c1_left c1_right =>
        subst c1_left
        exact c1_right
    case _ c1 c2 =>
      cases c1
      case intro c1_left c1_right =>
        subst c1_left
        exact c1_right
    case _ c1 c2 =>
      cases c2
      case intro c2_left c2_right =>
        subst c2_left
        exact c2_right
    case _ c1 c2 =>
      tauto
  all_goals
    tauto


theorem replaceFree_fastAdmits
  (F : Formula)
  (v t : VarName_)
  (h1 : ¬ occursIn t F) :
  fastAdmits t v (replaceFree v t F) :=
  by
  simp only [replaceFree]
  simp only [fastAdmits]
  exact replaceFreeAux_fastAdmitsAux F v t ∅ h1

--

theorem fastAdmitsAux_add_binders
  (F : Formula)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : fastAdmitsAux v u S F)
  (h2 : u ∉ T) :
  fastAdmitsAux v u (S ∪ T) F :=
  by
  induction F generalizing S
  all_goals
    simp only [fastAdmitsAux] at h1

    simp only [fastAdmitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp
    cases h1
    case inl h1 =>
      tauto
    case inr h1 =>
      specialize phi_ih (S ∪ {x}) h1
      right
      simp only [Finset.union_right_comm_assoc]
      exact phi_ih
  any_goals
    simp only [Finset.mem_union]
  all_goals
    tauto


theorem fastAdmitsAux_del_binders
  (F : Formula)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : fastAdmitsAux v u (S ∪ T) F) :
  fastAdmitsAux v u S F :=
  by
  induction F generalizing S
  all_goals
    simp only [fastAdmitsAux] at h1

    simp only [fastAdmitsAux]
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

theorem fastAdmitsAux_isFreeIn
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : fastAdmitsAux v u binders F)
  (h2 : var_is_free_in v F) :
  u ∉ binders :=
  by
  induction F generalizing binders
  all_goals
    simp only [fastAdmitsAux] at h1

    simp only [var_is_free_in] at h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h2
    case intro h2_left h2_right =>
      cases h1
      case inl h1 =>
        contradiction
      case inr h1 =>
        apply phi_ih
        · exact fastAdmitsAux_del_binders phi v u binders {x} h1
        · exact h2_right
  all_goals
    tauto


theorem fastAdmitsAux_mem_binders
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : fastAdmitsAux v u binders F)
  (h2 : u ∈ binders) :
  ¬ var_is_free_in v F :=
  by
  contrapose! h2
  exact fastAdmitsAux_isFreeIn F v u binders h1 h2

--

theorem fastAdmitsAux_imp_free_and_bound_unchanged
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders)
  (h2 : fastAdmitsAux v u binders F) :
  toIsBoundAux binders F =
    toIsBoundAux binders (fastReplaceFree v u F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [fastAdmitsAux] at h2

    simp only [fastReplaceFree]
  any_goals
    simp only [toIsBoundAux]
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
      simp only [toIsBoundAux]
      simp
      apply phi_ih
      · simp
        tauto
      · tauto


theorem free_and_bound_unchanged_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : v ∉ binders)
  (h2 : toIsBoundAux binders F =
    toIsBoundAux binders (fastReplaceFree v u F)) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [fastReplaceFree] at h2

    simp only [fastAdmitsAux]
  any_goals
    simp only [toIsBoundAux] at h2
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp at h2

    intro a1
    specialize h2 v a1
    simp at h2
    tauto
  case eq_ x y =>
    simp at h2

    cases h2
    case intro h2_left h2_right =>
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

    exact phi_ih binders h1 h2
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
      · simp only [toIsBoundAux] at h2
        simp at h2
        exact h2


example
  (F : Formula)
  (v u : VarName_) :
  fastAdmits v u F ↔
    toIsBound F = toIsBound (fastReplaceFree v u F) :=
  by
  simp only [fastAdmits]
  simp only [toIsBound]
  constructor
  · apply fastAdmitsAux_imp_free_and_bound_unchanged
    simp
  · apply free_and_bound_unchanged_imp_fastAdmitsAux
    simp


-- admits

theorem admitsAux_self
  (F : Formula)
  (v : VarName_)
  (binders : Finset VarName_) :
  admitsAux v v binders F := by
  induction F generalizing binders
  all_goals
    simp only [admitsAux]
  all_goals
    tauto


theorem admits_self
  (F : Formula)
  (v : VarName_) :
  admits v v F :=
  by
  simp only [admits]
  apply admitsAux_self

--

theorem not_isFreeIn_imp_admitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ var_is_free_in v F) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [var_is_free_in] at h1

    simp only [admitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    by_cases c1 : v = x
    · apply mem_binders_imp_admitsAux
      simp
      tauto
    · apply phi_ih
      tauto
  all_goals
    tauto


theorem not_isFreeIn_imp_admits
  (F : Formula)
  (v u : VarName_)
  (h1 : ¬ var_is_free_in v F) :
  admits v u F :=
  by
  simp only [admits]
  exact not_isFreeIn_imp_admitsAux F v u ∅ h1

--

theorem not_isBoundIn_imp_admitsAux
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ isBoundIn u F)
  (h2 : u ∉ binders) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  all_goals
    simp only [isBoundIn] at h1

    simp only [admitsAux]
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      apply phi_ih (binders ∪ {x}) h1_right
      simp
      tauto
  all_goals
    tauto


theorem not_isBoundIn_imp_admits
  (F : Formula)
  (v u : VarName_)
  (h1 : ¬ isBoundIn u F) :
  admits v u F :=
  by
  simp only [admits]
  apply not_isBoundIn_imp_admitsAux F v u ∅ h1
  simp

--

theorem replaceFreeAux_admitsAux
  (F : Formula)
  (v t : VarName_)
  (binders : Finset VarName_)
  (h1 : ¬ occursIn t F) :
  admitsAux t v binders (replaceFreeAux v t binders F) :=
  by
  induction F generalizing binders
  all_goals
    simp only [occursIn] at h1

    simp only [replaceFreeAux]
    simp only [admitsAux]
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    simp
    intro x a1 a2 a3
    by_cases c1 : v = x ∧ x ∉ binders
    case pos =>
      cases c1
      case intro c1_left c1_right =>
        subst c1_left
        exact c1_right
    case neg =>
      simp at c1
      specialize a2 c1
      subst a2
      contradiction
  case eq_ x y =>
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      intro a1
      split_ifs at a1
      case _ c1 c2 =>
        cases c1
        case intro c1_left c1_right =>
          subst c1_left
          exact c1_right
      case _ c1 c2 =>
        cases c1
        case intro c1_left c1_right =>
          subst c1_left
          exact c1_right
      case _ c1 c2 =>
        cases c2
        case intro c2_left c2_right =>
          subst c2_left
          exact c2_right
      case _ c1 c2 =>
        tauto
  all_goals
    tauto


theorem replaceFree_admits
  (F : Formula)
  (v t : VarName_)
  (h1 : ¬ occursIn t F) :
  admits t v (replaceFree v t F) :=
  by
  simp only [replaceFree]
  simp only [admits]
  exact replaceFreeAux_admitsAux F v t ∅ h1

--

theorem admitsAux_add_binders
  (F : Formula)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : admitsAux v u S F)
  (h2 : u ∉ T) :
  admitsAux v u (S ∪ T) F :=
  by
  induction F generalizing S
  all_goals
    simp only [admitsAux] at h1

    simp only [admitsAux]
  case pred_const_ X xs | pred_var_ X xs | eq_ x y |def_ X xs =>
    simp
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [Finset.union_right_comm S T {x}]
    tauto
  all_goals
    tauto


theorem admitsAux_del_binders
  (F : Formula)
  (v u : VarName_)
  (S T : Finset VarName_)
  (h1 : admitsAux v u (S ∪ T) F)
  (h2 : v ∉ T) :
  admitsAux v u S F :=
  by
  induction F generalizing S
  all_goals
    simp only [admitsAux] at h1

    simp only [admitsAux]
  case pred_const_ X xs | pred_var_ X xs | eq_ x y | def_ X xs =>
    simp at h1

    tauto
  case not_ phi phi_ih =>
    exact phi_ih S h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    simp only [Finset.union_right_comm S T {x}] at h1

    tauto


theorem admitsAux_isFreeIn
  (F : Formula)
  (v u : VarName_)
  (binders : Finset VarName_)
  (h1 : admitsAux v u binders F)
  (h2 : var_is_free_in v F)
  (h3 : v ∉ binders) :
  u ∉ binders :=
  by
  induction F generalizing binders
  all_goals
    simp only [admitsAux] at h1

    simp only [var_is_free_in] at h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    cases h2
    case intro h2_left h2_right =>
      apply phi_ih binders
      · apply admitsAux_del_binders phi v u binders {x} h1
        · simp
          exact h2_left
      · exact h2_right
      · exact h3
  all_goals
    tauto


theorem substitution_theorem_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' : Valuation_ D)
  (E : Env)
  (v t : VarName_)
  (binders : Finset VarName_)
  (F : Formula)
  (h1 : fastAdmitsAux v t binders F)
  (h2 : ∀ (v : VarName_), ¬ v ∈ binders → V' v = V v) :
  holds D I (Function.updateITE V v (V' t)) E F ↔
    holds D I V E (fastReplaceFree v t F) :=
  by
  induction E generalizing F binders V
  all_goals
    induction F generalizing binders V
    all_goals
      simp only [fastAdmitsAux] at h1

      simp only [fastReplaceFree]
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
      cases h1
      case intro h1_left h1_right =>
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
          push_neg
          intros v' a1 a2
          simp only [if_neg a2]
          exact h2 v' a1

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
              if v = x then t else x) xs)
      {
        simp only [List.map_eq_map_iff]
        intro x a2
        simp
        split_ifs
        case _ c2 =>
          apply h2
          subst c2
          exact h1 a2
        case _ c2 =>
          rfl
      }

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
      · simp only [fastAdmitsAux]
        exact h1
      · exact h2


theorem substitution_theorem
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env)
  (v t : VarName_)
  (F : Formula)
  (h1 : fastAdmits v t F) :
  holds D I (Function.updateITE V v (V t)) E F ↔
    holds D I V E (fastReplaceFree v t F) :=
  by
  simp only [fastAdmits] at h1

  apply substitution_theorem_aux D I V V E v t ∅ F h1
  simp


theorem substitution_is_valid
  (v t : VarName_)
  (F : Formula)
  (h1 : fastAdmits v t F)
  (h2 : F.is_valid) :
  (fastReplaceFree v t F).is_valid :=
  by
  simp only [is_valid] at h2

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem D I V E v t F h1]
  apply h2


#lint
