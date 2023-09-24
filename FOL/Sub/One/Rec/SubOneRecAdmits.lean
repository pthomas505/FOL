import FOL.Sub.One.Rec.SubOneRecReplaceFree
import FOL.Semantics
import FOL.Tactics


namespace FOL

namespace NV

open Formula


/-
[margaris]
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/
/--
  Helper function for admits.
-/
def admitsAux (v u : VarName) : Finset VarName → Formula → Prop
  | binders, pred_const_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | binders, pred_var_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | binders, eq_ x y =>
      (v = x ∨ v = y) ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | _, true_ => True
  | _, false_ => True
  | binders, not_ phi => admitsAux v u binders phi
  | binders, imp_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | binders, and_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | binders, or_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | binders, iff_ phi psi =>
      admitsAux v u binders phi ∧ admitsAux v u binders psi
  | binders, forall_ x phi => admitsAux v u (binders ∪ {x}) phi
  | binders, exists_ x phi => admitsAux v u (binders ∪ {x}) phi
  | binders, def_ _ xs =>
      v ∈ xs ∧ v ∉ binders → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)


instance
  (v u : VarName)
  (binders : Finset VarName)
  (F : Formula) :
  Decidable (admitsAux v u binders F) :=
  by
  induction F generalizing binders
  all_goals
    unfold admitsAux
    infer_instance


/--
  admits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P
-/
def admits (v u : VarName) (F : Formula) : Prop :=
  admitsAux v u ∅ F


instance
  (v u : VarName)
  (F : Formula) :
  Decidable (admits v u F) :=
  by
  unfold admits
  infer_instance


/--
  Helper function for fastAdmits.
-/
def fastAdmitsAux (v u : VarName) : Finset VarName → Formula → Prop
  | binders, pred_const_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | binders, pred_var_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | binders, eq_ x y =>
      (v = x ∨ v = y) → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
  | _, true_ => True
  | _, false_ => True
  | binders, not_ phi => fastAdmitsAux v u binders phi
  | binders, imp_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | binders, and_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | binders, or_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | binders, iff_ phi psi =>
      fastAdmitsAux v u binders phi ∧ fastAdmitsAux v u binders psi
  | binders, forall_ x phi => v = x ∨ fastAdmitsAux v u (binders ∪ {x}) phi
  | binders, exists_ x phi => v = x ∨ fastAdmitsAux v u (binders ∪ {x}) phi
  | binders, def_ _ xs =>
      v ∈ xs → -- if there is a free occurrence of v in P
        u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)


instance
  (v u : VarName)
  (binders : Finset VarName)
  (F : Formula) :
  Decidable (fastAdmitsAux v u binders F) :=
  by
  induction F generalizing binders
  all_goals
    unfold fastAdmitsAux
    infer_instance


/--
  fastAdmits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P

  This is a more efficient version of admits.
-/
def fastAdmits (v u : VarName) (F : Formula) : Prop :=
  fastAdmitsAux v u ∅ F


instance
  (v u : VarName)
  (F : Formula) :
  Decidable (fastAdmits v u F) :=
  by
  unfold fastAdmits
  infer_instance


/--
  Used to label each occurrence of a variable in a formula as free or bound.
-/
inductive BoolFormula : Type
  | pred_const_ : PredName → List Bool → BoolFormula
  | pred_var_ : PredName → List Bool → BoolFormula
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
def toIsBoundAux : Finset VarName → Formula → BoolFormula
  | binders, pred_const_ X xs =>
      BoolFormula.pred_const_ X (xs.map fun v : VarName => v ∈ binders)

  | binders, pred_var_ X xs =>
      BoolFormula.pred_var_ X (xs.map fun v : VarName => v ∈ binders)

  | binders, eq_ x y =>
      BoolFormula.eq_ (x ∈ binders) (y ∈ binders)

  | _, true_ => BoolFormula.true_

  | _, false_ => BoolFormula.false_

  | binders, not_ phi => BoolFormula.not_ (toIsBoundAux binders phi)

  | binders, imp_ phi psi =>
      BoolFormula.imp_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | binders, and_ phi psi =>
      BoolFormula.and_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | binders, or_ phi psi =>
      BoolFormula.or_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | binders, iff_ phi psi =>
      BoolFormula.iff_ (toIsBoundAux binders phi) (toIsBoundAux binders psi)

  | binders, forall_ x phi =>
      BoolFormula.forall_ True (toIsBoundAux (binders ∪ {x}) phi)

  | binders, exists_ x phi =>
      BoolFormula.forall_ True (toIsBoundAux (binders ∪ {x}) phi)

  | binders, def_ X xs =>
      BoolFormula.def_ X (xs.map fun v : VarName => v ∈ binders)

/--
  Creates a BoolFormula from a formula. Each bound occurence of a variable in the formula is mapped to true in the bool formula. Each free occurence of a variable in the formula is mapped to false in the bool formula.
-/
def toIsBound (F : Formula) : BoolFormula :=
  toIsBoundAux ∅ F


-- admits ↔ fastAdmits

theorem admitsAux_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : v ∉ binders)
  (h2 : admitsAux v u binders F) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux at h2
    simp at h2

    unfold fastAdmitsAux
    intro a1
    exact h2 a1 h1
  case eq_ x y =>
    unfold admitsAux at h2
    simp at h2

    unfold fastAdmitsAux
    intro a1
    exact h2 a1 h1
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold admitsAux at h2

    unfold fastAdmitsAux
    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsAux at h2

    cases h2
    case intro h2_left h2_right =>
      unfold fastAdmitsAux
      constructor
      · exact phi_ih binders h1 h2_left
      · exact psi_ih binders h1 h2_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsAux at h2

    unfold fastAdmitsAux
    by_cases c1 : v = x
    · left
      exact c1
    · right
      apply phi_ih (binders ∪ {x})
      · simp
        push_neg
        constructor
        · exact h1
        · exact c1
      · exact h2


theorem mem_binders_imp_admitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : v ∈ binders) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux
    simp
    intro _ a2
    contradiction
  case eq_ x y =>
    unfold admitsAux
    simp
    intro _ a2
    contradiction
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold admitsAux
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsAux
    constructor
    · exact phi_ih binders h1
    · exact psi_ih binders h1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsAux
    apply phi_ih
    simp
    left
    exact h1


theorem fastAdmitsAux_imp_admitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : fastAdmitsAux v u binders F) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastAdmitsAux at h1

    unfold admitsAux
    simp
    intros a1 _
    exact h1 a1
  case eq_ x y =>
    unfold fastAdmitsAux at h1

    unfold admitsAux
    intros a1
    cases a1
    case intro a1_left a1_right =>
      exact h1 a1_left
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold admitsAux
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastAdmitsAux at h1

    unfold admitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih binders h1_left
      · exact psi_ih binders h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold admitsAux
    cases h1
    case inl h1 =>
      apply mem_binders_imp_admitsAux
      subst h1
      simp
    case inr h1 =>
      apply phi_ih
      exact h1


theorem admits_iff_fastAdmits
  (F : Formula)
  (v u : VarName) :
  admits v u F ↔ fastAdmits v u F :=
  by
  unfold admits
  unfold fastAdmits
  constructor
  · apply admitsAux_imp_fastAdmitsAux
    simp
  · exact fastAdmitsAux_imp_admitsAux F v u ∅


-- fastAdmits

theorem fastAdmitsAux_self
  (F : Formula)
  (v : VarName)
  (binders : Finset VarName)
  (h1 : v ∉ binders) :
  fastAdmitsAux v v binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastAdmitsAux
    intro _
    exact h1
  case eq_ x y =>
    unfold fastAdmitsAux
    intro _
    exact h1
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold fastAdmitsAux
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastAdmitsAux
    constructor
    · exact phi_ih binders h1
    · exact psi_ih binders h1
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastAdmitsAux
    by_cases c1 : v = x
    · left
      exact c1
    · right
      apply phi_ih
      simp
      push_neg
      constructor
      · exact h1
      · exact c1


theorem fastAdmits_self
  (F : Formula)
  (v : VarName) :
  fastAdmits v v F :=
  by
  unfold fastAdmits
  apply fastAdmitsAux_self
  simp

--

theorem not_isFreeIn_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : ¬ isFreeIn v F) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold isFreeIn at h1

    unfold fastAdmitsAux
    intro a1
    contradiction
  case eq_ x y =>
    unfold isFreeIn at h1

    unfold fastAdmitsAux
    intro a1
    contradiction
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold isFreeIn at h1

    unfold fastAdmitsAux
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isFreeIn at h1
    push_neg at h1

    unfold fastAdmitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih binders h1_left
      · exact psi_ih binders h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isFreeIn at h1
    push_neg at h1

    unfold fastAdmitsAux
    by_cases c1 : v = x
    · left
      exact c1
    · right
      apply phi_ih (binders ∪ {x})
      exact h1 c1


theorem not_isFreeIn_imp_fastAdmits
  (F : Formula)
  (v u : VarName)
  (h1 : ¬ isFreeIn v F) :
  fastAdmits v u F :=
  by
  unfold fastAdmits
  exact not_isFreeIn_imp_fastAdmitsAux F v u ∅ h1

--

theorem not_isBoundIn_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : ¬ isBoundIn u F)
  (h2 : u ∉ binders) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastAdmitsAux
    intros _
    exact h2
  case eq_ x y =>
    unfold fastAdmitsAux
    intros _
    exact h2
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold isBoundIn at h1

    unfold fastAdmitsAux
    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isBoundIn at h1
    push_neg at h1

    unfold fastAdmitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih binders h1_left h2
      · exact psi_ih binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isBoundIn at h1
    push_neg at h1

    unfold fastAdmitsAux
    cases h1
    case intro h1_left h1_right =>
      right
      apply phi_ih (binders ∪ {x}) h1_right
      · simp
        push_neg
        constructor
        · exact h2 
        · exact h1_left


theorem not_isBoundIn_imp_fastAdmits
  (F : Formula)
  (v u : VarName)
  (h1 : ¬ isBoundIn u F) :
  fastAdmits v u F :=
  by
  unfold fastAdmits
  apply not_isBoundIn_imp_fastAdmitsAux F v u ∅ h1
  simp

--

theorem fastReplaceFree_aux_fastAdmitsAux
  (F : Formula)
  (v t : VarName)
  (binders : Finset VarName)
  (h1 : ¬ occursIn t F)
  (h2 : v ∉ binders) :
  fastAdmitsAux t v binders (fastReplaceFree v t F) :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastReplaceFree
    unfold fastAdmitsAux
    intro _
    exact h2
  case eq_ x y =>
    unfold fastReplaceFree
    unfold fastAdmitsAux
    intro _
    exact h2
  case true_ | false_ =>
    unfold fastReplaceFree
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold occursIn at h1

    unfold fastReplaceFree
    unfold fastAdmitsAux
    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold occursIn at h1
    push_neg at h1

    unfold fastReplaceFree
    unfold fastAdmitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih binders h1_left h2
      · exact psi_ih binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold occursIn at h1
    push_neg at h1

    unfold fastReplaceFree
    cases h1
    case intro h1_left h1_right =>
      split_ifs
      case inl c1 =>
        unfold fastAdmitsAux
        subst c1
        right
        apply not_isFreeIn_imp_fastAdmitsAux
        intro contra
        apply h1_right
        apply isFreeIn_imp_occursIn
        exact contra
      case inr c1 =>
        unfold fastAdmitsAux
        right
        apply phi_ih (binders ∪ {x}) h1_right
        simp
        push_neg
        constructor
        · exact h2
        · exact c1


theorem fastReplaceFree_fastAdmits
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ occursIn t F) :
  fastAdmits t v (fastReplaceFree v t F) :=
  by
  unfold fastAdmits
  apply fastReplaceFree_aux_fastAdmitsAux F v t ∅ h1
  simp

--

theorem replaceFreeAux_fastAdmitsAux
  (F : Formula)
  (v t : VarName)
  (binders : Finset VarName)
  (h1 : ¬ occursIn t F) :
  fastAdmitsAux t v binders (replaceFreeAux v t binders F) :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold occursIn at h1

    unfold replaceFreeAux
    unfold fastAdmitsAux
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
    unfold occursIn at h1
    push_neg at h1

    unfold replaceFreeAux
    unfold fastAdmitsAux
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
      cases a1
      case inl a1 | inr a1 =>
        cases h1
        case intro h1_left h1_right =>
          contradiction
  case true_ | false_ =>
    unfold replaceFreeAux
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold occursIn at h1

    unfold replaceFreeAux
    unfold fastAdmitsAux
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold occursIn at h1

    unfold replaceFreeAux
    unfold fastAdmitsAux
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold occursIn at h1

    unfold replaceFreeAux
    unfold fastAdmitsAux
    tauto


theorem replaceFree_fastAdmits
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ occursIn t F) :
  fastAdmits t v (replaceFree v t F) :=
  by
  unfold replaceFree
  unfold fastAdmits
  exact replaceFreeAux_fastAdmitsAux F v t ∅ h1

--

theorem fastAdmitsAux_add_binders
  (F : Formula)
  (v u : VarName)
  (S T : Finset VarName)
  (h1 : fastAdmitsAux v u S F)
  (h2 : u ∉ T) :
  fastAdmitsAux v u (S ∪ T) F :=
  by
  induction F generalizing S
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    simp
    tauto
  case eq_ x y =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    simp
    tauto
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    simp
    cases h1
    case inl h1 =>
      tauto
    case inr h1 =>
      specialize phi_ih (S ∪ {x}) h1
      right
      simp only [Finset.union_right_comm S {x} T] at phi_ih
      simp only [Finset.union_assoc S T {x}] at phi_ih
      exact phi_ih


theorem fastAdmitsAux_del_binders
  (F : Formula)
  (v u : VarName)
  (S T : Finset VarName)
  (h1 : fastAdmitsAux v u (S ∪ T) F) :
  fastAdmitsAux v u S F :=
  by
  induction F generalizing S
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastAdmitsAux at h1
    simp at h1

    unfold fastAdmitsAux
    tauto
  case eq_ x y =>
    unfold fastAdmitsAux at h1
    simp at h1

    unfold fastAdmitsAux
    tauto
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    tauto
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastAdmitsAux at h1

    unfold fastAdmitsAux
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastAdmitsAux at h1
    simp only [Finset.union_right_comm S T {x}] at h1

    unfold fastAdmitsAux
    tauto

--

theorem fastAdmitsAux_isFreeIn
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : fastAdmitsAux v u binders F)
  (h2 : isFreeIn v F) :
  u ∉ binders :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold fastAdmitsAux at h1

    unfold isFreeIn at h2

    tauto
  case eq_ x y =>
    unfold fastAdmitsAux at h1

    unfold isFreeIn at h2

    tauto
  case true_ | false_ =>
    unfold isFreeIn at h2

    contradiction
  case not_ phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold isFreeIn at h2

    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastAdmitsAux at h1

    unfold isFreeIn at h2

    cases h1
    case intro h1_left h1_right =>
      cases h2
      case inl h2 =>
        exact phi_ih binders h1_left h2
      case inr h2 =>
        exact psi_ih binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastAdmitsAux at h1

    unfold isFreeIn at h2

    cases h2
    case intro h2_left h2_right =>
      cases h1
      case inl h1 =>
        contradiction
      case inr h1 =>
        apply phi_ih
        · exact fastAdmitsAux_del_binders phi v u binders {x} h1
        · exact h2_right


theorem fastAdmitsAux_mem_binders
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : fastAdmitsAux v u binders F)
  (h2 : u ∈ binders) :
  ¬ isFreeIn v F :=
  by
  contrapose! h2
  exact fastAdmitsAux_isFreeIn F v u binders h1 h2

--

theorem fastAdmitsAux_imp_free_and_bound_unchanged
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : v ∉ binders)
  (h2 : fastAdmitsAux v u binders F) :
  toIsBoundAux binders F =
    toIsBoundAux binders (fastReplaceFree v u F) :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    induction xs
    case nil =>
      unfold fastReplaceFree
      simp
    case cons args_hd args_tl args_ih =>
      unfold fastAdmitsAux at h2
      simp at h2

      unfold fastAdmitsAux at args_ih
      unfold fastReplaceFree at args_ih
      unfold toIsBoundAux at args_ih
      simp at args_ih

      unfold fastReplaceFree
      unfold toIsBoundAux
      simp
      constructor
      · split_ifs
        case inl c1 =>
          subst c1
          tauto
        case inr c1 =>
          rfl
      · tauto
  case eq_ x y =>
    unfold fastAdmitsAux at h2

    unfold fastReplaceFree
    unfold toIsBoundAux
    simp
    constructor
    case left | right =>
      split_ifs
      case inl c1 =>
        subst c1
        tauto
      case inr c1 =>
        rfl
  case true_ | false_ =>
    rfl
  case not_ phi phi_ih =>
    unfold fastAdmitsAux at h2

    unfold fastReplaceFree
    unfold toIsBoundAux
    congr! 1
    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastAdmitsAux at h2

    unfold fastReplaceFree
    unfold toIsBoundAux
    cases h2
    case intro h2_left h2_right =>
      congr! 1
      · exact phi_ih binders h1 h2_left
      · exact psi_ih binders h1 h2_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastAdmitsAux at h2

    unfold fastReplaceFree
    split_ifs
    case inl c1 =>
      rfl
    case inr c1 =>
      unfold toIsBoundAux
      simp
      apply phi_ih
      · simp
        tauto
      · tauto


theorem free_and_bound_unchanged_imp_fastAdmitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : v ∉ binders)
  (h2 : toIsBoundAux binders F =
    toIsBoundAux binders (fastReplaceFree v u F)) :
  fastAdmitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    induction xs
    case nil =>
      unfold fastAdmitsAux
      simp
    case cons args_hd args_tl args_ih =>
      unfold fastReplaceFree at h2
      unfold toIsBoundAux at h2
      simp at h2

      unfold fastAdmitsAux at args_ih
      unfold fastReplaceFree at args_ih
      unfold toIsBoundAux at args_ih
      simp at args_ih

      unfold fastAdmitsAux
      simp
      intro a1
      cases a1
      case inl a1 =>
        subst a1
        cases h2
        case intro h2_left h2_right =>
          simp at h2_left
          tauto
      case inr a1 =>
        tauto
  case eq_ x y =>
    unfold fastReplaceFree at h2
    unfold toIsBoundAux at h2
    simp at h2

    unfold fastAdmitsAux
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
  case true_ | false_ =>
    unfold fastAdmitsAux
    simp
  case not_ phi phi_ih =>
    unfold fastReplaceFree at h2
    unfold toIsBoundAux at h2
    simp at h2

    unfold fastAdmitsAux
    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold fastReplaceFree at h2
    unfold toIsBoundAux at h2
    simp at h2

    unfold fastAdmitsAux
    cases h2
    case intro h2_left h2_right =>
      constructor
      · exact phi_ih binders h1 h2_left
      · exact psi_ih binders h1 h2_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold fastReplaceFree at h2

    unfold fastAdmitsAux
    split_ifs at h2
    case inl c1 =>
      left
      exact c1
    case inr c1 =>
      right
      apply phi_ih
      · simp
        tauto
      · unfold toIsBoundAux at h2
        simp at h2
        exact h2


example
  (F : Formula)
  (v u : VarName) :
  fastAdmits v u F ↔
    toIsBound F = toIsBound (fastReplaceFree v u F) :=
  by
  unfold fastAdmits
  unfold toIsBound
  constructor
  · apply fastAdmitsAux_imp_free_and_bound_unchanged
    simp
  · apply free_and_bound_unchanged_imp_fastAdmitsAux
    simp


-- admits

theorem admitsAux_self
  (F : Formula)
  (v : VarName)
  (binders : Finset VarName) :
  admitsAux v v binders F := by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux
    simp
  case eq_ x y =>
    unfold admitsAux
    simp
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold admitsAux
    exact phi_ih binders
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsAux
    tauto
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsAux
    tauto


theorem admits_self
  (F : Formula)
  (v : VarName) :
  admits v v F :=
  by
  unfold admits
  apply admitsAux_self

--

theorem not_isFreeIn_imp_admitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : ¬ isFreeIn v F) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold isFreeIn at h1

    unfold admitsAux
    simp
    tauto
  case eq_ x y =>
    unfold isFreeIn at h1

    unfold admitsAux
    simp
    tauto
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold isFreeIn at h1

    unfold admitsAux
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isFreeIn at h1
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
    unfold admitsAux
    constructor
    · exact phi_ih binders h1_left
    · exact psi_ih binders h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isFreeIn at h1
    simp at h1

    unfold admitsAux
    by_cases c1 : v = x
    · apply mem_binders_imp_admitsAux
      simp
      tauto
    · apply phi_ih
      exact h1 c1


theorem not_isFreeIn_imp_admits
  (F : Formula)
  (v u : VarName)
  (h1 : ¬ isFreeIn v F) :
  admits v u F :=
  by
  unfold admits
  exact not_isFreeIn_imp_admitsAux F v u ∅ h1

--

theorem not_isBoundIn_imp_admitsAux
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : ¬ isBoundIn u F)
  (h2 : u ∉ binders) :
  admitsAux v u binders F :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux
    simp
    intro _ _
    exact h2
  case eq_ x y =>
    unfold admitsAux
    simp
    intro _ _
    exact h2
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold isBoundIn at h1

    unfold admitsAux
    exact phi_ih binders h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold isBoundIn at h1
    push_neg at h1

    unfold admitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih binders h1_left h2
      · exact psi_ih binders h1_right h2
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold isBoundIn at h1
    push_neg at h1

    unfold admitsAux
    cases h1
    case intro h1_left h1_right =>
      apply phi_ih (binders ∪ {x}) h1_right
      simp
      tauto


theorem not_isBoundIn_imp_admits
  (F : Formula)
  (v u : VarName)
  (h1 : ¬ isBoundIn u F) :
  admits v u F :=
  by
  unfold admits
  apply not_isBoundIn_imp_admitsAux F v u ∅ h1
  simp

--

theorem replaceFreeAux_admitsAux
  (F : Formula)
  (v t : VarName)
  (binders : Finset VarName)
  (h1 : ¬ occursIn t F) :
  admitsAux t v binders (replaceFreeAux v t binders F) :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold occursIn at h1

    unfold replaceFreeAux
    unfold admitsAux
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
    unfold occursIn at h1
    push_neg at h1

    unfold replaceFreeAux
    unfold admitsAux
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
        cases a1
        case intro a1_left a1_right =>
          cases a1_left
          case inl a1 | inr a1 =>
          contradiction
  case true_ | false_ =>
    unfold replaceFreeAux
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold occursIn at h1

    unfold replaceFreeAux
    unfold admitsAux
    exact phi_ih binders h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold occursIn at h1
    push_neg at h1

    unfold replaceFreeAux
    unfold admitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih binders h1_left
      · exact psi_ih binders h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold occursIn at h1
    push_neg at h1

    unfold replaceFreeAux
    unfold admitsAux
    tauto


theorem replaceFree_admits
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ occursIn t F) :
  admits t v (replaceFree v t F) :=
  by
  unfold replaceFree
  unfold admits
  exact replaceFreeAux_admitsAux F v t ∅ h1

--

theorem admitsAux_add_binders
  (F : Formula)
  (v u : VarName)
  (S T : Finset VarName)
  (h1 : admitsAux v u S F)
  (h2 : u ∉ T) :
  admitsAux v u (S ∪ T) F :=
  by
  induction F generalizing S
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux at h1
    simp at h1

    unfold admitsAux
    simp
    tauto
  case eq_ x y =>
    unfold admitsAux at h1
    simp at h1

    unfold admitsAux
    simp
    tauto
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold admitsAux at h1

    unfold admitsAux
    exact phi_ih S h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsAux at h1

    unfold admitsAux
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact phi_ih S h1_left
    · exact psi_ih S h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsAux at h1

    unfold admitsAux
    simp only [Finset.union_right_comm S T {x}]
    tauto


theorem admitsAux_del_binders
  (F : Formula)
  (v u : VarName)
  (S T : Finset VarName)
  (h1 : admitsAux v u (S ∪ T) F)
  (h2 : v ∉ T) :
  admitsAux v u S F :=
  by
  induction F generalizing S
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux at h1
    simp at h1

    unfold admitsAux
    simp
    tauto
  case eq_ x y =>
    unfold admitsAux at h1
    simp at h1

    unfold admitsAux
    simp
    tauto
  case true_ | false_ =>
    unfold admitsAux
    simp
  case not_ phi phi_ih =>
    unfold admitsAux at h1

    unfold admitsAux
    exact phi_ih S h1
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsAux at h1

    unfold admitsAux
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih S h1_left
      · exact psi_ih S h1_right
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsAux at h1
    simp only [Finset.union_right_comm S T {x}] at h1

    unfold admitsAux
    tauto


theorem admitsAux_isFreeIn
  (F : Formula)
  (v u : VarName)
  (binders : Finset VarName)
  (h1 : admitsAux v u binders F)
  (h2 : isFreeIn v F)
  (h3 : v ∉ binders) :
  u ∉ binders :=
  by
  induction F generalizing binders
  case pred_const_ X xs | pred_var_ X xs | def_ X xs =>
    unfold admitsAux at h1
    simp at h1

    unfold isFreeIn at h2

    exact h1 h2 h3
  case eq_ x y =>
    unfold admitsAux at h1
    simp at h1

    unfold isFreeIn at h2

    exact h1 h2 h3
  case true_ | false_ =>
    unfold isFreeIn at h2

    contradiction
  case not_ phi phi_ih =>
    unfold admitsAux at h1

    unfold isFreeIn at h2

    exact phi_ih binders h1 h2 h3
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold admitsAux at h1

    unfold isFreeIn at h2

    cases h1
    case intro h1_left h1_right =>
      cases h2
      case inl h2 =>
        exact phi_ih binders h1_left h2 h3
      case inr h2 =>
        exact psi_ih binders h1_right h2 h3
  case forall_ x phi phi_ih | exists_ x phi phi_ih =>
    unfold admitsAux at h1

    unfold isFreeIn at h2

    cases h2
    case intro h2_left h2_right =>
      apply phi_ih binders
      · apply admitsAux_del_binders phi v u binders {x} h1
        · simp
          exact h2_left
      · exact h2_right
      · exact h3


theorem substitution_theorem_aux
  (D : Type)
  (I : Interpretation D)
  (V V' : VarAssignment D)
  (E : Env)
  (v t : VarName)
  (binders : Finset VarName)
  (F : Formula)
  (h1 : fastAdmitsAux v t binders F)
  (h2 : ∀ v : VarName, ¬ v ∈ binders → V' v = V v) :
  Holds D I (Function.updateIte V v (V' t)) E F ↔
    Holds D I V E (fastReplaceFree v t F) :=
  by
  induction E generalizing F binders V
  all_goals
    induction F generalizing binders V
    case pred_const_ X xs | pred_var_ X xs =>
      unfold fastAdmitsAux at h1

      unfold fastReplaceFree
      simp only [Holds]
      unfold Function.updateIte
      congr! 1
      simp
      simp only [List.map_eq_map_iff]
      intro x a1
      simp only [eq_comm]
      simp
      split_ifs
      case _ c1 =>
        subst c1
        tauto
      case _ c1 =>
        rfl
    case eq_ x y =>
      unfold fastAdmitsAux at h1

      unfold fastReplaceFree
      unfold Holds
      unfold Function.updateIte
      simp only [eq_comm]
      congr! 1
      all_goals
        split_ifs
        case _ c1 =>
          subst c1
          tauto
        case _ c1 =>
          rfl
    case true_ | false_ =>
      unfold fastReplaceFree
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold fastAdmitsAux at h1

      unfold fastReplaceFree
      simp only [Holds]
      congr! 1
      exact phi_ih V binders h1 h2
    case
        imp_ phi psi phi_ih psi_ih
      | and_ phi psi phi_ih psi_ih
      | or_ phi psi phi_ih psi_ih
      | iff_ phi psi phi_ih psi_ih =>
      unfold fastAdmitsAux at h1

      unfold fastReplaceFree
      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
      congr! 1
      · exact phi_ih V binders h1_left h2
      · exact psi_ih V binders h1_right h2
    case forall_ x phi phi_ih | exists_ x phi phi_ih =>
      unfold fastAdmitsAux at h1

      unfold fastReplaceFree
      split_ifs
      case _ c1 =>
        subst c1
        simp only [Holds]
        first | apply forall_congr' | apply exists_congr
        intro d
        congr! 1
        funext x
        unfold Function.updateIte
        split_ifs <;> rfl
      case _ c1 =>
        simp only [Holds]
        first | apply forall_congr' | apply exists_congr
        intro d
        cases h1
        case inl h1 =>
          contradiction
        case inr h1 =>
          simp only [Function.updateIte_comm V v x d (V' t) c1]
          apply phi_ih (Function.updateIte V x d) (binders ∪ {x}) h1
          unfold Function.updateIte
          simp
          push_neg
          intros v' a1
          cases a1
          case intro a1_left a1_right =>
            simp only [if_neg a1_right]
            tauto

  case nil.def_ X xs =>
    unfold fastReplaceFree
    simp only [Holds]

  case cons.def_ hd tl ih X xs =>
      unfold fastAdmitsAux at h1

      unfold fastReplaceFree
      simp only [Holds]
      unfold Function.updateIte
      congr! 1
      case _ =>
        simp
      case _ c1 =>
        apply Holds_coincide_Var
        intro v' a1
        simp

        have s1 : (List.map (fun a => if a = v then V' t else V a) xs) = (List.map (V ∘ fun x => if v = x then t else x) xs)
        {
        simp only [List.map_eq_map_iff]
        intro x a2
        simp only [eq_comm]
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
        apply Function.updateListIte_mem_eq_len
        · simp only [isFreeIn_iff_mem_freeVarSet] at a1
          simp only [← List.mem_toFinset]
          apply Finset.mem_of_subset hd.h1 a1
        · simp at c1
          cases c1
          case intro c1_left c1_right =>
            simp
            simp only [eq_comm]
            exact c1_right
      case _ _ =>
        apply ih V binders
        · unfold fastAdmitsAux
          exact h1
        · exact h2


theorem substitution_theorem
  (D : Type)
  (I : Interpretation D)
  (V : VarAssignment D)
  (E : Env)
  (v t : VarName)
  (F : Formula)
  (h1 : fastAdmits v t F) :
  Holds D I (Function.updateIte V v (V t)) E F ↔
    Holds D I V E (fastReplaceFree v t F) :=
  by
  unfold fastAdmits at h1

  apply substitution_theorem_aux D I V V E v t ∅ F h1
  simp


theorem substitution_is_valid
  (v t : VarName)
  (F : Formula)
  (h1 : fastAdmits v t F)
  (h2 : F.IsValid) :
  (fastReplaceFree v t F).IsValid :=
  by
  unfold IsValid at h2

  unfold IsValid
  intro D I V E
  simp only [← substitution_theorem D I V E v t F h1]
  apply h2


--#lint
