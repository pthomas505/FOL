import FOL.NV.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `is_repl_of_formula_in_formula_fun U V P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `U` in `P_u` by occurrences of `V`.
-/
def is_repl_of_formula_in_formula_fun
  (U V : Formula_) :
  Formula_ → Formula_ → Prop
  | not_ P_u, not_ P_v =>
    not_ P_u = not_ P_v ∨ (not_ P_u = U ∧ not_ P_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v

  | imp_ P_u Q_u, imp_ P_v Q_v =>
    imp_ P_u Q_u = imp_ P_v Q_v ∨ (imp_ P_u Q_u = U ∧ imp_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | and_ P_u Q_u, and_ P_v Q_v =>
    and_ P_u Q_u = and_ P_v Q_v ∨ (and_ P_u Q_u = U ∧ and_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | or_ P_u Q_u, or_ P_v Q_v =>
    or_ P_u Q_u = or_ P_v Q_v ∨ (or_ P_u Q_u = U ∧ or_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | iff_ P_u Q_u, iff_ P_v Q_v =>
    iff_ P_u Q_u = iff_ P_v Q_v ∨ (iff_ P_u Q_u = U ∧ iff_ P_v Q_v = V) ∨
    is_repl_of_formula_in_formula_fun U V P_u P_v ∧ is_repl_of_formula_in_formula_fun U V Q_u Q_v

  | forall_ x_u P_u, forall_ x_v P_v =>
    forall_ x_u P_u = forall_ x_v P_v ∨ (forall_ x_u P_u = U ∧ forall_ x_v P_v = V) ∨
    (x_u = x_v ∧ is_repl_of_formula_in_formula_fun U V P_u P_v)

  | exists_ x_u P_u, exists_ x_v P_v =>
    exists_ x_u P_u = exists_ x_v P_v ∨ (exists_ x_u P_u = U ∧ exists_ x_v P_v = V) ∨
    (x_u = x_v ∧ is_repl_of_formula_in_formula_fun U V P_u P_v)

  | P_u, P_v => P_u = P_v ∨ (P_u = U ∧ P_v = V)


/--
  `is_repl_of_formula_in_formula U V P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `U` in `P_u` by occurrences of `V`.
-/
inductive is_repl_of_formula_in_formula
  (U V : Formula_) :
  Formula_ → Formula_ → Prop

    -- not replacing an occurrence
  | same_
    (P_u P_v : Formula_) :
    P_u = P_v →
    is_repl_of_formula_in_formula U V P_u P_v

    -- replacing an occurrence
  | diff_
    (P_u P_v : Formula_) :
    P_u = U →
    P_v = V →
    is_repl_of_formula_in_formula U V P_u P_v

  | not_
    (P_u P_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V Q_u Q_v →
    is_repl_of_formula_in_formula U V (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x_u x_v : VarName_)
    (P_u P_v : Formula_) :
    x_u = x_v →
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V (forall_ x_u P_u) (forall_ x_v P_v)

  | exists_
    (x_u x_v : VarName_)
    (P_u P_v : Formula_) :
    x_u = x_v →
    is_repl_of_formula_in_formula U V P_u P_v →
    is_repl_of_formula_in_formula U V (exists_ x_u P_u) (exists_ x_v P_v)


example
  (U V : Formula_)
  (F F' : Formula_)
  (h1 : is_repl_of_formula_in_formula_fun U V F F') :
  is_repl_of_formula_in_formula U V F F' :=
  by
  induction F generalizing F'
  all_goals
    cases F'
  case
      pred_const_.pred_const_ X xs X' xs'
    | pred_var_.pred_var_ X xs X' xs'
    | eq_.eq_ x y x' y'
    | def_.def_ X xs X' xs' =>
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl c1 =>
      apply is_repl_of_formula_in_formula.same_
      exact c1
    case inr c1 =>
      obtain ⟨c1_left, c1_right⟩ := c1
      apply is_repl_of_formula_in_formula.diff_
      · exact c1_left
      · exact c1_right
  case
      true_.true_
    | false_.false_ =>
    apply is_repl_of_formula_in_formula.same_
    rfl
  case not_.not_ phi ih phi' =>
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1
        apply is_repl_of_formula_in_formula.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        apply is_repl_of_formula_in_formula.not_
        apply ih
        exact h1
  case
      imp_.imp_ phi psi phi_ih psi_ih phi' psi'
    | and_.and_ phi psi phi_ih psi_ih phi' psi'
    | or_.or_ phi psi phi_ih psi_ih phi' psi'
    | iff_.iff_ phi psi phi_ih psi_ih phi' psi' =>
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1
        apply is_repl_of_formula_in_formula.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1

        first
          | apply is_repl_of_formula_in_formula.imp_
          | apply is_repl_of_formula_in_formula.and_
          | apply is_repl_of_formula_in_formula.or_
          | apply is_repl_of_formula_in_formula.iff_
        · apply phi_ih
          exact h1_left
        · apply psi_ih
          exact h1_right
  case
      forall_.forall_ x phi ih x' phi'
    | exists_.exists_ x phi ih x' phi' =>

    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    case inl h1 =>
      apply is_repl_of_formula_in_formula.same_
      exact h1
    case inr h1 =>
      cases h1
      case inl h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1
        apply is_repl_of_formula_in_formula.diff_
        · exact h1_left
        · exact h1_right
      case inr h1 =>
        obtain ⟨h1_left, h1_right⟩ := h1

        first
          | apply is_repl_of_formula_in_formula.forall_
          | apply is_repl_of_formula_in_formula.exists_
        · exact h1_left
        · apply ih
          exact h1_right
  all_goals
    unfold is_repl_of_formula_in_formula_fun at h1
    cases h1
    · simp_all only [reduceCtorEq]
    · simp_all only
      apply is_repl_of_formula_in_formula.diff_
      · rfl
      · rfl


example
  (U V : Formula_)
  (F F' : Formula_)
  (h1 : is_repl_of_formula_in_formula U V F F') :
  is_repl_of_formula_in_formula_fun U V F F' :=
  by
  induction h1
  case same_ P_u P_v h1_ih =>
    induction P_u generalizing P_v
    all_goals
      cases P_v
      all_goals
        simp only [is_repl_of_formula_in_formula_fun]
        tauto
  case diff_ P_u P_v h1_ih_1 h1_ih_2 =>
    induction P_u generalizing P_v
    all_goals
      cases P_v
      all_goals
        simp only [is_repl_of_formula_in_formula_fun]
        tauto
  all_goals
    simp only [is_repl_of_formula_in_formula_fun]
    tauto


#lint
