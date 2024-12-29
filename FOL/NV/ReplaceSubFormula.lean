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

instance (U V F F' : Formula_) : Decidable (is_repl_of_formula_in_formula_fun U V F F') :=
  by
  induction F generalizing F'
  all_goals
    cases F'
    all_goals
      simp only [is_repl_of_formula_in_formula_fun]
      infer_instance


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


-------------------------------------------------------------------------------


/--
  is_repl_of_var_in_list_fun u v l_u l_v := True if and only if l_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in l_u by occurrences of v.
-/
def is_repl_of_var_in_list_fun
  (u v : VarName_) :
  List VarName_ → List VarName_ → Prop
  | [], [] => True
  | hd_u :: tl_u, hd_v :: tl_v =>
    (hd_u = hd_v ∨ (hd_u = u ∧ hd_v = v)) ∧ is_repl_of_var_in_list_fun u v tl_u tl_v
  | _, _ => False

instance (u v : VarName_) (xs xs' : List VarName_) : Decidable (is_repl_of_var_in_list_fun u v xs xs') :=
  by
  induction xs generalizing xs'
  all_goals
    cases xs'
    all_goals
      simp only [is_repl_of_var_in_list_fun]
      infer_instance


inductive is_repl_of_var_in_list
  (u v : VarName_) :
  List VarName_ → List VarName_ → Prop
  | nil_ : is_repl_of_var_in_list u v [] []

  | cons_same_
    (hd_u hd_v : VarName_)
    (tl_u tl_v : List VarName_) :
    hd_u = hd_v →
    is_repl_of_var_in_list u v tl_u tl_v →
    is_repl_of_var_in_list u v (hd_u :: tl_u) (hd_v :: tl_v)

  | cons_diff_
    (hd_u hd_v : VarName_)
    (tl_u tl_v : List VarName_) :
    hd_u = u →
    hd_v = v →
    is_repl_of_var_in_list u v tl_u tl_v →
    is_repl_of_var_in_list u v (hd_u :: tl_u) (hd_v :: tl_v)


lemma is_repl_of_var_in_list_fun_imp_is_repl_of_var_in_list
  (u v : VarName_)
  (us vs : List VarName_)
  (h1 : is_repl_of_var_in_list_fun u v us vs) :
  is_repl_of_var_in_list u v us vs :=
  by
  induction us generalizing vs
  case nil =>
    cases vs
    case nil =>
      apply is_repl_of_var_in_list.nil_
    case cons hd_v tl_v =>
      simp only [is_repl_of_var_in_list_fun] at h1
  case cons hd_u tl_u ih_u =>
    cases vs
    case nil =>
      simp only [is_repl_of_var_in_list_fun] at h1
    case cons hd_v tl_v =>
      simp only [is_repl_of_var_in_list_fun] at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      cases h1_left
      case _ h1_left =>
        apply is_repl_of_var_in_list.cons_same_
        · exact h1_left
        · apply ih_u
          exact h1_right
      case _ h1_left =>
        obtain ⟨h1_left_left, h1_left_right⟩ := h1_left
        apply is_repl_of_var_in_list.cons_diff_
        · exact h1_left_left
        · exact h1_left_right
        · apply ih_u
          exact h1_right


lemma is_repl_of_var_in_list_imp_is_repl_of_var_in_list_fun
  (u v : VarName_)
  (us vs : List VarName_)
  (h1 : is_repl_of_var_in_list u v us vs) :
  is_repl_of_var_in_list_fun u v us vs :=
  by
  induction h1
  all_goals
    simp only [is_repl_of_var_in_list_fun]
  all_goals
    tauto


-------------------------------------------------------------------------------


/--
  is_repl_of_var_in_formula_fun u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
def is_repl_of_var_in_formula_fun
  (u v : VarName_) :
  Formula_ → Formula_ → Prop
  | pred_var_ name_u args_u, pred_var_ name_v args_v =>
      name_u = name_v ∧ is_repl_of_var_in_list_fun u v args_u args_v
  | pred_const_ name_u args_u, pred_const_ name_v args_v =>
      name_u = name_v ∧ is_repl_of_var_in_list_fun u v args_u args_v
  | eq_ x_u y_u, eq_ x_v y_v =>
      is_repl_of_var_in_list_fun u v [x_u, y_u] [x_v, y_v]
  | true_, true_ => True
  | false_, false_ => True
  | not_ P_u, not_ P_v => is_repl_of_var_in_formula_fun u v P_u P_v
  | imp_ P_u Q_u, imp_ P_v Q_v =>
      is_repl_of_var_in_formula_fun u v P_u P_v ∧
      is_repl_of_var_in_formula_fun u v Q_u Q_v
  | and_ P_u Q_u, and_ P_v Q_v =>
      is_repl_of_var_in_formula_fun u v P_u P_v ∧
      is_repl_of_var_in_formula_fun u v Q_u Q_v
  | or_ P_u Q_u, or_ P_v Q_v =>
      is_repl_of_var_in_formula_fun u v P_u P_v ∧
      is_repl_of_var_in_formula_fun u v Q_u Q_v
  | iff_ P_u Q_u, iff_ P_v Q_v =>
      is_repl_of_var_in_formula_fun u v P_u P_v ∧
      is_repl_of_var_in_formula_fun u v Q_u Q_v
  | forall_ x P_u, forall_ x' P_v =>
      x = x' ∧ is_repl_of_var_in_formula_fun u v P_u P_v
  | exists_ x P_u, exists_ x' P_v =>
      x = x' ∧ is_repl_of_var_in_formula_fun u v P_u P_v
  | _, _ => False

instance (u v : VarName_) (F F' : Formula_) : Decidable (is_repl_of_var_in_formula_fun u v F F') :=
  by
  induction F generalizing F'
  all_goals
    cases F'
    all_goals
      simp only [is_repl_of_var_in_formula_fun]
      infer_instance


/--
  `is_repl_of_var_in_formula u v P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `u` in `P_u` by occurrences of `v`.
-/
inductive is_repl_of_var_in_formula
  (u v : VarName_) :
  Formula_ → Formula_ → Prop
  | pred_const_
    (name_u name_v : PredName_)
    (args_u args_v : List VarName_) :
    name_u = name_v →
    is_repl_of_var_in_list u v args_u args_v →
    is_repl_of_var_in_formula u v (pred_const_ name_u args_u) (pred_const_ name_v args_v)

  | pred_var_
    (name_u name_v : PredName_)
    (args_u args_v : List VarName_) :
    name_u = name_v →
    is_repl_of_var_in_list u v args_u args_v →
    is_repl_of_var_in_formula u v (pred_var_ name_u args_u) (pred_var_ name_v args_v)

  | eq_
    (x_u y_u x_v y_v : VarName_) :
    ((x_u = x_v) ∨ (x_u = u ∧ x_v = v)) →
    ((y_u = y_v) ∨ (y_u = u ∧ y_v = v)) →
    is_repl_of_var_in_formula u v (eq_ x_u y_u) (eq_ x_v y_v)

  | true_ :
    is_repl_of_var_in_formula u v true_ true_

  | false_ :
    is_repl_of_var_in_formula u v false_ false_

  | not_
    (P_u P_v : Formula_) :
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v Q_u Q_v →
    is_repl_of_var_in_formula u v (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v Q_u Q_v →
    is_repl_of_var_in_formula u v (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v Q_u Q_v →
    is_repl_of_var_in_formula u v (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v Q_u Q_v →
    is_repl_of_var_in_formula u v (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x_u x_v : VarName_)
    (P_u P_v : Formula_) :
    x_u = x_v →
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v (forall_ x_u P_u) (forall_ x_v P_v)

  | exists_
    (x_u x_v : VarName_)
    (P_u P_v : Formula_) :
    x_u = x_v →
    is_repl_of_var_in_formula u v P_u P_v →
    is_repl_of_var_in_formula u v (exists_ x_u P_u) (exists_ x_v P_v)


example
  (u v : VarName_)
  (n : ℕ)
  (args_u args_v : Fin n → VarName_)
  (h1 : ∀ (i : Fin n), args_u i = args_v i ∨ args_u i = u ∧ args_v i = v) :
  is_repl_of_var_in_list_fun u v (List.ofFn args_u) (List.ofFn args_v) :=
  by
  induction n
  case zero =>
    simp_all only [IsEmpty.forall_iff, List.ofFn_zero]
    unfold is_repl_of_var_in_list_fun
    trivial
  case succ m ih =>
    simp_all only [List.ofFn_succ]
    unfold is_repl_of_var_in_list_fun
    constructor
    · apply h1
    · exact ih (fun i => args_u i.succ) (fun i => args_v i.succ) fun i => h1 i.succ


example
  (u v : VarName_)
  (F F' : Formula_)
  (h1 : is_repl_of_var_in_formula u v F F') :
  is_repl_of_var_in_formula_fun u v F F' :=
  by
  induction h1
  case
      pred_const_ name_u name_v args_u args_v ih_1 ih_2
    | pred_var_ name_u name_v args_u args_v ih_1 ih_2 =>
    unfold is_repl_of_var_in_formula_fun
    constructor
    · exact ih_1
    · apply is_repl_of_var_in_list_imp_is_repl_of_var_in_list_fun
      exact ih_2
  case eq_ x_u y_u x_v y_v ih_1 ih_2 =>
    unfold is_repl_of_var_in_formula_fun
    simp only [is_repl_of_var_in_list_fun]
    tauto
  case true_ =>
    simp only [is_repl_of_var_in_formula_fun]
  case false_ =>
    simp only [is_repl_of_var_in_formula_fun]
  case not_ P_u P_v ih_1 ih_2 =>
    unfold is_repl_of_var_in_formula_fun
    exact ih_2
  case
      imp_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | and_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | or_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4
    | iff_ P_u Q_u P_v Q_v ih_1 ih_2 ih_3 ih_4 =>
    unfold is_repl_of_var_in_formula_fun
    tauto
  case
      forall_ x P_u P_v ih_1 ih_2
    | exists_ x P_u P_v ih_1 ih_2 =>
    unfold is_repl_of_var_in_formula_fun
    tauto


example
  (u v : VarName_)
  (F F' : Formula_)
  (h1 : is_repl_of_var_in_formula_fun u v F F') :
  is_repl_of_var_in_formula u v F F' :=
  by
  induction F generalizing F'
  all_goals
    cases F'
  case
      pred_const_.pred_const_ name_u args_u name_v args_v
    | pred_var_.pred_var_ name_u args_u name_v args_v =>
    simp only [is_repl_of_var_in_formula_fun] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    first
      | apply is_repl_of_var_in_formula.pred_const_
      | apply is_repl_of_var_in_formula.pred_var_
    · exact h1_left
    · apply is_repl_of_var_in_list_fun_imp_is_repl_of_var_in_list
      exact h1_right
  case eq_.eq_ x_u y_u x_v y_v =>
    simp only [is_repl_of_var_in_formula_fun] at h1
    simp only [is_repl_of_var_in_list_fun] at h1

    apply is_repl_of_var_in_formula.eq_
    · tauto
    · tauto
  case true_.true_ =>
    apply is_repl_of_var_in_formula.true_
  case false_.false_ =>
    apply is_repl_of_var_in_formula.false_
  case not_.not_ phi_u ih phi_v =>
    simp only [is_repl_of_var_in_formula_fun] at h1

    apply is_repl_of_var_in_formula.not_
    tauto
  case
      imp_.imp_ phi_u psi_u ih_1 ih_2 phi_v psi_v
    | and_.and_ phi_u psi_u ih_1 ih_2 phi_v psi_v
    | or_.or_ phi_u psi_u ih_1 ih_2 phi_v psi_v
    | iff_.iff_ phi_u psi_u ih_1 ih_2 phi_v psi_v =>
    simp only [is_repl_of_var_in_formula_fun] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    first
      | apply is_repl_of_var_in_formula.imp_
      | apply is_repl_of_var_in_formula.and_
      | apply is_repl_of_var_in_formula.or_
      | apply is_repl_of_var_in_formula.iff_
    · tauto
    · tauto
  case
      forall_.forall_ x_u phi_u ih x_v phi_v
    | exists_.exists_ x_u phi_u ih x_v phi_v =>
    simp only [is_repl_of_var_in_formula_fun] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    first
      | apply is_repl_of_var_in_formula.forall_
      | apply is_repl_of_var_in_formula.exists_
    · exact h1_left
    · apply ih
      exact h1_right
  all_goals
    simp only [is_repl_of_var_in_formula_fun] at h1


-------------------------------------------------------------------------------


/--
  `is_repl_of_var_in_formula_fin u v P_u P_v` := True if and only if `P_v` is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of `u` in `P_u` by occurrences of `v`.
-/
inductive is_repl_of_var_in_formula_fin
  (u v : VarName_) :
  Formula_ → Formula_ → Prop
  | pred_const_
    (name : PredName_)
    (n : ℕ)
    (args_u args_v : Fin n → VarName_) :
    (∀ (i : Fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
    is_repl_of_var_in_formula_fin u v (pred_const_ name (List.ofFn args_u)) (pred_const_ name (List.ofFn args_v))

  | pred_var_
    (name : PredName_)
    (n : ℕ)
    (args_u args_v : Fin n → VarName_) :
    (∀ (i : Fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
    is_repl_of_var_in_formula_fin u v (pred_var_ name (List.ofFn args_u)) (pred_var_ name (List.ofFn args_v))

  | eq_
    (x_u y_u x_v y_v : VarName_) :
    ((x_u = x_v) ∨ (x_u = u ∧ x_v = v)) →
    ((y_u = y_v) ∨ (y_u = u ∧ y_v = v)) →
    is_repl_of_var_in_formula_fin u v (eq_ x_u y_u) (eq_ x_v y_v)

  | true_ :
    is_repl_of_var_in_formula_fin u v true_ true_

  | false_ :
    is_repl_of_var_in_formula_fin u v false_ false_

  | not_
    (P_u P_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v P_u.not_ P_v.not_

  | imp_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v Q_u Q_v →
    is_repl_of_var_in_formula_fin u v (P_u.imp_ Q_u) (P_v.imp_ Q_v)

  | and_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v Q_u Q_v →
    is_repl_of_var_in_formula_fin u v (P_u.and_ Q_u) (P_v.and_ Q_v)

  | or_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v Q_u Q_v →
    is_repl_of_var_in_formula_fin u v (P_u.or_ Q_u) (P_v.or_ Q_v)

  | iff_
    (P_u Q_u : Formula_)
    (P_v Q_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v Q_u Q_v →
    is_repl_of_var_in_formula_fin u v (P_u.iff_ Q_u) (P_v.iff_ Q_v)

  | forall_
    (x : VarName_)
    (P_u P_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v (forall_ x P_u) (forall_ x P_v)

  | exists_
    (x : VarName_)
    (P_u P_v : Formula_) :
    is_repl_of_var_in_formula_fin u v P_u P_v →
    is_repl_of_var_in_formula_fin u v (exists_ x P_u) (exists_ x P_v)


--#lint
