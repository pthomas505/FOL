import FOL.Computing.EpsilonNFA

import Mathlib.Data.Set.Basic


set_option autoImplicit false


inductive RegExp
  (α : Type)
  [DecidableEq α] :
  Type
  | char : α → RegExp α
  | epsilon : RegExp α
  | zero : RegExp α
  | union : RegExp α → RegExp α → RegExp α
  | concat : RegExp α → RegExp α → RegExp α
  | closure : RegExp α → RegExp α
  deriving Repr


def RegExp.languageOf
  (α : Type)
  [DecidableEq α] :
  RegExp α → Set (List α)
  | char x => { [x] }
  | epsilon => { [] }
  | zero => ∅
  | union R S => R.languageOf ∪ S.languageOf

  -- For each string r in L(R) and each string s in L(S), the string rs, the concatenation of strings r and s, is in L(RS).
  | concat R S => { r ++ s | (r ∈ R.languageOf) (s ∈ S.languageOf) }

  -- l is the concatenation of a list of strings, each of which is in L(R).
  | closure R => { l | ∃ rs : List (List α), (∀ (r : List α), r ∈ rs → r ∈ R.languageOf) ∧ rs.join = l }


example
  {α : Type}
  [DecidableEq α]
  (R : RegExp α) :
  (RegExp.union R RegExp.zero).languageOf = R.languageOf ∧
    (RegExp.union RegExp.zero R).languageOf = R.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  [DecidableEq α]
  (R : RegExp α) :
  (RegExp.concat R RegExp.epsilon).languageOf = R.languageOf ∧
    (RegExp.concat RegExp.epsilon R).languageOf = R.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  [DecidableEq α]
  (R : RegExp α) :
  (RegExp.concat R RegExp.zero).languageOf = RegExp.zero.languageOf ∧
    (RegExp.concat RegExp.zero R).languageOf = RegExp.zero.languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  [DecidableEq α]
  (R S : RegExp α) :
  (RegExp.union R S).languageOf = (RegExp.union S R).languageOf :=
  by
  simp only [RegExp.languageOf]
  exact Set.union_comm (RegExp.languageOf α R) (RegExp.languageOf α S)


example
  {α : Type}
  [DecidableEq α]
  (R S T : RegExp α) :
  (RegExp.union (RegExp.union R S) T).languageOf =
    (RegExp.union R (RegExp.union S T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  exact Set.union_assoc (RegExp.languageOf α R) (RegExp.languageOf α S) (RegExp.languageOf α T)


example
  {α : Type}
  [DecidableEq α]
  (R S T : RegExp α) :
  (RegExp.concat (RegExp.concat R S) T).languageOf =
    (RegExp.concat R (RegExp.concat S T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  simp


example
  {α : Type}
  [DecidableEq α]
  (R S T : RegExp α) :
  (RegExp.concat R (RegExp.union S T)).languageOf =
    (RegExp.union (RegExp.concat R S) (RegExp.concat R T)).languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  constructor
  · simp
    intro xs a1 ys a2 a3
    subst a3
    cases a2
    case _ c1 =>
      left
      apply Exists.intro xs
      constructor
      · exact a1
      · apply Exists.intro ys
        tauto
    case _ c1 =>
      right
      apply Exists.intro xs
      constructor
      · exact a1
      · apply Exists.intro ys
        tauto
  · simp
    intro a1
    cases a1
    all_goals
      case _ c1 =>
        apply Exists.elim c1
        intro xs a2
        clear c1
        cases a2
        case _ a2_left a2_right =>
          apply Exists.elim a2_right
          intro ys a3
          apply Exists.intro xs
          constructor
          · tauto
          · apply Exists.intro ys
            tauto


example
  {α : Type}
  [DecidableEq α]
  (R S T : RegExp α) :
  (RegExp.concat (RegExp.union S T) R).languageOf =
    (RegExp.union (RegExp.concat S R) (RegExp.concat T R)).languageOf :=
  by
  simp only [RegExp.languageOf]
  aesop


example
  {α : Type}
  [DecidableEq α] :
  (RegExp.closure RegExp.zero).languageOf α = RegExp.epsilon.languageOf :=
  by
  simp only [RegExp.languageOf]
  ext cs
  simp
  constructor
  · aesop
  · intro a1
    apply Exists.intro []
    simp
    simp only [a1]


example
  {α : Type}
  [DecidableEq α]
  (R : RegExp α) :
  (RegExp.concat R (RegExp.closure R)).languageOf =
    (RegExp.concat (RegExp.closure R) R).languageOf :=
  by
    simp only [RegExp.languageOf]
    ext cs
    simp
    constructor
    · intro a1
      apply Exists.elim a1
      intro r a2
      clear a1

      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro rs a3
        clear a2_right

        cases a3
        case _ a3_left a3_right =>
          · obtain s1 := List.eq_nil_or_concat (r :: rs)
            simp at s1

            apply Exists.elim s1
            intro rs' a4
            clear s1

            apply Exists.elim a4
            intro r' a5
            clear a4

            have s2 : ∀ (x : List α), x ∈ (r :: rs) →
              x ∈ RegExp.languageOf α R :=
            by
              simp
              tauto

            apply Exists.intro rs'
            constructor
            · intro x a6
              apply s2
              simp only [a5]
              simp
              left
              exact a6

            · apply Exists.intro r'
              constructor
              · apply s2
                simp only [a5]
                simp
              · simp only [← a3_right]

                have s3 : List.join rs' ++ r' = List.join (rs' ++ [r']) :=
                by
                  simp

                simp only [s3]

                have s4 : r ++ List.join rs = List.join (r :: rs) :=
                by
                  simp

                simp only [s4]

                simp only [a5]
    · intro a1
      apply Exists.elim a1
      intro rs a2
      clear a1
      cases a2
      case _ a2_left a2_right =>
        apply Exists.elim a2_right
        intro r a3
        clear a2_right
        cases a3
        case _ a3_left a3_right =>
          subst a3_right

          have s2 : List.join rs ++ r = List.join (rs ++ [r]) :=
          by
            simp

          simp only [s2]
          clear s2

          have s3 : r ++ List.join rs = List.join ([r] ++ rs) :=
          by
            simp

          cases rs
          case nil =>
            apply Exists.intro r
            constructor
            · exact a3_left
            · apply Exists.intro []
              simp
          case cons hd tl =>
            simp at a2_left
            cases a2_left
            case _ a2_left_left a2_left_right =>
              apply Exists.intro hd
              constructor
              · exact a2_left_left
              · apply Exists.intro (tl ++ [r])
                constructor
                · simp
                  intro r' a4
                  cases a4
                  case _ a4_left =>
                    apply a2_left_right
                    exact a4_left
                  case _ a4_right =>
                    subst a4_right
                    exact a3_left
                · simp


def EpsilonNFA.wrapLeft
  {α : Type}
  [DecidableEq α]
  {σ_l : Type}
  [DecidableEq σ_l]
  (σ_r : Type)
  [DecidableEq σ_r]
  (e : EpsilonNFA α σ_l) :
  EpsilonNFA α (σ_l ⊕ σ_r) :=
  {
    symbol_step_list := e.symbol_step_list.map (fun (step : SymbolStepMultiple α σ_l) => ⟨
      Sum.inl step.start_state,
      step.symbol,
      step.stop_state_list.map Sum.inl
    ⟩),
    epsilon_step_list := e.epsilon_step_list.map (fun (step : EpsilonStepMultiple σ_l) => ⟨
      Sum.inl step.start_state,
      step.stop_state_list.map Sum.inl
    ⟩),
    starting_state_list := e.starting_state_list.map Sum.inl,
    accepting_state_list := e.accepting_state_list.map Sum.inl
  }


example
  (α : Type)
  [DecidableEq α]
  (σ_l σ_r : Type)
  [DecidableEq σ_l]
  [DecidableEq σ_r]
  (e : EpsilonNFA α σ_l)
  (xs : List α) :
  e.accepts xs ↔ (e.wrapLeft σ_r).accepts xs :=
  by
  set e_left := e.wrapLeft σ_r
  simp only [EpsilonNFA.accepts]
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.eval_from]
  simp
  constructor
  · intro a1
    left
    apply Exists.elim a1
    intro s a2
    clear a1
    cases a2
    case _ a2_left a2_right =>
      apply Exists.intro s
      constructor
      · simp only [e_left]
        sorry
      · simp only [e_left]
        simp only [EpsilonNFA.wrapLeft]
        simp
        exact a2_right
  · intro a1
    cases a1
    case _ c1 =>
      apply Exists.elim c1
      intro s a2
      clear c1
      cases a2
      case _ a2_left a2_right =>
        apply Exists.intro s
        constructor
        · sorry
        · sorry
    case _ c1 =>
      apply Exists.elim c1
      intro s a2
      clear c1
      simp only [e_left] at a2
      simp only [EpsilonNFA.wrapLeft] at a2
      simp at a2


def EpsilonNFA.wrapRight
  {α : Type}
  [DecidableEq α]
  {σ_l : Type}
  [DecidableEq σ_l]
  (σ_r : Type)
  [DecidableEq σ_r]
  (e : EpsilonNFA α σ_r) :
  EpsilonNFA α (σ_l ⊕ σ_r) :=
  {
    symbol_step_list := e.symbol_step_list.map (fun (step : SymbolStepMultiple α σ_r) => ⟨
      Sum.inr step.start_state,
      step.symbol,
      step.stop_state_list.map Sum.inr
    ⟩),
    epsilon_step_list := e.epsilon_step_list.map (fun (step : EpsilonStepMultiple σ_r) => ⟨
      Sum.inr step.start_state,
      step.stop_state_list.map Sum.inr
    ⟩),
    starting_state_list := e.starting_state_list.map Sum.inr,
    accepting_state_list := e.accepting_state_list.map Sum.inr
  }


def match_char_EpsilonNFA
  {α : Type}
  [DecidableEq α]
  (c : α) :
  EpsilonNFA α ℕ :=
  {
    symbol_step_list := [⟨0, c, [1]⟩]
    epsilon_step_list := []
    starting_state_list := [0]
    accepting_state_list := [1]
  }


example : (match_char_EpsilonNFA 'a').eval [] = [0] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['a'] = [1] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['b'] = [] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['a', 'b'] = [] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['b', 'a'] = [] := by rfl

example : ¬ (match_char_EpsilonNFA 'a').accepts [] :=
  by
  simp only [match_char_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.eval_from]
  simp

example : (match_char_EpsilonNFA 'a').accepts ['a'] :=
  by
  simp only [match_char_EpsilonNFA]

  simp only [EpsilonNFA.accepts]
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.eval_from]
  simp
  apply List.mem_of_elem_eq_true
  exact rfl

example : ¬ (match_char_EpsilonNFA 'a').accepts ['b'] :=
  by
  simp only [match_char_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  tauto

example : ¬ (match_char_EpsilonNFA 'a').accepts ['a', 'b'] :=
  by
  simp only [match_char_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  tauto

example : ¬ (match_char_EpsilonNFA 'a').accepts ['b', 'a'] :=
  by
  simp only [match_char_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  tauto


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x : α) :
  (match_char_EpsilonNFA c).accepts [x] ↔ c = x :=
  by
  simp only [match_char_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  simp
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.eval_from]
  simp
  simp only [EpsilonNFA.eval_one]
  simp
  simp only [symbol_step_multiple_list_to_fun]
  simp only [epsilon_closure]
  simp only [epsilon_step_multiple_list_to_graph]
  simp only [epsilon_step_multiple_list_to_single_list]
  simp only [epsilon_step_single_list_to_graph]
  simp
  split_ifs
  case pos c1 =>
    simp only [c1]
    simp
    apply List.mem_of_elem_eq_true
    exact rfl
  case neg c1 =>
    simp only [c1]
    simp
    exact List.count_eq_zero.mp rfl


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x : α)
  (xs : List α)
  (h1 : ¬ xs = []) :
  ¬ (match_char_EpsilonNFA c).accepts (x :: xs) :=
  by
  simp only [match_char_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  simp
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.eval_from]
  simp
  simp only [EpsilonNFA.eval_one]
  simp
  simp only [symbol_step_multiple_list_to_fun]
  simp only [epsilon_closure]
  simp only [epsilon_step_multiple_list_to_graph]
  simp only [epsilon_step_multiple_list_to_single_list]
  simp only [epsilon_step_single_list_to_graph]
  cases xs
  case nil =>
    simp at h1
  case cons xs_hd xs_tl =>
    simp
    split_ifs
    case _ c1 =>
      simp only [c1]
      simp
      sorry
    case _ c1 =>
      simp only [c1]
      simp
      sorry



def match_epsilon_EpsilonNFA
  (α : Type)
  [DecidableEq α] :
  EpsilonNFA α ℕ :=
  {
    symbol_step_list := []
    epsilon_step_list := [⟨ 0, [1] ⟩]
    starting_state_list := [0]
    accepting_state_list := [1]
  }

/-
example
  (α : Type)
  [DecidableEq α] :
  (match_epsilon_EpsilonNFA α).accepts [] :=
  by
  simp only [match_epsilon_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  simp
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.eval_from]
  simp
  simp only [EpsilonNFA.eval_one]
  simp
  simp only [symbol_step_multiple_list_to_fun]
  simp only [epsilon_closure]
  simp only [epsilon_step_multiple_list_to_graph]
  simp only [epsilon_step_multiple_list_to_single_list]
  simp only [epsilon_step_single_list_to_graph]
-/

/-

def match_zero_EpsilonNFA
  (α : Type)
  [DecidableEq α] :
  EpsilonNFA α ℕ :=
  {
/-
    stateSet := {0}
    symbolSet := {}
-/
    stepList := []
    startingStateList := [0]
    acceptingStateList := []
  }


example
  (α : Type)
  [DecidableEq α]
  (xs : List α) :
  ¬ (match_zero_EpsilonNFA α).accepts xs :=
  by
  simp only [match_zero_EpsilonNFA]
  simp only [EpsilonNFA.accepts]
  simp only [EpsilonNFA.eval]
  simp only [EpsilonNFA.evalFrom]
  simp


def match_union_EpsilonNFA
  {α : Type}
  [DecidableEq α]
  {σ_0 σ_1 : Type}
  [DecidableEq σ_0]
  [DecidableEq σ_1]
  (e1 : EpsilonNFA α σ_0)
  (e2 : EpsilonNFA α σ_1) :
  EpsilonNFA α (ℕ ⊕ (σ_0 ⊕ σ_1)) :=
  -- The states of e1 need to be made disjoint from the states of e2. Therefore the states of e1 are made Sum.inl instances of (σ_0 ⊕ σ_1) and the states of e2 are made Sum.inr instances of (σ_0 ⊕ σ_1).
  let e1' : EpsilonNFA α (σ_0 ⊕ σ_1) := e1.wrapLeft σ_1
  let e2' : EpsilonNFA α (σ_0 ⊕ σ_1) := e2.wrapRight σ_0

  -- The new EpsilonNFA needs to have a new starting state that is disjoint from the states of e1' and e2'. Therefore it is made a Sum.inl instance of (ℕ ⊕ (σ_0 ⊕ σ_1)) and the states of e1' and e2' are made Sum.inr instances of (ℕ ⊕ (σ_0 ⊕ σ_1)).
  let e1'' : EpsilonNFA α (ℕ ⊕ (σ_0 ⊕ σ_1)) := e1'.wrapRight ℕ
  let e2'' : EpsilonNFA α (ℕ ⊕ (σ_0 ⊕ σ_1)) := e2'.wrapRight ℕ

  let new_starting_state : ℕ ⊕ (σ_0 ⊕ σ_1) := Sum.inl 0

  -- A step on epsilon (represented as Option.none) from the new starting state to both the starting state of e1'' and the starting state of e2''.
  let new_starting_step : ((ℕ ⊕ (σ_0 ⊕ σ_1)) × Option α) × List (ℕ ⊕ (σ_0 ⊕ σ_1)) := ((new_starting_state, Option.none), List.dedup (e1''.startingStateList ++ e2''.startingStateList))

  {
/-
    stateSet := {new_starting_state} ∪ e1''.stateSet ∪ e2''.stateSet
    symbolSet := e1''.symbolSet ∪ e2''.symbolSet
-/
    stepList := new_starting_step :: e1''.stepList ++ e2''.stepList
    startingStateList := [new_starting_state]
    acceptingStateList := List.dedup (e1''.acceptingStateList ++ e2''.acceptingStateList)
  }


example
  (α : Type)
  [DecidableEq α]
  (σ_0 σ_1 : Type)
  [DecidableEq σ_0]
  [DecidableEq σ_1]
  (e1 : EpsilonNFA α σ_0)
  (e2 : EpsilonNFA α σ_1)
  (xs : List α)
  (h1 : e1.accepts xs) :
  (match_union_EpsilonNFA e1 e2).accepts xs :=
  by sorry


def match_concat_EpsilonNFA
  (α : Type)
  [DecidableEq α]
  (σ_0 σ_1 : Type)
  [DecidableEq σ_0]
  [DecidableEq σ_1]
  (e1 : EpsilonNFA α σ_0)
  (e2 : EpsilonNFA α σ_1) :
  EpsilonNFA α (σ_0 ⊕ σ_1) :=
  let e1' : EpsilonNFA α (σ_0 ⊕ σ_1) := e1.wrapLeft σ_1
  let e2' : EpsilonNFA α (σ_0 ⊕ σ_1) := e2.wrapRight σ_0
  {
/-
    stateSet := e1'.stateSet ∪ e2'.stateSet
    symbolSet := e1'.symbolSet ∪ e2'.symbolSet
-/
    -- Steps on epsilon from each of the accepting states of e1' to the starting state of e2'.
    stepList := e1'.acceptingStateList.map (fun (state : σ_0 ⊕ σ_1) => ((state, Option.none), e2'.startingStateList))

    startingStateList := e1'.startingStateList
    acceptingStateList := e2'.acceptingStateList
  }


def match_closure_EpsilonNFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ]
  (e : EpsilonNFA α σ) :
  EpsilonNFA α (ℕ ⊕ σ) :=

  let e' : EpsilonNFA α (ℕ ⊕ σ) := e.wrapRight ℕ

  let new_starting_state : ℕ ⊕ σ := Sum.inl 0

  -- A step on epsilon from the new starting state to the starting state of e'.
  let new_starting_step : ((ℕ ⊕ σ) × Option α) × List (ℕ ⊕ σ) := ((new_starting_state, Option.none), e'.startingStateList)

  -- Steps on epsilon from each of the accepting states of e' to the new starting state.
  let new_step_list := e'.acceptingStateList.map (fun (state : ℕ ⊕ σ) => ((state, Option.none), [new_starting_state]))

  {
/-
    stateSet := {new_starting_state} ∪ e'.stateSet
    symbolSet := e'.symbolSet
-/
    stepList := new_starting_step :: new_step_list
    startingStateList := [new_starting_state]
    acceptingStateList := new_starting_state :: e'.acceptingStateList
  }
-/
