import FOL.Computing.RegExp
import FOL.Computing.EpsilonNFA


set_option autoImplicit false


def EpsilonNFA.wrapLeft
  {α : Type}
  {σ_l : Type}
  (σ_r : Type)
  (e : EpsilonNFA α σ_l) :
  EpsilonNFA α (σ_l ⊕ σ_r) :=
  {
    symbol_arrow_list := e.symbol_arrow_list.map (fun (arrow : SymbolArrow α σ_l) => ⟨
      Sum.inl arrow.start_state,
      arrow.symbol,
      arrow.stop_state_list.map Sum.inl
    ⟩),
    epsilon_arrow_list := e.epsilon_arrow_list.map (fun (arrow : EpsilonArrow σ_l) => ⟨
      Sum.inl arrow.start_state,
      arrow.stop_state_list.map Sum.inl
    ⟩),
    starting_state_list := e.starting_state_list.map Sum.inl,
    accepting_state_list := e.accepting_state_list.map Sum.inl
  }


def EpsilonNFA.wrapRight
  {α : Type}
  (σ_l : Type)
  {σ_r : Type}
  (e : EpsilonNFA α σ_r) :
  EpsilonNFA α (σ_l ⊕ σ_r) :=
  {
    symbol_arrow_list := e.symbol_arrow_list.map (fun (arrow : SymbolArrow α σ_r) => ⟨
      Sum.inr arrow.start_state,
      arrow.symbol,
      arrow.stop_state_list.map Sum.inr
    ⟩),
    epsilon_arrow_list := e.epsilon_arrow_list.map (fun (arrow : EpsilonArrow σ_r) => ⟨
      Sum.inr arrow.start_state,
      arrow.stop_state_list.map Sum.inr
    ⟩),
    starting_state_list := e.starting_state_list.map Sum.inr,
    accepting_state_list := e.accepting_state_list.map Sum.inr
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
  induction xs
  case nil =>
    simp only [EpsilonNFA.accepts]
    simp only [EpsilonNFA.eval]
    simp only [EpsilonNFA.eval_from]
    sorry
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
      · sorry
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


@[reducible]
def RegExp.State
  (α : Type) :
  RegExp α → Type
| char _ => ℕ
| epsilon => ℕ
| zero => ℕ
| union R S => R.State ⊕ S.State
| concat R S => R.State ⊕ S.State
| closure R => Option R.State


def RegExp.toEpsilonNFA
  {α : Type}
  (e : RegExp α) :
  EpsilonNFA α e.State :=
  match e with
  | char c =>
    {
      symbol_arrow_list := [⟨0, c, [1]⟩]
      epsilon_arrow_list := []
      starting_state_list := [0]
      accepting_state_list := [1]
    }

  | epsilon =>
    {
      symbol_arrow_list := []
      epsilon_arrow_list := [⟨0, [1]⟩]
      starting_state_list := [0]
      accepting_state_list := [1]
    }

  | zero =>
    {
      symbol_arrow_list := []
      epsilon_arrow_list := []
      starting_state_list := [0]
      accepting_state_list := []
    }

  | union R S =>
    let R' := R.toEpsilonNFA.wrapLeft S.State
    let S' := S.toEpsilonNFA.wrapRight R.State
    {
      symbol_arrow_list := R'.symbol_arrow_list ++ S'.symbol_arrow_list
      epsilon_arrow_list := R'.epsilon_arrow_list ++ S'.epsilon_arrow_list
      starting_state_list := R'.starting_state_list ++ S'.starting_state_list
      accepting_state_list := R'.accepting_state_list ++ S'.accepting_state_list
    }

  | concat R S =>
    let R' := R.toEpsilonNFA.wrapLeft S.State
    let S' := S.toEpsilonNFA.wrapRight R.State
    {
      symbol_arrow_list := R'.symbol_arrow_list ++ S'.symbol_arrow_list
      epsilon_arrow_list := R'.accepting_state_list.map (fun (state) => ⟨ state, S'.starting_state_list ⟩)
      starting_state_list := R'.starting_state_list
      accepting_state_list := S'.accepting_state_list
    }

  | closure R => sorry


@[simp]
def match_char_EpsilonNFA
  {α : Type}
  [DecidableEq α]
  (c : α) :
  EpsilonNFA α ℕ :=
  {
    symbol_arrow_list := [⟨0, c, [1]⟩]
    epsilon_arrow_list := []
    starting_state_list := [0]
    accepting_state_list := [1]
  }


example : (match_char_EpsilonNFA 'a').eval [] = [0] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['a'] = [1] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['b'] = [] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['a', 'b'] = [] := by rfl
example : (match_char_EpsilonNFA 'a').eval ['b', 'a'] = [] := by rfl


example : ¬ (match_char_EpsilonNFA 'a').accepts [] :=
  by decide


example : (match_char_EpsilonNFA 'a').accepts ['a'] :=
  by
    simp
    decide

example : ¬ (match_char_EpsilonNFA 'a').accepts ['b'] :=
  by decide


example : ¬ (match_char_EpsilonNFA 'a').accepts ['a', 'b'] :=
  by decide


example : ¬ (match_char_EpsilonNFA 'a').accepts ['b', 'a'] :=
  by decide


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x : α) :
  (match_char_EpsilonNFA c).accepts [x] ↔ c = x :=
  by
    by_cases c1 : c = x
    case pos =>
      simp only [c1]
      simp
      decide
    case neg =>
      simp
      simp only [c1]
      decide


example
  (α : Type)
  [DecidableEq α]
  (c : α)
  (x y : α) :
  ¬ (match_char_EpsilonNFA c).accepts [x, y] :=
  by
  by_cases c1 : c = x
  case pos =>
    simp only [c1]
    simp
    decide
  case neg =>
    simp
    split_ifs
    case pos c2 =>
      contradiction
    case neg c2 =>
      simp
      decide


def match_epsilon_EpsilonNFA
  (α : Type)
  [DecidableEq α] :
  EpsilonNFA α ℕ :=
  {
    symbol_arrow_list := []
    epsilon_arrow_list := [⟨0, [1]⟩]
    starting_state_list := [0]
    accepting_state_list := [1]
  }


example
  (α : Type)
  [DecidableEq α] :
  (match_epsilon_EpsilonNFA α).accepts [] :=
  by
    simp
    apply Exists.intro 1
    tauto


def match_zero_EpsilonNFA
  (α : Type)
  [DecidableEq α] :
  EpsilonNFA α ℕ :=
  {
    symbol_arrow_list := []
    epsilon_arrow_list := []
    starting_state_list := [0]
    accepting_state_list := []
  }


example
  (α : Type)
  [DecidableEq α]
  (xs : List α) :
  ¬ (match_zero_EpsilonNFA α).accepts xs :=
  by
    simp
    tauto


def match_union_EpsilonNFA
  {α : Type}
  [DecidableEq α]
  {σ_0 σ_1 : Type}
  [DecidableEq σ_0]
  [DecidableEq σ_1]
  (e1 : EpsilonNFA α σ_0)
  (e2 : EpsilonNFA α σ_1) :
  EpsilonNFA α (σ_0 ⊕ σ_1) :=
  -- The states of e1 need to be made disjoint from the states of e2. Therefore the states of e1 are made Sum.inl instances of (σ_0 ⊕ σ_1) and the states of e2 are made Sum.inr instances of (σ_0 ⊕ σ_1).
  let e1' := e1.wrapLeft σ_1
  let e2' := e2.wrapRight σ_0
  {
    symbol_arrow_list := e1'.symbol_arrow_list ++ e2'.symbol_arrow_list
    epsilon_arrow_list := e1'.epsilon_arrow_list ++ e2'.epsilon_arrow_list
    starting_state_list := e1'.starting_state_list ++ e2'.starting_state_list
    accepting_state_list := e1'.accepting_state_list ++ e2'.accepting_state_list
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
  by
    simp at *
    apply Exists.elim h1
    intro s a1
    clear h1
    left
    apply Exists.intro s
    cases a1
    case _ left right =>
      sorry


/-
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