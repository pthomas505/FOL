import FOL.Computing.DFSList


set_option autoImplicit false


structure SymbolArrow
  (α : Type)
  (σ : Type) :
  Type :=
  (start_state : σ)
  (symbol : α)
  (stop_state : σ)
  deriving Repr


structure EpsilonArrow
  (σ : Type) :
  Type :=
  (start_state : σ)
  (stop_state : σ)
  deriving Repr


/--
  The accumulated stop states of all of the arrows in the list that have a start state and symbol matching the given state and symbol.
-/
@[simp]
def symbol_arrow_list_to_fun
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (symbol_arrow_list : List (SymbolArrow α σ))
  (start_state : σ)
  (symbol : α) :
  List σ :=
  (symbol_arrow_list.filterMap (fun (arrow : SymbolArrow α σ) =>
    if arrow.start_state = start_state ∧ arrow.symbol = symbol
    then Option.some arrow.stop_state
    else Option.none)).dedup


example : symbol_arrow_list_to_fun ([] : List (SymbolArrow Char Nat)) 0 'a' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩] 0 'b' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 1⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 1⟩] 0 'b' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 2⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 2⟩] 0 'b' = [2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'a', 2⟩] 0 'a' = [1, 2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'a', 1⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'a', 1⟩, ⟨0, 'a', 2⟩] 0 'a' = [1, 2] := by rfl


@[simp]
def epsilon_arrow_list_to_fun
  {σ : Type}
  [DecidableEq σ]
  (epsilon_arrow_list : List (EpsilonArrow σ))
  (start_state : σ) :
  List σ :=
  (epsilon_arrow_list.filterMap (fun (arrow : EpsilonArrow σ) =>
    if arrow.start_state = start_state
    then Option.some arrow.stop_state
    else Option.none)).dedup


def epsilon_arrow_fun_to_list
  {σ : Type}
  (epsilon_arrow_fun : σ → List σ)
  (state_list : List σ) :
  List (σ × List σ) :=
  state_list.map (fun (state : σ) => (state, epsilon_arrow_fun state))


structure EpsilonNFA
  (α : Type)
  (σ : Type) :
  Type :=
  (state_list : List σ)
  (symbol_arrow_fun : σ → α → List σ)
  (epsilon_arrow_fun : σ → List σ)
  (starting_state_list : List σ)
  (accepting_state_list : List σ)


@[simp]
def EpsilonNFA.epsilon_closure
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ) :
  List σ :=
  dfs (epsilon_arrow_fun_to_list e.epsilon_arrow_fun e.state_list) state_list


/--
  `EpsilonNFA.eval_one e l c` := Returns the list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `l` and consumes the symbol `c`.
-/
@[simp]
def EpsilonNFA.eval_one
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ)
  (symbol : α) :
  List σ :=
  e.epsilon_closure (state_list.map (fun (state : σ) => e.symbol_arrow_fun state symbol)).join.dedup


@[simp]
def EpsilonNFA.eval_from
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (starting_state_list : List σ)
  (input : List α) :
  List σ :=
  List.foldl e.eval_one (e.epsilon_closure starting_state_list) input


@[simp]
def EpsilonNFA.eval
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  List σ :=
  e.eval_from e.starting_state_list input


@[simp]
def EpsilonNFA.accepts
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ e.eval input ∧ s ∈ e.accepting_state_list


instance
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Decidable (e.accepts input) :=
  by
  induction input
  all_goals
    simp only [EpsilonNFA.accepts]
    infer_instance


example : EpsilonNFA.eval_from
  {
    state_list := ([0, 1] : List ℕ),
    symbol_arrow_fun := symbol_arrow_list_to_fun [⟨0, 'a', 1⟩],
    epsilon_arrow_fun := epsilon_arrow_list_to_fun [⟨0, 1⟩],starting_state_list := [0],
    accepting_state_list := [1]
  }
  []
  ([] : List Char) = [] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ([] : List Char) = [0] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['a'] = [] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['b'] = [] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 1⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 1⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['b'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1, 2], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 2⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1, 2], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'b', 2⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['b'] = [2] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1, 2], symbol_arrow_list_to_fun [⟨0, 'a', 1⟩, ⟨0, 'a', 2⟩], epsilon_arrow_list_to_fun [], [0], [1] ⟩ ['a'] = [2, 1] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [], epsilon_arrow_list_to_fun [⟨ 0, 1 ⟩], [0], [1] ⟩ ([] : List Char) = [1, 0] := by rfl

example : EpsilonNFA.eval ⟨ [0, 1], symbol_arrow_list_to_fun [], epsilon_arrow_list_to_fun [⟨ 0, 1 ⟩], [0], [1] ⟩ ['a'] = [] := by rfl
