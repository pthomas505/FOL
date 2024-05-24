import FOL.Computing.DFS


structure SymbolStepMultiple
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (start_state : σ)
  (symbol : α)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonStepMultiple
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (start_state : σ)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonStepSingle
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (start_state : σ)
  (stop_state : σ)
  deriving Repr


/--
  Translates an epsilon step that is from a single state to a list of states, to a list of epsilon steps that are each from a single state to a single state.
-/
def epsilon_step_multiple_to_single_list
  {σ : Type}
  [DecidableEq σ]
  (step : EpsilonStepMultiple σ) :
  List (EpsilonStepSingle σ) :=
  step.stop_state_list.map (fun (stop_state : σ) =>
    ⟨
      step.start_state,
      stop_state
    ⟩ )


/--
  Translates a list of epsilon steps that are each from a single state to a list of states, to a list of epsilon steps that are each from a single state to a single state.
-/
def epsilon_step_multiple_list_to_single_list
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepMultiple σ)) :
  List (EpsilonStepSingle σ) :=
  (step_list.map (fun (step : EpsilonStepMultiple σ) => epsilon_step_multiple_to_single_list step)).join


/--
  Translates a list of epsilon steps that are each from a single state to a single state, to an adjacency list representation of a graph.
-/
def epsilon_step_single_list_to_graph
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepSingle σ)) :
  Graph σ :=
    step_list.map (fun (step : (EpsilonStepSingle σ)) => (step.start_state, step.stop_state))


/--
  Translates a list of epsilon steps that are each from a single state to a list of states, to an adjacency list representation of a graph.
-/
def epsilon_step_multiple_list_to_graph
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepMultiple σ)) :
  Graph σ :=
  epsilon_step_single_list_to_graph (epsilon_step_multiple_list_to_single_list step_list)


/--
  Takes a list of epsilon steps that are each from a single state to a list of states and calculates the epsilon closure of a set of states with respect to the graph generated from the list of epsilon steps.
-/
def epsilon_closure
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStepMultiple σ))
  (state_list : List σ) :
  List σ :=
    dfs_aux (epsilon_step_multiple_list_to_graph epsilon_step_list) state_list []


/--
  Replaces the image of a symbol step with the epsilon closure of that image.
-/
def symbol_step_epsilon_closure
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStepMultiple σ))
  (symbol_step : SymbolStepMultiple α σ) :
  SymbolStepMultiple α σ :=
    ⟨
      symbol_step.start_state,
      symbol_step.symbol,
      epsilon_closure epsilon_step_list symbol_step.stop_state_list
    ⟩


structure EpsilonNFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (symbol_step_list : List (SymbolStepMultiple α σ))
  (epsilon_step_list : List (EpsilonStepMultiple σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


structure NFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (symbol_step_list : List (SymbolStepMultiple α σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


def SymbolStepMultiple.nodes_of
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step : SymbolStepMultiple α σ) :
  List σ :=
  { step.start_state } ∪ step.stop_state_list


def NFA.nodes_of
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ) :
  List σ :=
  (e.symbol_step_list.map SymbolStepMultiple.nodes_of).join


def NFA.symbols_of
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ) :
  List α :=
  (e.symbol_step_list.map (fun (step : SymbolStepMultiple α σ) => step.symbol))


def epsilon_nfa_to_nfa
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_nfa : EpsilonNFA α σ) :
  NFA α σ :=
  ⟨
    epsilon_nfa.symbol_step_list.map (symbol_step_epsilon_closure epsilon_nfa.epsilon_step_list),
    epsilon_closure epsilon_nfa.epsilon_step_list epsilon_nfa.starting_state_list,
    epsilon_nfa.accepting_state_list
  ⟩


#eval epsilon_nfa_to_nfa ⟨ [⟨0, 'a', [1]⟩], [⟨1, [2]⟩], [0], [1] ⟩

#eval epsilon_nfa_to_nfa ⟨ [⟨0, 'a', [1]⟩], [⟨1, [2]⟩, ⟨0, [2]⟩], [0], [1] ⟩

#eval epsilon_nfa_to_nfa ⟨ [⟨0, 'a', [1]⟩], [⟨1, [2]⟩, ⟨1, [2]⟩], [0], [1] ⟩

#eval epsilon_nfa_to_nfa ⟨ [⟨0, 'a', [1, 2]⟩], [⟨1, [2]⟩, ⟨0, [2]⟩], [0], [1] ⟩

#eval epsilon_nfa_to_nfa ⟨ [⟨0, 'a', [1, 2]⟩, ⟨1, 'b', [3]⟩], [⟨1, [2]⟩, ⟨2, [5]⟩], [0], [1] ⟩

#eval epsilon_nfa_to_nfa ⟨ [⟨0, 'a', [1, 2]⟩, ⟨1, 'b', [3]⟩], [⟨1, [2]⟩, ⟨2, [5]⟩], [0, 3, 3], [1] ⟩


/--
  The accumulated stop states of all of the steps in the list that have a start state and symbol matching the given state and symbol.
-/
def symbol_step_multiple_list_to_fun
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (SymbolStepMultiple α σ))
  (state : σ)
  (symbol : α) :
  List σ :=
  (step_list.filterMap (fun (step : SymbolStepMultiple α σ) =>
    if step.start_state = state ∧ step.symbol = symbol
    then Option.some step.stop_state_list
    else Option.none)).join


example : symbol_step_multiple_list_to_fun ([] : List (SymbolStepMultiple Char Nat)) 0 'a' == [] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩] 0 'a' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩] 0 'b' == [] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'a' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'b' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'a' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'b' == [2] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' == [1, 2] := by rfl


/--
  `NFA.eval_one e l c` := Returns the list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `l` and consumes the symbol `c`.
-/
def NFA.eval_one
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (state_list : List σ)
  (symbol : α) :
  List σ :=
  (state_list.map (fun (state : σ) => symbol_step_multiple_list_to_fun e.symbol_step_list state symbol)).join


def NFA.eval_from
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (starting_state_list : List σ) :
  List α → List σ :=
  List.foldl e.eval_one starting_state_list


/--
  `NFA.eval e cs` := Returns the final list of states that the nondeterministic automaton `e` transitions to if it starts at `e.starting_state_list` and consumes the list of symbols `cs`.
-/
def NFA.eval
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ) :
  List α → List σ :=
  e.eval_from e.starting_state_list


example : NFA.eval ⟨ [], [0], [1] ⟩ ['a'] == [] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩], [0], [1] ⟩ ['a'] == [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩], [0], [1] ⟩ ['b'] == [] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [0], [1] ⟩ ['a'] == [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [0], [1] ⟩ ['b'] == [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [0], [1] ⟩ ['a'] == [1] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [0], [1] ⟩ ['b'] == [2] := by rfl

example : NFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩], [0], [1] ⟩ ['a'] == [1, 2] := by rfl


def NFA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ e.eval input ∧ s ∈ e.accepting_state_list


instance
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : NFA α σ)
  (input : List α) :
  Decidable (e.accepts input) :=
  by
  induction input
  all_goals
    simp only [NFA.accepts]
    infer_instance
