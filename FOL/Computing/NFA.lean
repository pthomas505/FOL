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
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (start_state : σ)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonStepSingle
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (start_state : σ)
  (stop_state : σ)
  deriving Repr


def epsilon_step_multiple_to_epsilon_step_single_list
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step : EpsilonStepMultiple α σ) :
  List (EpsilonStepSingle α σ) :=
  step.stop_state_list.map (fun (stop_state : σ) =>
    ⟨
      step.start_state,
      stop_state
    ⟩ )


def epsilon_step_multiple_list_to_epsilon_step_single_list
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepMultiple α σ)) :
  List (EpsilonStepSingle α σ) :=
  (step_list.map (fun (step : EpsilonStepMultiple α σ) => epsilon_step_multiple_to_epsilon_step_single_list step)).join


def epsilon_step_single_list_to_graph
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepSingle α σ)) :
  Graph σ :=
    step_list.map (fun (step : (EpsilonStepSingle α σ)) => (step.start_state, step.stop_state))


def epsilon_step_multiple_list_to_graph
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepMultiple α σ)) :
  Graph σ :=
  epsilon_step_single_list_to_graph (epsilon_step_multiple_list_to_epsilon_step_single_list step_list)


def epsilon_closure
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStepMultiple α σ))
  (state_list : List σ) :
  List σ :=
    dfs_aux (epsilon_step_multiple_list_to_graph epsilon_step_list) state_list []


def symbol_step_epsilon_closure
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStepMultiple α σ))
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
  (epsilon_step_list : List (EpsilonStepMultiple α σ))
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
