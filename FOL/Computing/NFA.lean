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


def epsilon_step_multiple_to_single_list
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


def epsilon_step_multiple_list_to_single_list
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (EpsilonStepMultiple α σ)) :
  List (EpsilonStepSingle α σ) :=
  (step_list.map (fun (step : EpsilonStepMultiple α σ) => epsilon_step_multiple_to_single_list step)).join


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
  epsilon_step_single_list_to_graph (epsilon_step_multiple_list_to_single_list step_list)


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


/--
  Helper function for symbol_step_multiple_list_to_fun.
-/
def symbol_step_multiple_list_to_fun_aux
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (state_arg : σ)
  (symbol_arg : α)
  -- The accumulated results of all of the steps that have the state and symbol arguments as a pair.
  (image_acc : List σ) :
  List (SymbolStepMultiple α σ) → List σ
  | [] => List.dedup image_acc
  | ⟨ start_state, symbol, stop_state_list ⟩  :: tl =>
    let image : List σ :=
      if state_arg = start_state ∧ symbol_arg = symbol
      then stop_state_list
      else []
    symbol_step_multiple_list_to_fun_aux state_arg symbol_arg (image_acc ++ image) tl


/--
  Recursively iterates through the step list and returns the accumulated results of all of the steps that have the state and symbol arguments as a pair.
-/
def symbol_step_multiple_list_to_fun
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (step_list : List (SymbolStepMultiple α σ))
  (state_arg : σ)
  (symbol_arg : α) :
  List σ :=
  symbol_step_multiple_list_to_fun_aux state_arg symbol_arg [] step_list


example : symbol_step_multiple_list_to_fun ([] : List (SymbolStepMultiple Char Nat)) 0 'a' == [] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩] 0 'a' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩] 0 'b' == [] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'a' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'b' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'a' == [1] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'b' == [2] := by rfl

example : symbol_step_multiple_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' == [1, 2] := by rfl
