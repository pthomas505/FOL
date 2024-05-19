import FOL.Computing.DFS


structure SymbolStep
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (from_state : σ)
  (symbol : α)
  (to_state : σ)
  deriving Repr


structure EpsilonStep
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (from_state : σ)
  (to_state : σ)
  deriving Repr


structure NFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (symbol_step_list : List (SymbolStep α σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


structure EpsilonNFA
  (α : Type)
  [DecidableEq α]
  (σ : Type)
  [DecidableEq σ] :
  Type :=
  (symbol_step_list : List (SymbolStep α σ))
  (epsilon_step_list : List (EpsilonStep α σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


def epsilon_step_list_to_graph
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStep α σ)) :
  Graph σ :=
    epsilon_step_list.map (fun (step : (EpsilonStep α σ)) => (step.from_state, step.to_state))


def epsilon_closure
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStep α σ))
  (state_list : List σ) :
  List σ :=
    dfs_aux (epsilon_step_list_to_graph epsilon_step_list) state_list []


def symbol_step_epsilon_closure
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStep α σ))
  (symbol_step : SymbolStep α σ) :
  List (SymbolStep α σ) :=
  let to_state_list := epsilon_closure epsilon_step_list [symbol_step.to_state]

  to_state_list.map (fun (to_state : σ) =>
    ⟨
      symbol_step.from_state,
      symbol_step.symbol,
      to_state
    ⟩
  )


def symbol_step_list_epsilon_closure
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (epsilon_step_list : List (EpsilonStep α σ))
  (symbol_step_list : List (SymbolStep α σ)) :
  List (SymbolStep α σ) :=
  (symbol_step_list.map (fun (symbol_step : SymbolStep α σ) => symbol_step_epsilon_closure epsilon_step_list symbol_step)).join
