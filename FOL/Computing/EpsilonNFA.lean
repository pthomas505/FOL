import FOL.Computing.DFT


set_option autoImplicit false


structure SymbolArrow
  (α : Type)
  (σ : Type) :
  Type :=
  (start_state : σ)
  (symbol : α)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonArrow
  (σ : Type) :
  Type :=
  (start_state : σ)
  (stop_state_list : List σ)
  deriving Repr


structure EpsilonNFA
  (α : Type)
  (σ : Type) :
  Type :=
  (symbol_arrow_list : List (SymbolArrow α σ))
  (epsilon_arrow_list : List (EpsilonArrow σ))
  (starting_state_list : List σ)
  (accepting_state_list : List σ)
  deriving Repr


@[simp]
def epsilon_arrow_list_to_graph
  {σ : Type} :
  List (EpsilonArrow σ) → Graph σ
  | [] => []
  | (hd :: tl) => (hd.start_state, hd.stop_state_list) :: epsilon_arrow_list_to_graph tl


@[simp]
def EpsilonNFA.epsilon_closure
  {α : Type}
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ) :
  List σ :=
  dft (epsilon_arrow_list_to_graph e.epsilon_arrow_list) state_list


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
    then Option.some arrow.stop_state_list
    else Option.none)).join.dedup


example : symbol_arrow_list_to_fun ([] : List (SymbolArrow Char Nat)) 0 'a' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩] 0 'b' = [] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩] 0 'b' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩] 0 'b' = [2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' = [1, 2] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [1]⟩] 0 'a' = [1] := by rfl

example : symbol_arrow_list_to_fun [⟨0, 'a', [1]⟩, ⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩] 0 'a' = [1, 2] := by rfl


/--
  `EpsilonNFA.eval_one e l c` := Returns the list of states that the nondeterministic automaton `e` transitions to if it starts at the list of states `l` and consumes the symbol `c`.
-/
@[simp]
def EpsilonNFA.eval_one
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (state_list : List σ)
  (symbol : α) :
  List σ :=
  e.epsilon_closure (state_list.map (fun (state : σ) => (symbol_arrow_list_to_fun e.symbol_arrow_list) state symbol)).join.dedup


@[simp]
def EpsilonNFA.eval_from
  {α : Type}
  [DecidableEq α]
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
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  List σ :=
  e.eval_from e.starting_state_list input


@[simp]
def EpsilonNFA.accepts
  {α : Type}
  [DecidableEq α]
  {σ : Type}
  [DecidableEq σ]
  (e : EpsilonNFA α σ)
  (input : List α) :
  Prop :=
  ∃ (s : σ), s ∈ e.eval input ∧ s ∈ e.accepting_state_list


instance
  {α : Type}
  [DecidableEq α]
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



example : EpsilonNFA.eval_from ⟨ [⟨0, 'a', [1]⟩], [⟨0, [1]⟩], [0], [1] ⟩ [] ([] : List Char) = [] := by rfl

example : EpsilonNFA.eval ⟨ [], [], [0], [1] ⟩ ([] : List Char) = [0] := by rfl

example : EpsilonNFA.eval ⟨ [], [], [0], [1] ⟩ ['a'] = [] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩], [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩], [], [0], [1] ⟩ ['b'] = [] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [1]⟩], [], [0], [1] ⟩ ['b'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [], [0], [1] ⟩ ['a'] = [1] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'b', [2]⟩], [], [0], [1] ⟩ ['b'] = [2] := by rfl

example : EpsilonNFA.eval ⟨ [⟨0, 'a', [1]⟩, ⟨0, 'a', [2]⟩], [], [0], [1] ⟩ ['a'] = [2, 1] := by rfl

example : EpsilonNFA.eval ⟨ [], [⟨ 0, [1] ⟩], [0], [1] ⟩ ([] : List Char) = [1, 0] := by rfl

example : EpsilonNFA.eval ⟨ [], [⟨ 0, [1]⟩], [0], [1] ⟩ ['a'] = [] := by rfl
